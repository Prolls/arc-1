/**
 * Runtime diagnostics for SAP ADT.
 *
 * - Short dumps (ST22): list and read ABAP runtime errors
 * - ABAP traces: list and analyze profiler trace files
 * - Source diff: client-side unified diff between two revision sources
 *
 * All operations are read-only (GET requests).
 * Follows the same pure-function pattern as devtools.ts.
 */

import { createHash } from 'node:crypto';
import { AdtApiError } from './errors.js';
import type { AdtHttpClient } from './http.js';
import { checkOperation, OperationType, type SafetyConfig } from './safety.js';
import type {
  DumpChapter,
  DumpDetail,
  DumpEntry,
  GatewayCallStackEntry,
  GatewayErrorDetail,
  GatewayErrorEntry,
  GatewayExceptionInfo,
  GatewayServiceInfo,
  GatewaySourceLine,
  ObjectStateResult,
  ObjectStateSection,
  ObjectStateSourceVersion,
  SystemMessageEntry,
  TraceDbAccess,
  TraceEntry,
  TraceHitlistEntry,
  TraceStatement,
} from './types.js';
import { findDeepNodes, parseXml } from './xml-parser.js';

// ─── Source Diff ────────────────────────────────────────────────────

export interface DiffOptions {
  /** ADT path or "active"/"inactive" */
  version1: string;
  /** ADT path or "active"/"inactive" */
  version2: string;
  /** Base source URL for the object (e.g. /sap/bc/adt/programs/programs/ZPROG/source/main) */
  sourceUrl: string;
  /** Human-readable label for version1 (defaults to version1 value) */
  label1?: string;
  /** Human-readable label for version2 (defaults to version2 value) */
  label2?: string;
}

export interface DiffResult {
  label1: string;
  label2: string;
  /** Unified diff text (empty string when sources are identical) */
  diff: string;
  identical: boolean;
  /** Lines added in version2 relative to version1 */
  addedLines: number;
  /** Lines removed from version1 */
  removedLines: number;
}

/**
 * Compute a unified diff between two versions of an ABAP object source.
 *
 * Both versions are fetched in parallel. "active" and "inactive" are resolved
 * via the ?version= query param on the source URL; explicit ADT URIs are
 * fetched directly (as returned by SAPRead type=VERSIONS .revisions[].uri).
 *
 * ADT has no server-side diff endpoint — the diff is computed client-side.
 */
export async function diffObjectVersions(
  http: AdtHttpClient,
  safety: SafetyConfig,
  options: DiffOptions,
): Promise<DiffResult> {
  checkOperation(safety, OperationType.Read, 'DiffObjectVersions');

  const [src1, src2] = await Promise.all([
    fetchVersionSource(http, options.sourceUrl, options.version1),
    fetchVersionSource(http, options.sourceUrl, options.version2),
  ]);

  const label1 = options.label1 ?? options.version1;
  const label2 = options.label2 ?? options.version2;

  if (src1 === src2) {
    return { label1, label2, diff: '', identical: true, addedLines: 0, removedLines: 0 };
  }

  const { diff, addedLines, removedLines } = computeUnifiedDiff(src1, src2, label1, label2);
  return { label1, label2, diff, identical: false, addedLines, removedLines };
}

async function fetchVersionSource(http: AdtHttpClient, sourceUrl: string, version: string): Promise<string> {
  // Explicit ADT URI (from VERSIONS feed) — fetch directly
  if (version.startsWith('/sap/bc/adt/')) {
    const resp = await http.get(version, { Accept: 'text/plain' });
    return resp.body;
  }
  // "active" or "inactive" — append ?version= to the source URL
  const url = appendQueryParam(sourceUrl, 'version', version);
  const resp = await http.get(url, { Accept: 'text/plain, */*;q=0.8' });
  return resp.body;
}

/**
 * Generate a unified diff between two source strings.
 * Pure function — no external dependencies.
 */
export function computeUnifiedDiff(
  source1: string,
  source2: string,
  label1: string,
  label2: string,
  contextLines = 3,
): { diff: string; addedLines: number; removedLines: number } {
  const lines1 = source1.split('\n');
  const lines2 = source2.split('\n');

  const lcs = computeLcs(lines1, lines2);
  const hunks = buildHunks(lines1, lines2, lcs, contextLines);

  if (hunks.length === 0) {
    return { diff: '', addedLines: 0, removedLines: 0 };
  }

  let addedLines = 0;
  let removedLines = 0;
  const parts: string[] = [`--- ${label1}`, `+++ ${label2}`];

  for (const hunk of hunks) {
    const oldStart = hunk.oldStart + 1;
    const newStart = hunk.newStart + 1;
    parts.push(`@@ -${oldStart},${hunk.oldCount} +${newStart},${hunk.newCount} @@`);
    for (const line of hunk.lines) {
      parts.push(line);
      if (line.startsWith('+')) addedLines++;
      else if (line.startsWith('-')) removedLines++;
    }
  }

  return { diff: parts.join('\n'), addedLines, removedLines };
}

interface Hunk {
  oldStart: number;
  oldCount: number;
  newStart: number;
  newCount: number;
  lines: string[];
}

/**
 * Myers-style LCS via dynamic programming.
 * Returns an array of [i, j] pairs where lines1[i] === lines2[j].
 */
function computeLcs(lines1: string[], lines2: string[]): Array<[number, number]> {
  const m = lines1.length;
  const n = lines2.length;

  // dp[i][j] = length of LCS of lines1[0..i-1] and lines2[0..j-1]
  const dp: number[][] = Array.from({ length: m + 1 }, () => new Array(n + 1).fill(0));

  for (let i = 1; i <= m; i++) {
    for (let j = 1; j <= n; j++) {
      if (lines1[i - 1] === lines2[j - 1]) {
        dp[i]![j] = dp[i - 1]![j - 1]! + 1;
      } else {
        dp[i]![j] = Math.max(dp[i - 1]![j]!, dp[i]![j - 1]!);
      }
    }
  }

  // Backtrack to find the actual matching pairs
  const matches: Array<[number, number]> = [];
  let i = m;
  let j = n;
  while (i > 0 && j > 0) {
    if (lines1[i - 1] === lines2[j - 1]) {
      matches.push([i - 1, j - 1]);
      i--;
      j--;
    } else if (dp[i - 1]![j]! >= dp[i]![j - 1]!) {
      i--;
    } else {
      j--;
    }
  }
  return matches.reverse();
}

function buildHunks(lines1: string[], lines2: string[], lcs: Array<[number, number]>, contextLines: number): Hunk[] {
  // Build a flat edit list: context / removed / added
  interface Edit {
    type: 'context' | 'removed' | 'added';
    i: number; // index in lines1 (for context/removed)
    j: number; // index in lines2 (for context/added)
    text: string;
  }

  const edits: Edit[] = [];
  let i1 = 0;
  let i2 = 0;

  for (const [li, lj] of lcs) {
    while (i1 < li) {
      edits.push({ type: 'removed', i: i1, j: -1, text: lines1[i1]! });
      i1++;
    }
    while (i2 < lj) {
      edits.push({ type: 'added', i: -1, j: i2, text: lines2[i2]! });
      i2++;
    }
    edits.push({ type: 'context', i: i1, j: i2, text: lines1[i1]! });
    i1++;
    i2++;
  }
  while (i1 < lines1.length) {
    edits.push({ type: 'removed', i: i1, j: -1, text: lines1[i1]! });
    i1++;
  }
  while (i2 < lines2.length) {
    edits.push({ type: 'added', i: -1, j: i2, text: lines2[i2]! });
    i2++;
  }

  // Group edits into hunks with context
  const hunks: Hunk[] = [];
  const changeIndices = edits.map((e, idx) => (e.type !== 'context' ? idx : -1)).filter((idx) => idx >= 0);

  if (changeIndices.length === 0) return [];

  // Merge nearby changes into a single hunk window
  const windows: Array<[number, number]> = [];
  let start = Math.max(0, changeIndices[0]! - contextLines);
  let end = Math.min(edits.length - 1, changeIndices[0]! + contextLines);

  for (let k = 1; k < changeIndices.length; k++) {
    const nextStart = Math.max(0, changeIndices[k]! - contextLines);
    if (nextStart <= end + 1) {
      end = Math.min(edits.length - 1, changeIndices[k]! + contextLines);
    } else {
      windows.push([start, end]);
      start = nextStart;
      end = Math.min(edits.length - 1, changeIndices[k]! + contextLines);
    }
  }
  windows.push([start, end]);

  for (const [ws, we] of windows) {
    const slice = edits.slice(ws, we + 1);
    const hunkLines: string[] = [];
    let oldCount = 0;
    let newCount = 0;
    let oldStart = -1;
    let newStart = -1;

    for (const edit of slice) {
      if (edit.type === 'context') {
        if (oldStart < 0) oldStart = edit.i;
        if (newStart < 0) newStart = edit.j;
        hunkLines.push(` ${edit.text}`);
        oldCount++;
        newCount++;
      } else if (edit.type === 'removed') {
        if (oldStart < 0) oldStart = edit.i;
        hunkLines.push(`-${edit.text}`);
        oldCount++;
      } else {
        if (newStart < 0) newStart = edit.j;
        hunkLines.push(`+${edit.text}`);
        newCount++;
      }
    }

    hunks.push({
      oldStart: oldStart < 0 ? 0 : oldStart,
      oldCount,
      newStart: newStart < 0 ? 0 : newStart,
      newCount,
      lines: hunkLines,
    });
  }

  return hunks;
}

// ─── Short Dumps ────────────────────────────────────────────────────

const DEFAULT_DUMP_MAX_RESULTS = 50;
const DEFAULT_SYSTEM_MESSAGE_MAX_RESULTS = 50;
const DEFAULT_GATEWAY_ERROR_MAX_RESULTS = 50;
const MAX_RESULTS_CAP = 200;

export interface ListDumpsOptions {
  /** Filter by SAP user (uppercase) */
  user?: string;
  /** Maximum number of dumps to return (default 50) */
  maxResults?: number;
}

interface FeedQueryOptions {
  user?: string;
  maxResults?: number;
  from?: string;
  to?: string;
}

export interface ListSystemMessagesOptions extends FeedQueryOptions {}

export interface ListGatewayErrorsOptions extends FeedQueryOptions {}

export interface ObjectStateSectionInput {
  section: string;
  uri: string;
  /** Treat missing endpoints as unavailable instead of failing the whole diagnostic */
  optional?: boolean;
}

export interface GetObjectStateOptions {
  type: string;
  name: string;
  sections: ObjectStateSectionInput[];
}

/**
 * Compare active and inactive source versions for one ADT object.
 *
 * ARC-1 uses this as a compact diagnostic for activation mysteries where
 * SAPRead "looks right" but the activator still sees stale or divergent
 * source includes. The result intentionally returns hashes and byte counts,
 * not full source, so the diagnostic stays cheap and safe to paste into chat.
 */
export async function getObjectState(
  http: AdtHttpClient,
  safety: SafetyConfig,
  options: GetObjectStateOptions,
): Promise<ObjectStateResult> {
  checkOperation(safety, OperationType.Read, 'GetObjectState');

  const sections = await Promise.all(
    options.sections.map(async (input): Promise<ObjectStateSection> => {
      const [active, inactive] = await Promise.all([
        readObjectStateVersion(http, input.uri, 'active', input.optional),
        readObjectStateVersion(http, input.uri, 'inactive', input.optional),
      ]);

      return {
        section: input.section,
        uri: input.uri,
        active,
        inactive,
        divergent: sourceVersionsDiverge(active, inactive),
      };
    }),
  );

  return {
    type: options.type,
    name: options.name,
    checkedAt: new Date().toISOString(),
    hasInactiveDivergence: sections.some((section) => section.divergent),
    sections,
  };
}

async function readObjectStateVersion(
  http: AdtHttpClient,
  uri: string,
  version: 'active' | 'inactive',
  optional = false,
): Promise<ObjectStateSourceVersion> {
  const versionedUri = appendQueryParam(uri, 'version', version);
  try {
    const resp = await http.get(versionedUri, {
      Accept: 'text/plain, */*;q=0.8',
    });
    return {
      available: true,
      statusCode: resp.statusCode,
      etag: resp.headers.etag,
      byteLength: Buffer.byteLength(resp.body, 'utf8'),
      sha256: createHash('sha256').update(resp.body, 'utf8').digest('hex'),
    };
  } catch (err) {
    if (optional && err instanceof AdtApiError && err.statusCode === 404) {
      return {
        available: false,
        statusCode: 404,
      };
    }
    throw err;
  }
}

function sourceVersionsDiverge(active: ObjectStateSourceVersion, inactive: ObjectStateSourceVersion): boolean {
  if (active.available !== inactive.available) return true;
  if (!active.available || !inactive.available) return false;
  return active.sha256 !== inactive.sha256;
}

function appendQueryParam(path: string, key: string, value: string): string {
  const [baseAndQuery, fragment] = path.split('#', 2);
  const [base, query = ''] = (baseAndQuery ?? path).split('?', 2);
  const params = new URLSearchParams(query);
  params.set(key, value);
  const queryString = params.toString();
  return `${base}${queryString ? `?${queryString}` : ''}${fragment ? `#${fragment}` : ''}`;
}

/**
 * List ABAP short dumps (ST22 equivalent).
 *
 * Endpoint: GET /sap/bc/adt/runtime/dumps
 * Returns an Atom feed with dump entries.
 */
export async function listDumps(
  http: AdtHttpClient,
  safety: SafetyConfig,
  options?: ListDumpsOptions,
): Promise<DumpEntry[]> {
  checkOperation(safety, OperationType.Read, 'ListDumps');

  const queryString = buildFeedQueryString(options, DEFAULT_DUMP_MAX_RESULTS, 'user');
  const resp = await http.get(`/sap/bc/adt/runtime/dumps${queryString}`, {
    Accept: 'application/atom+xml;type=feed',
  });

  return parseDumpList(resp.body);
}

/**
 * Get full dump detail including formatted text.
 *
 * Makes two requests:
 * 1. XML metadata (chapters, links, attributes)
 * 2. Formatted plain text (full dump content)
 *
 * The dump ID from `listDumps` already arrives URL-encoded (the SAP feed
 * encodes spaces in the server/user/client/dump-number suffix as `%20`).
 * When a caller passes a raw ID (e.g. copied from ST22 with literal
 * whitespace), we encode it ourselves so the path stays valid. The
 * detail payload keeps the caller's original ID for round-tripping.
 */
export async function getDump(http: AdtHttpClient, safety: SafetyConfig, dumpId: string): Promise<DumpDetail> {
  checkOperation(safety, OperationType.Read, 'GetDump');

  const safeId = normalizeDumpId(dumpId);

  // Fetch XML metadata and formatted text in parallel
  const [xmlResp, textResp] = await Promise.all([
    http.get(`/sap/bc/adt/runtime/dump/${safeId}`, {
      Accept: 'application/vnd.sap.adt.runtime.dump.v1+xml',
    }),
    http.get(`/sap/bc/adt/runtime/dump/${safeId}/formatted`, {
      Accept: 'text/plain',
    }),
  ]);

  return parseDumpDetail(xmlResp.body, textResp.body, dumpId);
}

/**
 * Idempotently URL-encode a dump ID. If the value already contains a `%`
 * sequence we treat it as already-encoded (the listing endpoint emits
 * `%20` for spaces); otherwise we encode it once. Trims surrounding
 * whitespace which would otherwise be encoded as `%20` and break lookup.
 */
function normalizeDumpId(dumpId: string): string {
  const trimmed = String(dumpId ?? '').trim();
  if (!trimmed) return '';
  return trimmed.includes('%') ? trimmed : encodeURIComponent(trimmed);
}

// ─── System Messages + Gateway Errors ──────────────────────────────

/**
 * List SM02 system messages.
 *
 * Endpoint: GET /sap/bc/adt/runtime/systemmessages
 * Returns an Atom feed with system message entries.
 */
export async function listSystemMessages(
  http: AdtHttpClient,
  safety: SafetyConfig,
  options?: ListSystemMessagesOptions,
): Promise<SystemMessageEntry[]> {
  checkOperation(safety, OperationType.Read, 'ListSystemMessages');

  const queryString = buildFeedQueryString(options, DEFAULT_SYSTEM_MESSAGE_MAX_RESULTS, 'user');
  const resp = await http.get(`/sap/bc/adt/runtime/systemmessages${queryString}`, {
    Accept: 'application/atom+xml;type=feed',
  });

  return parseSystemMessages(resp.body);
}

/**
 * List SAP Gateway error log entries (/IWFND/ERROR_LOG).
 *
 * Endpoint: GET /sap/bc/adt/gw/errorlog
 * Returns an Atom feed with gateway error entries.
 */
export async function listGatewayErrors(
  http: AdtHttpClient,
  safety: SafetyConfig,
  options?: ListGatewayErrorsOptions,
): Promise<GatewayErrorEntry[]> {
  checkOperation(safety, OperationType.Read, 'ListGatewayErrors');

  const queryString = buildFeedQueryString(options, DEFAULT_GATEWAY_ERROR_MAX_RESULTS, 'username');
  const resp = await http.get(`/sap/bc/adt/gw/errorlog${queryString}`, {
    Accept: 'application/atom+xml;type=feed',
  });

  return parseGatewayErrors(resp.body);
}

/**
 * Read one gateway error detail payload.
 *
 * The ADT /sap/bc/adt/gw/errorlog/{type}/{id} endpoint returns an HTML
 * fragment (not XML), so the parser extracts tabular values from known
 * section anchors (#HEADER, #SERVICE, #CONTEXT, #SOURCE, #STACK).
 *
 * Supports either:
 * - full/relative ADT detail URL from a feed entry,
 * - id of the form "{errorType}/{transactionId}" (as emitted by the feed), or
 * - transaction id + errorType parameters.
 */
export async function getGatewayErrorDetail(
  http: AdtHttpClient,
  safety: SafetyConfig,
  params: { detailUrl?: string; id?: string; errorType?: string },
): Promise<GatewayErrorDetail> {
  checkOperation(safety, OperationType.Read, 'GetGatewayErrorDetail');

  const path = resolveGatewayErrorDetailPath(params);
  const resp = await http.get(path, {
    Accept: 'text/html, application/xhtml+xml, application/xml;q=0.5',
  });

  return parseGatewayErrorDetail(resp.body);
}

// ─── ABAP Traces ────────────────────────────────────────────────────

/**
 * List ABAP profiler trace files.
 *
 * Endpoint: GET /sap/bc/adt/runtime/traces/abaptraces
 * Returns an Atom feed with trace entries.
 */
export async function listTraces(http: AdtHttpClient, safety: SafetyConfig): Promise<TraceEntry[]> {
  checkOperation(safety, OperationType.Read, 'ListTraces');

  const resp = await http.get('/sap/bc/adt/runtime/traces/abaptraces', {
    Accept: 'application/atom+xml;type=feed',
  });

  return parseTraceList(resp.body);
}

/**
 * Get trace hitlist (execution hot spots).
 *
 * Returns the most expensive procedures sorted by gross time.
 */
export async function getTraceHitlist(
  http: AdtHttpClient,
  safety: SafetyConfig,
  traceId: string,
): Promise<TraceHitlistEntry[]> {
  checkOperation(safety, OperationType.Read, 'GetTraceHitlist');

  const resp = await http.get(`/sap/bc/adt/runtime/traces/abaptraces/${traceId}/hitlist`, {
    Accept: 'application/xml',
  });

  return parseTraceHitlist(resp.body);
}

/**
 * Get trace call tree (statements).
 *
 * Returns the hierarchical call tree with timing data.
 */
export async function getTraceStatements(
  http: AdtHttpClient,
  safety: SafetyConfig,
  traceId: string,
): Promise<TraceStatement[]> {
  checkOperation(safety, OperationType.Read, 'GetTraceStatements');

  const resp = await http.get(`/sap/bc/adt/runtime/traces/abaptraces/${traceId}/statements`, {
    Accept: 'application/xml',
  });

  return parseTraceStatements(resp.body);
}

/**
 * Get trace database accesses.
 *
 * Returns table access statistics (which tables, how many times, buffered vs not).
 */
export async function getTraceDbAccesses(
  http: AdtHttpClient,
  safety: SafetyConfig,
  traceId: string,
): Promise<TraceDbAccess[]> {
  checkOperation(safety, OperationType.Read, 'GetTraceDbAccesses');

  const resp = await http.get(`/sap/bc/adt/runtime/traces/abaptraces/${traceId}/dbAccesses`, {
    Accept: 'application/xml',
  });

  return parseTraceDbAccesses(resp.body);
}

// ─── Parsers ────────────────────────────────────────────────────────

/**
 * Parse dump listing Atom feed.
 *
 * Robust against localized category labels and missing self links.
 */
export function parseDumpList(xml: string): DumpEntry[] {
  const parsed = parseXml(xml);
  const entryNodes = findDeepNodes(parsed, 'entry');

  return entryNodes
    .map((entry) => {
      const author = toRecordArray(entry.author)[0];
      const user = String(author?.name ?? '');

      const categories = toRecordArray(entry.category);
      const { error, program } = parseDumpCategories(categories);

      const timestamp = String(entry.published ?? entry.updated ?? '');
      const id = extractDumpId(entry);

      return { id, timestamp, user, error, program };
    })
    .filter((entry) => entry.id.length > 0);
}

/**
 * Parse dump detail XML metadata + formatted text.
 *
 * The XML response has attributes on the root dump:dump element:
 * - error, author, exception, terminatedProgram, datetime
 *
 * And dump:chapter elements with name, title, category attributes.
 */
export function parseDumpDetail(xml: string, formattedText: string, dumpId: string): DumpDetail {
  const parsed = parseXml(xml);
  const dumps = findDeepNodes(parsed, 'dump');
  const root = dumps[0] ?? {};

  const error = String(root['@_error'] ?? '');
  const exception = String(root['@_exception'] ?? '');
  const program = String(root['@_terminatedProgram'] ?? '');
  const user = String(root['@_author'] ?? '');
  const timestamp = String(root['@_datetime'] ?? '');

  // Find termination link by relation attribute (scope to dump root, not full document)
  const links = findDeepNodes(root, 'link');
  const termLink = links.find(
    (l) => String(l['@_relation'] ?? '') === 'http://www.sap.com/adt/relations/runtime/dump/termination',
  );
  const terminationUri = termLink ? String(termLink['@_uri'] ?? '') || undefined : undefined;

  // Extract chapters (scope to dump root, not full document)
  const chapterNodes = findDeepNodes(root, 'chapter');
  const chapters: DumpChapter[] = chapterNodes.map((ch) => ({
    name: String(ch['@_name'] ?? ''),
    title: String(ch['@_title'] ?? ''),
    category: String(ch['@_category'] ?? ''),
    line: safePositiveInt(ch['@_line']),
    chapterOrder: safePositiveInt(ch['@_chapterOrder']),
    categoryOrder: safePositiveInt(ch['@_categoryOrder']),
  }));
  const sections = splitDumpSections(formattedText, chapters);

  return {
    id: dumpId,
    error,
    exception,
    program,
    user,
    timestamp,
    chapters,
    formattedText,
    sections,
    terminationUri,
  };
}

/**
 * Parse system message feed.
 */
export function parseSystemMessages(xml: string): SystemMessageEntry[] {
  const parsed = parseXml(xml);
  const entryNodes = findDeepNodes(parsed, 'entry');

  return entryNodes
    .map((entry) => {
      const links = toRecordArray(entry.link);
      const selfHref = extractSelfLinkHref(links);
      const categories = toRecordArray(entry.category);
      const severity = String(categories[0]?.['@_term'] ?? '');

      const contentNode = toRecordArray(entry.content)[0];
      const summaryNode = toRecordArray(entry.summary)[0];

      return {
        id: String(entry.id ?? ''),
        title: String(entry.title ?? ''),
        text: String(contentNode?.['#text'] ?? summaryNode?.['#text'] ?? entry.summary ?? ''),
        severity,
        validFrom: String(entry['@_validFrom'] ?? entry.validFrom ?? entry.updated ?? entry.published ?? ''),
        validTo: String(entry['@_validTo'] ?? entry.validTo ?? ''),
        createdBy: String(toRecordArray(entry.author)[0]?.name ?? ''),
        timestamp: String(entry.updated ?? entry.published ?? ''),
        detailUrl: selfHref || undefined,
      };
    })
    .filter((entry) => entry.id.length > 0 || entry.title.length > 0 || entry.text.length > 0);
}

/**
 * Parse gateway error log feed.
 *
 * Real ADT feed entries encode the error class + transaction id in
 * <atom:id>ErrorClass/transactionId</atom:id>, the full label in
 * <atom:title>Type: short text</atom:title>, and the structured payload in
 * the <atom:summary type="html"> HTML blob (same content the detail
 * endpoint returns). No <atom:category> or <atom:link rel="self"> is
 * emitted, so the parser derives the detail URL from the atom:id and
 * extracts header fields from the summary HTML when available.
 */
export function parseGatewayErrors(xml: string): GatewayErrorEntry[] {
  const parsed = parseXml(xml);
  const entryNodes = findDeepNodes(parsed, 'entry');

  return entryNodes
    .map((entry) => {
      const atomId = String(entry.id ?? '');
      const rawTitle = String(entry.title ?? '').trim();
      const summaryHtml = extractEntrySummaryHtml(entry);
      const { errorType: idErrorType, transactionId: idTransactionId } = splitGatewayAtomId(atomId);

      const links = toRecordArray(entry.link);
      const selfHref = extractSelfLinkHref(links);

      // Legacy / forward-compat: some feeds may expose <atom:category term="Frontend Error"/>
      const categoryTerm = String(toRecordArray(entry.category)[0]?.['@_term'] ?? '').trim();

      // Multi-source derivation so one missing field does not lose everything.
      const summaryType = extractHtmlHeaderValue(summaryHtml, 'Type');
      const titleType = rawTitle.includes(':') ? rawTitle.slice(0, rawTitle.indexOf(':')).trim() : '';
      const typeFromId = splitCamelCase(idErrorType);
      const type = summaryType || categoryTerm || titleType || typeFromId;

      const summaryShortText = extractHtmlHeaderValue(summaryHtml, 'Short Text');
      const titleShortText = rawTitle.includes(':') ? rawTitle.slice(rawTitle.indexOf(':') + 1).trim() : rawTitle;
      const shortText = summaryShortText || titleShortText;

      const summaryTransactionId = extractTransactionIdFromHtml(summaryHtml);
      const transactionId = summaryTransactionId || idTransactionId || extractTailId(atomId);

      const detailUrl =
        selfHref ||
        (idErrorType && idTransactionId
          ? `/sap/bc/adt/gw/errorlog/${encodeURIComponent(idErrorType)}/${encodeURIComponent(idTransactionId)}`
          : '');

      return {
        type,
        shortText,
        transactionId,
        dateTime: String(entry.updated ?? entry.published ?? ''),
        username: String(toRecordArray(entry.author)[0]?.name ?? ''),
        detailUrl,
        package:
          getOptionalString(entry, ['@_package', 'package']) ??
          (extractHtmlHeaderValue(summaryHtml, 'Package') || undefined),
        applicationComponent:
          getOptionalString(entry, ['@_applicationComponent', 'applicationComponent']) ??
          (extractHtmlHeaderValue(summaryHtml, 'Application Component') || undefined),
        client:
          getOptionalString(entry, ['@_client', 'client']) ??
          (extractHtmlHeaderValue(summaryHtml, 'Client') || undefined),
        requestKind:
          getOptionalString(entry, ['@_requestKind', 'requestKind']) ??
          (extractHtmlHeaderValue(summaryHtml, 'Request Kind') || undefined),
      };
    })
    .filter((entry) => entry.transactionId.length > 0 || entry.detailUrl.length > 0);
}

/**
 * Parse gateway error detail payload.
 *
 * Accepts either the legacy XML envelope (with <errorEntry>) if the backend
 * ever returns one, or the HTML fragment that the real /sap/bc/adt/gw/errorlog
 * endpoint returns. Missing sections fall back to empty values rather than
 * throwing, so callers can still surface partial data to the LLM.
 */
export function parseGatewayErrorDetail(payload: string): GatewayErrorDetail {
  const trimmed = (payload ?? '').trim();
  const looksLikeXmlEnvelope = trimmed.startsWith('<?xml') || /<errorEntry[\s>]/.test(trimmed);

  if (looksLikeXmlEnvelope) {
    const xmlResult = parseGatewayErrorDetailXml(trimmed);
    if (xmlResult) return xmlResult;
  }

  return parseGatewayErrorDetailHtml(trimmed);
}

function parseGatewayErrorDetailXml(xml: string): GatewayErrorDetail | undefined {
  try {
    const parsed = parseXml(xml);
    const errorNode = findDeepNodes(parsed, 'errorEntry')[0];
    if (!errorNode) return undefined;

    const callStackEntries = parseGatewayCallStack(errorNode);
    const sourceLines = parseGatewaySourceLines(errorNode);
    const exceptions = parseGatewayExceptions(errorNode);

    const serviceInfoNode = toRecordArray(errorNode.serviceInfo)[0];
    const errorContextNode = toRecordArray(errorNode.errorContext)[0];
    const sourceCodeNode = toRecordArray(errorNode.sourceCode)[0];

    const serviceInfo: GatewayServiceInfo = {
      namespace: String(serviceInfoNode?.['@_namespace'] ?? ''),
      serviceName: String(serviceInfoNode?.['@_serviceName'] ?? ''),
      serviceVersion: String(serviceInfoNode?.['@_serviceVersion'] ?? ''),
      groupId: String(serviceInfoNode?.['@_groupId'] ?? ''),
      serviceRepository: String(serviceInfoNode?.['@_serviceRepository'] ?? ''),
      destination: String(serviceInfoNode?.['@_destination'] ?? ''),
    };

    return {
      type: String(errorNode['@_type'] ?? ''),
      shortText: String(errorNode.shortText ?? ''),
      transactionId: String(errorNode.transactionId ?? ''),
      package: String(errorNode.package ?? ''),
      applicationComponent: String(errorNode.applicationComponent ?? ''),
      dateTime: String(errorNode.dateTime ?? ''),
      username: String(errorNode.username ?? ''),
      client: String(errorNode.client ?? ''),
      requestKind: String(errorNode.requestKind ?? ''),
      serviceInfo,
      errorContext: {
        errorInfo: String(errorContextNode?.errorInfo ?? ''),
        resolution: {},
        exceptions,
      },
      sourceCode: {
        lines: sourceLines,
        errorLine: safePositiveInt(sourceCodeNode?.['@_errorLine']),
      },
      callStack: callStackEntries,
    };
  } catch {
    return undefined;
  }
}

function parseGatewayErrorDetailHtml(html: string): GatewayErrorDetail {
  const header = extractHtmlSection(html, 'HEADER');
  const service = extractHtmlSection(html, 'SERVICE');
  const context = extractHtmlSection(html, 'CONTEXT');
  const source = extractHtmlSection(html, 'SOURCE');
  const stack = extractHtmlSection(html, 'STACK');

  const resolution: Record<string, string> = {};
  const sapNote = extractHtmlHeaderValue(context, 'SAP_NOTE');
  if (sapNote) resolution.sapNote = sapNote;
  const sapNoteLink = extractHtmlHeaderValue(context, 'LINK_TO_SAP_NOTE');
  if (sapNoteLink) resolution.linkToSapNote = sapNoteLink;

  return {
    type: extractHtmlHeaderValue(header, 'Type'),
    shortText: extractHtmlHeaderValue(header, 'Short Text'),
    transactionId: extractTransactionIdFromHtml(header),
    package: extractHtmlHeaderValue(header, 'Package'),
    applicationComponent: extractHtmlHeaderValue(header, 'Application Component'),
    dateTime: extractHtmlHeaderValue(header, 'Date/Time'),
    username: extractHtmlHeaderValue(header, 'Username'),
    client: extractHtmlHeaderValue(header, 'Client'),
    requestKind: extractHtmlHeaderValue(header, 'Request Kind'),
    serviceInfo: {
      namespace: extractHtmlHeaderValue(service, 'Service Namespace'),
      serviceName: extractHtmlHeaderValue(service, 'Service Name'),
      serviceVersion: extractHtmlHeaderValue(service, 'Service Version'),
      groupId: extractHtmlHeaderValue(service, 'Group ID'),
      serviceRepository: extractHtmlHeaderValue(service, 'Service Repository'),
      destination: extractHtmlHeaderValue(service, 'Destination'),
    },
    errorContext: {
      errorInfo: extractHtmlHeaderValue(context, 'ERROR_INFO'),
      resolution,
      exceptions: extractGatewayExceptionsFromHtml(context),
    },
    sourceCode: extractGatewaySourceFromHtml(source),
    callStack: extractGatewayCallStackFromHtml(stack),
  };
}

/**
 * Parse trace listing Atom feed.
 *
 * Trace entries may contain extended attributes in a trc: namespace.
 */
export function parseTraceList(xml: string): TraceEntry[] {
  const parsed = parseXml(xml);
  const entryNodes = findDeepNodes(parsed, 'entry');

  return entryNodes
    .map((entry) => {
      const title = String(entry.title ?? '');
      const timestamp = String(entry.updated ?? entry.published ?? '');

      // Extract trace ID from self link href
      const links = Array.isArray(entry.link) ? entry.link : entry.link ? [entry.link] : [];
      const selfLink = (links as Array<Record<string, unknown>>).find((l) => String(l['@_rel'] ?? '') === 'self');
      const href = String(selfLink?.['@_href'] ?? '');
      const traceMatch = href.match(/\/sap\/bc\/adt\/runtime\/traces\/abaptraces\/([^"]*)/);
      const id = traceMatch?.[1] || '';

      // Extended trace data (namespace-prefixed attributes are stripped by removeNSPrefix)
      const state = entry['@_state'] != null ? String(entry['@_state']) : undefined;
      const objectName = entry['@_objectName'] != null ? String(entry['@_objectName']) : undefined;
      const runtimeStr = entry['@_runtime'] != null ? String(entry['@_runtime']) : undefined;

      return { id, title, timestamp, state, objectName, runtime: runtimeStr ? Number(runtimeStr) : undefined };
    })
    .filter((e) => e.id || e.title);
}

/**
 * Parse trace hitlist XML.
 *
 * Hitlist entries contain procedure names and timing data.
 */
export function parseTraceHitlist(xml: string): TraceHitlistEntry[] {
  const parsed = parseXml(xml);
  const nodes = findDeepNodes(parsed, 'hitListEntry');

  return nodes.map((node) => ({
    callingProgram: String(node['@_callingProgram'] ?? ''),
    calledProgram: String(node['@_calledProgram'] ?? ''),
    hitCount: Number(node['@_hitCount'] ?? 0),
    grossTime: Number(node['@_grossTime'] ?? 0),
    netTime: Number(node['@_traceEventNetTime'] ?? node['@_netTime'] ?? 0),
  }));
}

/**
 * Parse trace statements (call tree) XML.
 */
export function parseTraceStatements(xml: string): TraceStatement[] {
  const parsed = parseXml(xml);
  // Try both tag names: traceStatement and statement
  let nodes = findDeepNodes(parsed, 'traceStatement');
  if (nodes.length === 0) {
    nodes = findDeepNodes(parsed, 'statement');
  }

  return nodes
    .filter((node) => node['@_callLevel'] != null)
    .map((node) => ({
      callLevel: Number(node['@_callLevel'] ?? 0),
      hitCount: Number(node['@_hitCount'] ?? 0),
      isProceduralUnit: String(node['@_isProceduralUnit'] ?? '') === 'true',
      grossTime: Number(node['@_grossTime'] ?? 0),
      description: String(node['@_description'] ?? node['@_name'] ?? ''),
    }));
}

/**
 * Parse trace database accesses XML.
 */
export function parseTraceDbAccesses(xml: string): TraceDbAccess[] {
  const parsed = parseXml(xml);
  // Try both tag names: dbAccess and access
  let nodes = findDeepNodes(parsed, 'dbAccess');
  if (nodes.length === 0) {
    nodes = findDeepNodes(parsed, 'access');
  }

  return nodes
    .filter((node) => node['@_tableName'] != null)
    .map((node) => ({
      tableName: String(node['@_tableName'] ?? ''),
      statement: String(node['@_statement'] ?? ''),
      type: String(node['@_type'] ?? ''),
      totalCount: Number(node['@_totalCount'] ?? 0),
      bufferedCount: Number(node['@_bufferedCount'] ?? 0),
      accessTime: Number(node['@_accessTime'] ?? 0),
    }));
}

// ─── Helpers ────────────────────────────────────────────────────────

function buildFeedQueryString(
  options: FeedQueryOptions | undefined,
  defaultMaxResults: number,
  userAttribute: string,
): string {
  const params: string[] = [];
  const maxResults = clampMaxResults(options?.maxResults, defaultMaxResults);
  params.push(`$top=${maxResults}`);

  const user = String(options?.user ?? '').trim();
  if (user) {
    params.push(`$query=${encodeURIComponent(`and(equals(${userAttribute},${user}))`)}`);
  }

  const from = String(options?.from ?? '').trim();
  if (from) params.push(`from=${encodeURIComponent(from)}`);
  const to = String(options?.to ?? '').trim();
  if (to) params.push(`to=${encodeURIComponent(to)}`);

  return params.length > 0 ? `?${params.join('&')}` : '';
}

function clampMaxResults(maxResults: number | undefined, fallback: number): number {
  if (!Number.isFinite(maxResults)) return fallback;
  return Math.max(1, Math.min(MAX_RESULTS_CAP, Math.trunc(maxResults!)));
}

function toRecordArray(value: unknown): Array<Record<string, unknown>> {
  if (Array.isArray(value)) {
    return value.filter((entry): entry is Record<string, unknown> => Boolean(entry) && typeof entry === 'object');
  }
  if (value && typeof value === 'object') return [value as Record<string, unknown>];
  return [];
}

function safePositiveInt(value: unknown): number {
  const parsed = Number(value);
  return Number.isFinite(parsed) && parsed > 0 ? Math.trunc(parsed) : 0;
}

function normalizeLabel(label: string): string {
  return label.toLowerCase().replace(/[_-]+/g, ' ').replace(/\s+/g, ' ').trim();
}

function parseDumpCategories(categories: Array<Record<string, unknown>>): { error: string; program: string } {
  const normalized = categories
    .map((category) => ({
      term: String(category['@_term'] ?? ''),
      label: normalizeLabel(String(category['@_label'] ?? '')),
    }))
    .filter((entry) => entry.term.length > 0);

  if (normalized.length === 0) return { error: '', program: '' };

  const errorByLabel = normalized.find(
    (entry) =>
      entry.label.includes('runtime error') || (entry.label.includes('error') && !entry.label.includes('program')),
  )?.term;
  const programByLabel = normalized.find((entry) => entry.label.includes('program'))?.term;

  const fallbackError = normalized[0]?.term ?? '';
  const fallbackProgram = normalized[1]?.term ?? normalized.find((entry) => entry.term !== fallbackError)?.term ?? '';

  return {
    error: errorByLabel ?? fallbackError,
    program: programByLabel ?? fallbackProgram,
  };
}

function extractSelfLinkHref(links: Array<Record<string, unknown>>): string {
  const selfLink = links.find((link) => String(link['@_rel'] ?? '') === 'self');
  return String(selfLink?.['@_href'] ?? links[0]?.['@_href'] ?? '');
}

function extractDumpId(entry: Record<string, unknown>): string {
  const links = toRecordArray(entry.link);
  const selfHref = extractSelfLinkHref(links);
  const fromLink = extractIdFromPath(selfHref, ['/runtime/dump/']);
  if (fromLink) return fromLink;

  const atomId = String(entry.id ?? '');
  const fromAtomId = extractIdFromPath(atomId, ['/runtime/dump/', '/runtime/dumps/']);
  if (fromAtomId) return fromAtomId;

  const serialized = JSON.stringify(entry);
  const fallback = serialized.match(/\/runtime\/dumps?\/([^"\\\s<]+)/)?.[1] ?? '';
  return fallback.trim();
}

function extractIdFromPath(rawPath: string, markers: string[]): string {
  const path = normalizeAdtPath(rawPath, false);
  if (!path) return '';

  for (const marker of markers) {
    const idx = path.indexOf(marker);
    if (idx >= 0) {
      const start = idx + marker.length;
      const tail = path.slice(start);
      const id = tail.split(/[/?#]/)[0] ?? '';
      if (id.trim()) return id.trim();
    }
  }
  return '';
}

function extractTailId(value: string): string {
  const normalized = normalizeAdtPath(value, false);
  if (!normalized) return value;
  const parts = normalized.split('/').filter(Boolean);
  return parts[parts.length - 1] ?? value;
}

function splitDumpSections(formattedText: string, chapters: DumpChapter[]): Record<string, string> {
  if (!formattedText) return {};

  const lines = formattedText.split(/\r?\n/);
  const sortable = chapters
    .filter((chapter) => chapter.line > 0)
    .sort((a, b) => {
      if (a.line !== b.line) return a.line - b.line;
      if (a.chapterOrder !== b.chapterOrder) return a.chapterOrder - b.chapterOrder;
      return a.name.localeCompare(b.name);
    });

  if (sortable.length === 0) return {};

  const sections: Record<string, string> = {};
  for (let i = 0; i < sortable.length; i++) {
    const chapter = sortable[i]!;
    const next = sortable[i + 1];
    const startLine = Math.max(0, chapter.line - 1);
    const endLine = next?.line ? Math.max(startLine, next.line - 1) : lines.length;
    const rawSection = lines.slice(startLine, endLine).join('\n').trim();
    const normalized = shouldNormalizeWrappedLines(chapter) ? joinWrappedLines(rawSection) : rawSection;
    const sectionId = chapter.name || `section_${i + 1}`;
    sections[sectionId] = normalized;
  }

  return sections;
}

function shouldNormalizeWrappedLines(chapter: DumpChapter): boolean {
  const title = normalizeLabel(chapter.title);
  return (
    title.includes('source code') ||
    title.includes('active calls') ||
    title.includes('call stack') ||
    title.includes('kernel')
  );
}

function joinWrappedLines(text: string): string {
  if (!text.includes('\\')) return text;

  const lines = text.split('\n');
  const result: string[] = [];

  for (const line of lines) {
    if (result.length > 0 && result[result.length - 1]!.endsWith('\\')) {
      const prev = result[result.length - 1]!;
      result[result.length - 1] = `${prev.slice(0, -1)}${line.trimStart()}`;
      continue;
    }
    result.push(line);
  }

  return result.join('\n');
}

function getOptionalString(entry: Record<string, unknown>, keys: string[]): string | undefined {
  for (const key of keys) {
    const value = entry[key];
    if (value != null && String(value).trim().length > 0) {
      return String(value);
    }
  }
  return undefined;
}

function parseGatewayCallStack(root: Record<string, unknown>): GatewayCallStackEntry[] {
  const callStackNode = toRecordArray(root.callStack)[0];
  const entries = toRecordArray(callStackNode?.entry);

  return entries.map((entry, index) => ({
    number: safePositiveInt(entry['@_number']) || index + 1,
    event: String(entry['@_event'] ?? ''),
    program: String(entry['@_program'] ?? ''),
    name: String(entry['@_name'] ?? ''),
    line: safePositiveInt(entry['@_line']),
  }));
}

function parseGatewaySourceLines(root: Record<string, unknown>): GatewaySourceLine[] {
  const sourceCodeNode = toRecordArray(root.sourceCode)[0];
  const lines = toRecordArray(sourceCodeNode?.line);

  return lines.map((line, index) => ({
    number: safePositiveInt(line['@_number']) || index + 1,
    content: typeof line['#text'] === 'string' ? line['#text'] : String(line ?? ''),
    isError: String(line['@_isError'] ?? '').toLowerCase() === 'true',
  }));
}

function parseGatewayExceptions(root: Record<string, unknown>): GatewayExceptionInfo[] {
  const errorContextNode = toRecordArray(root.errorContext)[0];
  const exceptionsNode = toRecordArray(errorContextNode?.exceptions)[0];
  const exceptions = toRecordArray(exceptionsNode?.exception);

  return exceptions.map((entry) => ({
    type: String(entry['@_type'] ?? ''),
    text: String(entry['#text'] ?? ''),
    raiseLocation: String(entry['@_raiseLocation'] ?? ''),
  }));
}

function resolveGatewayErrorDetailPath(params: { detailUrl?: string; id?: string; errorType?: string }): string {
  const detailUrl = String(params.detailUrl ?? '').trim();
  if (detailUrl) {
    return normalizeAdtPath(detailUrl, true);
  }

  const id = String(params.id ?? '').trim();
  if (!id) {
    throw new Error('Gateway error detail requires either "detailUrl" or "id" with "errorType".');
  }

  if (id.includes('/sap/bc/adt/')) {
    return normalizeAdtPath(id, true);
  }

  // Feed atom:id is emitted as "{errorType}/{transactionId}" — accept that form directly.
  if (id.includes('/') && !params.errorType) {
    const [derivedType, ...rest] = id.split('/');
    const derivedId = rest.join('/');
    if (derivedType && derivedId) {
      return `/sap/bc/adt/gw/errorlog/${encodeURIComponent(decodeUriComponentSafe(derivedType))}/${encodeURIComponent(decodeUriComponentSafe(derivedId))}`;
    }
  }

  const errorType = String(params.errorType ?? '').trim();
  if (!errorType) {
    throw new Error('Gateway error detail by transaction ID requires "errorType".');
  }

  // Feed returns display form "Frontend Error" (with space) in atom:title, but the
  // detail URL path expects the compact identifier form "FrontendError". Strip
  // whitespace to allow callers to pass either shape.
  const normalizedType = errorType.replace(/\s+/g, '');

  return `/sap/bc/adt/gw/errorlog/${encodeURIComponent(normalizedType)}/${encodeURIComponent(decodeUriComponentSafe(id))}`;
}

function normalizeAdtPath(rawPath: string, requireAdtPrefix: boolean): string {
  if (!rawPath) return '';
  const trimmed = rawPath.trim();

  let normalized = trimmed;
  if (/^https?:\/\//i.test(trimmed)) {
    try {
      const url = new URL(trimmed);
      normalized = `${url.pathname}${url.search}`;
    } catch {
      normalized = trimmed;
    }
  }

  if (/^adt:\/\//i.test(normalized)) {
    const marker = normalized.indexOf('/sap/bc/adt/');
    if (marker >= 0) {
      normalized = normalized.slice(marker);
    }
  }

  if (!normalized.startsWith('/') && normalized.includes('/sap/bc/adt/')) {
    normalized = normalized.slice(normalized.indexOf('/sap/bc/adt/'));
  }

  if (requireAdtPrefix && !normalized.startsWith('/sap/bc/adt/')) {
    throw new Error(`Unsupported ADT detail URL: ${rawPath}`);
  }

  return normalized;
}

// ─── Gateway HTML helpers ──────────────────────────────────────────
//
// The gateway error log detail endpoint returns an HTML fragment built
// from known section anchors. We extract tabular values with regex rather
// than a full HTML parser to keep the dependency surface small and stay
// resilient to whitespace/attribute variations across releases.

function splitGatewayAtomId(atomId: string): { errorType: string; transactionId: string } {
  const cleaned = decodeHtmlEntities(String(atomId ?? '')).trim();
  if (!cleaned) return { errorType: '', transactionId: '' };

  const marker = '/sap/bc/adt/gw/errorlog/';
  if (cleaned.includes(marker)) {
    const tail = cleaned.slice(cleaned.indexOf(marker) + marker.length);
    const [errorType, ...rest] = tail.split('/');
    return {
      errorType: decodeUriComponentSafe(errorType ?? ''),
      transactionId: decodeUriComponentSafe(rest.join('/') ?? ''),
    };
  }

  const slashIdx = cleaned.indexOf('/');
  if (slashIdx >= 0) {
    return {
      errorType: decodeUriComponentSafe(cleaned.slice(0, slashIdx)),
      transactionId: decodeUriComponentSafe(cleaned.slice(slashIdx + 1)),
    };
  }
  return { errorType: '', transactionId: decodeUriComponentSafe(cleaned) };
}

function splitCamelCase(value: string): string {
  if (!value) return '';
  return value
    .replace(/([a-z])([A-Z])/g, '$1 $2')
    .replace(/([A-Z]+)([A-Z][a-z])/g, '$1 $2')
    .replace(/\s+/g, ' ')
    .trim();
}

function extractEntrySummaryHtml(entry: Record<string, unknown>): string {
  const summary = entry.summary;
  if (summary == null) return '';
  if (typeof summary === 'string') return decodeHtmlEntities(summary);

  const summaryNode = toRecordArray(summary)[0];
  if (!summaryNode) return '';
  const text = summaryNode['#text'];
  if (typeof text === 'string' && text.length > 0) return decodeHtmlEntities(text);
  return decodeHtmlEntities(String(summaryNode ?? ''));
}

function extractHtmlSection(html: string, anchorId: string): string {
  if (!html) return '';
  const startRe = new RegExp(`<h4[^>]*id="${escapeRegex(anchorId)}"[^>]*>`, 'i');
  const start = html.search(startRe);
  if (start < 0) return '';
  const rest = html.slice(start);
  const nextH4 = rest.slice(1).search(/<h4[\s>]/i);
  return nextH4 > 0 ? rest.slice(0, nextH4 + 1) : rest;
}

function extractHtmlHeaderValue(html: string, label: string): string {
  if (!html || !label) return '';
  const labelPattern = escapeRegex(label).replace(/_/g, '[_\\s]?');
  const re = new RegExp(
    `<b[^>]*>\\s*(?:&nbsp;|\\s)*${labelPattern}\\s*</b>\\s*</td>\\s*<td[^>]*>([\\s\\S]*?)</td>`,
    'i',
  );
  const match = html.match(re);
  if (!match?.[1]) return '';
  return sanitizeHtmlCellValue(match[1]);
}

function extractTransactionIdFromHtml(html: string): string {
  const raw = extractHtmlHeaderValue(html, 'Transaction ID');
  if (!raw) return '';
  // Strip the "(Replay in GW Client)" link/suffix that SAP appends.
  const firstToken = raw.split(/\s+/).find((part) => /^[A-Za-z0-9]{16,}$/.test(part));
  return firstToken ?? raw;
}

function extractGatewayExceptionsFromHtml(contextHtml: string): GatewayExceptionInfo[] {
  if (!contextHtml) return [];
  const exceptionsIdx = contextHtml.search(/–\s*Exceptions\s*<\/b>/i);
  const attributesIdx = contextHtml.search(/–\s*Attributes\s*<\/b>/i);
  if (exceptionsIdx < 0) return [];
  const slice = contextHtml.slice(exceptionsIdx, attributesIdx > exceptionsIdx ? attributesIdx : contextHtml.length);

  const exceptions: GatewayExceptionInfo[] = [];
  const exceptionBlockRe = /<b[^>]*>[^<]*–\s*(\/?[^\s<]+)\s*<\/b>/g;
  let match: RegExpExecArray | null;
  while ((match = exceptionBlockRe.exec(slice)) !== null) {
    const name = (match[1] ?? '').trim();
    if (!name || /^Exceptions$/i.test(name)) continue;
    const afterIdx = match.index + match[0].length;
    const block = slice.slice(afterIdx, afterIdx + 2500);
    const text = extractHtmlHeaderValue(block, 'Text');
    exceptions.push({ type: name, text, raiseLocation: '' });
  }
  return exceptions;
}

function extractGatewaySourceFromHtml(sourceHtml: string): { lines: GatewaySourceLine[]; errorLine: number } {
  if (!sourceHtml) return { lines: [], errorLine: 0 };

  // Line numbers and current-line markers sit in the first <td id="sourcetablecolumn">.
  const columnMatches = Array.from(sourceHtml.matchAll(/<td[^>]*id="sourcetablecolumn"[^>]*>([\s\S]*?)<\/td>/gi));
  const numberHtml = columnMatches[0]?.[1] ?? '';
  const lineNumberMatches = Array.from(
    numberHtml.matchAll(/<span[^>]*class="linenumber[^"]*"[^>]*>([\s\S]*?)<\/span>/gi),
  );
  const numbers: Array<number | null> = lineNumberMatches.map((m) => {
    const value = stripHtmlTags(m[1] ?? '').trim();
    return /^\d+$/.test(value) ? Number(value) : null;
  });

  // Line source cells sit in the second <td id="sourcetablecolumn">.
  const sourceCellHtml = columnMatches[1]?.[1] ?? '';
  const lineDivs = Array.from(sourceCellHtml.matchAll(/<div[^>]*class="sourceline([^"]*)"[^>]*>([\s\S]*?)<\/div>/gi));

  const lines: GatewaySourceLine[] = [];
  let errorLine = 0;
  let fallback = 1;

  for (let i = 0; i < lineDivs.length; i++) {
    const match = lineDivs[i]!;
    const classes = (match[1] ?? '').trim();
    const isError = /\bhighlight\b/i.test(classes);
    const raw = stripHtmlTags(match[2] ?? '');
    const content = decodeHtmlEntities(raw).replace(/\s+$/, '');
    const assignedNumber = numbers[i];
    const resolvedNumber = typeof assignedNumber === 'number' && assignedNumber > 0 ? assignedNumber : fallback;
    fallback = resolvedNumber + 1;
    lines.push({ number: resolvedNumber, content, isError });
    if (isError && errorLine === 0) errorLine = resolvedNumber;
  }

  return { lines, errorLine };
}

function extractGatewayCallStackFromHtml(stackHtml: string): GatewayCallStackEntry[] {
  if (!stackHtml) return [];
  const tableMatch = stackHtml.match(/<table[\s\S]*?<\/table>/i);
  if (!tableMatch) return [];
  const tableHtml = tableMatch[0];
  const rowMatches = Array.from(tableHtml.matchAll(/<tr[^>]*>([\s\S]*?)<\/tr>/gi));

  const entries: GatewayCallStackEntry[] = [];
  for (const row of rowMatches) {
    const cells = Array.from(row[1]!.matchAll(/<td[^>]*>([\s\S]*?)<\/td>/gi)).map((m) => m[1] ?? '');
    if (cells.length < 5) continue;
    const numberValue = Number(stripHtmlTags(cells[0]!).replace(/\D+/g, '').trim());
    if (!Number.isFinite(numberValue) || numberValue <= 0) continue;

    entries.push({
      number: numberValue,
      event: decodeHtmlEntities(stripHtmlTags(cells[1]!)).trim(),
      program: decodeHtmlEntities(stripHtmlTags(cells[2]!)).trim(),
      name: decodeHtmlEntities(stripHtmlTags(cells[3]!)).trim(),
      line: safePositiveInt(stripHtmlTags(cells[4]!).replace(/\D+/g, '')),
    });
  }
  return entries;
}

function sanitizeHtmlCellValue(raw: string): string {
  let value = stripHtmlTags(raw);
  value = decodeHtmlEntities(value);
  return value.replace(/\s+/g, ' ').trim();
}

// Loop until stable so adversarial nested input (e.g. `<<script>script>`) is fully
// stripped — single-pass regex would leave `<script>` behind. Closes CodeQL alert
// `js/incomplete-multi-character-sanitization` (alert #6).
export function stripHtmlTags(html: string): string {
  let result = String(html ?? '');
  let prev: string;
  do {
    prev = result;
    result = result.replace(/<[^>]*>/g, '');
  } while (result !== prev);
  return result;
}

// `&amp;` is decoded LAST so chained entities like `&amp;lt;` resolve to `&lt;`
// (the literal four-char text) rather than `<`. Closes CodeQL alert
// `js/double-escaping` (alert #7).
export function decodeHtmlEntities(text: string): string {
  return String(text ?? '')
    .replace(/&nbsp;/gi, ' ')
    .replace(/&lt;/gi, '<')
    .replace(/&gt;/gi, '>')
    .replace(/&quot;/gi, '"')
    .replace(/&apos;/gi, "'")
    .replace(/&ndash;/gi, '–')
    .replace(/&mdash;/gi, '—')
    .replace(/&#(\d+);/g, (_, code: string) => String.fromCodePoint(Number(code)))
    .replace(/&#x([0-9a-f]+);/gi, (_, code: string) => String.fromCodePoint(parseInt(code, 16)))
    .replace(/&amp;/gi, '&');
}

function decodeUriComponentSafe(value: string): string {
  if (!value?.includes('%')) return value;
  try {
    return decodeURIComponent(value);
  } catch {
    return value;
  }
}

function escapeRegex(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}
