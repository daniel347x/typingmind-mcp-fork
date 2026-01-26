const express = require('express');
const {
  StreamableHTTPClientTransport,
} = require('@modelcontextprotocol/sdk/client/streamableHttp.js');
const {
  SSEClientTransport,
} = require('@modelcontextprotocol/sdk/client/sse.js');
const stringify = require('json-stable-stringify');
const cors = require('cors');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { execFile } = require('child_process');
const vm = require('vm');
const https = require('https');
const { Readable } = require('stream');
const acorn = require('acorn');
const acornJsx = require('acorn-jsx');
const tsParser = require('@typescript-eslint/parser');
const { findAvailablePort } = require('./port-finder');
const { authMiddleware } = require('./auth');
const { Client } = require('@modelcontextprotocol/sdk/client/index.js');
const {
  StdioClientTransport,
  getDefaultEnvironment,
} = require('@modelcontextprotocol/sdk/client/stdio.js');

const CONNECTOR_VERSION =
  '2026-01-26 - add sql_autopilot + multi-set exclusion locks, write_file/write_text_file gating, and connector-deploy cp+git via TOOL EXCLUSION SETS v6';

// Store active MCP clients
const clients = new Map();

/**
 * TOOL ROUTING & GLOBAL HANDLER INFRASTRUCTURE
 *
 * This connector is our universal interface to all MCP tools.
 * The goal is to make it easy to:
 *  - Attach per-tool handlers (tool A, tool B, tool C, ...)
 *  - Attach group-level handlers (e.g., all file I/O tools, all run_command calls)
 *  - Add global pre/post hooks for every tool call in one place.
 *
 * For now, we only implement a thin routing layer and a stub for file I/O tools.
 * Behaviour is intentionally unchanged – everything still forwards to client.callTool().
 *
 * In future decades, we will:
 *  - Implement UTF-8 normalization preflight for all file reads/writes/edits
 *  - Add granular PowerShell allowances for SNAPNAX/Obsidian/PARALLAX/Araxis
 *  - Add logging/metrics per tool and per group.
 */

// Known tool-name groups (can be expanded safely over time)
// NOTE: This is intentionally conservative and only used for routing decisions.
//       Behaviour remains unchanged until handlers are implemented.
const FILE_IO_TOOL_NAMES = new Set([
  // TypingMind filesystem server tools
  'read_file',
  'read_text_file',
  'read_multiple_files',
  'read_media_file',
  'write_file',
  'edit_file',
  'create_directory',
  'list_directory',
  'list_directory_with_sizes',
  'directory_tree',
  'move_file',
  'delete_file',
  'get_file_info',

  // SSH-based file tools
  'ssh-read-lines',
  'ssh-write-chunk',
  'ssh-edit-block',
  'ssh-search-code',
  'ssh-read-file',

  // Workflowy export/import that touches JSON/Markdown on disk
  'workflowy_bulk_export',
  'workflowy_bulk_import',
  'generate_markdown_from_json',
]);

function isFileIoTool(toolName) {
  return FILE_IO_TOOL_NAMES.has(toolName);
}

/**
 * Global handler for file I/O tools.
 *
 * Eventually this will:
 *  - Inspect any file paths in toolArgs
 *  - Detect encoding (UTF-8 vs UTF-16 vs Windows-1252 vs binary)
 *  - Normalize eligible text files to UTF-8 (no BOM) before read/write/edit
 *
 * As of Decade 70, this also:
 *  - Detects literal "\\n" sequences in edit_file oldText/newText
 *  - Converts them to real newline characters ("\n") before calling the filesystem server
 *  - Logs a small summary for each normalization event
 */
const EDIT_FILE_NORMALIZATION_LOG =
  'E:\\__daniel347x\\__Obsidian\\__Inking into Mind\\--TypingMind\\Projects - All\\Projects - Individual\\TODO\\temp\\edit_file_normalization.log';
const EDIT_FILE_HEX_DEBUG_LOG = EDIT_FILE_NORMALIZATION_LOG.replace(
  'edit_file_normalization.log',
  'edit_file_hex_debug.log',
);
const EDIT_FILE_TRACKING_ROOT = path.join(
  path.dirname(EDIT_FILE_NORMALIZATION_LOG),
  '.edit_files_tracking',
);
const EDIT_FILE_MAX_PASSES_PER_EDIT = 1024;

function appendEditSessionLog(sessionDir, entry) {
  if (!sessionDir) return;
  try {
    const logPath = path.join(sessionDir, 'edit_log.jsonl');
    const line = JSON.stringify(entry) + '\n';
    fs.appendFile(logPath, line, 'utf8', () => {});
  } catch (e) {
    console.error('edit_file session log append failure:', e);
  }
}

function windowsPathToWsl(p) {
  if (!p || typeof p !== 'string') return null;
  const match = /^([A-Za-z]):\\(.*)$/.exec(p);
  if (!match) return null;
  const drive = match[1].toLowerCase();
  const rest = match[2].replace(/\\\\/g, '/');
  return `/mnt/${drive}/${rest}`;
}

function computeSessionDiffText(origPath, currentPath) {
  return new Promise((resolve) => {
    if (!origPath || !currentPath) {
      console.log(
        '[MCP CONNECTOR] session-diff: missing path(s), orig=%s current=%s',
        origPath || '(null)',
        currentPath || '(null)',
      );
      resolve(null);
      return;
    }
    const pythonExe = 'python';
    const scriptPath =
      'E:/__daniel347x/__Obsidian/__Inking into Mind/--TypingMind/Projects - All/Projects - Individual/TODO/session_diff_trampoline.py';
    const args = [scriptPath, origPath, currentPath];

    console.log(
      '[MCP CONNECTOR] session-diff: invoking python diff, orig=%s current=%s',
      origPath,
      currentPath,
    );

    execFile(pythonExe, args, { encoding: 'utf8' }, (err, stdout, stderr) => {
      if (err && !stdout) {
        console.error(
          'edit_file session diff python error:',
          err,
          stderr || '',
        );
        resolve(null);
        return;
      }
      if (stdout && stdout.trim()) {
        console.log(
          '[MCP CONNECTOR] session-diff: non-empty diff returned (length=%d)',
          stdout.length,
        );
        resolve(stdout);
        return;
      }
      console.log(
        '[MCP CONNECTOR] session-diff: empty diff output (no changes or diff failure)',
      );
      resolve(null);
    });
  });
}

// Quill Guardian Index Path
const QUILL_INDEX_PATH =
  'E:\\__daniel347x\\__Obsidian\\__Inking into Mind\\--TypingMind\\Projects - All\\Projects - Individual\\TODO\\temp\\.quill-guardian\\index.json';

// Boot-time hex debug marker: prove connector startup is using this file
try {
  fs.appendFile(
    EDIT_FILE_HEX_DEBUG_LOG,
    JSON.stringify({
      timestamp: new Date().toISOString(),
      phase: 'connector-startup',
    }) + '\
',
    () => {},
  );
} catch (e) {
  console.error('connector startup hex debug failure:', e);
}

// Cache path for last-known MCP servers configuration (from /start).
// This allows the connector to auto-start all MCP clients on its own
// after a restart, without waiting for TypingMind to send /start again.
const MCP_SERVERS_CACHE_PATH =
  'E:/__daniel347x/__Obsidian/__Inking into Mind/--TypingMind/Projects - All/Projects - Individual/TODO/MCP_Servers/mcp_servers_cache.json';

// NOTE: MCP_SERVERS_CACHE_PATH is read-only from the connector's point of view.
// Dan maintains this JSON file manually when MCP server definitions change.

function loadCachedMcpServers() {
  try {
    if (!fs.existsSync(MCP_SERVERS_CACHE_PATH)) {
      return null;
    }
    const raw = fs.readFileSync(MCP_SERVERS_CACHE_PATH, 'utf8');
    if (!raw) return null;
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== 'object') {
      return null;
    }
    // We store { mcpServers }, but also accept a plain map for forward compatibility.
    if (parsed.mcpServers && typeof parsed.mcpServers === 'object') {
      return parsed.mcpServers;
    }
    return parsed;
  } catch (err) {
    console.error('Failed to load cached MCP servers configuration:', err);
    return null;
  }
}

function saveCachedMcpServers(mcpServers) {
  // Intentionally disabled: the MCP servers cache is maintained manually
  // by Dan. The connector only reads from MCP_SERVERS_CACHE_PATH and does
  // not write to it.
  if (!mcpServers || typeof mcpServers !== 'object') {
    return;
  }
  return;
}

function summarizeLiteralNewlines(str) {
  if (typeof str !== 'string') return 0;
  const matches = str.match(/\\n/g);
  return matches ? matches.length : 0;
}

function logEditFileNormalization(context, summaryRecords) {
  try {
    const entry = {
      timestamp: new Date().toISOString(),
      toolName: context.toolName,
      path: context.toolArgs && context.toolArgs.path,
      records: summaryRecords,
      marker: 'edit_file_normalization_v2',
    };
    fs.appendFile(
      EDIT_FILE_NORMALIZATION_LOG,
      JSON.stringify(entry) + '\n',
      () => {},
    );
  } catch (e) {
    // Logging failures should never break tool calls
    console.error('edit_file normalization log failure:', e);
  }
}

// Stage 1: UTF-8 normalization + backslash-hell / newline-agnostic comparison
// This layer is responsible for preventing false-negative matches when tools
// like edit_file compare oldText against file contents.
// Responsibilities:
//   - Ensure the target file is UTF-8 without BOM
//   - Tokenize fileText and oldText into semantic tokens (CHAR, NEWLINE, TAB,
//     BACKSLASH_HELL(kind))
//   - Find matches under extremely flexible newline/tab/backslash/quote rules
//   - Canonicalize oldText to the exact substring present in the file so that
//     downstream tools can rely on simple byte-equality searches.

async function ensureUtf8NoBom(filePath) {
  try {
    const buf = await fs.promises.readFile(filePath);
    if (!buf || buf.length === 0) return;

    let start = 0;
    // Strip UTF-8 BOM if present
    if (
      buf.length >= 3 &&
      buf[0] === 0xef &&
      buf[1] === 0xbb &&
      buf[2] === 0xbf
    ) {
      start = 3;
    }

    const body = buf.slice(start);
    // Try to detect valid UTF-8 via round-trip
    const utf8String = body.toString('utf8');
    const roundtrip = Buffer.from(utf8String, 'utf8');
    const isValidUtf8 = roundtrip.equals(body);

    let normalizedBuf;
    if (isValidUtf8) {
      // Already UTF-8 (with or without BOM); ensure no BOM
      normalizedBuf = roundtrip;
    } else {
      // Fallback: assume legacy single-byte encoding (latin1/Windows-1252).
      // Decode as latin1 and re-encode as UTF-8. This may change bytes but is
      // acceptable; Git will see a diff, but semantics are preserved for text.
      const latin1String = buf.toString('latin1');
      normalizedBuf = Buffer.from(latin1String, 'utf8');
    }

    if (!normalizedBuf.equals(buf)) {
      await fs.promises.writeFile(filePath, normalizedBuf);
    }
  } catch (e) {
    console.error('ensureUtf8NoBom failure:', e);
  }
}

// Backslash-hell clump taxonomy. The universe is keyed by the final character
// after a run of backslashes ("target char"). Each entry controls how clumps
// are classified for comparison.
const DEFAULT_CLUMP_MAP = {
  n: { kind: 'newline', enabled: true },
  N: { kind: 'newline', enabled: true },
  r: { kind: 'newline', enabled: true },
  R: { kind: 'newline', enabled: true },
  t: { kind: 'tab', enabled: true },
  T: { kind: 'tab', enabled: true },
  '\\': { kind: 'backslash', enabled: true },
  '"': { kind: 'quote', enabled: true },
  "'": { kind: 'quote', enabled: true },
  '`': { kind: 'quote', enabled: true },

  // Other escape targets start disabled by default; can be enabled per-tool later.
  '&': { kind: 'other', enabled: false },
  b: { kind: 'other', enabled: false },
  f: { kind: 'other', enabled: false },
  0: { kind: 'other', enabled: false },
};

function tokenizeForInfiniteFlex(text, clumpMap = DEFAULT_CLUMP_MAP) {
  const tokens = [];
  if (typeof text !== 'string' || text.length === 0) {
    return tokens;
  }

  let i = 0;
  const len = text.length;

  while (i < len) {
    const ch = text[i];

    // Direct newline chars
    if (ch === '\n') {
      tokens.push({
        type: 'NEWLINE',
        kind: 'newline',
        lexeme: text.slice(i, i + 1),
      });
      i += 1;
      continue;
    }
    if (ch === '\r') {
      if (i + 1 < len && text[i + 1] === '\n') {
        tokens.push({
          type: 'NEWLINE',
          kind: 'newline',
          lexeme: text.slice(i, i + 2),
        });
        i += 2;
      } else {
        tokens.push({
          type: 'NEWLINE',
          kind: 'newline',
          lexeme: text.slice(i, i + 1),
        });
        i += 1;
      }
      continue;
    }

    // Direct tab
    if (ch === '\t') {
      tokens.push({ type: 'TAB', kind: 'tab', lexeme: text.slice(i, i + 1) });
      i += 1;
      continue;
    }

    // Backslash hell clump
    if (ch === '\\') {
      const start = i;
      while (i < len && text[i] === '\\') {
        i += 1;
      }
      const runEnd = i;
      const nextCh = i < len ? text[i] : null;

      let kind = 'other';
      const spec = nextCh != null ? clumpMap[nextCh] : undefined;
      if (spec && spec.enabled) {
        kind = spec.kind;
      }

      let end = runEnd;
      if (nextCh != null) {
        end = i + 1;
      }
      const lexeme = text.slice(start, end);
      if (nextCh != null) {
        i += 1;
      }

      if (kind === 'newline') {
        tokens.push({ type: 'NEWLINE', kind: 'newline', lexeme });
      } else if (kind === 'tab') {
        tokens.push({ type: 'TAB', kind: 'tab', lexeme });
      } else if (kind === 'quote') {
        tokens.push({
          type: 'BACKSLASH_HELL',
          kind: 'quote',
          lexeme,
        });
      } else if (kind === 'backslash') {
        tokens.push({
          type: 'BACKSLASH_HELL',
          kind: 'backslash',
          lexeme,
        });
      } else {
        tokens.push({ type: 'BACKSLASH_HELL', kind: 'other', lexeme });
      }
      continue;
    }

    // Ordinary char
    tokens.push({ type: 'CHAR', lexeme: ch });
    i += 1;
  }

  return tokens;
}

function tokensEqualInfiniteFlex(a, b) {
  if (!a || !b) return false;

  if (a.type === 'CHAR' && b.type === 'CHAR') {
    return a.lexeme === b.lexeme;
  }

  if (a.type === 'NEWLINE' && b.type === 'NEWLINE') {
    // Any newline clump equals any other newline clump
    return true;
  }

  if (a.type === 'TAB' && b.type === 'TAB') {
    // Any tab clump equals any other tab clump
    return true;
  }

  if (a.type === 'BACKSLASH_HELL' && b.type === 'BACKSLASH_HELL') {
    return a.kind === b.kind;
  }

  // Allow NEWLINE <-> newline-kind BACKSLASH_HELL
  if (
    a.type === 'NEWLINE' &&
    b.type === 'BACKSLASH_HELL' &&
    b.kind === 'newline'
  ) {
    return true;
  }
  if (
    b.type === 'NEWLINE' &&
    a.type === 'BACKSLASH_HELL' &&
    a.kind === 'newline'
  ) {
    return true;
  }

  // Allow TAB <-> tab-kind BACKSLASH_HELL
  if (a.type === 'TAB' && b.type === 'BACKSLASH_HELL' && b.kind === 'tab') {
    return true;
  }
  if (b.type === 'TAB' && a.type === 'BACKSLASH_HELL' && a.kind === 'tab') {
    return true;
  }

  return false;
}

function findTokenMatchInfiniteFlex(fileTokens, oldTokens) {
  const n = fileTokens.length;
  const m = oldTokens.length;
  if (!n || !m || m > n) return -1;

  outer: for (let start = 0; start <= n - m; start += 1) {
    for (let j = 0; j < m; j += 1) {
      if (!tokensEqualInfiniteFlex(fileTokens[start + j], oldTokens[j])) {
        continue outer;
      }
    }
    return start;
  }

  return -1;
}

function computeTokenOffsets(tokens) {
  const offsets = [];
  let offset = 0;
  for (const t of tokens) {
    offsets.push(offset);
    offset += t.lexeme ? t.lexeme.length : 0;
  }
  return offsets;
}

function isEmojiCodePoint(cp) {
  if (typeof cp !== 'number' || !Number.isFinite(cp)) return false;
  return (
    (cp >= 0x1f300 && cp <= 0x1faff) ||
    (cp >= 0x1f1e6 && cp <= 0x1f1ff) ||
    (cp >= 0x2600 && cp <= 0x26ff) ||
    (cp >= 0x2700 && cp <= 0x27bf) ||
    (cp >= 0x1f3fb && cp <= 0x1f3ff) ||
    cp === 0xfe0e ||
    cp === 0xfe0f
  );
}

function stripEmoji(text) {
  if (typeof text !== 'string' || text.length === 0) return '';
  let out = '';
  let i = 0;
  while (i < text.length) {
    const cp = text.codePointAt(i);
    const ch = String.fromCodePoint(cp);
    const cpLen = ch.length;
    if (!isEmojiCodePoint(cp)) {
      out += ch;
    }
    i += cpLen;
  }
  return out;
}

function buildEmojiStrippedWithMap(text) {
  const noEmojiChars = [];
  const mapOutToOriginal = [];
  if (typeof text !== 'string' || text.length === 0) {
    return { stripped: '', mapOutToOriginal };
  }
  let i = 0;
  while (i < text.length) {
    const cp = text.codePointAt(i);
    const ch = String.fromCodePoint(cp);
    const cpLen = ch.length;
    if (!isEmojiCodePoint(cp)) {
      mapOutToOriginal[noEmojiChars.length] = i;
      noEmojiChars.push(ch);
    }
    i += cpLen;
  }
  return { stripped: noEmojiChars.join(''), mapOutToOriginal };
}

function findEmojiInsensitiveMatch(fileText, oldText) {
  if (typeof fileText !== 'string' || typeof oldText !== 'string') return null;
  const oldStripped = stripEmoji(oldText);
  if (!oldStripped) return null;
  const { stripped: fileStripped, mapOutToOriginal } =
    buildEmojiStrippedWithMap(fileText);
  if (!fileStripped) return null;
  const idx = fileStripped.indexOf(oldStripped);
  if (idx === -1) return null;
  const startChar = mapOutToOriginal[idx];
  if (typeof startChar !== 'number') return null;
  let remaining = oldStripped.length;
  let current = startChar;
  while (current < fileText.length && remaining > 0) {
    const cp = fileText.codePointAt(current);
    const ch = String.fromCodePoint(cp);
    const cpLen = ch.length;
    if (!isEmojiCodePoint(cp)) {
      remaining -= 1;
    }
    current += cpLen;
  }
  const endChar = current;
  if (endChar <= startChar) return null;
  return { startChar, endChar };
}

async function applyEditFileInfiniteFlex(context) {
  if (!context || context.toolName !== 'edit_file') return context;

  const args = context.toolArgs || {};
  const filePath = args.path;
  const edits = Array.isArray(args.edits) ? args.edits : [];

  if (!filePath || edits.length === 0) {
    return context;
  }

  try {
    await ensureUtf8NoBom(filePath);
  } catch (e) {
    console.error('ensureUtf8NoBom error for edit_file:', e);
  }

  let fileText;
  try {
    fileText = await fs.promises.readFile(filePath, 'utf8');
  } catch (e) {
    console.error('Failed to read file for edit_file infinite-flex:', e);
    return context;
  }

  const fileTokens = tokenizeForInfiniteFlex(fileText);
  const fileOffsets = computeTokenOffsets(fileTokens);

  const updatedEdits = [];
  const summaryRecords = [];

  edits.forEach((edit, index) => {
    const e = { ...edit };
    if (typeof e.oldText !== 'string' || e.oldText.length === 0) {
      updatedEdits.push(e);
      return;
    }

    const oldTokens = tokenizeForInfiniteFlex(e.oldText);
    if (!oldTokens.length) {
      updatedEdits.push(e);
      return;
    }

    let matchIndex = findTokenMatchInfiniteFlex(fileTokens, oldTokens);

    if (matchIndex === -1) {
      const emojiMatch = findEmojiInsensitiveMatch(fileText, e.oldText);
      if (emojiMatch) {
        const { startChar, endChar } = emojiMatch;
        const canonicalOldText = fileText.slice(startChar, endChar);
        if (canonicalOldText !== e.oldText) {
          summaryRecords.push({
            editIndex: index,
            originalLength: e.oldText.length,
            canonicalLength: canonicalOldText.length,
            matchIndex: -1,
            reason: 'emoji-flex-fallback',
          });
          e.oldText = canonicalOldText;
        }
        updatedEdits.push(e);
        return;
      }

      updatedEdits.push(e);
      return;
    }

    const startChar = fileOffsets[matchIndex];
    let endChar = startChar;
    for (let k = 0; k < oldTokens.length; k += 1) {
      const t = fileTokens[matchIndex + k];
      endChar += t.lexeme ? t.lexeme.length : 0;
    }

    const canonicalOldText = fileText.slice(startChar, endChar);
    if (canonicalOldText !== e.oldText) {
      summaryRecords.push({
        editIndex: index,
        originalLength: e.oldText.length,
        canonicalLength: canonicalOldText.length,
        matchIndex,
      });
      e.oldText = canonicalOldText;
    }

    updatedEdits.push(e);
  });

  if (summaryRecords.length > 0) {
    context.toolArgs = { ...args, edits: updatedEdits };
    logEditFileNormalization(context, summaryRecords);
  }

  return context;
}

function normalizeEditFileArgs(context) {
  if (!context || context.toolName !== 'edit_file') return context;
  const args = context.toolArgs || {};
  const edits = Array.isArray(args.edits) ? args.edits : [];

  let changed = false;
  const summaryRecords = [];

  const normalizedEdits = edits.map((edit, index) => {
    const e = { ...edit };
    let oldCount = 0;
    let newCount = 0;

    if (typeof e.oldText === 'string') {
      oldCount = summarizeLiteralNewlines(e.oldText);
      const normalized = e.oldText.replace(/\\n/g, '\n');
      if (normalized !== e.oldText) {
        e.oldText = normalized;
        changed = true;
      }
    }

    if (typeof e.newText === 'string') {
      newCount = summarizeLiteralNewlines(e.newText);
      const normalized = e.newText.replace(/\\n/g, '\n');
      if (normalized !== e.newText) {
        e.newText = normalized;
        changed = true;
      }
    }

    if (oldCount || newCount) {
      summaryRecords.push({
        editIndex: index,
        oldLiteralBackslashNCount: oldCount,
        newLiteralBackslashNCount: newCount,
      });
    }

    return e;
  });

  if (changed) {
    context.toolArgs = { ...args, edits: normalizedEdits };
    if (summaryRecords.length > 0) {
      logEditFileNormalization(context, summaryRecords);
    }
  }

  return context;
}

function hexFromBuffer(buf, maxBytes) {
  if (!buf) return '';
  if (!Buffer.isBuffer(buf)) {
    buf = Buffer.from(String(buf), 'utf8');
  }
  const limit =
    typeof maxBytes === 'number' && maxBytes > 0
      ? Math.min(maxBytes, buf.length)
      : buf.length;
  let out = '';
  for (let i = 0; i < limit; i += 1) {
    out += buf[i].toString(16).padStart(2, '0');
  }
  return out;
}

function analyzeEditFileMismatch(fileBuf, oldBuf) {
  const idx = fileBuf.indexOf(oldBuf);
  if (idx !== -1) {
    return {
      indexOfResult: idx,
      usedPrefixFallback: false,
    };
  }

  const prefixLength = Math.min(16, oldBuf.length);
  const prefix = oldBuf.slice(0, prefixLength);
  const first = fileBuf.indexOf(prefix);
  if (first === -1) {
    return {
      indexOfResult: -1,
      usedPrefixFallback: true,
      prefixFound: false,
    };
  }
  const second = fileBuf.indexOf(prefix, first + 1);
  if (second !== -1) {
    return {
      indexOfResult: -1,
      usedPrefixFallback: true,
      prefixFound: true,
      prefixAmbiguous: true,
      prefixIndex: first,
      secondIndex: second,
    };
  }

  const base = first;
  const limit = Math.min(oldBuf.length, fileBuf.length - base);
  let mismatchOffset = -1;
  let fileByte = null;
  let oldByte = null;

  for (let i = 0; i < limit; i += 1) {
    if (fileBuf[base + i] !== oldBuf[i]) {
      mismatchOffset = i;
      fileByte = fileBuf[base + i];
      oldByte = oldBuf[i];
      break;
    }
  }

  return {
    indexOfResult: -1,
    usedPrefixFallback: true,
    prefixFound: true,
    prefixAmbiguous: false,
    prefixIndex: base,
    mismatchOffset,
    fileByte,
    oldByte,
  };
}

async function debugEditFileBytes(context) {
  try {
    const args = context.toolArgs || {};
    const filePath = args.path;
    const edits = Array.isArray(args.edits) ? args.edits : [];
    fs.appendFile(
      EDIT_FILE_HEX_DEBUG_LOG,
      JSON.stringify({
        timestamp: new Date().toISOString(),
        phase: 'entered-debugEditFileBytes',
        path: filePath || '(none)',
        toolName: context && context.toolName,
        editsLength: edits.length,
      }) + '\n',
      () => {},
    );
    if (!filePath || edits.length === 0) {
      fs.appendFile(
        EDIT_FILE_HEX_DEBUG_LOG,
        JSON.stringify({
          timestamp: new Date().toISOString(),
          phase: 'no-path-or-edits',
          path: filePath || '(none)',
          toolName: context && context.toolName,
          editsLength: edits.length,
        }) + '\n',
        () => {},
      );
      return;
    }

    const firstEdit = edits[0];
    if (typeof firstEdit.oldText !== 'string') {
      return;
    }

    const fileBuf = await fs.promises.readFile(filePath);
    const oldBuf = Buffer.from(firstEdit.oldText, 'utf8');

    const analysis = analyzeEditFileMismatch(fileBuf, oldBuf);

    const debugEntry = {
      timestamp: new Date().toISOString(),
      path: filePath,
      toolName: context.toolName,
      oldTextLength: firstEdit.oldText.length,
      oldBytesLength: oldBuf.length,
      fileBytesLength: fileBuf.length,
      indexOfResult: analysis.indexOfResult,
      analysis,
      oldTextHex: hexFromBuffer(oldBuf, 1024),
    };

    const previewWindow = 64;
    if (typeof analysis.prefixIndex === 'number' && analysis.prefixIndex >= 0) {
      const start = Math.max(0, analysis.prefixIndex - previewWindow);
      const end = Math.min(
        fileBuf.length,
        analysis.prefixIndex + oldBuf.length + previewWindow,
      );
      debugEntry.fileSliceHex = hexFromBuffer(
        fileBuf.slice(start, end),
        (end - start) * 2,
      );
      debugEntry.fileSliceOffset = start;
    } else {
      debugEntry.fileHexPreview = hexFromBuffer(fileBuf, 512);
    }

    fs.appendFile(
      EDIT_FILE_HEX_DEBUG_LOG,
      JSON.stringify(debugEntry) + '\n',
      () => {},
    );
  } catch (e) {
    console.error('edit_file hex debug failure:', e);
    try {
      const fallbackEntry = {
        timestamp: new Date().toISOString(),
        path:
          (context &&
            context.toolArgs &&
            context.toolArgs.path) || '(unknown)',
        toolName: context && context.toolName,
        error: String((e && e.message) || e),
        note: 'debugEditFileBytes failed before reading file or writing full analysis',
      };
      fs.appendFile(
        EDIT_FILE_HEX_DEBUG_LOG,
        JSON.stringify(fallbackEntry) + '\n',
        () => {},
      );
    } catch (inner) {
      console.error(
        'edit_file hex debug fallback logging failure:',
        inner,
      );
    }
  }
}

async function handleFileIoPreflight(context) {
  // context: { clientId, clientEntry, toolName, toolArgs }
  try {
    fs.appendFile(
      EDIT_FILE_HEX_DEBUG_LOG,
      JSON.stringify({
        timestamp: new Date().toISOString(),
        phase: 'entered-handleFileIoPreflight',
        toolName: context && context.toolName,
        path:
          (context &&
            context.toolArgs &&
            context.toolArgs.path) || '(none)',
      }) + '\n',
      () => {},
    );
  } catch (e) {
    console.error('handleFileIoPreflight hex debug failure:', e);
  }
  // Decade 70: perform literal "\\n" → "\n" normalization for edit_file, plus light logging.

  if (context && context.toolName === 'edit_file') {
    await applyEditFileInfiniteFlex(context);
    await debugEditFileBytes(context);
  }

  return context;
}

// Stage 2: Guardian validation & per-edit backups for structurally constrained
// files (JSON, Python, JavaScript). This layer:
//   - Creates a per-edit backup BEFORE edit_file runs
//   - Runs a language-specific validator AFTER the edit completes
//   - On structural failure, returns a structured error that includes the
//     backup path so the caller can inspect/restore; it does NOT attempt
//     auto-restore or auto-fix.
function getStructuredFileKind(filePath) {
  if (!filePath || typeof filePath !== 'string') {
    return null;
  }
  try {
    const ext = path.extname(filePath).toLowerCase();
    if (ext === '.json') return 'json';
    if (ext === '.py') return 'python';
    if (['.js', '.jsx', '.mjs'].includes(ext)) return 'javascript';
    if (['.ts', '.tsx'].includes(ext)) return 'typescript';
    return null;
  } catch (e) {
    console.error('stage2 getStructuredFileKind error:', e);
    return null;
  }
}

async function createStage2Backup(filePath, kind) {
  try {
    const stat = await fs.promises.stat(filePath);
    if (!stat || !stat.isFile()) {
      // No original file exists (e.g., first write to a new path)
      return { backupPath: null, mode: 'no-original' };
    }
    const dir = path.dirname(filePath);
    const base = path.basename(filePath);
    const stamp = new Date().toISOString().replace(/[:.]/g, '-');
    const rand = Math.random().toString(16).slice(2, 8);
    const backupName = `${base}.stage2-backup-${kind || 'unknown'}-${stamp}-${rand}`;
    const backupPath = path.join(dir, backupName);
    await fs.promises.copyFile(filePath, backupPath);
    return { backupPath, mode: 'normal' };
  } catch (e) {
    if (e && (e.code === 'ENOENT' || e.code === 'ENOTDIR')) {
      // No original file exists
      return { backupPath: null, mode: 'no-original' };
    }
    console.error('stage2 backup creation failed:', e);
    return { backupPath: null, mode: 'error' };
  }
}

async function validateStructuredFile(filePath, kind) {
  try {
    if (kind === 'json') {
      const text = await fs.promises.readFile(filePath, 'utf8');
      try {
        JSON.parse(text);
        return { ok: true };
      } catch (parseError) {
        // Enhanced error detection for newline-in-string corruption
        const errorMsg = String(parseError.message || parseError);
        
        // Try to extract position from error (varies by JS engine)
        let errorPos = -1;
        const posMatch = errorMsg.match(/position\s+(\d+)/);
        if (posMatch) {
          errorPos = parseInt(posMatch[1], 10);
        }

        // Check if error is near unescaped newlines in string context
        if (errorPos >= 0 && errorPos < text.length) {
          // Look for newline characters around error position
          const searchStart = Math.max(0, errorPos - 5);
          const searchEnd = Math.min(text.length, errorPos + 5);
          const snippet = text.slice(searchStart, searchEnd);
          
          // Check if there's a newline in this region
          if (snippet.includes('\n') || snippet.includes('\r')) {
            // Check if we're inside a string value (heuristic: look back for unclosed quote)
            let inString = false;
            let quoteChar = null;
            for (let i = 0; i < errorPos; i++) {
              const ch = text[i];
              if (ch === '"' || ch === "'") {
                if (inString && ch === quoteChar) {
                  // Check if it's escaped
                  let backslashCount = 0;
                  let j = i - 1;
                  while (j >= 0 && text[j] === '\\') {
                    backslashCount++;
                    j--;
                  }
                  // Even number of backslashes = quote is NOT escaped
                  if (backslashCount % 2 === 0) {
                    inString = false;
                    quoteChar = null;
                  }
                } else if (!inString) {
                  inString = true;
                  quoteChar = ch;
                }
              }
            }

            if (inString) {
              // Check what kind of character is causing the issue
              const charAtError = errorPos < text.length ? text[errorPos] : null;
              
              // Quote detection (unescaped DOUBLE quote inside string)
              // Note: Single quotes are legal inside JSON strings (which use double quotes)
              if (charAtError === '"') {
                // Count preceding backslashes to see if this quote is escaped
                let backslashCount = 0;
                let j = errorPos - 1;
                while (j >= 0 && text[j] === '\\') {
                  backslashCount++;
                  j--;
                }
                // Even number of backslashes = quote is NOT escaped
                if (backslashCount % 2 === 0) {
                  return {
                    ok: false,
                    error: `Unescaped quote character detected inside JSON string value.\n\n` +
                      `LIKELY CAUSE: Your newText contained a quote (${charAtError}) that was not properly escaped.\n\n` +
                      `SOLUTION: For quotes in JSON strings, escape them in your newText.\n\n` +
                      `Original parse error: ${errorMsg}`,
                    enhancedDiagnostic: 'unescaped-quote-in-json-string',
                  };
                }
              }
              
              // Newline detection (if quote check didn't match)
              return {
                ok: false,
                error: 'Unescaped newline character detected inside JSON string value.\n\n' +
                  'LIKELY CAUSE: Your newText argument contained backslash-n (\\n) which was converted to a real newline character (HEX 0x0A) during processing, breaking JSON syntax.\n\n' +
                  'SOLUTION: For JSON files, Stage 1 flexible matcher already handles newline variations in matching. The file likely already has the correct structure. Consider if you need to modify newline-containing fields at all.\n\n' +
                  'If you do need to edit: use four backslashes + n (\\\\\\\\n) in your newText for a literal backslash-n in the resulting JSON, or verify your escaping strategy.\n\n' +
                  `Original parse error: ${errorMsg}`,
                enhancedDiagnostic: 'newline-in-json-string',
              };
            }
          }
        }

        // Generic JSON parse error
        return { ok: false, error: errorMsg };
      }
    }

    if (kind === 'python') {
      return await new Promise((resolve) => {
        execFile(
          'python',
          ['-m', 'py_compile', filePath],
          (error, stdout, stderr) => {
            if (error) {
              const rawError =
                (stderr && String(stderr).trim()) ||
                (error && error.message) ||
                String(error);

              // If Python is not available on PATH, treat this as a hard
              // failure for Stage 2. We do NOT allow validation to pass when
              // the validator is missing.
              if (error.code === 'ENOENT') {
                console.error('stage2 python validator unavailable:', rawError);
                const msg =
                  'Python validator (py_compile) is not available on PATH. ' +
                  'Stage 2 cannot validate this Python file; the edit has been blocked.\n\n' +
                  `Raw error: ${rawError}`;
                return resolve({
                  ok: false,
                  error: msg,
                  validatorUnavailable: true,
                });
              }

              // Enhanced Python error with bidirectional escape-sequence context
              const enhancedMsg =
                'Python syntax validation error:\n' +
                rawError + '\n\n' +
                'LIKELY CAUSE (in 90%+ of Python corruption cases):\n' +
                'Your newText argument contained characters that were transformed during processing, in EITHER DIRECTION:\n\n' +
                'DIRECTION 1 (escape → literal character):\n' +
                '  - Newline: \\\\n became HEX 0x0A (real newline), breaking a string literal or creating unexpected line breaks\n' +
                '  - Quote: \\\\" became unescaped quote, terminating strings prematurely\n' +
                '  - Tab: \\\\t became HEX 0x09 (real tab)\n\n' +
                'DIRECTION 2 (literal character → escape):\n' +
                '  - Real newline (0x0A) became literal \\\\n text, changing string semantics or breaking syntax\n' +
                '  - Real quote became escaped quote, changing meaning\n' +
                '  - Real tab became literal \\\\t text\n\n' +
                'Either direction can break Python syntax when these transformations occur inside string literals, docstrings, or other contexts where the distinction matters.\n\n' +
                'The Python compiler output above provides specific hints about what broke and where.\n\n' +
                'SOLUTION: Restore from the backup and retry your edit, paying close attention to how newlines, quotes, and other special characters are represented in your newText argument.';

              return resolve({
                ok: false,
                error: enhancedMsg,
                enhancedDiagnostic: 'python-syntax-error',
              });
            }
            return resolve({ ok: true });
          },
        );
      });
    }

    if (kind === 'javascript' || kind === 'typescript') {
      const code = await fs.promises.readFile(filePath, 'utf8');
      try {
        if (kind === 'typescript') {
          try {
            tsParser.parse(code, {
              ecmaVersion: 'latest',
              sourceType: 'module',
              jsx: filePath.endsWith('x'),
            });
            return { ok: true };
          } catch (tsError) {
            console.warn(`TypeScript parser failed, falling back to Acorn for ${filePath}:`, tsError);
            // Fall through to Acorn if TypeScript parser fails
          }
        }
        
        const Parser = acorn.Parser.extend(acornJsx());
        Parser.parse(code, {
          ecmaVersion: 'latest',
          sourceType: 'module',
        });
        return { ok: true };
      } catch (e) {
        const msg = (e && e.message) || String(e);
        return { ok: false, error: `JavaScript/TypeScript syntax validation error:\n${msg}` };
      }
    }

    // Unknown kind => no structural validation performed.
    return { ok: true, validatorUnavailable: true };
  } catch (e) {
    const msg = (e && e.message) || String(e);
    return { ok: false, error: msg };
  }
}

function indentFlexSplitLines(text) {
  if (typeof text !== 'string') return [];
  const rawLines = text.split('\n');
  return rawLines.map((line) => line.replace(/\r$/, ''));
}

function indentFlexLeadingSpaces(line) {
  if (typeof line !== 'string') return 0;
  let i = 0;
  while (i < line.length && line[i] === ' ') {
    i += 1;
  }
  return i;
}

function indentFlexComputeBaseIndent(lines) {
  let min = null;
  for (const line of lines) {
    if (!line || !line.trim()) continue;
    const ls = indentFlexLeadingSpaces(line);
    if (min === null || ls < min) {
      min = ls;
    }
  }
  return min == null ? 0 : min;
}

function indentFlexDedentLines(lines, baseIndent) {
  if (!Array.isArray(lines) || typeof baseIndent !== 'number' || baseIndent <= 0) {
    return Array.isArray(lines) ? [...lines] : [];
  }
  return lines.map((line) => {
    if (!line || !line.trim()) return line;
    return line.slice(baseIndent);
  });
}

function findUniquePythonIndentFlexMatch(fileText, oldText) {
  if (typeof fileText !== 'string' || typeof oldText !== 'string') return null;

  const fileRawLines = fileText.split('\n');
  const fileLines = fileRawLines.map((line) => line.replace(/\r$/, ''));
  const lineStarts = [];
  let offset = 0;
  for (const raw of fileRawLines) {
    lineStarts.push(offset);
    offset += raw.length + 1;
  }

  const oldLines = indentFlexSplitLines(oldText);
  while (oldLines.length && !oldLines[oldLines.length - 1].trim()) {
    oldLines.pop();
  }
  if (!oldLines.length) return null;

  const oldBaseIndent = indentFlexComputeBaseIndent(oldLines);
  const dedentedOldLines = indentFlexDedentLines(oldLines, oldBaseIndent);
  const dedentedOldBlock = dedentedOldLines.join('\n');
  const L = oldLines.length;

  let match = null;

  for (let i = 0; i + L <= fileLines.length; i += 1) {
    const block = fileLines.slice(i, i + L);
    const blockBaseIndent = indentFlexComputeBaseIndent(block);
    if (blockBaseIndent === 0 && block.every((line) => !line || !line.trim())) {
      continue;
    }

    let compatible = true;
    for (const line of block) {
      if (!line || !line.trim()) continue;
      if (indentFlexLeadingSpaces(line) < blockBaseIndent) {
        compatible = false;
        break;
      }
    }
    if (!compatible) continue;

    const dedentedBlockLines = indentFlexDedentLines(block, blockBaseIndent);
    const dedentedBlock = dedentedBlockLines.join('\n');
    if (dedentedBlock === dedentedOldBlock) {
      const startLine = i;
      const endLine = i + L - 1;
      const startChar = lineStarts[startLine];
      const endChar = lineStarts[endLine] + fileRawLines[endLine].length;
      const candidate = {
        startChar,
        endChar,
        baseIndent: blockBaseIndent,
      };
      if (match) {
        return null;
      }
      match = candidate;
    }
  }

  return match;
}

function attemptPythonIndentFlexAutoFix(fileText, edit) {
  if (
    !edit ||
    typeof edit.oldText !== 'string' ||
    typeof edit.newText !== 'string'
  ) {
    return null;
  }

  const oldLines = indentFlexSplitLines(edit.oldText);
  const newLines = indentFlexSplitLines(edit.newText);

  const oldBaseIndent = indentFlexComputeBaseIndent(oldLines);
  const newBaseIndent = indentFlexComputeBaseIndent(newLines);

  // If base indents differ, assume the agent is intentionally changing indent; do not auto-fix.
  if (oldBaseIndent !== newBaseIndent) {
    return null;
  }

  const match = findUniquePythonIndentFlexMatch(fileText, edit.oldText);
  if (!match) {
    return null;
  }

  const { startChar, endChar, baseIndent } = match;
  const canonicalOldText = fileText.slice(startChar, endChar);

  const dedentedNewLines = indentFlexDedentLines(newLines, newBaseIndent);
  const reindentedNewLines = dedentedNewLines.map((line) => {
    if (!line || !line.trim()) return line;
    return ' '.repeat(baseIndent) + line;
  });
  const canonicalNewText = reindentedNewLines.join('\n');

  return {
    canonicalOldText,
    canonicalNewText,
  };
}

async function runStructuredFileWithStage2Guard(clientEntry, context) {
  const args = context.toolArgs || {};
  const filePath = args.path;
  const kind = getStructuredFileKind(filePath);

  // If we don't have a usable path, fall back to default behaviour.
  // All files (structured or not) now pass through this guardian layer so that
  // direct edit_file first-match semantics and backup/rollback apply consistently.
  // The structural validators are only activated for known structured kinds
  // (json/python/javascript/typescript) via getStructuredFileKind/validateStructuredFile.
  if (!filePath) {
    return clientEntry.client.callTool(
      {
        name: context.toolName,
        arguments: context.toolArgs,
      },
      undefined,
      {
        timeout: 900000,
        resetTimeoutOnProgress: true,
      },
    );
  }

  const backupInfo = await createStage2Backup(filePath, kind);
  const backupPath = backupInfo && backupInfo.backupPath;

  if (backupInfo && backupInfo.mode === 'error') {
    console.error(
      'stage2: unable to create backup before structured file edit; proceeding without backup for',
      filePath,
    );
  }

  const useDirectReplaceAll =
    context &&
    context.toolName === 'edit_file' &&
    context.useDirectReplaceAll === true;

  let toolResult;
  try {
    if (useDirectReplaceAll) {
      const edits = Array.isArray(args.edits) ? args.edits : [];
      const edit = edits[0];

      if (
        !edit ||
        typeof edit.oldText !== 'string' ||
        typeof edit.newText !== 'string'
      ) {
        toolResult = {
          isError: true,
          content: [
            {
              type: 'text',
              text:
                'edit_file direct first-match requires a single edit with string oldText and newText.',
            },
          ],
        };
      } else if (edit.oldText.length === 0) {
        toolResult = {
          isError: true,
          content: [
            {
              type: 'text',
              text:
                'edit_file direct first-match: empty oldText is not allowed.',
            },
          ],
        };
      } else {
        const currentText = await fs.promises.readFile(filePath, 'utf8');
        const parts = currentText.split(edit.oldText);
        const occurrences = parts.length - 1;

        console.log(
          '[MCP CONNECTOR] edit_file direct first-match on %s (matches=%d, oldLen=%d, newLen=%d)',
          filePath,
          occurrences,
          edit.oldText.length,
          edit.newText.length,
        );

        if (occurrences === 0) {
          let autoFixed = false;

          if (kind === 'python') {
            try {
              const flex = attemptPythonIndentFlexAutoFix(currentText, edit);
              if (
                flex &&
                typeof flex.canonicalOldText === 'string' &&
                typeof flex.canonicalNewText === 'string'
              ) {
                edit.oldText = flex.canonicalOldText;
                edit.newText = flex.canonicalNewText;

                const partsFlex = currentText.split(edit.oldText);
                const occurrencesFlex = partsFlex.length - 1;

                if (occurrencesFlex > 0) {
                  const updatedTextFlex = partsFlex[0] + edit.newText + partsFlex.slice(1).join(edit.oldText);
                  await fs.promises.writeFile(filePath, updatedTextFlex, 'utf8');

                  toolResult = {
                    isError: false,
                    content: [
                      {
                        type: 'text',
                        text:
                          `edit_file direct first-match (python indent-flex) replaced 1 of ${occurrencesFlex} occurrence` +
                          `${occurrencesFlex === 1 ? '' : 's'} of oldText in ${filePath}.`,
                      },
                    ],
                    directReplaceAll: {
                      occurrences: occurrencesFlex,
                      pythonIndentFlex: true,
                    },
                  };
                  autoFixed = true;
                }
              }
            } catch (e) {
              console.error('edit_file python indent-flex auto-fix error:', e);
            }
          }

          if (!autoFixed) {
            toolResult = {
              isError: true,
              content: [
                {
                  type: 'text',
                  text: `edit_file direct first-match: NO MATCH – 0 occurrences of oldText found in ${filePath}. The file was NOT modified.`,
                },
              ],
              directReplaceAll: {
                occurrences,
                noMatch: true,
              },
            };
          }
        } else {
          const updatedText = parts[0] + edit.newText + parts.slice(1).join(edit.oldText);
          await fs.promises.writeFile(filePath, updatedText, 'utf8');

          toolResult = {
            isError: false,
            content: [
              {
                type: 'text',
                text: `edit_file direct first-match replaced 1 of ${occurrences} occurrence${
                  occurrences === 1 ? '' : 's'
                } of oldText in ${filePath}.`,
              },
            ],
            directReplaceAll: {
              occurrences,
            },
          };
        }
      }
    } else {
      toolResult = await clientEntry.client.callTool(
        {
          name: context.toolName,
          arguments: context.toolArgs,
        },
        undefined,
        {
          timeout: 900000,
          resetTimeoutOnProgress: true,
        },
      );
    }
  } catch (error) {
    // Underlying tool call failed; bubble the error unchanged.
    throw error;
  }

  const validation = await validateStructuredFile(filePath, kind);
  if (validation && validation.ok) {
    // On success, clean up the backup file (if any) and return the original result
    if (backupPath) {
      try {
        await fs.promises.unlink(backupPath);
      } catch (e) {
        console.error(`stage2: failed to clean up backup file ${backupPath}`, e);
      }
    }
    return toolResult;
  }

  const errorMessage =
    (validation && validation.error) || 'Unknown structural validation error';

  let corruptPath = null;
  let restoreError = null;

  if (backupPath) {
    try {
      const dir = path.dirname(filePath);
      const base = path.basename(filePath);
      const stamp = new Date().toISOString().replace(/[:.]/g, '-');
      const rand = Math.random().toString(16).slice(2, 8);
      const corruptName = `${base}.stage2-corrupted-${kind || 'unknown'}-${stamp}-${rand}`;
      corruptPath = path.join(dir, corruptName);
      await fs.promises.copyFile(filePath, corruptPath);
    } catch (e) {
      console.error('stage2: failed to save corrupted post-edit file for', filePath, e);
    }

    try {
      await fs.promises.copyFile(backupPath, filePath);
    } catch (e) {
      restoreError = e;
      console.error('stage2: failed to restore backup file', backupPath, 'to', filePath, e);
    }

    try {
      await fs.promises.unlink(backupPath);
    } catch (e) {
      console.error(`stage2: failed to clean up backup file after restore ${backupPath}`, e);
    }
  }

  const backupLine = backupPath
    ? `Pre-edit backup: ${backupPath}`
    : 'Pre-edit backup: (none - file was created by this operation; no prior version exists.)';

  let restoreLine;
  if (backupPath) {
    if (restoreError) {
      restoreLine = `Attempted to auto-restore original file from backup but FAILED: ${String(restoreError)}`;
    } else if (corruptPath) {
      restoreLine = `Auto-restored original file from backup. Corrupted post-edit contents saved as: ${corruptPath}`;
    } else {
      restoreLine = 'Auto-restored original file from backup.';
    }
  } else {
    restoreLine = 'No pre-edit backup was available (file was created by this operation); the current file may be invalid.';
  }

  const lines = [
    `Stage 2 guardian validation FAILED for ${kind.toUpperCase()} file after ${context.toolName}.`,
    '',
    `Path: ${filePath}`,
    backupLine,
    restoreLine,
    '',
    `Validator error: ${errorMessage}`,
    '',
    'The invalid edit has been rolled back to the last known-good version. Inspect the saved corrupted copy if needed.',
  ];

  return {
    isError: true,
    content: [
      {
        type: 'text',
        text: lines.join('\n'),
      },
    ],
    stage2Validation: {
      kind,
      filePath,
      backupPath,
      corruptPath,
      error: errorMessage,
      originalResult: toolResult,
    },
  };
}

// Per-file edit_file lock map to serialize edits on the same path.
// This implements the EMERGENCY requirement: queue edit_file operations
// per absolute path so Guardian Stage 2 and the OS never collide on
// temp-file renames or __pycache__ updates.
const EDIT_FILE_LOCKS = new Map();
// Per-file JEWEL lock map to serialize nexus_transform_jewel operations on the
// same working_gem JSON. This prevents concurrent JEWELSTORM edits from
// colliding on a single jewel_file path.
const JEWEL_LOCKS = new Map();
// Global lock maps for QUILL and JEWELSTORM Python script executions invoked via run_command.
// We currently key them with a single global key so all QUILL (or JEWELSTORM)
// operations are strictly serialized with a small guard interval, mirroring
// the edit_file lock spacing semantics.
const QUILL_RUN_LOCKS = new Map();
const JEWEL_RUN_LOCKS = new Map();

// ═══════════════════════════════════════════════════════════════════════════
// TOOL EXCLUSION SETS FRAMEWORK
// ═══════════════════════════════════════════════════════════════════════════
//
// Prevents specific tool calls from running in parallel when they could
// conflict with each other (e.g., nexus_anchor_jewels and nexus_weave_enchanted_async
// both operating on the same NEXUS tag/terrain files).
//
// Each exclusion set has:
// - setId: Human-readable identifier
// - tools: Array of tool matchers, each with:
//     * toolName: Exact tool name to match (optional)
//     * toolNameContains: Case-insensitive substring match on tool name (optional)
//     * argKey: Optional - which argument field to inspect on toolArgs
//     * argPattern: Optional - RegExp tested against that argument value
//
// Logic: If ANY tool in a set is currently executing, NO OTHER tool in that
// same set can start until the first one completes. Different sets can run
// in parallel (they track different resource conflicts).
//
// Extensible: Add more sets as needed (NEXUS operations, file mutations, etc.)
//
const TOOL_EXCLUSION_SETS = [
  {
    setId: 'nexus-jewel-weave',
    description:
      'All NEXUS-related operations (MCP tools with "nexus" in the name, plus run_command whose command contains "nexus") are serialized to avoid races between mapping, JEWELSTORM, and WEAVE.',
    tools: [
      // Any MCP tool whose name contains "nexus" (case-insensitive)
      { toolNameContains: 'nexus' },
      // Any run_command whose command string mentions "nexus" (case-insensitive)
      { toolName: 'run_command', argKey: 'command', argPattern: /nexus/i },
    ],
  },
  {
    setId: 'sql-autopilot',
    description:
      'db-autopilot SQL pipeline (write .sql locally, SCP via WSL, execute via dbap_run.py) serialized globally to avoid file-not-found races.',
    tools: [
      // Local SQL file creation for db-autopilot
      { toolName: 'write_file', argKey: 'path', argPattern: /\.sql$/i },
      { toolName: 'write_text_file', argKey: 'path', argPattern: /\.sql$/i },
      // WSL scp step copying .sql into ~/db-autopilot/tmp on A100
      {
        toolName: 'run_command',
        argKey: 'command',
        argPattern: /scp.*\.sql/i,
      },
      // db-autopilot execution step on A100
      {
        toolName: 'exec',
        argKey: 'command',
        argPattern: /dbap_run\.py/i,
      },
    ],
  },
  {
    setId: 'connector-deploy',
    description:
      'MCP connector deployment operations (copy updated server.js into typingmind-mcp-fork and git add/commit/push in that repo) serialized to avoid races.',
    tools: [
      // WSL cp from Obsidian MCP_Servers typingmind_mcp_connector into typingmind-mcp-fork repo
      {
        toolName: 'run_command',
        argKey: 'command',
        // Any WSL cp-like command (typically used for copying built code into repos)
        argPattern: /\bcp\b/i,
      },
      // Any git-related run_command (git add/commit/push) – grouping is handled
      // in combination with the global git lock to avoid overlapping deploy steps.
      {
        toolName: 'run_command',
        argKey: 'command',
        argPattern: /\bgit\b/i,
      },
    ],
  },
  // Future sets can be added here:
  // {
  //   setId: 'workflowy-bulk-import',
  //   description: 'Workflowy bulk import/export operations',
  //   tools: [
  //     { toolName: 'workflowy_bulk_import' },
  //     { toolName: 'workflowy_bulk_export' },
  //   ],
  // },
];

// Active locks per exclusion set (Map: setId -> Promise)
const EXCLUSION_SET_LOCKS = new Map();

/**
 * Check if a tool call matches any tool matcher in an exclusion set.
 * Returns true if the tool should be part of this exclusion set's queue.
 *
 * Matching supports:
 *  - toolName: exact match (optional)
 *  - toolNameContains: case-insensitive substring match on tool name (optional)
 *  - argKey + argPattern: regex tested against a specific argument value (optional)
 */
function toolMatchesExclusionMatcher(toolName, toolArgs, matcher) {
  if (!matcher) return false;

  // Exact tool name match (if specified)
  if (matcher.toolName && matcher.toolName !== toolName) {
    return false;
  }

  // Substring match on tool name (case-insensitive)
  if (matcher.toolNameContains) {
    const needle = String(matcher.toolNameContains).toLowerCase();
    const name = (toolName || '').toLowerCase();
    if (!name.includes(needle)) {
      return false;
    }
  }

  // Argument-based regex match (e.g., run_command.command contains "nexus")
  if (matcher.argKey && matcher.argPattern) {
    const value = toolArgs && toolArgs[matcher.argKey];
    if (typeof value !== 'string') {
      return false;
    }
    try {
      if (!matcher.argPattern.test(value)) {
        return false;
      }
    } catch (e) {
      console.error('exclusion-set argPattern test failure:', e);
      return false;
    }
  }

  return true;
}

/**
 * Find which exclusion set (if any) this tool call belongs to.
 * Returns the set object or null.
 */
function findExclusionSetForTool(toolName, toolArgs) {
  for (const set of TOOL_EXCLUSION_SETS) {
    for (const matcher of set.tools || []) {
      if (toolMatchesExclusionMatcher(toolName, toolArgs, matcher)) {
        return set;
      }
    }
  }
  return null;
}

/**
 * Run a tool call through an exclusion set's sequential queue.
 * Mirrors the pattern used for QUILL_RUN_LOCKS / JEWEL_RUN_LOCKS / GIT_RUN_LOCKS.
 */
async function runToolWithExclusionSetLock(clientEntry, context, exclusionSet) {
  const setId = exclusionSet.setId;
  const previous = EXCLUSION_SET_LOCKS.get(setId) || Promise.resolve();
  const alreadyQueued = EXCLUSION_SET_LOCKS.has(setId);
  const callId = context.callId || 'unknown';

  try {
    logRunCommandCleanse({
      stage: 'exclusion-set-lock-queue',
      callId,
      toolName: context.toolName,
      exclusionSetId: setId,
      queuedBefore: alreadyQueued,
      ts: new Date().toISOString(),
      hrtime_ns: String(process.hrtime.bigint()),
    });
  } catch (e) {
    console.error('exclusion-set lock queue log failure:', e);
  }

  const chained = previous
    .catch(() => {
      // Swallow errors from prior operations in this set
    })
    .then(async () => {
      try {
        try {
          logRunCommandCleanse({
            stage: 'exclusion-set-lock-run',
            callId,
            toolName: context.toolName,
            exclusionSetId: setId,
            queuedBefore: alreadyQueued,
            ts: new Date().toISOString(),
            hrtime_ns: String(process.hrtime.bigint()),
          });
        } catch (e) {
          console.error('exclusion-set lock run log failure:', e);
        }

        // Match the 500ms guard interval used for other lock types
        await new Promise((resolve) => setTimeout(resolve, 500));

        return clientEntry.client.callTool(
          {
            name: context.toolName,
            arguments: context.toolArgs,
          },
          undefined,
          {
            timeout: 900000,
            resetTimeoutOnProgress: true,
          },
        );
      } catch (err) {
        throw err;
      }
    })
    .finally(() => {
      const current = EXCLUSION_SET_LOCKS.get(setId);
      if (current === chained) {
        EXCLUSION_SET_LOCKS.delete(setId);
      }
      try {
        logRunCommandCleanse({
          stage: 'exclusion-set-lock-complete',
          callId,
          toolName: context.toolName,
          exclusionSetId: setId,
          ts: new Date().toISOString(),
          hrtime_ns: String(process.hrtime.bigint()),
        });
      } catch (e) {
        console.error('exclusion-set lock complete log failure:', e);
      }
    });

  EXCLUSION_SET_LOCKS.set(setId, chained);
  return chained;
}

// ═══════════════════════════════════════════════════════════════════════════
// END TOOL EXCLUSION SETS FRAMEWORK
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Multi-set exclusion helpers: allow a tool call to participate in
 * multiple exclusion sets simultaneously.
 */
function findExclusionSetsForTool(toolName, toolArgs) {
  const matches = [];
  for (const set of TOOL_EXCLUSION_SETS) {
    for (const matcher of set.tools || []) {
      if (toolMatchesExclusionMatcher(toolName, toolArgs, matcher)) {
        matches.push(set);
        break;
      }
    }
  }
  return matches;
}

async function runToolWithExclusionSetsLock(
  clientEntry,
  context,
  exclusionSets,
  runner,
) {
  if (typeof runner !== 'function') {
    // Fallback: behave as if no exclusion sets; direct callTool
    return clientEntry.client.callTool(
      {
        name: context.toolName,
        arguments: context.toolArgs,
      },
      undefined,
      {
        timeout: 900000,
        resetTimeoutOnProgress: true,
      },
    );
  }

  if (!Array.isArray(exclusionSets) || exclusionSets.length === 0) {
    return runner();
  }

  const setIds = exclusionSets
    .map((s) => (s && typeof s.setId === 'string' ? s.setId : null))
    .filter((id) => !!id);

  if (setIds.length === 0) {
    return runner();
  }

  const previousList = setIds.map(
    (id) => EXCLUSION_SET_LOCKS.get(id) || Promise.resolve(),
  );
  const alreadyQueued = setIds.some((id) => EXCLUSION_SET_LOCKS.has(id));
  const callId = context.callId || 'unknown';

  try {
    logRunCommandCleanse({
      stage: 'exclusion-set-lock-queue',
      callId,
      toolName: context.toolName,
      exclusionSetIds: setIds,
      queuedBefore: alreadyQueued,
      ts: new Date().toISOString(),
      hrtime_ns: String(process.hrtime.bigint()),
    });
    console.log(
      '[MCP CONNECTOR] exclusion-set LOCK-QUEUE: callId=%s tool=%s sets=%s queuedBefore=%s',
      callId,
      context.toolName,
      setIds.join(','),
      String(alreadyQueued),
    );
  } catch (e) {
    console.error('exclusion-set lock queue log failure:', e);
  }

  const chained = Promise.all(
    previousList.map((p) => p.catch(() => {})),
  )
    .then(async () => {
      try {
        try {
          logRunCommandCleanse({
            stage: 'exclusion-set-lock-run',
            callId,
            toolName: context.toolName,
            exclusionSetIds: setIds,
            queuedBefore: alreadyQueued,
            ts: new Date().toISOString(),
            hrtime_ns: String(process.hrtime.bigint()),
          });
          console.log(
            '[MCP CONNECTOR] exclusion-set RUN: callId=%s tool=%s sets=%s queuedBefore=%s',
            callId,
            context.toolName,
            setIds.join(','),
            String(alreadyQueued),
          );
        } catch (e) {
          console.error('exclusion-set lock run log failure:', e);
        }

        // Match the 500ms guard interval used for other lock types
        await new Promise((resolve) => setTimeout(resolve, 500));

        return runner();
      } catch (err) {
        throw err;
      }
    })
    .finally(() => {
      for (const setId of setIds) {
        const current = EXCLUSION_SET_LOCKS.get(setId);
        if (current === chained) {
          EXCLUSION_SET_LOCKS.delete(setId);
        }
      }
      try {
        logRunCommandCleanse({
          stage: 'exclusion-set-lock-complete',
          callId,
          toolName: context.toolName,
          exclusionSetIds: setIds,
          ts: new Date().toISOString(),
          hrtime_ns: String(process.hrtime.bigint()),
        });
        console.log(
          '[MCP CONNECTOR] exclusion-set COMPLETE: callId=%s tool=%s sets=%s',
          callId,
          context.toolName,
          setIds.join(','),
        );
      } catch (e) {
        console.error('exclusion-set lock complete log failure:', e);
      }
    });

  for (const setId of setIds) {
    EXCLUSION_SET_LOCKS.set(setId, chained);
  }
  return chained;
}

function getEditFileLockKey(filePath) {
  if (!filePath || typeof filePath !== 'string') return null;
  try {
    return path.normalize(filePath).toLowerCase();
  } catch (e) {
    return filePath;
  }
}

function findSessionDirForHash(rootDir, token) {
  if (!rootDir || !token) {
    return path.join(rootDir || '', token || '');
  }
  try {
    const entries = fs.readdirSync(rootDir, { withFileTypes: true });
    const matches = entries
      .filter(
        (d) =>
          d.isDirectory() &&
          (d.name === token || d.name.endsWith(`_${token}`)),
      )
      .map((d) => d.name);
    if (matches.length === 1) {
      return path.join(rootDir, matches[0]);
    }
    if (matches.length > 1) {
      matches.sort();
      return path.join(rootDir, matches[matches.length - 1]);
    }
    return path.join(rootDir, token);
  } catch (e) {
    console.error('edit_file: failed to locate session dir for hash', token, e);
    return path.join(rootDir, token);
  }
}

function sanitizeEditFileTag(raw) {
  if (typeof raw !== 'string') return null;
  const trimmed = raw.trim();
  if (!trimmed) return null;
  // Replace any run of invalid characters with a single dash, then trim dashes.
  let safe = trimmed.replace(/[^A-Za-z0-9_-]+/g, '-');
  safe = safe.replace(/^-+|-+$/g, '');
  if (!safe) return null;
  // Optional length limit to keep folder names reasonable.
  if (safe.length > 64) {
    safe = safe.slice(0, 64);
  }
  return safe;
}

function clipForLog(str, max) {
  if (typeof str !== 'string') return '';
  if (typeof max !== 'number' || max <= 0) return str;
  if (str.length <= max) return str;
  const clipped = str.slice(0, max);
  return `${clipped}... [${str.length - max} more chars]`;
}

async function runStructuredFileWithStage2GuardLocked(clientEntry, context) {
  const args = context.toolArgs || {};
  const filePath = args.path;
  const key = getEditFileLockKey(filePath);

  // If we don't have a usable path, fall back to normal behaviour.
  if (!key) {
    return runStructuredFileWithStage2Guard(clientEntry, context);
  }

  const previous = EDIT_FILE_LOCKS.get(key) || Promise.resolve();
  const alreadyQueued = EDIT_FILE_LOCKS.has(key);
  const callId = context.callId || 'unknown';

  // Log queueing event with high precision timestamp
  try {
    logRunCommandCleanse({
      stage: 'edit-file-lock-queue',
      callId,
      path: filePath,
      lockKey: key,
      queuedBefore: alreadyQueued,
      ts: new Date().toISOString(),
      hrtime_ns: String(process.hrtime.bigint()),
    });
  } catch (e) {
    console.error('edit-file lock queue log failure:', e);
  }

  // Chain onto the previous promise so edits for the same path are
  // executed strictly sequentially, but edits for different paths can
  // still run in parallel.
  const chained = previous
    .catch(() => {
      // Swallow errors from prior edits so they don't break the chain
      // for subsequent callers.
    })
    .then(async () => {
      try {
        try {
          logRunCommandCleanse({
            stage: 'edit-file-lock-run',
            callId,
            path: filePath,
            lockKey: key,
            queuedBefore: alreadyQueued,
            ts: new Date().toISOString(),
            hrtime_ns: String(process.hrtime.bigint()),
          });
        } catch (e) {
          console.error('edit-file lock run log failure:', e);
        }

        // Small spacing delay between sequential edits on the same file.
        // This helps avoid OS-level rename collisions (EPERM) on Windows
        // even when edits are properly serialized at the connector level.
        await new Promise((resolve) => setTimeout(resolve, 500));

        return await runStructuredFileWithStage2Guard(clientEntry, context);
      } catch (err) {
        throw err;
      }
    })
    .finally(() => {
      const current = EDIT_FILE_LOCKS.get(key);
      if (current === chained) {
        EDIT_FILE_LOCKS.delete(key);
      }
      try {
        logRunCommandCleanse({
          stage: 'edit-file-lock-complete',
          callId,
          path: filePath,
          lockKey: key,
          ts: new Date().toISOString(),
          hrtime_ns: String(process.hrtime.bigint()),
        });
      } catch (e) {
        console.error('edit-file lock complete log failure:', e);
      }
    });

  EDIT_FILE_LOCKS.set(key, chained);
  return chained;
}

// Per-file lock for JEWELSTORM transform_jewel operations, keyed by jewel_file.
// Mirrors the edit_file lock semantics: sequentialize operations per path and
// add a small spacing delay to avoid OS-level file collisions.
async function runTransformJewelWithLock(clientEntry, context) {
  const args = context.toolArgs || {};
  const jewelPath = args.jewel_file;
  const key = getEditFileLockKey(jewelPath);

  // If we don't have a usable path, fall back to normal behaviour.
  if (!key) {
    return clientEntry.client.callTool(
      {
        name: context.toolName,
        arguments: context.toolArgs,
      },
      undefined,
      {
        timeout: 900000,
        resetTimeoutOnProgress: true,
      },
    );
  }

  const previous = JEWEL_LOCKS.get(key) || Promise.resolve();
  const alreadyQueued = JEWEL_LOCKS.has(key);
  const callId = context.callId || 'unknown';

  try {
    logRunCommandCleanse({
      stage: 'jewel-lock-queue',
      callId,
      jewel_file: jewelPath,
      lockKey: key,
      queuedBefore: alreadyQueued,
      ts: new Date().toISOString(),
      hrtime_ns: String(process.hrtime.bigint()),
    });
  } catch (e) {
    console.error('jewel lock queue log failure:', e);
  }

  const chained = previous
    .catch(() => {
      // Swallow errors from prior operations so they don't break the chain
      // for subsequent callers on the same jewel_file.
    })
    .then(async () => {
      try {
        try {
          logRunCommandCleanse({
            stage: 'jewel-lock-run',
            callId,
            jewel_file: jewelPath,
            lockKey: key,
            queuedBefore: alreadyQueued,
            ts: new Date().toISOString(),
            hrtime_ns: String(process.hrtime.bigint()),
          });
        } catch (e) {
          console.error('jewel lock run log failure:', e);
        }

        // Small spacing delay between sequential transform_jewel operations on
        // the same file. This mirrors the edit_file 500ms guard interval.
        await new Promise((resolve) => setTimeout(resolve, 500));

        return await clientEntry.client.callTool(
          {
            name: context.toolName,
            arguments: context.toolArgs,
          },
          undefined,
          {
            timeout: 900000,
            resetTimeoutOnProgress: true,
          },
        );
      } catch (err) {
        throw err;
      }
    })
    .finally(() => {
      const current = JEWEL_LOCKS.get(key);
      if (current === chained) {
        JEWEL_LOCKS.delete(key);
      }
      try {
        logRunCommandCleanse({
          stage: 'jewel-lock-complete',
          callId,
          jewel_file: jewelPath,
          lockKey: key,
          ts: new Date().toISOString(),
          hrtime_ns: String(process.hrtime.bigint()),
        });
      } catch (e) {
        console.error('jewel lock complete log failure:', e);
      }
    });

  JEWEL_LOCKS.set(key, chained);
  return chained;
}

// Global run_command lock for QUILL Python scripts. We serialize all detected
// QUILL run_command calls through a single queue and add a 500ms spacing delay,
// mirroring the edit_file per-path lock semantics but at QUILL-operation granularity.
async function runQuillRunCommandWithLock(clientEntry, context) {
  const key = 'quill-global';
  const previous = QUILL_RUN_LOCKS.get(key) || Promise.resolve();
  const alreadyQueued = QUILL_RUN_LOCKS.has(key);
  const callId = context.callId || 'unknown';

  try {
    logRunCommandCleanse({
      stage: 'quill-run-lock-queue',
      callId,
      toolName: context.toolName,
      command:
        (context && context.toolArgs && context.toolArgs.command) || '(none)',
      lockKey: key,
      queuedBefore: alreadyQueued,
      ts: new Date().toISOString(),
      hrtime_ns: String(process.hrtime.bigint()),
    });
  } catch (e) {
    console.error('quill run-command lock queue log failure:', e);
  }

  const chained = previous
    .catch(() => {
      // Swallow errors from prior QUILL operations so they don't break the chain.
    })
    .then(async () => {
      try {
        try {
          logRunCommandCleanse({
            stage: 'quill-run-lock-run',
            callId,
            toolName: context.toolName,
            command:
              (context && context.toolArgs && context.toolArgs.command) ||
              '(none)',
            lockKey: key,
            queuedBefore: alreadyQueued,
            ts: new Date().toISOString(),
            hrtime_ns: String(process.hrtime.bigint()),
          });
        } catch (e) {
          console.error('quill run-command lock run log failure:', e);
        }

        // Match edit_file guard interval: 500ms between sequential operations.
        await new Promise((resolve) => setTimeout(resolve, 500));

        return clientEntry.client.callTool(
          {
            name: context.toolName,
            arguments: context.toolArgs,
          },
          undefined,
          {
            timeout: 900000,
            resetTimeoutOnProgress: true,
          },
        );
      } catch (err) {
        throw err;
      }
    })
    .finally(() => {
      const current = QUILL_RUN_LOCKS.get(key);
      if (current === chained) {
        QUILL_RUN_LOCKS.delete(key);
      }
      try {
        logRunCommandCleanse({
          stage: 'quill-run-lock-complete',
          callId,
          toolName: context.toolName,
          command:
            (context && context.toolArgs && context.toolArgs.command) ||
            '(none)',
          lockKey: key,
          ts: new Date().toISOString(),
          hrtime_ns: String(process.hrtime.bigint()),
        });
      } catch (e) {
        console.error('quill run-command lock complete log failure:', e);
      }
    });

  QUILL_RUN_LOCKS.set(key, chained);
  return chained;
}

// Global run_command lock for JEWELSTORM Python scripts. Same pattern as QUILL:
// serialize all jewelstrike/jewelmorph/jeweldrop calls with a 500ms spacing delay.
async function runJewelRunCommandWithLock(clientEntry, context) {
  const key = 'jewel-global';
  const previous = JEWEL_RUN_LOCKS.get(key) || Promise.resolve();
  const alreadyQueued = JEWEL_RUN_LOCKS.has(key);
  const callId = context.callId || 'unknown';

  try {
    logRunCommandCleanse({
      stage: 'jewel-run-lock-queue',
      callId,
      toolName: context.toolName,
      command:
        (context && context.toolArgs && context.toolArgs.command) || '(none)',
      lockKey: key,
      queuedBefore: alreadyQueued,
      ts: new Date().toISOString(),
      hrtime_ns: String(process.hrtime.bigint()),
    });
  } catch (e) {
    console.error('jewel run-command lock queue log failure:', e);
  }

  const chained = previous
    .catch(() => {
      // Swallow errors from prior operations so they don't break the chain.
    })
    .then(async () => {
      try {
        try {
          logRunCommandCleanse({
            stage: 'jewel-run-lock-run',
            callId,
            toolName: context.toolName,
            command:
              (context && context.toolArgs && context.toolArgs.command) ||
              '(none)',
            lockKey: key,
            queuedBefore: alreadyQueued,
            ts: new Date().toISOString(),
            hrtime_ns: String(process.hrtime.bigint()),
          });
        } catch (e) {
          console.error('jewel run-command lock run log failure:', e);
        }

        // Same 500ms safety spacing as edit_file / QUILL.
        await new Promise((resolve) => setTimeout(resolve, 500));

        return clientEntry.client.callTool(
          {
            name: context.toolName,
            arguments: context.toolArgs,
          },
          undefined,
          {
            timeout: 900000,
            resetTimeoutOnProgress: true,
          },
        );
      } catch (err) {
        throw err;
      }
    })
    .finally(() => {
      const current = JEWEL_RUN_LOCKS.get(key);
      if (current === chained) {
        JEWEL_RUN_LOCKS.delete(key);
      }
      try {
        logRunCommandCleanse({
          stage: 'jewel-run-lock-complete',
          callId,
          toolName: context.toolName,
          command:
            (context && context.toolArgs && context.toolArgs.command) ||
            '(none)',
          lockKey: key,
          ts: new Date().toISOString(),
          hrtime_ns: String(process.hrtime.bigint()),
        });
      } catch (e) {
        console.error('jewel run-command lock complete log failure:', e);
      }
    });

  JEWEL_RUN_LOCKS.set(key, chained);
  return chained;
}

/**
 * Determine if a PowerShell run_command invocation is in the small
 * safe-operations whitelist (SNAPNAX, Obsidian/PARALLAX, Araxis).
 *
 * This section also contains the run_command cleansing framework:
 *  - We can transform known-good but fragile commands (Araxis, SNAPNAX, Obsidian, etc.)
 *  - We log every transformation to a dedicated log for later inspection
 *  - Future cleansers can be added without touching the HTTP routes.
 */

// Log for all run_command cleansing activity (including no-op detections)
const RUN_COMMAND_CLEANSE_LOG =
  'E:\\__daniel347x\\__Obsidian\\__Inking into Mind\\--TypingMind\\Projects - All\\Projects - Individual\\TODO\\temp\\run_command_cleanse.log';

function logRunCommandCleanse(entry) {
  try {
    const payload = {
      timestamp: new Date().toISOString(),
      marker: 'run_command_cleansing_v1',
      ...entry,
    };
    fs.appendFile(
      RUN_COMMAND_CLEANSE_LOG,
      JSON.stringify(payload) + '\n',
      () => {},
    );
  } catch (e) {
    console.error('run_command cleanse log failure:', e);
  }
}

/**
 * Very lightweight parser that finds quoted Windows paths of the form:
 *   "<drive>:\\...\\something.ext"
 * where the path is immediately preceded by one of ", ', or `.
 *
 * This is intentionally conservative and only used for cleansing helpers.
 */
function findQuotedWindowsPathsInCommand(cmd) {
  const results = [];
  if (!cmd || typeof cmd !== 'string') return results;

  const len = cmd.length;
  for (let i = 0; i < len - 3; i += 1) {
    const delim = cmd[i];
    if (delim !== '"' && delim !== "'" && delim !== '`') continue;
    const drive = cmd[i + 1];
    if (!/[A-Za-z]/.test(drive)) continue;
    if (cmd[i + 2] !== ':' || cmd[i + 3] !== '\\') continue;

    const start = i + 1; // start of path (after the quote/backtick)
    let j = start;
    while (j < len && cmd[j] !== delim) {
      j += 1;
    }
    if (j >= len) break; // unmatched delimiter, bail out

    const pathText = cmd.slice(start, j);
    results.push({
      path: pathText,
      start,
      end: j,
      delim,
    });
    i = j; // skip past this path
  }

  return results;
}

/**
 * Find WSL/Unix-style paths in commands and convert them to Windows paths.
 * Detects patterns like: '/mnt/e/...' or '/mnt/c/Users/...' (quoted or unquoted)
 * Converts to: 'E:\\...' or 'C:\\Users\\...'
 * 
 * Handles:
 * - Single-quoted paths: 'cp \'/mnt/e/path with spaces\' ...'
 * - Double-quoted paths: "cp \"/mnt/e/path\" ..."
 * - Unquoted paths: cp /mnt/e/path_no_spaces ...
 */
function findAndConvertUnixPaths(cmd) {
  const results = [];
  if (!cmd || typeof cmd !== 'string') return results;

  // Strategy: Look for '/mnt/[drive]/' prefix, then consume until quote end or whitespace
  // We'll scan character by character to handle quotes properly
  
  const len = cmd.length;
  let i = 0;
  
  while (i < len) {
    // Look for '/mnt/' prefix
    if (cmd.slice(i, i + 5) === '/mnt/') {
      // Check if next char is a drive letter
      if (i + 5 < len && /[a-z]/i.test(cmd[i + 5])) {
        const driveLetter = cmd[i + 5].toUpperCase();
        
        // Check if followed by '/'
        if (i + 6 < len && cmd[i + 6] === '/') {
          // We have '/mnt/[drive]/' - now extract the rest of the path
          const pathStart = i + 7; // Start after '/mnt/e/'
          
          // Determine if this path is quoted
          let quoteChar = null;
          if (i > 0 && (cmd[i - 1] === "'" || cmd[i - 1] === '"')) {
            quoteChar = cmd[i - 1];
          }
          
          // Find path end (quote close or whitespace)
          let pathEnd = pathStart;
          while (pathEnd < len) {
            const ch = cmd[pathEnd];
            if (quoteChar) {
              // Inside quotes - stop at matching quote
              if (ch === quoteChar) break;
            } else {
              // Unquoted - stop at whitespace or quote
              if (ch === ' ' || ch === "'" || ch === '"') break;
            }
            pathEnd++;
          }
          
          const unixPath = cmd.slice(pathStart, pathEnd);
          const windowsPath = `${driveLetter}:\\${unixPath.replace(/\//g, '\\')}`;
          
          results.push({
            path: windowsPath,
            original: cmd.slice(i, pathEnd),
          });
          
          i = pathEnd; // Skip past this path
          continue;
        }
      }
    }
    i++;
  }

  return results;
}

/**
 * Build a canonical Araxis Merge PowerShell command that is robust
 * against spaces in file paths.
 *
 * NOTE: This intentionally uses a simpler -ArgumentList @('left','right')
 * form instead of reusing whatever the agent provided. The goal is to
 * give Araxis exactly two string arguments (left file, right file) with
 * safe quoting.
 */
function cleanExtractedPath(p) {
  if (!p || typeof p !== 'string') return p;
  let prev = null;
  let cleaned = p;
  let safety = 0;
  // Fixed-point normalization: keep stripping obvious junk (backticks, quotes,
  // odd trailing backslashes) until the string stops changing, or we hit a
  // small iteration limit.
  while (cleaned !== prev && safety < 5) {
    prev = cleaned;
    cleaned = cleaned.trim();
    cleaned = cleaned.replace(/[`"']+$/g, '');
    cleaned = cleaned.replace(/\\+$/g, (match) =>
      match.length % 2 === 0 ? match : match.slice(0, -1),
    );
    safety += 1;
    try {
      logRunCommandCleanse({
        kind: 'araxis-path-normalize-iteration',
        iteration: safety,
        before: prev,
        after: cleaned,
      });
    } catch (e) {
      console.error('araxis path normalize iteration log failure:', e);
    }
  }
  return cleaned;
}

function buildAraxisCommand(leftPath, rightPath) {
  if (!leftPath || !rightPath) return null;

  const pythonScript =
    'E:\\__daniel347x\\__Obsidian\\__Inking into Mind\\--TypingMind\\Projects - All\\Projects - Individual\\TODO\\araxis_trampoline.py';

  // Escape double quotes inside arguments for safe command-line construction
  const esc = (p) => String(p).replace(/"/g, '\\"');

  const p1 = esc(leftPath);
  const p2 = esc(rightPath);

  // Direct Python trampoline: non-blocking launch of Araxis via subprocess.Popen
  // in araxis_trampoline.py. This avoids PowerShell quoting hell entirely
  // while preserving the exact Merge.exe "left" "right" semantics.
  return `python "${pythonScript}" "${p1}" "${p2}"`;
}

/**
 * Detect and transform Araxis Merge PowerShell invocations that were
 * generated with fragile escaping. If we can confidently extract two
 * .md paths, we rebuild the command with a known-good quoting pattern.
 */
function transformAraxisCommand(rawCommand) {
  if (!rawCommand || typeof rawCommand !== 'string') {
    return { changed: false, command: rawCommand };
  }

  const lower = rawCommand.toLowerCase();
  const hasMergeExe = lower.includes('araxis merge\\merge.exe');

  const isPowershellAraxis =
    hasMergeExe &&
    lower.includes('start-process') &&
    lower.includes('-argumentlist');

  const isCmdAraxis =
    hasMergeExe &&
    (lower.includes('cmd /c') || lower.includes('cmd.exe /c'));

  const looksLikeAraxis = isPowershellAraxis || isCmdAraxis;

  if (!looksLikeAraxis) {
    return { changed: false, command: rawCommand };
  }

  const quotedPaths = findQuotedWindowsPathsInCommand(rawCommand);

  // Grab all non-executable paths (skip the Araxis .exe itself)
  let filePaths = quotedPaths
    .map((q) => q.path)
    .filter((p) => !/merge\.exe$/i.test(p));

  // Fallback: if findQuotedWindowsPathsInCommand didn't find two paths
  // (common with complex nesting like 'start ""'), try a simpler regex
  // that just looks for any quoted strings that look like absolute paths.
  if (filePaths.length < 2) {
    const looseMatches = [];
    // Match "E:\..." or 'E:\...' (lazy)
    const re = /["']([A-Za-z]:\\[^"']+)["']/g;
    let m;
    while ((m = re.exec(rawCommand)) !== null) {
      if (!/merge\.exe$/i.test(m[1])) {
        looseMatches.push(m[1]);
      }
    }
    // Append any new finds unique from what we already have
    for (const match of looseMatches) {
      if (!filePaths.includes(match)) {
        filePaths.push(match);
      }
    }
  }

  if (filePaths.length < 2) {
    logRunCommandCleanse({
      kind: 'araxis-detect-failed',
      originalCommand: rawCommand,
      reason: 'could-not-find-two-target-paths',
      discoveredPaths: quotedPaths,
    });
    return { changed: false, command: rawCommand };
  }

  const leftPath = cleanExtractedPath(filePaths[filePaths.length - 2]);
  const rightPath = cleanExtractedPath(filePaths[filePaths.length - 1]);

  // Optional safety: only transform if both target files actually exist.
  let leftExists = false;
  let rightExists = false;
  try {
    leftExists = fs.existsSync(leftPath);
    rightExists = fs.existsSync(rightPath);
  } catch (e) {
    console.error('Araxis path existence check failed:', e);
  }

  if (!leftExists || !rightExists) {
    logRunCommandCleanse({
      kind: 'araxis-paths-missing',
      originalCommand: rawCommand,
      leftPath,
      rightPath,
      leftExists,
      rightExists,
    });
    return { changed: false, command: rawCommand };
  }

  const rebuilt = buildAraxisCommand(leftPath, rightPath);
  if (!rebuilt) {
    logRunCommandCleanse({
      kind: 'araxis-build-failed',
      originalCommand: rawCommand,
      leftPath,
      rightPath,
    });
    return { changed: false, command: rawCommand };
  }

  if (rebuilt === rawCommand) {
    // Nothing actually changed – no need to log noisy entries.
    return { changed: false, command: rawCommand };
  }

  logRunCommandCleanse({
    kind: 'araxis-transformed',
    originalCommand: rawCommand,
    transformedCommand: rebuilt,
    leftPath,
    rightPath,
  });

  return { changed: true, command: rebuilt };
}

/**
 * Build a canonical WindSurf CMD command that is robust
 * against spaces in file paths.
 *
 * Uses CMD double-quote escaping instead of PowerShell (PowerShell array
 * syntax failed - WindSurf splits arguments incorrectly).
 * The -r flag reuses existing WindSurf window instead of opening new instance.
 */
function buildWindSurfCommand(filePath) {
  if (!filePath) return null;

  const windsurfExe =
    'C:\\Users\\danie\\AppData\\Local\\Programs\\Windsurf\\Windsurf.exe';

  // CMD syntax: cmd /c ""program.exe" -flag "path with spaces""
  // The outer quotes are consumed by cmd /c, inner quotes protect the path.
  return `cmd /c ""${windsurfExe}" -r "${filePath}""`;
}

/**
 * Detect and transform WindSurf PowerShell invocations that were
 * generated with fragile escaping. If we can confidently extract a
 * file path, we rebuild the command with known-good quoting pattern.
 */
function transformWindSurfCommand(rawCommand) {
  if (!rawCommand || typeof rawCommand !== 'string') {
    return { changed: false, command: rawCommand };
  }

  const lower = rawCommand.toLowerCase();
  const looksLikeWindSurf =
    lower.includes('start-process') &&
    (lower.includes('windsurf.exe') || lower.includes('windsrf.exe'));

  if (!looksLikeWindSurf) {
    return { changed: false, command: rawCommand };
  }

  const quotedPaths = findQuotedWindowsPathsInCommand(rawCommand);

  // Filter out the .exe itself - we want the target file
  let filePaths = quotedPaths
    .map((q) => q.path)
    .filter((p) => !p.toLowerCase().endsWith('.exe'));

  // Fallback: if findQuotedWindowsPathsInCommand didn't find the path,
  // try a simpler regex for paths in -ArgumentList context
  if (filePaths.length === 0) {
    const argListMatch = rawCommand.match(/-ArgumentList[^'"]*['"]([E-Z]:\\[^'"]+)['"]/);
    if (argListMatch && argListMatch[1]) {
      filePaths = [argListMatch[1]];
    }
  }

  if (filePaths.length === 0) {
    logRunCommandCleanse({
      kind: 'windsurf-no-file-path',
      originalCommand: rawCommand,
      reason: 'could-not-extract-file-path',
      quotedPathsFound: quotedPaths.length,
    });
    return { changed: false, command: rawCommand };
  }

  const targetFile = filePaths[0]; // Use first non-.exe path
  const rebuilt = buildWindSurfCommand(targetFile);

  if (!rebuilt) {
    logRunCommandCleanse({
      kind: 'windsurf-build-failed',
      originalCommand: rawCommand,
      targetFile,
    });
    return { changed: false, command: rawCommand };
  }

  if (rebuilt === rawCommand) {
    // Nothing actually changed
    return { changed: false, command: rawCommand };
  }

  logRunCommandCleanse({
    kind: 'windsurf-transformed',
    originalCommand: rawCommand,
    transformedCommand: rebuilt,
    targetFile,
  });

  return { changed: true, command: rebuilt };
}

/**
 * QUARTZ PHASE 2: GUARDIAN INTERCEPTION
 *
 * This logic enforces the Quill Invariant:
 * 1. Tomes (original files) locked by an active Quill session are IMMUTABLE to all tools.
 * 2. Working Stones (temp files) are MUTABLE only if they belong to an active session.
 */

function getQuillIndex() {
  try {
    if (!fs.existsSync(QUILL_INDEX_PATH)) {
      return {};
    }
    const content = fs.readFileSync(QUILL_INDEX_PATH, 'utf8');
    return JSON.parse(content);
  } catch (e) {
    console.error('Failed to read Quill Index:', e);
    return {};
  }
}

function validateQuillGuardianship(toolName, toolArgs) {
  // 1. Classify Command Intent
  let isDangerous = false;
  let commandString = '';

  // Tier 1: Direct File Tools (Always Dangerous)
  const directWriteTools = new Set([
    'write_file',
    'edit_file',
    'move_file',
    'delete_file',
    'ssh-write-chunk',
    'ssh-edit-block'
  ]);

  if (directWriteTools.has(toolName)) {
    isDangerous = true;
    // Extract path(s) for checking
    if (toolArgs.path) commandString += ` "${toolArgs.path}"`;
    if (toolArgs.source) commandString += ` "${toolArgs.source}"`;
    if (toolArgs.destination) commandString += ` "${toolArgs.destination}"`;
  }

  // Tier 2: Run Command (Heuristic Check)
  if (toolName === 'run_command' && toolArgs.command) {
    const cmd = toolArgs.command;
    // Heuristic: dangerous verbs
    // We match these loosely to catch variations like "cp", "mv", "Set-Content", ">", ">>"
    // The goal is broad safety, accepting some false positives.
    const dangerousVerbs = [
      'cp ', 'mv ', 'rm ', 'del ', 'copy ', 'move ', 'ren ', 'rename ',
      'sed ', 'tee ', // stream editors/redirectors
      'Set-Content', 'Add-Content', 'Out-File', 'Clear-Content',
      'New-Item', 'Remove-Item', 'Move-Item', 'Copy-Item', 'Rename-Item', // PowerShell cmdlets
      '>', '>>' // redirection is dangerous
    ];
    
    // Exception: Safe verifications (Araxis, WindSurf, etc.) are whitelisted elsewhere,
    // but we still want to check what files they are touching if they *look* like writes.
    // However, Start-Process usually launches viewers. We'll focus on file manipulation verbs.
    
    if (dangerousVerbs.some(v => cmd.includes(v))) {
      isDangerous = true;
      commandString = cmd;
    }
  }

  // If not dangerous, allow.
  if (!isDangerous) {
    return { ok: true };
  }

  // 2. Hunt Paths
  // Use existing extraction logic to find all potential paths in the "command string"
  // (which we constructed from args for direct tools, or is the raw command for run_command)
  const potentialPaths = findQuotedWindowsPathsInCommand(commandString);
  
  // Also extract and convert WSL/Unix paths
  const unixPaths = findAndConvertUnixPaths(commandString);
  for (const up of unixPaths) {
    potentialPaths.push({ path: up.path });
  }
  
  // Also check for raw unquoted paths in direct tool args (since findQuoted... expects quotes)
  if (directWriteTools.has(toolName)) {
    if (toolArgs.path) potentialPaths.push({ path: toolArgs.path });
    if (toolArgs.source) potentialPaths.push({ path: toolArgs.source });
    if (toolArgs.destination) potentialPaths.push({ path: toolArgs.destination });
  }

  if (potentialPaths.length === 0) {
    return { ok: true }; // No paths found to guard
  }

  // 3. Validate against Index
  const index = getQuillIndex();
  
  // Invert index for O(1) lookup of working stones
  // Map: working_path -> tome_path
  const workingToTome = {};
  Object.values(index).forEach(entry => {
    if (entry.working) {
      // Normalize path separators for comparison
      const norm = path.normalize(entry.working).toLowerCase();
      workingToTome[norm] = true;
    }
  });

  for (const item of potentialPaths) {
    const targetPath = path.normalize(item.path); // Normalize slashes
    const targetPathLower = targetPath.toLowerCase();
    const fileName = path.basename(targetPath);

    // CHECK A: Is this a LOCKED TOME?
    // The index keys are the absolute paths to the Tomes.
    // We check if our target matches any key in the index.
    for (const tomeKey of Object.keys(index)) {
        const tomePathLower = path.normalize(tomeKey).toLowerCase();
        if (targetPathLower === tomePathLower) {
             return {
                ok: false,
                error: `🚫 GUARDIAN INTERCEPT: This file is currently a TOME under Quill Strike.\n\n` +
                       `Locked File: ${targetPath}\n\n` +
                       `You cannot edit it directly. You must edit the Working Stone instead.\n` +
                       `Working Stone: ${index[tomeKey].working}`
            };
        }
    }

    // CHECK B: Is this an INVALID WORKING STONE?
    // Heuristic: Filename starts with "qm-" but is NOT in the index as a valid working stone.
    if (fileName.startsWith('qm-')) {
        if (!workingToTome[targetPathLower]) {
             return {
                ok: false,
                error: `🚫 GUARDIAN INTERCEPT: This appears to be a stale or invalid Working Stone.\n\n` +
                       `Target: ${targetPath}\n\n` +
                       `No active Quill session tracks this file. If this is a leftover file, use 'quilldrop.py' to clean up.`
            };
        }
    }
  }

  return { ok: true };
}


/**
 * Detect whether a tool call is a QUILL-related operation.
 *
 * For now we treat QUILL as any run_command invocation that calls one of the
 * core Python scripts:
 *   - quillstrike.py
 *   - quillmorph.py (or historical quillmorphy.py)
 *   - quilldrop.py
 *
 * This can be expanded later (e.g. dedicated MCP tools) without changing
 * the queuing logic.
 */
function isQuillRelatedOperation(toolName, toolArgs) {
  if (toolName !== 'run_command' || !toolArgs || typeof toolArgs.command !== 'string') {
    return false;
  }

  const cmd = toolArgs.command.toLowerCase();

  return (
    cmd.includes('quillstrike.py') ||
    cmd.includes('quillmorph.py') ||
    cmd.includes('quillmorphy.py') || // tolerate historical spelling
    cmd.includes('quilldrop.py')
  );
}

/**
 * Detect whether a tool call is a JEWELSTORM-related operation when invoked via run_command.
 * We look for:
 *   - jewelstrike.py
 *   - jewelmorph.py
 *   - jeweldrop.py
 */
function isJewelstormRelatedOperation(toolName, toolArgs) {
  if (toolName !== 'run_command' || !toolArgs || typeof toolArgs.command !== 'string') {
    return false;
  }

  const cmd = toolArgs.command.toLowerCase();

  return (
    cmd.includes('jewelstrike.py') ||
    cmd.includes('jewelmorph.py') ||
    cmd.includes('jeweldrop.py')
  );
}

/**
 * Apply all known cleansing transforms to run_command arguments.
 * Returns either the original args or a shallow-cloned copy with
 * `command` rewritten.
 */
function cleanseRunCommandArgs(toolArgs) {
  if (!toolArgs || typeof toolArgs.command !== 'string') {
    return toolArgs || {};
  }

  let command = toolArgs.command;
  let changed = false;

  // 1) Araxis Merge command fixer
  const araxis = transformAraxisCommand(command);
  if (araxis.changed) {
    command = araxis.command;
    changed = true;
  }

  // 2) WindSurf command fixer
  const windsurf = transformWindSurfCommand(command);
  if (windsurf.changed) {
    command = windsurf.command;
    changed = true;
  }

  if (!changed) {
    return toolArgs;
  }

  return {
    ...toolArgs,
    command,
  };
}

function isSafePowerShellCommand(rawCommand) {
  if (!rawCommand || typeof rawCommand !== 'string') {
    return false;
  }
  const cmd = rawCommand.toLowerCase();

  // If this is our normalized Araxis command, it will include the marker.
  const hasAraxisMarker = cmd.includes('#araxis_safe');

  // SNAPNAX (Workflowy deep link)
  const hasSnapnax =
    cmd.includes("start-process 'workflowy://") ||
    cmd.includes('start-process "workflowy://');

  // Obsidian (including PARALLAX diff)
  const hasObsidian =
    cmd.includes("start-process 'obsidian://") ||
    cmd.includes('start-process "obsidian://');

  // Araxis Merge compare (allow any Start-Process pattern pointing at Araxis Merge)
  const hasAraxis =
    cmd.includes('start-process') &&
    cmd.includes('araxis merge') &&
    cmd.includes('merge.exe');

  // Git push via PowerShell (safe: no file mutation by PowerShell itself)
  const hasGitPush = cmd.includes('git push');

  // Copy-Item (safe: file copy operation, no content mutation)
  const hasCopyItem = cmd.includes('copy-item');

  // WindSurf code editor (safe: URI-style launch, no file corruption)
  const hasWindSurf =
    cmd.includes('start-process') &&
    (cmd.includes('windsurf.exe') || cmd.includes('windsrf.exe'));

  return (
    hasAraxisMarker ||
    hasSnapnax ||
    hasObsidian ||
    hasAraxis ||
    hasGitPush ||
    hasCopyItem ||
    hasWindSurf
  );
}

/**
 * Main dispatcher for all tool calls.
 *
 * This is the single choke point for every MCP tool invocation. It can:
 *  - Run group-level pre-handlers (file I/O, run_command, etc.)
 *  - Route to per-tool handlers (if/when we add them)
 *  - Fall back to the default client.callTool() behaviour.
 */
function generateCallId() {
  // Simple per-call identifier: 6 hex chars from random bytes
  try {
    return Math.random().toString(16).slice(2, 8);
  } catch (e) {
    return 'call-xxxxxx';
  }
}

async function dispatchToolCall(clientEntry, toolName, toolArgs) {
  const context = {
    clientId: clientEntry.id,
    clientEntry,
    toolName,
    toolArgs: toolArgs || {},
    callId: generateCallId(),
  };

  // Stage 0: global entry log for this tool call
  try {
    fs.appendFile(
      RUN_COMMAND_CLEANSE_LOG,
      JSON.stringify({
        timestamp: new Date().toISOString(),
        stage: 'stage0-entry',
        callId: context.callId,
        toolName,
        path:
          (toolArgs &&
            toolArgs.path) ||
          (toolArgs && toolArgs.command) ||
          '(none)',
      }) + '\n',
      () => {},
    );
  } catch (e) {
    console.error('stage0 entry log failure:', e);
  }

  // QUARTZ PHASE 2: GUARDIAN INTERCEPTION
  // Check if this operation touches a locked Quill Tome or invalid Working Stone
  const guard = validateQuillGuardianship(toolName, context.toolArgs);
  if (!guard.ok) {
    console.log(`🚫 GUARDIAN BLOCKED: ${toolName} on protected file.`);
    try {
      logRunCommandCleanse({
        stage: 'stage1-quartz-guardian-block',
        callId: context.callId,
        toolName,
        reason: 'quill-guardian-intercept',
        error: guard.error,
      });
    } catch (e) {
      console.error('stage1 guardian log failure:', e);
    }
    return {
      content: [{ type: 'text', text: guard.error }],
      isError: true
    };
  }

  // Hard block raw `npx asar` invocations in run_command.
  // This prevents fragile inline ASAR pack/copy chains and forces use of the
  // GLIMPSE deploy trampoline Python script instead.
  if (
    toolName === 'run_command' &&
    context.toolArgs &&
    typeof context.toolArgs.command === 'string' &&
    /npx\s+asar/i.test(context.toolArgs.command)
  ) {
    const msg =
      '🚫 MCP CONNECTOR: Raw `npx asar` invocations are disabled.\n\n' +
      'Use the GLIMPSE deploy trampoline instead:\n\n' +
      '  python "E:\\__daniel347x\\__Obsidian\\__Inking into Mind\\--TypingMind\\Projects - All\\Projects - Individual\\TODO\\glimpse_deploy_trampoline.py" <version-tag>\n\n' +
      'This script handles WSL `npx asar pack` and copying into Workflowy resources.\n';

    try {
      logRunCommandCleanse({
        stage: 'npx-asar-block',
        callId: context.callId,
        toolName,
        command: context.toolArgs.command,
        reason: 'raw-npx-asar-disallowed',
      });
    } catch (e) {
      console.error('npx asar block log failure:', e);
    }

    return {
      isError: true,
      content: [{ type: 'text', text: msg }],
    };
  }

  // Group-level preflight handlers (Stage 1)
  if (isFileIoTool(toolName)) {
    try {
      logRunCommandCleanse({
        stage: 'stage1-fileio-preflight-enter',
        callId: context.callId,
        toolName,
        path:
          (context &&
            context.toolArgs &&
            context.toolArgs.path) || '(none)',
      });
    } catch (e) {
      console.error('stage1 file-io log failure:', e);
    }
    await handleFileIoPreflight(context);
  }

  // TODO: in future, add per-tool handlers here (e.g., run_command routing).

  // Stage 2 guardian: for edit_file and write_file on structurally constrained files,
  // wrap the underlying call with per-edit backup + post-call validation.
  // For edit_file we also enforce a per-path queue so that multiple
  // edit_file calls against the same file are executed sequentially
  // through Guardian Stage 2, avoiding OS-level collisions.
  if (context.toolName === 'edit_file') {
    try {
      logRunCommandCleanse({
        stage: 'stage2-structured-guard-enter',
        callId: context.callId,
        toolName,
        path:
          (context &&
            context.toolArgs &&
            context.toolArgs.path) || '(none)',
      });
    } catch (e) {
      console.error('stage2 structured-guard log failure:', e);
    }
    console.log(
      '[MCP CONNECTOR] Stage2 GUARD ENTER (edit_file): callId=%s path=%s',
      context.callId,
      (context && context.toolArgs && context.toolArgs.path) || '(none)',
    );

    const args = context.toolArgs || {};
    const basePath =
      (context &&
        context.toolArgs &&
        context.toolArgs.path) || '(none)';

    // Guard: do not allow edit_file to target files inside the tracking root.
    const candidatePath = args.path;
    if (candidatePath && EDIT_FILE_TRACKING_ROOT) {
      try {
        const normalizedTarget = path.normalize(candidatePath).toLowerCase();
        const normalizedRoot = path
          .normalize(EDIT_FILE_TRACKING_ROOT)
          .toLowerCase();
        if (normalizedTarget.startsWith(normalizedRoot)) {
          return {
            isError: true,
            content: [
              {
                type: 'text',
                text:
                  '🚫 MCP connector: direct edit_file calls targeting the tracking folder (.edit_files_tracking) are not allowed.\n' +
                  'Use edit_session_hash with the original file path instead.',
              },
            ],
          };
        }
      } catch (e) {
        console.error('edit_file tracking-folder guard error:', e);
      }
    }

    let edits = Array.isArray(args.edits) ? [...args.edits] : [];
    const editsFile =
      typeof args.edits_file === 'string' && args.edits_file.length > 0
        ? args.edits_file
        : null;
    const sessionHashArg =
      typeof args.edit_session_hash === 'string' &&
      args.edit_session_hash.length > 0
        ? args.edit_session_hash
        : null;

    let sessionHash = sessionHashArg;
    let sessionDir = null;
    let sessionOrigPath = null;
    let sessionSuccessPath = null;
    let sessionEditsPath = null;
    let origBackupPath = null;

    if (editsFile) {
      try {
        const specText = await fs.promises.readFile(editsFile, 'utf8');
        const spec = JSON.parse(specText);
        if (spec && Array.isArray(spec.edits)) {
          edits = spec.edits.map((e) =>
            e && typeof e === 'object' ? { ...e } : e,
          );
        } else {
          console.error(
            'edit_file: edits_file JSON missing `edits` array:',
            editsFile,
          );
        }
      } catch (e) {
        console.error('edit_file: failed to load edits_file:', editsFile, e);
      }
    }

    if (sessionHashArg) {
      try {
        sessionDir = path.join(EDIT_FILE_TRACKING_ROOT, sessionHashArg);
        const sessionSpecText = await fs.promises.readFile(
          path.join(sessionDir, 'edits_remaining.json'),
          'utf8',
        );
        const sessionSpec = JSON.parse(sessionSpecText);
        if (sessionSpec && Array.isArray(sessionSpec.edits)) {
          edits = sessionSpec.edits.map((e) =>
            e && typeof e === 'object' ? { ...e } : e,
          );
        }
        if (sessionSpec && typeof sessionSpec.path === 'string') {
          args.path = sessionSpec.path;
        }
      } catch (e) {
        console.error(
          'edit_file: failed to load session edits_remaining.json for hash',
          sessionHashArg,
          e,
        );
      }
    }

    if (!Array.isArray(edits) || edits.length === 0) {
      if (args.edits_file) {
        const cleanedArgs = { ...args, edits, edits_file: undefined };
        const cleanedContext = { ...context, toolArgs: cleanedArgs };
        return runStructuredFileWithStage2GuardLocked(
          clientEntry,
          cleanedContext,
        );
      }
      return runStructuredFileWithStage2GuardLocked(clientEntry, context);
    }

    const cleanedArgs = { ...args, edits, edits_file: undefined };
    let fileText = null;

    const effectivePath = cleanedArgs.path || args.path;

    if (effectivePath) {
      try {
        const buf = await fs.promises.readFile(effectivePath);
        if (buf && buf.length > 0) {
          let normalizedPath;
          try {
            normalizedPath = path.normalize(effectivePath).toLowerCase();
          } catch (e) {
            normalizedPath = (effectivePath || '').toLowerCase();
          }

          if (!sessionHash) {
            sessionHash = crypto
              .createHash('sha1')
              .update(normalizedPath)
              .update('\n')
              .update(buf)
              .digest('hex')
              .slice(0, 16);
          }

          if (sessionHash && !sessionHashArg) {
            try {
              const stamp = new Date()
                .toISOString()
                .replace(/[:.]/g, '-')
                .replace('T', '_');
              const rawTag = args.edit_file_tag;
              const safeTag = sanitizeEditFileTag(rawTag);
              const dirName = safeTag
                ? `${stamp}_${safeTag}_${sessionHash}`
                : `${stamp}_${sessionHash}`;
              sessionDir = path.join(EDIT_FILE_TRACKING_ROOT, dirName);
              await fs.promises.mkdir(sessionDir, { recursive: true });

              const metaPath = path.join(sessionDir, 'session_meta.json');
              let existingMeta = null;
              try {
                if (fs.existsSync(metaPath)) {
                  const rawMeta = await fs.promises.readFile(
                    metaPath,
                    'utf8',
                  );
                  existingMeta = JSON.parse(rawMeta);
                }
              } catch (e) {
                console.error(
                  'edit_file: failed to read session_meta.json:',
                  metaPath,
                  e,
                );
              }

              if (existingMeta && existingMeta.original_path) {
                let existingNorm;
                try {
                  existingNorm = path
                    .normalize(existingMeta.original_path)
                    .toLowerCase();
                } catch (e) {
                  existingNorm =
                    (existingMeta.original_path || '').toLowerCase();
                }
                if (existingNorm !== normalizedPath) {
                  const msg =
                    '🚫 edit_file multi-edit: session hash appears to belong to a different file.\n\n' +
                    `Session dir: ${sessionDir}\n` +
                    `Stored original_path: ${existingMeta.original_path}\n` +
                    `Current path: ${effectivePath}\n\n` +
                    'This likely indicates a stale tracking folder or a hash collision. ' +
                    'Please clear or rename this session folder (.edit_files_tracking) before reusing this hash.';
                  return {
                    isError: true,
                    content: [{ type: 'text', text: msg }],
                  };
                }
              } else {
                const meta = {
                  original_path: effectivePath,
                  created_at: new Date().toISOString(),
                  session_hash: sessionHash || null,
                };
                try {
                  await fs.promises.writeFile(
                    metaPath,
                    JSON.stringify(meta, null, 2),
                    'utf8',
                  );
                } catch (e) {
                  console.error(
                    'edit_file: failed to write session_meta.json:',
                    metaPath,
                    e,
                  );
                }
              }

              const parsed = path.parse(effectivePath);
              sessionOrigPath = path.join(sessionDir, `orig${parsed.ext}`);
              await fs.promises.writeFile(sessionOrigPath, buf);
              sessionSuccessPath = path.join(
                sessionDir,
                `success-until${parsed.ext}`,
              );
              sessionEditsPath = path.join(
                sessionDir,
                'edits_remaining.json',
              );
            } catch (e) {
              console.error(
                'edit_file: failed to initialize tracking session dir:',
                EDIT_FILE_TRACKING_ROOT,
                e,
              );
            }
          } else if (sessionHashArg && !sessionDir) {
            sessionDir = findSessionDirForHash(
              EDIT_FILE_TRACKING_ROOT,
              sessionHashArg,
            );

            const metaPath = path.join(sessionDir, 'session_meta.json');
            try {
              let existingMeta = null;
              if (fs.existsSync(metaPath)) {
                const rawMeta = await fs.promises.readFile(metaPath, 'utf8');
                existingMeta = JSON.parse(rawMeta);
              }
              if (existingMeta && existingMeta.original_path) {
                let existingNorm;
                try {
                  existingNorm = path
                    .normalize(existingMeta.original_path)
                    .toLowerCase();
                } catch (e) {
                  existingNorm =
                    (existingMeta.original_path || '').toLowerCase();
                }
                let resumeNorm;
                try {
                  resumeNorm = path.normalize(effectivePath).toLowerCase();
                } catch (e) {
                  resumeNorm = (effectivePath || '').toLowerCase();
                }
                if (existingNorm !== resumeNorm) {
                  const msg =
                    '🚫 edit_file multi-edit: session hash appears to belong to a different file.\n\n' +
                    `Session dir: ${sessionDir}\n` +
                    `Stored original_path: ${existingMeta.original_path}\n` +
                    `Current path: ${effectivePath}\n\n` +
                    'This likely indicates a stale tracking folder or a hash collision. ' +
                    'Please clear or rename this session folder (.edit_files_tracking) before reusing this hash.';
                  return {
                    isError: true,
                    content: [{ type: 'text', text: msg }],
                  };
                }
              }
            } catch (e) {
              console.error(
                'edit_file: failed to validate session_meta.json for resume:',
                metaPath,
                e,
              );
            }

            const parsed = path.parse(effectivePath);
            sessionSuccessPath = path.join(
              sessionDir,
              `success-until${parsed.ext}`,
            );
            sessionEditsPath = path.join(
              sessionDir,
              'edits_remaining.json',
            );
          }

          const hash = crypto
            .createHash('sha1')
            .update(buf)
            .digest('hex')
            .slice(0, 8);
          const parsed = path.parse(effectivePath);
          if (sessionDir) {
            origBackupPath = path.join(
              sessionDir,
              `orig-run-${hash}${parsed.ext}`,
            );
          } else {
            origBackupPath = path.join(
              parsed.dir,
              `orig-${hash}-${parsed.base}`,
            );
          }
          await fs.promises.copyFile(effectivePath, origBackupPath);
        }
      } catch (e) {
        console.error(
          'edit_file multi-edit: failed to create orig backup:',
          effectivePath,
          e,
        );
      }
    }

    const successfulEdits = [];
    const failedEdits = [];
    const noOpEdits = [];
    const existenceChecks = [];
    let remainingEditsPath = sessionEditsPath || null;

    for (let i = 0; i < cleanedArgs.edits.length; i += 1) {
      const edit = cleanedArgs.edits[i];
      if (!edit || typeof edit.oldText !== 'string') {
        continue;
      }

      const isExistenceCheck =
        typeof edit.oldText === 'string' &&
        typeof edit.newText === 'string' &&
        edit.oldText.length > 0 &&
        edit.oldText === edit.newText;

      if (isExistenceCheck) {
        let found = false;
        try {
          if (effectivePath) {
            const currentTextForCheck = await fs.promises.readFile(
              effectivePath,
              'utf8',
            );
            found = currentTextForCheck.includes(edit.oldText);
          }
        } catch (e) {
          console.error(
            'edit_file existence-check: failed to read file for existence test:',
            effectivePath || basePath,
            e,
          );
        }

        existenceChecks.push({
          index: i,
          found,
          oldText:
            typeof edit.oldText === 'string'
              ? clipForLog(edit.oldText, 256)
              : null,
          newText:
            typeof edit.newText === 'string'
              ? clipForLog(edit.newText, 256)
              : null,
        });

        try {
          appendEditSessionLog(sessionDir, {
            ts: new Date().toISOString(),
            kind: 'existence_check',
            session_hash: sessionHash || null,
            path: effectivePath || basePath,
            edit_index: i,
            found,
          });
        } catch (e) {
          console.error('edit_file session log existence-check error:', e);
        }

        // Skip direct replace-all path; file remains unchanged for this edit.
        continue;
      }

      let passes = 0;
      const singleContext = {
        ...context,
        useDirectReplaceAll: true,
        toolArgs: {
          ...cleanedArgs,
          edits: [edit],
        },
      };

      try {
        appendEditSessionLog(sessionDir, {
          ts: new Date().toISOString(),
          kind: 'edit_attempt',
          session_hash: sessionHash || null,
          path: effectivePath || basePath,
          edit_index: i,
          pass_index: passes,
          oldText_length:
            typeof edit.oldText === 'string' ? edit.oldText.length : null,
          newText_length:
            typeof edit.newText === 'string' ? edit.newText.length : null,
          oldText_preview:
            typeof edit.oldText === 'string'
              ? edit.oldText.slice(0, 80)
              : null,
          newText_preview:
            typeof edit.newText === 'string'
              ? edit.newText.slice(0, 80)
              : null,
        });
      } catch (e) {
        console.error('edit_file session log attempt error:', e);
      }

      const result = await runStructuredFileWithStage2GuardLocked(
        clientEntry,
        singleContext,
      );
      passes += 1;

      try {
        let errorText = null;
        if (
          result &&
          result.isError &&
          Array.isArray(result.content) &&
          result.content[0] &&
          typeof result.content[0].text === 'string'
        ) {
          errorText = result.content[0].text.slice(0, 200);
        }

        appendEditSessionLog(sessionDir, {
          ts: new Date().toISOString(),
          kind: 'edit_result',
          session_hash: sessionHash || null,
          path: effectivePath || basePath,
          edit_index: i,
          pass_index: passes - 1,
          isError: !!(result && result.isError),
          error_text_preview: errorText,
        });
      } catch (e) {
        console.error('edit_file session log result error:', e);
      }

      if (result && result.isError) {
        // Record failure but DO NOT restore the entire file back to original.
        let errorText = null;
        let fullErrorText = null;
        if (
          result &&
          Array.isArray(result.content) &&
          result.content.length > 0
        ) {
          // Aggregate all text parts for a complete validator report.
          fullErrorText = result.content
            .map((p) => (p && typeof p.text === 'string' ? p.text : ''))
            .join('\n');
        }
        if (
          result &&
          result.isError &&
          Array.isArray(result.content) &&
          result.content[0] &&
          typeof result.content[0].text === 'string'
        ) {
          errorText = result.content[0].text.slice(0, 200);
        }

        failedEdits.push({
          index: i,
          passes_attempted: passes,
          oldText:
            typeof edit.oldText === 'string'
              ? clipForLog(edit.oldText, 256)
              : null,
          newText:
            typeof edit.newText === 'string'
              ? clipForLog(edit.newText, 256)
              : null,
          error_preview: errorText,
          error_full: fullErrorText,
        });

        if (effectivePath && sessionSuccessPath) {
          try {
            await fs.promises.copyFile(effectivePath, sessionSuccessPath);
          } catch (e) {
            console.error(
              'edit_file multi-edit: failed to write success-until checkpoint:',
              sessionSuccessPath,
              e,
            );
          }
        }

        // Continue with next edit; do NOT abort the pipeline.
        continue;
      }

      // Success path: distinguish no-op vs change and cascade only when changed.
      const occurrences =
        result &&
        result.directReplaceAll &&
        typeof result.directReplaceAll.occurrences === 'number'
          ? result.directReplaceAll.occurrences
          : null;

      if (occurrences === 0) {
        noOpEdits.push({
          index: i,
          oldText:
            typeof edit.oldText === 'string'
              ? clipForLog(edit.oldText, 256)
              : null,
          newText:
            typeof edit.newText === 'string'
              ? clipForLog(edit.newText, 256)
              : null,
        });
        // No cascade: file did not change for this edit.
        continue;
      }

      successfulEdits.push({
        index: i,
        oldText:
          typeof edit.oldText === 'string'
            ? clipForLog(edit.oldText, 256)
            : null,
        newText:
          typeof edit.newText === 'string'
            ? clipForLog(edit.newText, 256)
            : null,
      });
    }

    // If any edits failed, write a consolidated remaining-edits spec for convenience.
    if (failedEdits.length > 0) {
      try {
        const failedSpec = {
          path: effectivePath || basePath,
          failed_indices: failedEdits.map((e) => e.index),
          edits: failedEdits.map((e) => {
            const originalEdit = cleanedArgs.edits[e.index];
            return
              originalEdit && typeof originalEdit === 'object'
                ? { ...originalEdit }
                : originalEdit;
          }),
        };

        if (!remainingEditsPath && EDIT_FILE_TRACKING_ROOT) {
          const tempDir = path.dirname(EDIT_FILE_NORMALIZATION_LOG);
          const stamp = new Date().toISOString().replace(/[:.]/g, '-');
          const rand = Math.random().toString(16).slice(2, 8);
          const remainingName = `remaining-edits-${stamp}-${rand}.json`;
          remainingEditsPath = path.join(tempDir, remainingName);
        }

        if (remainingEditsPath) {
          await fs.promises.writeFile(
            remainingEditsPath,
            JSON.stringify(failedSpec, null, 2),
            'utf8',
          );
        }
      } catch (e) {
        console.error(
          'edit_file multi-edit: failed to write consolidated remaining-edits spec:',
          e,
        );
      }
    }

    const noOpCount = noOpEdits.length;
    const succeededCount = successfulEdits.length + noOpCount;
    const failedCount = failedEdits.length;
    const totalEdits = cleanedArgs.edits.length;

    const existenceCheckCount = existenceChecks.length;
    const failedExistenceChecks = existenceChecks.filter(
      (e) => e && e.found === false,
    );
    const failedExistenceCount = failedExistenceChecks.length;

    const successContent = [];
    const summaryLines = [];

    summaryLines.push(
      `edit_file multi-edit pipeline completed ${totalEdits} edits on ${basePath}.`,
    );

    const hasRealErrors = failedCount > 0;
    const hasExistenceWarnings = failedExistenceCount > 0;

    if (hasRealErrors) {
      // Errors first, with explicit index list (0-based)
      const failedIndexes = failedEdits
        .map((e) => e.index)
        .filter((idx) => typeof idx === 'number')
        .sort((a, b) => a - b);
      summaryLines.push(
        `❌ ERRORS: ${failedCount} out of ${totalEdits} – indexes (0-based): ${failedIndexes.join(
          ', ',
        )}`,
      );

      if (hasExistenceWarnings) {
        const failedExistenceIndexes = failedExistenceChecks
          .map((e) => e.index)
          .filter((idx) => typeof idx === 'number')
          .sort((a, b) => a - b);
        summaryLines.push(
          `⚠️ EXISTENCE CHECK FAILED: ${failedExistenceCount} out of ${existenceCheckCount} existence checks – indexes (0-based): ${failedExistenceIndexes.join(
            ', ',
          )}`,
        );
      }

      // Then successes, without a green checkmark, and with indexes
      const successIndexes = successfulEdits
        .map((e) => e.index)
        .filter((idx) => typeof idx === 'number')
        .sort((a, b) => a - b);
      const successCount = successfulEdits.length;
      if (successCount > 0) {
        summaryLines.push(
          `SUCCESSES: ${successCount} out of ${totalEdits} – indexes (0-based): ${successIndexes.join(
            ', ',
          )}`,
        );
      } else {
        summaryLines.push(`SUCCESSES: 0 out of ${totalEdits}`);
      }

      if (noOpCount > 0) {
        const noOpIndexes = noOpEdits
          .map((e) => e.index)
          .filter((idx) => typeof idx === 'number')
          .sort((a, b) => a - b);
        summaryLines.push(
          `⚪ NO-OPS: ${noOpCount} out of ${totalEdits} – indexes (0-based): ${noOpIndexes.join(
            ', ',
          )}`,
        );
      }
    } else {
      if (hasExistenceWarnings) {
        const failedExistenceIndexes = failedExistenceChecks
          .map((e) => e.index)
          .filter((idx) => typeof idx === 'number')
          .sort((a, b) => a - b);
        summaryLines.push(
          `⚠️ EXISTENCE CHECK FAILED: ${failedExistenceCount} out of ${existenceCheckCount} existence checks – indexes (0-based): ${failedExistenceIndexes.join(
            ', ',
          )}`,
        );

        // Successes without green checkmark when existence check failed
        summaryLines.push(
          `SUCCESSES: ${succeededCount} out of ${totalEdits}`,
        );
      } else {
        // No errors and no existence warnings: green checkmark
        summaryLines.push(
          `✅ SUCCESSES: ${succeededCount} out of ${totalEdits}`,
        );
      }

      if (!hasExistenceWarnings && existenceCheckCount > 0) {
        const existenceIndexes = existenceChecks
          .map((e) => e.index)
          .filter((idx) => typeof idx === 'number')
          .sort((a, b) => a - b);
        summaryLines.push(
          `EXISTENCE CHECKS: ${existenceCheckCount} (all found) – indexes (0-based): ${existenceIndexes.join(
            ', ',
          )}`,
        );
      }

      if (noOpCount > 0) {
        const noOpIndexes = noOpEdits
          .map((e) => e.index)
          .filter((idx) => typeof idx === 'number')
          .sort((a, b) => a - b);
        summaryLines.push(
          `⚪ NO-OPS: ${noOpCount} out of ${totalEdits} – indexes (0-based): ${noOpIndexes.join(
            ', ',
          )}`,
        );
      }

      // Errors line last when there are no errors, de-emphasized
      summaryLines.push('ERRORS: 0');
    }

    successContent.push({
      type: 'text',
      text: summaryLines.join('\n'),
    });

    if (successfulEdits.length) {
      const lines = [];
      lines.push('\n✅ SUCCEEDED EDITS (index: oldText → newText):');
      for (const e of successfulEdits) {
        lines.push(
          `- [${e.index}] oldText: ${JSON.stringify(
            e.oldText,
          )} → newText: ${JSON.stringify(e.newText)}`,
        );
      }
      successContent.push({ type: 'text', text: lines.join('\n') });
    }

    if (noOpEdits.length) {
      const lines = [];
      lines.push(
        '\n⚪ NO-OP EDITS (index: oldText → newText – no occurrences of oldText were found this round):',
      );
      lines.push(
        '   WARNING: FOR THE FOLLOWING EDITS, oldText COULD NOT BE FOUND. PLEASE CHECK oldText TO ENSURE IT IS EXACTLY CORRECT. ' +
          'Alternatively, these edits may already have been completed in a prior edit_file call, or earlier edits in this batch may have already made the necessary changes.',
      );
      for (const e of noOpEdits) {
        lines.push(
          `- [${e.index}] oldText: ${JSON.stringify(
            e.oldText,
          )} → newText: ${JSON.stringify(e.newText)}`,
        );
      }
      successContent.push({ type: 'text', text: lines.join('\n') });
    }

    if (failedCount) {
      const lines = [];
      lines.push('\n❌ FAILED EDITS (index: oldText → newText | error):');
      for (const e of failedEdits) {
        lines.push(
          `- [${e.index}] oldText: ${JSON.stringify(
            e.oldText,
          )} → newText: ${JSON.stringify(e.newText)}`,
        );
        if (e.error_preview) {
          lines.push(`    error: ${e.error_preview}`);
        }
      }
      if (remainingEditsPath) {
        lines.push(
          `\nRemaining failed edits were saved to: ${remainingEditsPath}`,
        );
      }
      successContent.push({ type: 'text', text: lines.join('\n') });
    }

    if (existenceCheckCount > 0) {
      const lines = [];
      lines.push(
        '\n⚠️ EXISTENCE CHECKS (oldText === newText, file unchanged):',
      );
      for (const e of existenceChecks) {
        if (!e) continue;
        const status = e.found ? 'FOUND' : 'NOT FOUND';
        lines.push(
          `- [${e.index}] ${status}: oldText: ${JSON.stringify(
            e.oldText,
          )} → newText: ${JSON.stringify(e.newText)}`,
        );
      }
      successContent.push({ type: 'text', text: lines.join('\n') });
    }

    try {
      const origForDiff = sessionOrigPath || origBackupPath;
      const currentForDiff = effectivePath;
      console.log(
        '[MCP CONNECTOR] multi-edit FINAL diff: orig=%s current=%s',
        origForDiff || '(null)',
        currentForDiff || '(null)',
      );
      const diffText = await computeSessionDiffText(origForDiff, currentForDiff);
      if (diffText && diffText.trim()) {
        successContent.push({
          type: 'text',
          text:
            '\n---\n' + '📄 Diff vs original (session):\n\n' + diffText,
        });
      } else {
        console.log(
          '[MCP CONNECTOR] multi-edit FINAL diff: no diff text returned',
        );
      }
    } catch (e) {
      console.error('edit_file session diff (final path) error:', e);
    }

    if (failedCount) {
      const validatorLines = [];
      for (const e of failedEdits) {
        if (!e || !e.error_full) continue;
        validatorLines.push(
          `\nFAILED EDIT #${e.index} VALIDATOR REPORT:\n\n` +
            '---\n' +
            e.error_full +
            '\n---\n',
        );
      }
      if (validatorLines.length > 0) {
        successContent.push({
          type: 'text',
          text: validatorLines.join(''),
        });
      }
    }

    return {
      isError: failedCount > 0,
      content: successContent,
      multiEdit: {
        session_hash: sessionHash || null,
        tracking_root: EDIT_FILE_TRACKING_ROOT,
        tracking_dir: sessionDir,
        tracking_orig_path: sessionOrigPath,
        success_count: succeededCount,
        failed_count: failedCount,
        remaining_edits_path: remainingEditsPath || null,
      },
    };
  }

  if (context.toolName === 'write_file') {
    try {
      logRunCommandCleanse({
        stage: 'stage2-structured-guard-enter',
        callId: context.callId,
        toolName,
        path:
          (context &&
            context.toolArgs &&
            context.toolArgs.path) || '(none)',
      });
    } catch (e) {
      console.error('stage2 structured-guard log failure:', e);
    }
    console.log(
      '[MCP CONNECTOR] Stage2 GUARD ENTER (write_file): callId=%s path=%s',
      context.callId,
      (context && context.toolArgs && context.toolArgs.path) || '(none)',
    );

    const exclusionSetsForWrite = findExclusionSetsForTool(
      context.toolName,
      context.toolArgs,
    );

    const runWrite = async () =>
      runStructuredFileWithStage2Guard(clientEntry, context);

    if (
      Array.isArray(exclusionSetsForWrite) &&
      exclusionSetsForWrite.length > 0
    ) {
      const setIds = exclusionSetsForWrite
        .map((s) => (s && typeof s.setId === 'string' ? s.setId : null))
        .filter((id) => !!id);
      try {
        logRunCommandCleanse({
          stage: 'exclusion-set-detected',
          callId: context.callId,
          toolName: context.toolName,
          exclusionSetIds: setIds,
          ts: new Date().toISOString(),
        });
      } catch (e) {
        console.error('exclusion-set detection log failure (write_file):', e);
      }
      return runToolWithExclusionSetsLock(
        clientEntry,
        context,
        exclusionSetsForWrite,
        runWrite,
      );
    }

    return runWrite();
  }

  if (context.toolName === 'write_text_file') {
    try {
      logRunCommandCleanse({
        stage: 'stage2-structured-guard-enter',
        callId: context.callId,
        toolName,
        path:
          (context &&
            context.toolArgs &&
            context.toolArgs.path) || '(none)',
      });
    } catch (e) {
      console.error('stage2 structured-guard log failure:', e);
    }
    console.log(
      '[MCP CONNECTOR] Stage2 GUARD ENTER (write_text_file): callId=%s path=%s',
      context.callId,
      (context && context.toolArgs && context.toolArgs.path) || '(none)',
    );

    const exclusionSetsForWriteText = findExclusionSetsForTool(
      context.toolName,
      context.toolArgs,
    );

    const runWriteText = async () =>
      runStructuredFileWithStage2Guard(clientEntry, context);

    if (
      Array.isArray(exclusionSetsForWriteText) &&
      exclusionSetsForWriteText.length > 0
    ) {
      const setIds = exclusionSetsForWriteText
        .map((s) => (s && typeof s.setId === 'string' ? s.setId : null))
        .filter((id) => !!id);
      try {
        logRunCommandCleanse({
          stage: 'exclusion-set-detected',
          callId: context.callId,
          toolName: context.toolName,
          exclusionSetIds: setIds,
          ts: new Date().toISOString(),
        });
      } catch (e) {
        console.error(
          'exclusion-set detection log failure (write_text_file):',
          e,
        );
      }
      return runToolWithExclusionSetsLock(
        clientEntry,
        context,
        exclusionSetsForWriteText,
        runWriteText,
      );
    }

    return runWriteText();
  }

  // JEWELSTORM transform_jewel guard: serialize nexus_transform_jewel calls
  // per jewel_file path to avoid concurrent mutations of the same working_gem.
  if (context.toolName === 'nexus_transform_jewel') {
    try {
      logRunCommandCleanse({
        stage: 'jewel-lock-enter',
        callId: context.callId,
        toolName,
        jewel_file:
          (context &&
            context.toolArgs &&
            context.toolArgs.jewel_file) || '(none)',
      });
    } catch (e) {
      console.error('jewel-lock enter log failure:', e);
    }
    return runTransformJewelWithLock(clientEntry, context);
  }

  // QUILL Python scripts invoked via run_command: serialize all such operations
  // through a connector-side queue with a 500ms guard interval.
  if (
    context.toolName === 'run_command' &&
    isQuillRelatedOperation(context.toolName, context.toolArgs)
  ) {
    try {
      logRunCommandCleanse({
        stage: 'quill-run-lock-enter',
        callId: context.callId,
        toolName,
        command:
          (context && context.toolArgs && context.toolArgs.command) ||
          '(none)',
      });
    } catch (e) {
      console.error('quill run-command lock enter log failure:', e);
    }
    return runQuillRunCommandWithLock(clientEntry, context);
  }

  // JEWELSTORM Python scripts invoked via run_command: same queuing semantics.
  if (
    context.toolName === 'run_command' &&
    isJewelstormRelatedOperation(context.toolName, context.toolArgs)
  ) {
    try {
      logRunCommandCleanse({
        stage: 'jewel-run-lock-enter',
        callId: context.callId,
        toolName,
        command:
          (context && context.toolArgs && context.toolArgs.command) ||
          '(none)',
      });
    } catch (e) {
      console.error('jewel run-command lock enter log failure:', e);
    }
    return runJewelRunCommandWithLock(clientEntry, context);
  }

  // Check TOOL EXCLUSION SETS before default behavior
  const exclusionSets = findExclusionSetsForTool(
    context.toolName,
    context.toolArgs,
  );
  if (Array.isArray(exclusionSets) && exclusionSets.length > 0) {
    const setIds = exclusionSets
      .map((s) => (s && typeof s.setId === 'string' ? s.setId : null))
      .filter((id) => !!id);
    try {
      logRunCommandCleanse({
        stage: 'exclusion-set-detected',
        callId: context.callId,
        toolName: context.toolName,
        exclusionSetIds: setIds,
        ts: new Date().toISOString(),
      });
    } catch (e) {
      console.error('exclusion-set detection log failure:', e);
    }
    return runToolWithExclusionSetsLock(
      clientEntry,
      context,
      exclusionSets,
      async () => {
        try {
          logRunCommandCleanse({
            stage: 'stage3-calltool-enter',
            callId: context.callId,
            toolName,
          });
        } catch (e) {
          console.error('stage3 callTool log failure:', e);
        }

        return clientEntry.client.callTool(
          {
            name: context.toolName,
            arguments: context.toolArgs,
          },
          undefined, // schema parameter
          {
            timeout: 900000, // 15 minutes (900000ms)
            resetTimeoutOnProgress: true, // Reset timeout on progress notifications
          },
        );
      },
    );
  }

  // Default behaviour: forward directly to the underlying MCP client
  try {
    logRunCommandCleanse({
      stage: 'stage3-calltool-enter',
      callId: context.callId,
      toolName,
    });
  } catch (e) {
    console.error('stage3 callTool log failure:', e);
  }

  return clientEntry.client.callTool(
    {
      name: context.toolName,
      arguments: context.toolArgs,
    },
    undefined, // schema parameter
    {
      timeout: 900000, // 15 minutes (900000ms)
      resetTimeoutOnProgress: true, // Reset timeout on progress notifications
    },
  );
}

const createRemoteClient = async ({ clientId, url }) => {
  let client = undefined;
  const baseUrl = new URL(url);
  try {
    client = new Client({
      name: `mcp-streamable-http-bridge-${clientId}`,
      version: '1.0.0',
    });
    const transport = new StreamableHTTPClientTransport(new URL(baseUrl));
    await client.connect(transport);
    console.log('Connected using Streamable HTTP transport');
  } catch (error) {
    // If that fails with a 4xx error, try the older SSE transport
    console.log(
      'Streamable HTTP connection failed, falling back to SSE transport',
    );
    client = new Client({
      name: `mcp-sse-http-bridge-${clientId}`,
      version: '1.0.0',
    });
    const sseTransport = new SSEClientTransport(baseUrl);
    await client.connect(sseTransport);
    console.log('Connected using SSE transport');
  }

  return client;
};

// Helper function to start a client with given configuration
async function startClient(clientId, config) {
  const { command, url, args = [], env = {} } = config;

  if (!command && !url) {
    throw new Error('command or url is required');
  }

  let client;

  if (command) {
    // Create transport for the MCP client
    const transport = new StdioClientTransport({
      command,
      args,
      env:
        Object.values(env).length > 0
          ? {
              // see https://github.com/modelcontextprotocol/typescript-sdk/issues/216
              ...getDefaultEnvironment(),
              ...env,
            }
          : undefined, // cannot be {}, it will cause error
    });

    // Create and initialize the client
    client = new Client({
      name: `mcp-http-bridge-${clientId}`,
      version: '1.0.0',
    });

    // Connect the client to the transport
    await client.connect(transport);

    // Patch listTools so we can expose connector-side enhancements (e.g. edits_file)
    const originalListTools = client.listTools.bind(client);
    client.listTools = async (...listArgs) => {
      const result = await originalListTools(...listArgs);
      try {
        if (result && Array.isArray(result.tools)) {
          for (const tool of result.tools) {
            if (!tool || tool.name !== 'edit_file') continue;

            const schema = tool.inputSchema || tool.parameters || {};
            if (schema && schema.type === 'object') {
              const props = schema.properties || {};
              const newProps = {
                ...props,
                edits_file: {
                  type: 'string',
                  description:
                    'Optional path to a JSON file of the form { "edits": [ {"oldText": ..., "newText": ...}, ... ] }. When provided, the MCP connector loads this file and runs a guarded multi-edit pipeline with backups, checkpoints, and a remaining-edits spec for resume.',
                },
                edit_session_hash: {
                  type: 'string',
                  description:
                    'Optional resume token for a multi-edit session managed under .edit_files_tracking/<hash>. When provided, the connector ignores inline edits/edits_file and instead loads edits_remaining.json from the corresponding tracking folder to resume the guarded multi-edit pipeline.',
                },
                edit_file_tag: {
                  type: 'string',
                  description:
                    'Optional human-readable tag for this multi-edit session. The connector sanitizes this value to [A-Za-z0-9_-] and incorporates it into the timestamped tracking folder name to aid discovery (e.g., 2025-12-08_06-13-42_myTag_<hash>).',
                },
              };

              schema.properties = newProps;
              tool.inputSchema = schema;
              tool.parameters = schema;
            }
          }
        }
      } catch (e) {
        console.error('edit_file tool schema patch failed:', e);
      }
      return result;
    };

    // Warm up the server immediately (force lazy-loaded backends to start)
    try {
      console.log(`Warming up client ${clientId}...`);
      await client.listTools();
      console.log(`Client ${clientId} warmed up successfully`);
    } catch (e) {
      console.warn(`Warmup failed for client ${clientId} (non-fatal):`, e.message);
    }
  } else if (url) {
    client = await createRemoteClient({ clientId, url });
  } else {
    throw new Error('Either command or url must be provided');
  }

  // Store the client with its ID
  clients.set(clientId, {
    id: clientId,
    client,
    command,
    args,
    env,
    config, // Store original config for restart
    createdAt: new Date(),
  });

  return {
    id: clientId,
    message: 'MCP client started successfully',
  };
}

/**
 * Start the MCP server
 * @param {string} authToken Authentication token
 * @returns {Promise<{port: number}>} The port the server is running on
 */
async function start(authToken) {
  const app = express();

  // Find an available port
  const port = process.env.PORT || (await findAvailablePort());
  if (!port) {
    throw new Error(
      'No available ports found. Please specify a port by using the PORT environment variable.',
    );
  }

  const timestamp = new Date().toISOString().replace('T', ' ').replace(/\..+/, '');
  console.log(
    `[${timestamp}] 🛠️ [MCP CONNECTOR] Starting TypingMind MCP server bridge – version ${CONNECTOR_VERSION} on port ${port}`,
  );

  // Configure middleware
  app.use(cors());
  app.use(express.json());

  // Add authentication to all endpoints
  const auth = authMiddleware(authToken);

  // Health check endpoint
  app.get('/ping', auth, (req, res) => {
    res.status(200).json({ status: 'ok' });
  });

  // Auto-start MCP clients from cached /start configuration (if available).
  // This lets the connector warm all MCP servers (and their lazy internals)
  // as soon as it starts, without requiring TypingMind to POST /start again.
  try {
    const cached = loadCachedMcpServers();
    if (cached && typeof cached === 'object') {
      console.log('Auto-starting MCP clients from cached configuration...');
      const startPromises = Object.entries(cached).map(
        async ([serverId, config]) => {
          try {
            if (clients.has(serverId)) {
              const hasConfigChanged =
                stringify(clients.get(serverId).config) !== stringify(config);
              if (!hasConfigChanged) {
                return;
              }
              console.log(
                'Restarting client with cached config at startup:',
                serverId,
              );
              clients.get(serverId).client.close();
            }
            await startClient(serverId, config);
          } catch (error) {
            console.error(
              `Failed to auto-start client ${serverId} from cache:`,
              error,
            );
          }
        },
      );
      await Promise.all(startPromises);
    }
  } catch (e) {
    console.error('Error during auto-start from cached MCP servers config:', e);
  }

  // Start MCP clients using Claude Desktop config format
  app.post('/start', auth, async (req, res) => {
    try {
      const { mcpServers } = req.body;

      if (!mcpServers || typeof mcpServers !== 'object') {
        return res
          .status(400)
          .json({ error: 'mcpServers configuration is required' });
      }

      // Persist latest config so future connector restarts can auto-start clients
      saveCachedMcpServers(mcpServers);

      const results = {
        success: [],
        errors: [],
      };

      // Process each server configuration
      const startPromises = Object.entries(mcpServers).map(
        async ([serverId, config]) => {
          try {
            // Check if this client already exists
            if (clients.has(serverId)) {
              const hasConfigChanged =
                stringify(clients.get(serverId).config) !== stringify(config);
              if (!hasConfigChanged) {
                return;
              }
              console.log('Restarting client with new config:', serverId);
              clients.get(serverId).client.close();
            }

            const result = await startClient(serverId, config);
            results.success.push(result);
          } catch (error) {
            console.error(`Failed to initialize client ${serverId}:`, error);
            results.errors.push({
              id: serverId,
              error: `Failed to initialize: ${error.message}`,
            });
          }
        },
      );

      // Wait for all clients to be processed
      await Promise.all(startPromises);

      // Return appropriate response
      if (results.errors.length === 0) {
        return res.status(201).json({
          message: 'All MCP clients started successfully',
          clients: results.success,
        });
      } else {
        return res.status(400).json({
          message: 'Some MCP clients failed to start',
          success: results.success,
          errors: results.errors,
        });
      }
    } catch (error) {
      console.error('Error starting clients:', error);
      return res.status(500).json({ error: 'Internal server error' });
    }
  });

  // Restart a specific client
  app.post('/restart/:id', auth, async (req, res) => {
    const { id } = req.params;
    const clientEntry = clients.get(id);

    if (!clientEntry) {
      return res.status(404).json({ error: 'Client not found' });
    }

    try {
      // Get the original configuration
      const config = clientEntry.config || {
        command: clientEntry.command,
        args: clientEntry.args,
        env: clientEntry.env,
      };

      // Close the existing client
      await clientEntry.client.close();
      clients.delete(id);

      // Start a new client with the same configuration
      const result = await startClient(id, config);

      return res.status(200).json({
        message: `Client ${id} restarted successfully`,
        client: result,
      });
    } catch (error) {
      console.error(`Error restarting client ${id}:`, error);
      return res.status(500).json({
        error: 'Failed to restart client',
        details: error.message,
      });
    }
  });

  app.get('/clients', auth, async (req, res) => {
    try {
      // Create an array of promises that will fetch tools for each client
      const clientDetailsPromises = Array.from(clients.values()).map(
        async (clientEntry) => {
          const { id, command, args, createdAt } = clientEntry;

          try {
            // Get tools for this client
            const result = await clientEntry.client.listTools();
            const tools = result.tools || [];

            // Extract just the tool names into an array
            const toolNames = tools.map((tool) => tool.name);

            return {
              id,
              command,
              args,
              createdAt,
              tools: toolNames,
            };
          } catch (error) {
            console.error(`Error getting tools for client ${id}:`, error);
            return {
              id,
              command,
              args,
              createdAt,
              tools: [],
              toolError: error.message,
            };
          }
        },
      );

      // Wait for all promises to resolve
      const clientsList = await Promise.all(clientDetailsPromises);

      res.status(200).json(clientsList);
    } catch (error) {
      console.error('Error fetching clients list:', error);
      res.status(500).json({
        error: 'Failed to retrieve clients list',
        details: error.message,
      });
    }
  });

  app.get('/clients/:id', auth, (req, res) => {
    const clientId = req.params.id;
    const clientEntry = clients.get(clientId);

    if (!clientEntry) {
      return res.status(404).json({ error: 'Client not found' });
    }

    const { id, command, args, createdAt } = clientEntry;

    res.status(200).json({ id, command, args, createdAt });
  });

  // Get tools for a specific client
  app.get('/clients/:id/tools', auth, async (req, res) => {
    const { id } = req.params;
    const clientEntry = clients.get(id);

    if (!clientEntry) {
      return res.status(404).json({ error: 'Client not found' });
    }

    try {
      const result = await clientEntry.client.listTools();
      res.status(200).json(result.tools);
    } catch (error) {
      console.error(`Error getting tools for client ${id}:`, error);
      res.status(500).json({
        error: 'Failed to get tools',
        details: error.message,
      });
    }
  });

  // Call a tool for a specific client
  app.post('/clients/:id/call_tools', auth, async (req, res) => {
    const { id } = req.params;
    const { name } = req.body;
    let toolArgs = req.body.arguments || {};

    if (!name) {
      return res.status(400).json({ error: 'Tool name is required' });
    }

    const clientEntry = clients.get(id);
    if (!clientEntry) {
      return res.status(404).json({ error: 'Client not found' });
    }

    // Allow a cleansing pass for run_command before PowerShell guardrails run.
    if (name === 'run_command') {
      toolArgs = cleanseRunCommandArgs(toolArgs);
    }

    // 🚫 PowerShell guardrail: COMMENTED OUT 2026-01-16 for WSL testing
    // Historical context: This was added to prevent file corruption from backtick-n literal newlines.
    // Dan has indicated the issue is no longer relevant and wants to test WSL-based SQL workflows.
    // If old edge cases reappear, uncomment and enhance this block.
    /*
    if (name === 'run_command' && toolArgs && toolArgs.command) {
      const cmd = toolArgs.command.toLowerCase();
      // Check if PowerShell is being EXECUTED (not just mentioned in arguments)
      const isPowershellExecution =
        cmd.startsWith('powershell') ||
        cmd.startsWith('pwsh') ||
        cmd.includes('powershell.exe') ||
        cmd.includes('pwsh.exe') ||
        /^[a-z]:\\.*\\powershell/i.test(toolArgs.command) || // Full path to powershell
        /^[a-z]:\\.*\\pwsh/i.test(toolArgs.command); // Full path to pwsh

      if (isPowershellExecution) {
        if (isSafePowerShellCommand(toolArgs.command)) {
          console.log(`✅ ALLOWED safe PowerShell execution: ${toolArgs.command}`);
        } else {
          console.log(`🚫 BLOCKED PowerShell execution attempt: ${toolArgs.command}`);
          return res.status(403).json({
            content: [
              {
                type: 'text',
                text:
                  '🚫 PowerShell blocked for file safety (except for a small whitelist used for SNAPNAX/Obsidian/PARALLAX/Araxis operations).\n\n' +
                  'Most PowerShell commands are disabled to prevent file corruption from backtick-n literal newlines.\n\n' +
                  'Tested alternatives for other tasks:\n' +
                  '- WSL grep: wsl bash -c "grep -r pattern /mnt/e/path"\n' +
                  '- MCP search: search_files(path, pattern)\n' +
                  '- MCP list: list_directory(path)\n' +
                  '- CMD taskkill: cmd.exe /C "taskkill /F /IM process.exe"\n\n' +
                  'All alternatives tested and working.',
              },
            ],
            isError: false,
          });
        }
      }
    }
    */

    try {
      // All tool calls now flow through the dispatcher so we can add
      // global/group/per-tool handling in one place without touching
      // individual MCP servers.
      const result = await dispatchToolCall(clientEntry, name, toolArgs || {});

      res.status(200).json(result);
    } catch (error) {
      console.error(`Error calling tool for client ${id}:`, error);
      res.status(500).json({
        error: 'Failed to call tool',
        details: error.message,
      });
    }
  });

  // Clean up resources for a client
  app.delete('/clients/:id', auth, async (req, res) => {
    const { id } = req.params;
    const clientEntry = clients.get(id);

    if (!clientEntry) {
      return res.status(404).json({ error: 'Client not found' });
    }

    try {
      // Close the client properly
      await clientEntry.client.close();
      clients.delete(id);

      res.status(200).json({ message: 'Client deleted successfully' });
    } catch (error) {
      console.error(`Error deleting client ${id}:`, error);
      res.status(500).json({
        error: 'Failed to delete client',
        details: error.message,
      });
    }
  });

  // MCP Connect endpoint - proxy fetch requests
  app.post('/mcp-connect', auth, async (req, res) => {
    try {
      const { url, options } = req.body;

      if (!url) {
        return res.status(400).json({ error: 'URL is required' });
      }

      // Make the fetch request
      const response = await fetch(url, options);

      // Filter out headers that can cause decoding issues when forwarding streams
      const headers = {};
      const exposedHeaders = [];
      response.headers.forEach((value, key) => {
        const lowerKey = key.toLowerCase();
        // Skip headers that can cause content decoding errors:
        // - Content-Encoding: body stream may already be decompressed
        // - Content-Length: stream length may differ
        // - Transfer-Encoding: hop-by-hop header, shouldn't be forwarded
        // Skip CORS headers - these should be set by our server's CORS middleware, not proxied
        if (
          lowerKey !== 'content-encoding' &&
          lowerKey !== 'content-length' &&
          lowerKey !== 'transfer-encoding' &&
          !lowerKey.startsWith('access-control-')
        ) {
          headers[key] = value;
          exposedHeaders.push(key);
        }
      });

      // Forward status and headers (must be set before streaming)
      res.status(response.status);

      // Expose all proxied headers for CORS
      if (exposedHeaders.length > 0) {
        res.setHeader(
          'Access-Control-Expose-Headers',
          exposedHeaders.join(', '),
        );
      }

      Object.keys(headers).forEach((key) => {
        res.setHeader(key, headers[key]);
      });

      // Stream the response body using Node.js Readable.fromWeb()
      if (response.body) {
        const nodeStream = Readable.fromWeb(response.body);
        nodeStream.pipe(res);
      } else {
        res.end();
      }
    } catch (error) {
      console.error('Error in mcp-connect:', error);
      if (!res.headersSent) {
        res.status(500).json({
          error: 'Internal server error',
          details: error.message,
        });
      }
    }
  });

  // OPTIONS handler for mcp-connect CORS preflight
  app.options('/mcp-connect', auth, (req, res) => {
    res.status(204).end();
  });

  // Global error handler
  app.use((err, req, res, next) => {
    console.error('Unhandled error:', err);
    res.status(500).json({
      error: 'Internal server error',
      details: err.message,
    });
  });

  // Start the server (HTTP or HTTPS)
  return new Promise((resolve, reject) => {
    const host = process.env.HOSTNAME || '0.0.0.0';

    // Check if certificate and key files are specified
    const certFile = process.env.CERTFILE;
    const keyFile = process.env.KEYFILE;

    let server;

    if (certFile && keyFile) {
      try {
        // Read certificate files
        const httpsOptions = {
          cert: fs.readFileSync(certFile),
          key: fs.readFileSync(keyFile),
        };

        // Create HTTPS server
        server = https.createServer(httpsOptions, app);
        server.listen(port, host, () => {
          resolve({ port, host, protocol: 'https' });
        });
      } catch (error) {
        console.error('Error setting up HTTPS server:', error);
        reject(error);
      }
    } else {
      // Create HTTP server (fallback)
      server = app.listen(port, host, () => {
        resolve({ port, host, protocol: 'http' });
      });
    }

    // Handle graceful shutdown
    process.on('SIGINT', () => {
      console.log('\nShutting down MCP server...');
      server.close(() => {
        process.exit(0);
      });
    });
  });
}

// Graceful shutdown handling
process.on('SIGINT', async () => {
  console.log('Shutting down server...');

  // Close all clients
  for (const [id, clientEntry] of clients.entries()) {
    try {
      await clientEntry.client.close();
      console.log(`Closed client ${id}`);
    } catch (error) {
      console.error(`Error closing client ${id}:`, error);
    }
  }

  process.exit(0);
});

module.exports = {
  start,
};
