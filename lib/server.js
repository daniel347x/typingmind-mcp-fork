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
  try {
    if (!mcpServers || typeof mcpServers !== 'object') {
      return;
    }
    const payload = { mcpServers };
    fs.writeFileSync(
      MCP_SERVERS_CACHE_PATH,
      JSON.stringify(payload, null, 2),
      'utf8',
    );
  } catch (err) {
    console.error('Failed to write cached MCP servers configuration:', err);
  }
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

async function runStructuredFileWithStage2Guard(clientEntry, context) {
  const args = context.toolArgs || {};
  const filePath = args.path;
  const kind = getStructuredFileKind(filePath);

  // If we don't recognize this as a structured file, fall back to default behaviour.
  if (!filePath || !kind) {
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

  let toolResult;
  try {
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

function getEditFileLockKey(filePath) {
  if (!filePath || typeof filePath !== 'string') return null;
  try {
    return path.normalize(filePath).toLowerCase();
  } catch (e) {
    return filePath;
  }
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
            path: filePath,
            lockKey: key,
            queuedBefore: alreadyQueued,
          });
        } catch (e) {
          console.error('edit-file lock log failure:', e);
        }
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
    });

  EDIT_FILE_LOCKS.set(key, chained);
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


// Global QUILL mutex (connector-side).
// Prevent multiple QUILL operations (quillstrike / quillmorph / quilldrop)
// from being in-flight at the same time through this connector.
let quillOperationInProgress = false;

/**
 * Detect whether a tool call is a QUILL-related operation.
 *
 * For now we treat QUILL as any run_command invocation that calls one of the
 * core Python scripts:
 *   - quillstrike.py
 *   - quillmorph.py
 *   - quilldrop.py
 *
 * This can be expanded later (e.g. dedicated MCP tools) without changing
 * the mutex logic.
 */
function isQuillRelatedOperation(toolName, toolArgs) {
  if (toolName !== 'run_command' || !toolArgs || typeof toolArgs.command !== 'string') {
    return false;
  }

  const cmd = toolArgs.command.toLowerCase();

  return (
    cmd.includes('quillstrike.py') ||
    cmd.includes('quillmorph.py') ||
    cmd.includes('quilldrop.py')
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
    return runStructuredFileWithStage2GuardLocked(clientEntry, context);
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
    return runStructuredFileWithStage2Guard(clientEntry, context);
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

    // 🚫 PowerShell guardrail: block general PowerShell, allow only a small safe whitelist
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

    // 🔒 QUILL MCP mutex: serialize quillstrike/quillmorph/quilldrop
    const isQuill = isQuillRelatedOperation(name, toolArgs);

    if (isQuill && quillOperationInProgress) {
      const msg =
        '🚫 QUILL MCP CONNECTOR: Another QUILL operation is already in progress.\n\n' +
        'Only one quillstrike/quillmorph/quilldrop operation may run at a time. ' +
        'Wait for the current QUILL scroll to complete, then try again.\n\n' +
        'This connector-side mutex complements the Python guardian lock (index.lock).';

      console.log(`🚫 QUILL MCP mutex blocked parallel QUILL operation for tool ${name}.`);

      return res.status(429).json({
        isError: true,
        content: [{ type: 'text', text: msg }],
      });
    }

    if (isQuill) {
      quillOperationInProgress = true;
    }

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
    } finally {
      if (isQuill) {
        quillOperationInProgress = false;
      }
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
