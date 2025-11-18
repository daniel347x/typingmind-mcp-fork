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
const https = require('https');
const { Readable } = require('stream');
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
  'E\\__daniel347x\\__Obsidian\\__Inking into Mind\\--TypingMind\\Projects - All\\Projects - Individual\\TODO\\temp\\edit_file_normalization.log';
const EDIT_FILE_HEX_DEBUG_LOG = EDIT_FILE_NORMALIZATION_LOG.replace(
  'edit_file_normalization.log',
  'edit_file_hex_debug.log',
);

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
    if (!filePath || edits.length === 0) {
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
  }
}

async function handleFileIoPreflight(context) {
  // context: { clientId, clientEntry, toolName, toolArgs }
  // Decade 70: perform literal "\\n" → "\n" normalization for edit_file, plus light logging.
  normalizeEditFileArgs(context);

  if (context && context.toolName === 'edit_file') {
    await debugEditFileBytes(context);
  }

  return context;
}

/**
 * Determine if a PowerShell run_command invocation is in the small
 * safe-operations whitelist (SNAPNAX, Obsidian/PARALLAX, Araxis).
 */
function isSafePowerShellCommand(rawCommand) {
  if (!rawCommand || typeof rawCommand !== 'string') {
    return false;
  }
  const cmd = rawCommand.toLowerCase();

  // SNAPNAX (Workflowy deep link)
  const hasSnapnax =
    cmd.includes("start-process 'workflowy://") ||
    cmd.includes('start-process "workflowy://');

  // Obsidian (including PARALLAX diff)
  const hasObsidian =
    cmd.includes("start-process 'obsidian://") ||
    cmd.includes('start-process "obsidian://');

  // Araxis Merge compare
  const hasAraxis = cmd.includes(
    "start-process -filepath 'c:\\users\\danie\\appdata\\local\\apps\\araxis\\araxis merge\\merge.exe'",
  );

  // Git push via PowerShell (safe: no file mutation by PowerShell itself)
  const hasGitPush = cmd.includes('git push');

  // Copy-Item (safe: file copy operation, no content mutation)
  const hasCopyItem = cmd.includes('copy-item');

  return hasSnapnax || hasObsidian || hasAraxis || hasGitPush || hasCopyItem;
}

/**
 * Main dispatcher for all tool calls.
 *
 * This is the single choke point for every MCP tool invocation. It can:
 *  - Run group-level pre-handlers (file I/O, run_command, etc.)
 *  - Route to per-tool handlers (if/when we add them)
 *  - Fall back to the default client.callTool() behaviour.
 */
async function dispatchToolCall(clientEntry, toolName, toolArgs) {
  const context = {
    clientId: clientEntry.id,
    clientEntry,
    toolName,
    toolArgs: toolArgs || {},
  };

  // Group-level preflight handlers (no-op for now)
  if (isFileIoTool(toolName)) {
    await handleFileIoPreflight(context);
  }

  // TODO: in future, add per-tool handlers here (e.g., run_command routing).

  // Default behaviour: forward directly to the underlying MCP client
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

  // Start MCP clients using Claude Desktop config format
  app.post('/start', auth, async (req, res) => {
    try {
      const { mcpServers } = req.body;

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
    const { name, arguments: toolArgs } = req.body;

    if (!name) {
      return res.status(400).json({ error: 'Tool name is required' });
    }

    const clientEntry = clients.get(id);
    if (!clientEntry) {
      return res.status(404).json({ error: 'Client not found' });
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
            content: [{
              type: 'text',
              text:
                '🚫 PowerShell blocked for file safety (except for a small whitelist used for SNAPNAX/Obsidian/PARALLAX/Araxis operations).\n\n' +
                'Most PowerShell commands are disabled to prevent file corruption from backtick-n literal newlines.\n\n' +
                'Tested alternatives for other tasks:\n' +
                '- WSL grep: wsl bash -c "grep -r pattern /mnt/e/path"\n' +
                '- MCP search: search_files(path, pattern)\n' +
                '- MCP list: list_directory(path)\n' +
                '- CMD taskkill: cmd.exe /C "taskkill /F /IM process.exe"\n\n' +
                'All alternatives tested and working.'
            }],
            isError: false
          });
        }
      }
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
