const net = require('net');

// List of ports to try in order
const PORTS = [50880, 50881];

/**
 * Check if a port is available
 * @param {number} port The port to check
 * @returns {Promise<boolean>} True if the port is available
 */
function isPortAvailable(port) {
  return new Promise((resolve) => {
    const server = net.createServer();

    server.once('error', () => {
      resolve(false);
    });

    server.once('listening', () => {
      server.close();
      resolve(true);
    });

    server.listen(port);
  });
}

/**
 * Find an available port from the list
 * @returns {Promise<number|null>} The available port or null if none found
 */
async function findAvailablePort() {
  for (const port of PORTS) {
    if (await isPortAvailable(port)) {
      return port;
    }
  }
  return null;
}

module.exports = {
  findAvailablePort,
};
