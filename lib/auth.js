/**
 * Middleware to verify authentication token
 * @param {string} authToken The token to check against
 * @returns {Function} Express middleware function
 */
function authMiddleware(authToken) {
  return (req, res, next) => {
    const authHeader = req.headers.authorization;

    if (!authHeader) {
      return res
        .status(401)
        .json({ error: 'Authorization header is required' });
    }

    const [type, token] = authHeader.split(' ');

    if (type !== 'Bearer') {
      return res
        .status(401)
        .json({ error: 'Authorization type must be Bearer' });
    }

    if (token !== authToken) {
      return res.status(401).json({ error: 'Invalid authentication token' });
    }

    next();
  };
}

module.exports = {
  authMiddleware,
};
