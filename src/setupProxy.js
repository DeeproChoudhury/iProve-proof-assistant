module.exports = function(app) {
  // app.use(sslRedirect());
  app.use('/', (req, res, next) => {
    if (process.env.ENV === 'production' && req.header('x-forwarded-proto') !== 'https') {
      res.redirect(`https://${req.header('host')}${req.url}`)
    }
    else {
      res.set({
        'Cross-Origin-Embedder-Policy': 'require-corp',
        'Cross-Origin-Opener-Policy': 'same-origin'
      });
      next();
    }
  });
};
