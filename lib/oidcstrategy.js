/**
 * Copyright (c) Microsoft Corporation
 *  All Rights Reserved
 *  MIT License
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this
 * software and associated documentation files (the 'Software'), to deal in the Software
 * without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS
 * OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 * OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

'use strict';

/* eslint no-underscore-dangle: 0 */

// third party packages
const async = require('async');
const base64url = require('base64url');
const cacheManager = require('cache-manager');
const jws = require('jws');
const objectTransform = require('oniyi-object-transform');
const passport = require('passport');
const querystring = require('querystring');
const url = require('url');
const util = require('util');
const _ = require('lodash');

// internal packages
const aadutils = require('./aadutils');
const jwt = require('./jsonWebToken');
const nonceHandler = require('./nonceHandler');
const policyHandler = require('./policyHandler');
const stateHandler = require('./stateHandler');
const urlValidator = require('valid-url');

// we will use 'new' to get an instance of the following classes
const Log = require('./logging').getLogger;
const Metadata = require('./metadata').Metadata;
const OAuth2 = require('oauth').OAuth2;
const Validator = require('./validator').Validator;

// global variable definitions
const log = new Log('AzureAD: OIDC Passport Strategy');

const memoryCache = cacheManager.caching({ store: 'memory', max: 3600, ttl: 1800 /* seconds */ });
const ttl = 1800; // 30 minutes cache
// Note: callback is optional in set() and del().

function makeProfileObject(src, raw) {
  var email;
  if (src.emails) {
    if (Array.isArray(src.emails) && src.emails.length > 0)
      email = src.emails[0];
    else
      email = src.emails;
  }

  return {
    // Prior to OpenID Connect Basic Client Profile 1.0 - draft 22, the
    // 'sub' key was named 'user_id'.  Many providers still use the old
    // key, so fallback to that.
    id: src.sub || src.oid || src.user_id,
    displayName: src.name,
    name: {
      familyName: src.family_name,
      givenName: src.given_name,
      middleName: src.middle_name,
    },
    email: src.upn || src.preferred_username || src.oid || email,
    _raw: raw,
    _json: src,
  };
}

function onProfileLoaded(strategy, args) {
  function verified(err, user, info) {
    if (err) {
      return strategy.error(err);
    }
    if (!user) {
      return strategy.fail(info);
    }
    return strategy.success(user, info);
  }

  const verifyArityArgsMap = {
    8: 'iss sub profile jwtClaims access_token refresh_token params',
    7: 'iss sub profile access_token refresh_token params',
    6: 'iss sub profile access_token refresh_token',
    4: 'iss sub profile',
    3: 'iss sub',
  };

  const arity = (strategy._passReqToCallback) ? strategy._verify.length - 1 : strategy._verify.length;
  let verifyArgs = [args.profile, verified];

  if (verifyArityArgsMap[arity]) {
    verifyArgs = verifyArityArgsMap[arity]
      .split(' ')
      .map((argName) => {
        return args[argName];
      })
      .concat([verified]);
  }

  if (strategy._passReqToCallback) {
    verifyArgs.unshift(args.req);
  }

  return strategy._verify.apply(strategy, verifyArgs);
}

/**
 * Applications must supply a `verify` callback, for which the function
 * signature is:
 *
 *     function(token, done) { ... }
 *
 * `token` is the verified and decoded bearer token provided as a credential.
 * The verify callback is responsible for finding the user who posesses the
 * token, and invoking `done` with the following arguments:
 *
 *     done(err, user, info);
 *
 * If the token is not valid, `user` should be set to `false` to indicate an
 * authentication failure.  Additional token `info` can optionally be passed as
 * a third argument, which will be set by Passport at `req.authInfo`, where it
 * can be used by later middleware for access control.  This is typically used
 * to pass any scope associated with the token.
 *
 * Options:
 *
 *   - `identityMetadata`   (1) Required
 *                          (2) Must be a https url string
 *                          (3) Description:
 *                          the metadata endpoint provided by the Microsoft Identity Portal that provides 
 *                          the keys and other important info at runtime. Examples:
 *                          - https://login.microsoftonline.com/your_tenant_name.onmicrosoft.com/.well-known/openid-configuration
 *                          - https://login.microsoftonline.com/your_tenant_guid/.well-known/openid-configuration
 *                          - https://login.microsoftonline.com/common/.well-known/openid-configuration
 *
 *   - `clientID`           (1) Required
 *                          (2) must be a string
 *                          (3) Description:
 *                          The Client ID of your app in AAD
 *
 *   - `responseType`       (1) Required
 *                          (2) must be 'code', 'code id_token' or 'id_token'
 *                          (3) Description:
 *                          for login only flows use 'id_token'. For accessing resources use `code id_token`
 *
 *   - `responseMode`       (1) Required
 *                          (2) must be 'query' or 'form_post'
 *                          (3) Description:
 *                          For login only flows we should have token passed back to us in a POST
 *
 *   - `returnURL`          (1) Required
 *                          (2) must be a http or https url string
 *                          (3) Description:
 *                          The reply URL registered in AAD for your app
 * 
 *   - `clientSecret`       (1) Required if `responseType` is 'code' or 'code id_token'
 *                          (2) must be a string
 *                          (3) Description:
 *                          The app key or keys of your app from AAD. 
 *                          NOTE: For B2C, the app key sometimes contains '\', please replace '\' with '\\' in the app key
 *
 *   - `isB2C`              (1) Required for B2C
 *                          (2) must be true for B2C, default is false
 *                          (3) Description:
 *                          set to true if you are using B2C, default is false
 *
 *   - `issuer`             (1) Recommended if you are using 'common' endpoint, ignored for non-common endpoint
 *                          (2) must be a string or an array of strings
 *                          (3) Description:
 *                          For common endpoint, we don't validate issuer unless it is provided.
 *                          For non-common endpoint, we use the issuer provided by metadata, this field will be ignored
 *
 *   - `scope`              (1) Optional
 *                          (2) must be a string or an array of strings
 *                          (3) Description:
 *                          list of scope values indicating the required scope of the access token for accessing the requested
 *                          resource. Ex: ['email', 'profile']. 
 *                          We send 'openid' by default. For B2C, we also send 'offline_access' (to get refresh_token) and
 *                          clientID (to get access_token) by default.
 *
 *   - `passReqToCallback`  (1) Optional, default is false
 *                          (2) must be true or false
 *                          (3) Description:
 *                          if you want the Req to go back to the calling function for other processing use this.
 *
 *   - `loggingLevel`       (1) Optional
 *                          (2) must be 'info', 'warn', 'error'
 *                          (3) Description:
 *
 *
 * Examples:
 *
 * passport.use(new OIDCStrategy({
 *   identityMetadata: config.creds.identityMetadata,
 *   clientID: config.creds.clientID,
 *   responseType: config.creds.responseType,
 *   responseMode: config.creds.responseMode
 *   callbackURL: config.creds.returnURL, 
 *   clientSecret: config.creds.clientSecret,
 *   isB2C: config.creds.isB2C,
 *   issuer: config.creds.issuer,
 *   scope: config.creds.scopes,
 *   passReqToCallback: config.creds.passReqToCallback,
 *   loggingLevel: config.creds.loggingLevel
 * },
 *       function(token, done) {
 *         User.findById(token.sub, function (err, user) {
 *           if (err) { return done(err); }
 *           if (!user) { return done(null, false); }
 *           return done(null, user, token);
 *         });
 *       }
 *     ));
 *
 * For further details on HTTP Bearer authentication, refer to [The OAuth 2.0 Authorization Protocol: Bearer Tokens](http://tools.ietf.org/html/draft-ietf-oauth-v2-bearer)
 * For further details on JSON Web Token, refert to [JSON Web Token](http://tools.ietf.org/html/draft-ietf-oauth-json-web-token)
 *
 * @param {object} options - The Options.
 * @param {Function} verify - The verify callback.
 * @constructor
 */
function Strategy(options, verify) {
  passport.Strategy.call(this);

  /*
   *  Caution when you want to change these values in the member functions of
   *  Strategy, don't use `this`, since `this` points to a subclass of `Strategy`.
   *  To get `Strategy`, use Object.getPrototypeOf(this).
   *  
   *  More comments at the beginning of `Strategy.prototype.authenticate`. 
   */
  this._options = options;
  this.name = 'azuread-openidconnect';

  // stuff related to verify function
  this._verify = verify;
  this._passReqToCallback = !!options.passReqToCallback;

  /* When a user is authenticated for the first time, passport adds a new field
   * to req.session called 'passport', and puts a 'user' property inside (or your
   * choice of field name and property name if you change passport._key and 
   * passport._userProperty values). req.session['passport']['user'] is usually 
   * user_id (or something similar) of the authenticated user to reduce the size
   * of session. When the user logs out, req.session['passport']['user'] will be
   * destroyed. Any request between login (when authenticated for the first time)
   * and logout will have the 'user_id' in req.session['passport']['user'], so
   * passport can fetch it, find the user object in database and put the user
   * object into a new field: req.user. Then the subsequent middlewares and the 
   * app can use the user object. This is how passport keeps user authenticated. 
   *
   * For state validation, we also take advantage of req.session. we create a new
   * field: req.session[sessionKey], where the sessionKey is our choice (in fact, 
   * this._key, see below). When we send a request with state, we put state into
   * req.session[sessionKey].state; when we expect a request with state in query
   * or body, we compare the state in query/body with the one stored in 
   * req.session[sessionKey].state, and then destroy req.session[sessionKey].state.
   * User can provide a state by using `authenticate(Strategy, {state: 'xxx'})`, or
   * one will be generated automatically. This is essentially how passport-oauth2
   * library does the state validation, and we use the same way in our library. 
   *
   * request structure will look like the following. In real request some fields
   * might not be there depending on the purpose of the request.
   *
   *    request ---|--- sessionID
   *               |--- session --- |--- ...
   *               |                |--- 'passport' ---| --- 'user': 'user_id etc'
   *               |                |---  sessionKey---| --- state: 'xxx'            
   *               |--- ...
   *               |--- 'user':  full user info
   */
  this._key = options.sessionKey || ('OIDC: ' + options.callbackURL);

  options.isB2C = !!options.isB2C;


  // if logging level specified, switch to it.
  if (options.loggingLevel) { log.levels('console', options.loggingLevel); }

  /*
   * Take care of identityMetadata
   * (1) Check if it is common endpoint
   * (2) For B2C, one cannot use the common endpoint, tenant name or guid must be specified
   * (3) We add telemetry to identityMetadata automatically
   */

  // check existence
  if (!options.identityMetadata) {
    log.error('OIDCStrategy requires a metadata location that contains cert data for RSA and ECDSA callback.');
    throw new TypeError(`OIDCStrategy requires a metadata location that contains cert data for RSA and ECDSA callback.`);
  }

  // check if we are using the common endpoint
  options.isCommonEndpoint = (options.identityMetadata.indexOf('/common/') != -1);

  // common endpoint is not allowed for B2C
  if (options.isCommonEndpoint && options.isB2C) {
    throw new Error(`Cannot use common endpoint for B2C. Please use your tenant name or tenant guid.`);
  }

  // add telemetry
  options.identityMetadata = options.identityMetadata.concat(`?${aadutils.getLibraryProductParameterName()}=${aadutils.getLibraryProduct()}`)
  .concat(`&${aadutils.getLibraryVersionParameterName()}=${aadutils.getLibraryVersion()}`);

  /*
   * Take care of issuer
   * (1) For non-common endpoint, we always validate issuer, and we use the issuer
   *     value from the metadata.
   * (2) For common endpoint, we validate issuer only if user provides an issuer or
   *     an array of accepted issuers from the config file. It is highly recommended
   *     that the user provides the accepted issuer(s). 
   */

  // For non-common endpoint, we use the issuer value from metadata
  if (!options.isCommonEndpoint && options.issuer) {
    log.warn(`For non-common endpoint we use the issuer from metadata. User provided issuer will be ignored.`);
    options.issuer = null;
  }

  // For common endpoint, give a warning if issuer is not provided by user
  if (options._isCommonEndpoint) {
    if (!options.issuer)
      log.warn(`Production environments should always validate the issuer.`);
    // make it an array
    if (!Array.isArray(options.issuer))
      options.issuer = [options.issuer];
  }

  /*
   * Take care of scope
   */
  if (!Array.isArray(options.scope))
    options.scope = [options.scope];
  if (options.scope.indexOf('openid') === -1)
    options.scope.push('openid');
  // B2C, use 'offline_access' scope to get refresh_token
  if (options.isB2C && options.scope.indexOf('offline_access') === -1)
    options.scope.push('offline_access');
  // B2C, use clientId scope to get access_token
  if (options.isB2C && options.scope.indexOf(options.clientID) === -1)
    options.scope.push(options.clientID);
  options.scope = options.scope.join(' ');

  /*
   * Check if we are using v2 endpoint, v2 doesn't have an userinfo endpoint
   */
  if (options.identityMetadata.indexOf('/v2.0/') != -1)
    options._isV2 = true;

  /*
   * validate other necessary option items provided, we validate them here and only once
   */

  var itemsToValidate = objectTransform({
    source: options,
    pick: ['clientID', 'callbackURL', 'responseType', 'responseMode', 'identityMetadata']
  });

  var validatorConfiguration = {
    clientID: Validator.isNonEmpty,
    callbackURL: Validator.isURL,
    responseType: Validator.isTypeLegal,
    responseMode: Validator.isModeLegal,
    identityMetadata: Validator.isHttpsURL
  };
  // validator will throw exception if a required option is missing
  var validator = new Validator(validatorConfiguration);
  validator.validate(itemsToValidate);

  // we allow 'http' for the callbackURL, but don't recommend using 'http'
  if (urlValidator.isHttpUri(options.callbackURL))
    log.warn(`Using http for callbackURL is not recommended, please consider using https`);
}

// Inherit from `passport.Strategy`.
util.inherits(Strategy, passport.Strategy);

/**
 * Authenticate request by delegating to an OpenID Connect provider.
 *
 * @param {Object} req
 * @param {Object} options
 * @api protected
 */
Strategy.prototype.authenticate = function authenticateStrategy(req, authenticate_options) {
  /* 
   * We should be careful using 'this'. Avoid the usage like `this.xxx = ...`
   * unless you know what you are doing.
   *
   * In the passport source code 
   * (https://github.com/jaredhanson/passport/blob/master/lib/middleware/authenticate.js)
   * when it attempts to call the `oidcstrategy.authenticate` function, passport
   * creates an instance inherting oidcstrategy and then calls `instance.authenticate`.  
   * Therefore, when we come here, `this` is the instance, its prototype is the
   * actual oidcstrategy, i.e. the `Strategy`. This means:
   * (1) `this._options = `, `this._verify = `, etc only adds new fields to the
   *      instance, it doesn't change the values in oidcstrategy, i.e. `Strategy`. 
   * (2) `this._options`, `this._verify`, etc returns the field in the instance,
   *     and if there is none, returns the field in oidcstrategy, i.e. `strategy`.
   * (3) each time we call `authenticate`, we will get a brand new instance
   * 
   * If you want to change the values in `Strategy`, use 
   *      const oidcstrategy = Object.getPrototypeOf(self);
   * to get the strategy first.
   *
   * Note: Simply do `const self = Object.getPrototypeOf(this)` and use `self`
   * won't work, since the `this` instance has a couple of functions like
   * success/fail/error... which `authenticate` will call. The following is the
   * structure of `this`:
   *
   *   this
   *   | --  success:  function(user, info)
   *   | --  fail:     function(challenge, status)
   *   | --  redirect: function(url, status)
   *   | --  pass:     function()
   *   | --  __proto__:  Strategy
   *                 | --  _verify
   *                 | --  _options
   *                 | --  ...
   *                 | --  __proto__:
   *                              | --  authenticate:  function(req, options)
   *                              | --  ...
   */ 
  const self = this;
  const options = self._options;
  var params = {}; // params is used to save id_token, code, policy, metadataUrl, metadata, cacheKey
  var oauthConfig = {}; // configuration for oauth flow 
  var optionsToValidate = {}; // the options we will validate, such as issuer, audience

  async.waterfall(
    [
      /*****************************************************************************
       * Step 1. Extract parameters from the request, such as 'id_token', 'code', 
       * and 'policy' 
       ****************************************************************************/
      (next) => {
        var err, err_description, id_token, code, policy;
        err = err_description = id_token = code = policy = null;

        // we shouldn't get any access_token or refresh_token from the request
        if ((req.query && (req.query.access_token || req.query.refresh_token)) ||
          (req.body && (req.body.access_token || req.body.refresh_token)))
          return self.failWithLog('neither access token nor refresh token is expected in the incoming request');

        // the source (query or body) to get err, id_token, code etc
        var source = null;

        if (req.query && (req.query.error || req.query.id_token || req.query.code))
          source = req.query;
        else if (req.body && (req.body.error || req.body.id_token || req.body.code))
          source = req.body;

        if (source) {
          err = source.error;
          err_description = source.error_description;
          id_token = source.id_token;
          code = source.code;
        }

        // handle the error
        if (err)
          return self._errorResponseHandler(err, err_description);

        // if there is no error, then we need to figure out the policy for B2C
        // so later we can load the corret medatadata
        // (1) hybrid/implicit/code flow (we get either 'id_token' or 'code' or both)
        //     this case 'policy' is stored in session
        // (2) otherwise, 'policy' should be in the query
        if (options.isB2C) {
          if (!id_token && !code) {
            policy = req.query.p;
            if (!policy || policy === '')
              return self.failWithLog('missing policy in the request for B2C');
          } else {
            policy = policyHandler.getPolicy(req, self._key);
            if (!policy || policy === '')
              return self.failWithLog('missing policy in the session for B2C');
          }

          // validate B2C policy, it must start with "B2C_1_" (ignoring the case)
          if (policy.length <= 6 || policy.substring(0,6).toUpperCase() !== 'B2C_1_')
            return self.failWithLog('invalid B2C policy');
        }

        params = {id_token: id_token, code: code, policy: policy};
        log.info('recieved the following parameters in the request: ' + params);

        return next(null);
      },

      /*****************************************************************************
       * Step 2. Compute metadata url and load metadata
       ****************************************************************************/
      (next) => {
        var metadataUrl = self._options.identityMetadata;
        var cachekey = 'ordinary'; // non B2C metadata cachekey

        if (options.isB2C) {
          metadataUrl = metadataUrl.concat(`&p=${params.policy}`);
          cachekey = 'policy: ' + params.policy;  // B2C metadata cachekey
          log.info(`B2C metadataUrl is: ${metadataUrl}`);
        } else {
          log.info(`metadataUrl is: ${metadataUrl}`);
        }

        params.metadataUrl = metadataUrl;
        params.cachekey = cachekey;

        return self.setOptions(params, oauthConfig, optionsToValidate, next);
      },

      /***************************************************************************** 
       * Step 3. Handle the flows
       *----------------------------------------------------------------------------
       * (1) implicit flow (response_type = 'id_token')
       *     This case we get a 'id_token'
       * (2) hybrid flow (response_type = 'id_token code')
       *     This case we get both 'id_token' and 'code'
       * (3) authorization code flow (response_type = 'code')
       *     This case we get a 'code', we will use it to get 'access_token' and 'id_token'
       * (4) for any other request, we will ask for authorization and initialize 
       *     the authorization process 
       ****************************************************************************/
      (next) => {
        var id_token = params.id_token;
        var code = params.code;

        if (!id_token && !code) {
          // ask for authorization, initialize the authorization process
          return self._flowInitializationHandler(req, oauthConfig, next);
        }

        // check state
        var stateCheckResult = stateHandler.verifyState(req, self._key);
        if (!stateCheckResult.valid) {
          return self.failWithLog(stateCheckResult.errorMessage);
        }

        if (id_token && code) {
          // handle hybrid flow
          return self._hybridFlowHandler(params, oauthConfig, optionsToValidate, req, next);
        } else if (id_token) {
          // handle implicit flow
          return self._implicitFlowHandler(params, optionsToValidate, req, next);
        } else {
          // handle authorization code flow
          return self._authCodeFlowHandler(params, oauthConfig, optionsToValidate, req, next);
        }
      }
    ],

    (waterfallError) => {
      // this code gets called after the three steps above are done
      if (waterfallError) {
        return self.error(waterfallError);
      }
      return true;
    });
};

/**
 */
Strategy.prototype.setOptions = function setOptions(params, oauthConfig, optionsToValidate, done) {
  const self = this;

  var metadataUrl = params.metadataUrl;
  var cachekey = params.cachekey;
  var metadata = new Metadata(metadataUrl, 'oidc', self._options);

  async.waterfall([

    // load metadata
    (next) => {
      log.info('Parsing Metadata: ', metadataUrl);

      memoryCache.wrap(cachekey, (cacheCallback) => {
        metadata.fetch((fetchMetadataError) => {
          if (fetchMetadataError) {
            return cacheCallback(new Error(`Unable to fetch metadata: ${fetchMetadataError}`));
          }
          return cacheCallback(null, metadata);
        });
      }, { ttl }, next);
    },

    // set oauthConfig and optionsToValidate
    (metadata, next) => {
      if (!metadata.oidc)
        return self.failWithLog('failed to load metadata');

      params.metadata = metadata;

      // set optionsToValidate
      // audience
      optionsToValidate.audience = self._options.clientID;
      optionsToValidate.allowMultiAudiencesInToken = false;

      // algorithms
      optionsToValidate.algorithms = metadata.oidc.algorithms;

      // issuer
      optionsToValidate.validateIssuer = true;
      if (!self._options.isCommonEndpoint)
        optionsToValidate.issuer = [metadata.oidc.issuer];
      else if (self._options.issuer)
        optionsToValidate.issuer = self._options.issuer;
      else
        optionsToValidate.validateIssuer = false;

      // set oauthConfig
      aadutils.copyObjectFields(metadata.oidc, oauthConfig, ['auth_endpoint', 'algorithms', 'token_endpoint', 'userinfo_endpoint']);
      aadutils.copyObjectFields(self._options, oauthConfig, ['clientID', 'clientSecret', 'responseType', 'responseMode', 'scope', 'callbackURL']);

      // validate oauthConfig
      const validatorConfig = {
        auth_endpoint: Validator.isHttpsURL,
        token_endpoint: Validator.isHttpsURL,
        algorithms: Validator.isNonEmpty
      };

      // validator will throw exception if a required option is missing
      const checker = new Validator(validatorConfig);
      checker.validate(oauthConfig);

      next(null);
    },
  ], done);
};

/**
 * validate id_token, and pass the validated claims and the payload to callback
 * if code (resp. access_token) is provided, we will validate the c_hash (resp at_hash) as well
 *
 * @param {String} id_token
 * @param {String} code (if you want to validate c_hash)
 * @param {String} access_token (if you want to validate at_hash)
 * @param {Object} req
 * @param {Function} callback
 */
Strategy.prototype._validateResponse = function validateResponse(params, optionsToValidate, req, callback) {
  const self = this;

  var id_token = params.id_token;
  var code = params.code;
  var access_token = params.access_token;

  // decode id_token
  const decoded = jws.decode(id_token);
  if (decoded == null)
    return self.failWithLog('Invalid JWT token');

  log.info('token decoded: ', decoded);

  // get Pem Key
  var PEMkey = null;
  if (decoded.header.kid) {
    PEMkey = params.metadata.generateOidcPEM(decoded.header.kid);
  } else if (decoded.header.x5t) {
    PEMkey = params.metadata.generateOidcPEM(decoded.header.x5t);
  } else {
    return self.failWithLog('We did not receive a token we know how to validate');
  }

  // verify id_token signature and claims
  return jwt.verify(id_token, PEMkey, optionsToValidate, (err, jwtClaims) => {
    if (err) {
      if (err.message)
        return self.failWithLog(err.message);
      else
        return self.failWithLog("cannot verify id token");
    }

    log.info("Claims received: ", jwtClaims);

    // jwt checks the 'nbf', 'exp', 'aud', 'iss' claims
    // there are a few other things we will check below

    // For B2C, check the policy
    if (self._options.isB2C) {
      if (!jwtClaims.acr || jwtClaims.acr.length <= 6 || jwtClaims.acr.substring(0,6).toUpperCase() !== 'B2C_1_')
        return self.failWithLog('invalid B2C policy in id_token');

      var acr = jwtClaims.acr.substring(6);
      var p = params.policy.substring(6);

      if (p !== acr) {
        log.error(`jwtClaims.acr doesn't match the policy used`);
        return self.failWithLog("acr in id_token does not match the policy used");
      }
    }

    // check the nonce in claims
    var nonceCheckResult = nonceHandler.verifyNonce(req, self._key, jwtClaims.nonce);
    if (!nonceCheckResult.valid)
      return self.failWithLog(nonceCheckResult.errorMessage);

    // check c_hash
    if (jwtClaims.c_hash) {
      // checkHashValueRS256 checks if code is null, so we don't bother here
      if (!aadutils.checkHashValueRS256(code, jwtClaims.c_hash)) 
        return self.failWithLog("invalid c_hash");
    }

    // check at_hash
    if (jwtClaims.at_hash) {
      // checkHashValueRS256 checks if access_token is null, so we don't bother here
      if (!aadutils.checkHashValueRS256(access_token, jwtClaims.at_hash))
        return self.failWithLog("invalid at_hash");
    }

    // return jwt claims and jwt claims string
    var idTokenSegments = id_token.split('.');
    var jwtClaimsStr = base64url.decode(idTokenSegments[1]);
    return callback(jwtClaimsStr, jwtClaims);
  });
};

/**
 * handle error response
 *
 * @params {String} err 
 * @params {String} err_description
 */
Strategy.prototype._errorResponseHandler = function errorResponseHandler(err, err_description) {
  const self = this;

  log.info('Error received in the response was: ', err);
  if (err_description)
    log.info('Error description received in the response was: ', err_description);

  // Unfortunately, we cannot return the 'error description' to the user, since 
  // it goes to http header by default and it usually contains characters that
  // http header doesn't like, which causes the program to crash. 
  return self.failWithLog(err);
};

/**
 * handle the response where we only get 'id_token' in the response
 *
 * @params {Object} id_token 
 * @params {Object} req
 * @params {Function} next
 */
Strategy.prototype._implicitFlowHandler = function implicitFlowHandler(params, optionsToValidate, req, next) {
  /* we will do the following things in order
   * (1) validate id_token
   * (2) use the claims in the id_token for user's profile
   */

  const self = this;

  log.info('entering Strategy.prototype._implicitFlowHandler, received id_token: ' + params.id_token);

  // validate the id_token
  return self._validateResponse(params, optionsToValidate, req, (jwtClaimsStr, jwtClaims) => {
    const sub = jwtClaims.sub;
    const iss = jwtClaims.iss;
    
    // we are not doing auth code so we set the tokens to null
    const access_token = null;
    const refresh_token = null;
    const params = null;

    log.info('we are in implicit flow, use the content in id_token as the profile');

    return onProfileLoaded(self, {
      req,
      sub,
      iss,
      profile: makeProfileObject(jwtClaims, jwtClaimsStr),
      jwtClaims,
      access_token,
      refresh_token,
      params,
    });
  });
};

/**
 * handle the response where we get 'id_token' and 'code' in the response
 *
 * @params {Object} id_token 
 * @params {Object} code
 * @params {Object} req
 * @params {Function} next
 */
Strategy.prototype._hybridFlowHandler = function hybridFlowHandler(params, oauthConfig, optionsToValidate, req, next) {
  /* we will do the following things in order
   * (1) validate the id_token and the code
   * (2) if there is no userinfo token needed (or ignored if using AAD v2 ), we use 
   *     the claims in id_token for user's profile
   * (3) if userinfo token is needed, we will use the 'code' and the authorization code flow
   */
  const self = this;

  log.info('entering Strategy.prototype._hybridFlowHandler, received code: ' + params.code + ', received id_token: ' + params.id_token);

  // nonce is deleted after id_token is valiated. If we use the authorization code
  // flow, we will get a second id_token, so we want to save the nonce and use it
  // for the second id_token validation later. 
  var nonce = req.session[self._key].nonce;

  // save nonce, since if we use the authorization code flow later, we have to check 
  // nonce again.

  // validate the id_token and the code
  return self._validateResponse(params, optionsToValidate, req, (jwtClaimsStr, jwtClaims) => {
    // c_hash is required for 'code id_token' flow. If we have c_hash, then _validateResponse already
    // validates it; otherwise, _validateResponse ignores the c_hash check, and we check here
    if (!jwtClaims.c_hash)
      return self.failWithLog("we are in hybrid flow using code id_token, but c_hash is not found in id_token");

    const sub = jwtClaims.sub;
    const iss = jwtClaims.iss;

    // since we will get a second id_token, we put nonce back into req.session
    nonceHandler.addNonceToSession(req, self._key, nonce);

    // now we use the authorization code flow
    return self._authCodeFlowHandler(params, oauthConfig, optionsToValidate, req, next, iss, sub);
  });
};

/**
 * handle the response where we only get 'code' in the response
 *
 * @params {Object} code
 * @params {Object} req
 * @params {Function} next
 * // the following are required if you used 'code id_token' flow then call this function to 
 * // redeem the code for another id_token from the token endpoint. iss and sub are those 
 * // in the id_token from authorization endpoint, and they should match those in the id_token
 * // from the token endpoint 
 * @params {String} iss
 * @params {String} sub
 */
Strategy.prototype._authCodeFlowHandler = function authCodeFlowHandler(params, oauthConfig, optionsToValidate, req, next, iss, sub) {
  /* we will do the following things in order:
   * (1) use code to get id_token and access_token
   * (2) validate the id_token and the access_token received
   * (3) if user asks for userinfo and we are using AAD v1, then we use access_token to get
   *     userinfo, then make sure the userinfo has the same 'sub' as that in the 'id_token'
   */
  const self = this;
  var code = params.code;

  log.info('entering Strategy.prototype._authCodeFlowHandler, received code: ' + code);

  var issFromPrevIdToken = iss;
  var subFromPrevIdToken = sub;

  let libraryVersion = aadutils.getLibraryVersion();
  let libraryVersionParameterName = aadutils.getLibraryVersionParameterName();
  let libraryProduct = aadutils.getLibraryProduct();
  let libraryProductParameterName = aadutils.getLibraryProductParameterName();

  const oauth2 = new OAuth2(
    oauthConfig.clientID, // consumerKey
    oauthConfig.clientSecret, // consumer secret
    '', // baseURL (empty string because we use absolute urls for authorize and token paths)
    oauthConfig.auth_endpoint, // authorizePath
    oauthConfig.token_endpoint, // accessTokenPath
    {libraryProductParameterName : libraryProduct,
     libraryVersionParameterName : libraryVersion} // customHeaders
  );

  return oauth2.getOAuthAccessToken(code, {
    grant_type: 'authorization_code',
    redirect_uri: oauthConfig.callbackURL,
    scope: oauthConfig.scope
  }, (getOAuthAccessTokenError, access_token, refresh_token, items) => {
    if (getOAuthAccessTokenError) {
      if (getOAuthAccessTokenError.message)
        return self.failWithLog('failed to redeem authorization code: ' + getOAuthAccessTokenError.message);
      else
        return self.failWithLog('failed to redeem authorization code');
    }

    // id_token should be present
    if (!items.id_token)
      return self.failWithLog('id_token is not received');

    // token_type must be 'Bearer'
    if (items.token_type !== 'Bearer') {
      log.info('token_type received is: ', items.token_type);
      return self.failWithLog(`token_type received is not 'Bearer'`);
    }

    log.info('received id_token: ', items.id_token);

    items.access_token = access_token;
    items.metadata = params.metadata;
    items.policy = params.policy;

    return self._validateResponse(items, optionsToValidate, req, (jwtClaimsStr, jwtClaims) => {
      // for 'code id_token' flow, check iss/sub in the id_token from the authorization endpoint
      // with those in the id_token from token endpoint
      if (issFromPrevIdToken && issFromPrevIdToken !== jwtClaims.iss)
        return self.failWithLog('After redeeming the code, iss in id_token from authorize_endpoint does not match iss in id_token from token_endpoint');
      if (subFromPrevIdToken && subFromPrevIdToken !== jwtClaims.sub)
        return self.failWithLog('After redeeming the code, iss in id_token from authorize_endpoint does not match iss in id_token from token_endpoint');

      const sub = jwtClaims.sub;
      const iss = jwtClaims.iss;
      
      // load the userinfo if this is not v2
      if (!self._options._isV2) {
        // make sure we get an access_token
        if (!access_token)
          return self.failWithLog("we want to access userinfo endpoint, but access_token is not received");

        let parsedUrl;
        try {
          parsedUrl = url.parse(oauthConfig.userinfo_endpoint, true);
        } catch (urlParseException) {
          return self.failWithLog(`Failed to parse config property 'userInfoURL' with value ${oauthConfig.userinfo_endpoint}`);
        }

        parsedUrl.query.schema = 'openid';
        delete parsedUrl.search; // delete operations are slow; should we rather just overwrite it with {}
        const userInfoURL = url.format(parsedUrl);

        // ask oauth2 to use authorization header to bearer access token
        oauth2.useAuthorizationHeaderforGET(true);
        return oauth2.get(userInfoURL, access_token, (getUserInfoError, body) => {
          if (getUserInfoError) {
            if (getUserInfoError.message)
              return self.fail('failed to fetch user profile: ' + getUserInfoError.message);
            else
              return self.fail('failed to fetch user profile');
          }

          log.info('Profile loaded from MS identity', body);

          var userinfoReceived = null;
          // use try / catch around JSON.parse --> could fail unexpectedly
          try {
            userinfoReceived = JSON.parse(body);
          } catch (ex) {
            return next(ex);
          }

          // make sure the 'sub' in userinfo is the same as the one in 'id_token'
          if (userinfoReceived.sub !== jwtClaims.sub) {
            log.error('sub in userinfo is ' + userinfoReceived.sub + ', but does not match sub in id_token, which is ' + id_token.sub);
            return self.failWithLog('sub received in userinfo and id_token do not match');
          }

          return onProfileLoaded(self, {
            req,
            sub,
            iss,
            profile: makeProfileObject(userinfoReceived, body),
            jwtClaims,
            access_token,
            refresh_token,
            params,
          });
        });
      } else {
        // v2 doesn't have userinfo endpoint, so we use the content in id_token as the profile
        log.info('v2 has no userinfo endpoint, using the content in id_token as the profile');

        return onProfileLoaded(self, {
          req,
          sub,
          iss,
          profile: makeProfileObject(jwtClaims, jwtClaimsStr),
          jwtClaims,
          access_token,
          refresh_token,
          params,
        });
      }
    });
  });
};

/**
 * prepare the initial authorization request
 *
 * @params {Object} req
 * @params {Function} next
 */
Strategy.prototype._flowInitializationHandler = function flowInitializationHandler(req, oauthConfig, next) {
  // The request being authenticated is initiating OpenID Connect
  // authentication. Prior to redirecting to the provider, configuration will
  // be loaded. The configuration is typically either pre-configured or
  // discovered dynamically. When using dynamic discovery, a user supplies
  // their identifer as input.

  const self = this;

  log.info(`entering Strategy.prototype._flowInitializationHandler`);

  const params = {
    'redirect_uri': oauthConfig.callbackURL,
    'response_type': oauthConfig.responseType,
    'response_mode': oauthConfig.responseMode,
    'client_id': oauthConfig.clientID
  };

  log.info('We are sending the response_type: ', params.response_type);
  log.info('We are sending the response_mode: ', params.response_mode);

  // add state to params and session, use a randomly generated one
  let state = params.state = aadutils.uid(32);
  stateHandler.addStateToSession(req, self._key, state);

  // add policy to session
  if (req.query.p)
    policyHandler.addPolicyToSession(req, self._key, req.query.p);

  // add nonce, use a randomly generated one
  let nonce = params.nonce = aadutils.uid(32);
  nonceHandler.addNonceToSession(req, self._key, nonce);

  // add scope
  params.scope = oauthConfig.scope;

  // add telemetry
  params[aadutils.getLibraryProductParameterName()] = aadutils.getLibraryProduct();
  params[aadutils.getLibraryVersionParameterName()] = aadutils.getLibraryVersion();
  let location;

  // Implement support for standard OpenID Connect params (display, prompt, etc.)
  if (req.query.p)
    location = `${oauthConfig.auth_endpoint}&${querystring.stringify(params)}`;
  else
    location = `${oauthConfig.auth_endpoint}?${querystring.stringify(params)}`;

  return self.redirect(location);
};

Strategy.prototype.failWithLog = function(message) {
  log.error(message);
  return this.fail(message);
}

module.exports = Strategy;
