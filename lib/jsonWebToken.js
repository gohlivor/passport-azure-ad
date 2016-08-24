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

'use restrict';

const jws = require('jws');

/* Verify the token and return the payload
 *
 * @jwtString
 * @PEMKey
 * @options
 *   - algorithms (required)
 *   - audience (required)
 *   - issuer (optional, validate if provided)
 *   - subject (optional, validate if provided)
 *   - ignoreExpiration (optional, if not set true we will validate expiration)
 * @callback
 */
exports.verify = function(jwtString, PMEKey, options, callback) {

  /*********************************************************************
   * Checking parameters
   ********************************************************************/

  // All of the four parameters are required
  if (!jwtString)
    throw new Error('jwtString must be provided in jsonWebToken.verify');
  if (!PMEKey)
    throw new Error('PMEKey must be provided in jsonWebToken.verify');
  if (!options)
    throw new Error('options must be provided in jsonWebToken.verify');
  if (!callback)
    throw new Error('callback must be provided in jsonWebToken.verify');
  if (typeof callback !== 'function')
    throw new Error('callback in jsonWebToken.verify must be a function');

  // asynchronous wrapper for callback
  var done = function() {
    var args = Array.prototype.slice.call(arguments, 0);
    return process.nextTick(function() {
      callback.apply(null, args);
    });
  };

  // make sure we have the required fields in options
  if (!options.audience)
    return done(new Error('options.audience is missing in jsonWebToken.verify'));
  if (!options.algorithms)
    return done(new Error('options.algorithms is missing in jsonWebToken.verify'));
  if (!Array.isArray(options.algorithms) || options.algorithms.length == 0)
    return done(new Error('options.algorithms must be an array containing at least 1 algorithm'));

  /*********************************************************************
   * Checking jwtString structure, getting header, payload and signature
   ********************************************************************/

  // split jwtString, make sure we have three parts and we have signature
  var parts = jwtString.split('.');
  if (parts.length !== 3)
    return done(new Error('jwtString is malformed'));
  if (parts[2] === '')
    return done(new Error('signature is missing in jwtString'));
  
  // decode jwsString
  var decodedToken;
  try {
    decodedToken = jws.decode(jwtString);
  } catch(err) {
    return done(new Error('invalid token'));
  }

  if (!decodedToken) {
    return done(new Error('invalid token'));
  }

  // get header, payload and signature
  var header = decodedToken.header;
  var payload = decodedToken.payload;
  var signature = decodedToken.signature;

  if (!header)
    return done(new Error('missing header in the token'));
  if (!payload)
    return done(new Error('missing payload in the token'));
  if (!signature)
    return done(new Error('missing signature in the token'));

  /*********************************************************************
   * validate algorithm and signature
   ********************************************************************/

  // alg in the token header should be one of those provided in options.algorithms
  if (!~options.algorithms.indexOf(header.alg)) {
    return done(new Error('invalid algorithm'));
  }

  try {
    var valid = jws.verify(jwtString, header.alg, PMEKey);
    if (!valid)
      return done(new Error('invalid signature'));
  } catch (e) {
    return done(e);
  }

  /*********************************************************************
   * validate payload content
   ********************************************************************/

  // (1) issuer
  //   - check the existence and the format of payload.iss
  //   - validate if options.issuer is set
  if (typeof payload.iss !== 'string')
    return done(new Error('invalid iss value in payload'));
  if (options.issuer && options.issuer !== payload.iss)
    return done(new Error('jwt issuer is invalid. expected: ' + options.issuer));

  // (2) subject
  //   - check the existence and the format of payload.sub
  //   - validate if options.subject is set
  if (typeof payload.sub !== 'string')
    return done(new Error('invalid sub value in payload'));
  if (options.subject && options.subject !== payload.sub)
      return done(new Error('jwt subject is invalid. expected: ' + options.subject));

  // (3) audience
  //   - always validate
  //   - allow payload.aud to be an array of audience
  //   - options.audience must be a string
  if (typeof options.audience !== 'string')
    return done(new Error('invalid options.audience value'));
  var payload_audience = Array.isArray(payload.aud) ? payload.aud : [payload.aud];
  if (payload_audience.indexOf(options.audience) == -1)
    return done(new Error('jwt audience is invalid. expected: ' + options.audience));

  // (4) expiration
  //   - check the existence and the format of payload.exp
  //   - validate unless options.ignoreExpiration is set true
  if (typeof payload.exp !== 'number')
    return done(new Error('invalid exp value in payload'));
  if (!options.ignoreExpiration) {
    if (Math.floor(Date.now() / 1000) >= payload.exp) {
      return done(new Error('jwt is expired'));
    }
  }

  // (5) iat
  //   - check the existence and the format of payload.exp
  if (typeof payload.iat !== 'number')
    return done(new Error('invalid iat value in payload'));

  // (6) nbf
  //   - check if it exists
  if (payload.nbf) {
    if (typeof payload.nbf !== 'number')
      return done(new Error('invalid nbf value in payload'));
    if (payload.nbf > Math.floor(Date.now() / 1000))
      return done(new Error('jwt is not active'));
  }

  /*********************************************************************
   * return the payload content
   ********************************************************************/

  return done(null, payload);
};