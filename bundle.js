
(function(l, i, v, e) { v = l.createElement(i); v.async = 1; v.src = '//' + (location.host || 'localhost').split(':')[0] + ':35729/livereload.js?snipver=1'; e = l.getElementsByTagName(i)[0]; e.parentNode.insertBefore(v, e)})(document, 'script');
(function (React, ReactDOM, showdown) {
    'use strict';

    var React__default = 'default' in React ? React['default'] : React;
    ReactDOM = ReactDOM && ReactDOM.hasOwnProperty('default') ? ReactDOM['default'] : ReactDOM;

    /*! *****************************************************************************
    Copyright (c) Microsoft Corporation. All rights reserved.
    Licensed under the Apache License, Version 2.0 (the "License"); you may not use
    this file except in compliance with the License. You may obtain a copy of the
    License at http://www.apache.org/licenses/LICENSE-2.0

    THIS CODE IS PROVIDED ON AN *AS IS* BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
    KIND, EITHER EXPRESS OR IMPLIED, INCLUDING WITHOUT LIMITATION ANY IMPLIED
    WARRANTIES OR CONDITIONS OF TITLE, FITNESS FOR A PARTICULAR PURPOSE,
    MERCHANTABLITY OR NON-INFRINGEMENT.

    See the Apache Version 2.0 License for specific language governing permissions
    and limitations under the License.
    ***************************************************************************** */
    /* global Reflect, Promise */

    var extendStatics = function(d, b) {
        extendStatics = Object.setPrototypeOf ||
            ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
            function (d, b) { for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p]; };
        return extendStatics(d, b);
    };

    function __extends(d, b) {
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    }

    var __assign = function() {
        __assign = Object.assign || function __assign(t) {
            for (var s, i = 1, n = arguments.length; i < n; i++) {
                s = arguments[i];
                for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p)) t[p] = s[p];
            }
            return t;
        };
        return __assign.apply(this, arguments);
    };

    function __rest(s, e) {
        var t = {};
        for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p) && e.indexOf(p) < 0)
            t[p] = s[p];
        if (s != null && typeof Object.getOwnPropertySymbols === "function")
            for (var i = 0, p = Object.getOwnPropertySymbols(s); i < p.length; i++) if (e.indexOf(p[i]) < 0)
                t[p[i]] = s[p[i]];
        return t;
    }

    function __awaiter(thisArg, _arguments, P, generator) {
        return new (P || (P = Promise))(function (resolve, reject) {
            function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
            function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
            function step(result) { result.done ? resolve(result.value) : new P(function (resolve) { resolve(result.value); }).then(fulfilled, rejected); }
            step((generator = generator.apply(thisArg, _arguments || [])).next());
        });
    }

    function __generator(thisArg, body) {
        var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g;
        return g = { next: verb(0), "throw": verb(1), "return": verb(2) }, typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
        function verb(n) { return function (v) { return step([n, v]); }; }
        function step(op) {
            if (f) throw new TypeError("Generator is already executing.");
            while (_) try {
                if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;
                if (y = 0, t) op = [op[0] & 2, t.value];
                switch (op[0]) {
                    case 0: case 1: t = op; break;
                    case 4: _.label++; return { value: op[1], done: false };
                    case 5: _.label++; y = op[1]; op = [0]; continue;
                    case 7: op = _.ops.pop(); _.trys.pop(); continue;
                    default:
                        if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                        if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                        if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                        if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                        if (t[2]) _.ops.pop();
                        _.trys.pop(); continue;
                }
                op = body.call(thisArg, _);
            } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
            if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
        }
    }

    var commonjsGlobal = typeof globalThis !== 'undefined' ? globalThis : typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : typeof self !== 'undefined' ? self : {};

    function unwrapExports (x) {
    	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
    }

    function createCommonjsModule(fn, module) {
    	return module = { exports: {} }, fn(module, module.exports), module.exports;
    }

    // Copyright Joyent, Inc. and other Node contributors.

    // If obj.hasOwnProperty has been overridden, then calling
    // obj.hasOwnProperty(prop) will break.
    // See: https://github.com/joyent/node/issues/1707
    function hasOwnProperty(obj, prop) {
      return Object.prototype.hasOwnProperty.call(obj, prop);
    }

    var decode = function(qs, sep, eq, options) {
      sep = sep || '&';
      eq = eq || '=';
      var obj = {};

      if (typeof qs !== 'string' || qs.length === 0) {
        return obj;
      }

      var regexp = /\+/g;
      qs = qs.split(sep);

      var maxKeys = 1000;
      if (options && typeof options.maxKeys === 'number') {
        maxKeys = options.maxKeys;
      }

      var len = qs.length;
      // maxKeys <= 0 means that we should not limit keys count
      if (maxKeys > 0 && len > maxKeys) {
        len = maxKeys;
      }

      for (var i = 0; i < len; ++i) {
        var x = qs[i].replace(regexp, '%20'),
            idx = x.indexOf(eq),
            kstr, vstr, k, v;

        if (idx >= 0) {
          kstr = x.substr(0, idx);
          vstr = x.substr(idx + 1);
        } else {
          kstr = x;
          vstr = '';
        }

        k = decodeURIComponent(kstr);
        v = decodeURIComponent(vstr);

        if (!hasOwnProperty(obj, k)) {
          obj[k] = v;
        } else if (Array.isArray(obj[k])) {
          obj[k].push(v);
        } else {
          obj[k] = [obj[k], v];
        }
      }

      return obj;
    };

    // Copyright Joyent, Inc. and other Node contributors.

    var stringifyPrimitive = function(v) {
      switch (typeof v) {
        case 'string':
          return v;

        case 'boolean':
          return v ? 'true' : 'false';

        case 'number':
          return isFinite(v) ? v : '';

        default:
          return '';
      }
    };

    var encode = function(obj, sep, eq, name) {
      sep = sep || '&';
      eq = eq || '=';
      if (obj === null) {
        obj = undefined;
      }

      if (typeof obj === 'object') {
        return Object.keys(obj).map(function(k) {
          var ks = encodeURIComponent(stringifyPrimitive(k)) + eq;
          if (Array.isArray(obj[k])) {
            return obj[k].map(function(v) {
              return ks + encodeURIComponent(stringifyPrimitive(v));
            }).join(sep);
          } else {
            return ks + encodeURIComponent(stringifyPrimitive(obj[k]));
          }
        }).join(sep);

      }

      if (!name) return '';
      return encodeURIComponent(stringifyPrimitive(name)) + eq +
             encodeURIComponent(stringifyPrimitive(obj));
    };

    var querystring = createCommonjsModule(function (module, exports) {

    exports.decode = exports.parse = decode;
    exports.encode = exports.stringify = encode;
    });
    var querystring_1 = querystring.decode;
    var querystring_2 = querystring.parse;
    var querystring_3 = querystring.encode;
    var querystring_4 = querystring.stringify;

    var slugify = createCommonjsModule(function (module, exports) {
    (function (name, root, factory) {
      {
        module.exports = factory();
        module.exports['default'] = factory();
      }
    }('slugify', commonjsGlobal, function () {
      /* eslint-disable */
      var charMap = JSON.parse('{"$":"dollar","%":"percent","&":"and","<":"less",">":"greater","|":"or","¢":"cent","£":"pound","¤":"currency","¥":"yen","©":"(c)","ª":"a","®":"(r)","º":"o","À":"A","Á":"A","Â":"A","Ã":"A","Ä":"A","Å":"A","Æ":"AE","Ç":"C","È":"E","É":"E","Ê":"E","Ë":"E","Ì":"I","Í":"I","Î":"I","Ï":"I","Ð":"D","Ñ":"N","Ò":"O","Ó":"O","Ô":"O","Õ":"O","Ö":"O","Ø":"O","Ù":"U","Ú":"U","Û":"U","Ü":"U","Ý":"Y","Þ":"TH","ß":"ss","à":"a","á":"a","â":"a","ã":"a","ä":"a","å":"a","æ":"ae","ç":"c","è":"e","é":"e","ê":"e","ë":"e","ì":"i","í":"i","î":"i","ï":"i","ð":"d","ñ":"n","ò":"o","ó":"o","ô":"o","õ":"o","ö":"o","ø":"o","ù":"u","ú":"u","û":"u","ü":"u","ý":"y","þ":"th","ÿ":"y","Ā":"A","ā":"a","Ă":"A","ă":"a","Ą":"A","ą":"a","Ć":"C","ć":"c","Č":"C","č":"c","Ď":"D","ď":"d","Đ":"DJ","đ":"dj","Ē":"E","ē":"e","Ė":"E","ė":"e","Ę":"e","ę":"e","Ě":"E","ě":"e","Ğ":"G","ğ":"g","Ģ":"G","ģ":"g","Ĩ":"I","ĩ":"i","Ī":"i","ī":"i","Į":"I","į":"i","İ":"I","ı":"i","Ķ":"k","ķ":"k","Ļ":"L","ļ":"l","Ľ":"L","ľ":"l","Ł":"L","ł":"l","Ń":"N","ń":"n","Ņ":"N","ņ":"n","Ň":"N","ň":"n","Ő":"O","ő":"o","Œ":"OE","œ":"oe","Ŕ":"R","ŕ":"r","Ř":"R","ř":"r","Ś":"S","ś":"s","Ş":"S","ş":"s","Š":"S","š":"s","Ţ":"T","ţ":"t","Ť":"T","ť":"t","Ũ":"U","ũ":"u","Ū":"u","ū":"u","Ů":"U","ů":"u","Ű":"U","ű":"u","Ų":"U","ų":"u","Ź":"Z","ź":"z","Ż":"Z","ż":"z","Ž":"Z","ž":"z","ƒ":"f","Ơ":"O","ơ":"o","Ư":"U","ư":"u","ǈ":"LJ","ǉ":"lj","ǋ":"NJ","ǌ":"nj","Ș":"S","ș":"s","Ț":"T","ț":"t","˚":"o","Ά":"A","Έ":"E","Ή":"H","Ί":"I","Ό":"O","Ύ":"Y","Ώ":"W","ΐ":"i","Α":"A","Β":"B","Γ":"G","Δ":"D","Ε":"E","Ζ":"Z","Η":"H","Θ":"8","Ι":"I","Κ":"K","Λ":"L","Μ":"M","Ν":"N","Ξ":"3","Ο":"O","Π":"P","Ρ":"R","Σ":"S","Τ":"T","Υ":"Y","Φ":"F","Χ":"X","Ψ":"PS","Ω":"W","Ϊ":"I","Ϋ":"Y","ά":"a","έ":"e","ή":"h","ί":"i","ΰ":"y","α":"a","β":"b","γ":"g","δ":"d","ε":"e","ζ":"z","η":"h","θ":"8","ι":"i","κ":"k","λ":"l","μ":"m","ν":"n","ξ":"3","ο":"o","π":"p","ρ":"r","ς":"s","σ":"s","τ":"t","υ":"y","φ":"f","χ":"x","ψ":"ps","ω":"w","ϊ":"i","ϋ":"y","ό":"o","ύ":"y","ώ":"w","Ё":"Yo","Ђ":"DJ","Є":"Ye","І":"I","Ї":"Yi","Ј":"J","Љ":"LJ","Њ":"NJ","Ћ":"C","Џ":"DZ","А":"A","Б":"B","В":"V","Г":"G","Д":"D","Е":"E","Ж":"Zh","З":"Z","И":"I","Й":"J","К":"K","Л":"L","М":"M","Н":"N","О":"O","П":"P","Р":"R","С":"S","Т":"T","У":"U","Ф":"F","Х":"H","Ц":"C","Ч":"Ch","Ш":"Sh","Щ":"Sh","Ъ":"U","Ы":"Y","Ь":"","Э":"E","Ю":"Yu","Я":"Ya","а":"a","б":"b","в":"v","г":"g","д":"d","е":"e","ж":"zh","з":"z","и":"i","й":"j","к":"k","л":"l","м":"m","н":"n","о":"o","п":"p","р":"r","с":"s","т":"t","у":"u","ф":"f","х":"h","ц":"c","ч":"ch","ш":"sh","щ":"sh","ъ":"u","ы":"y","ь":"","э":"e","ю":"yu","я":"ya","ё":"yo","ђ":"dj","є":"ye","і":"i","ї":"yi","ј":"j","љ":"lj","њ":"nj","ћ":"c","џ":"dz","Ґ":"G","ґ":"g","฿":"baht","ა":"a","ბ":"b","გ":"g","დ":"d","ე":"e","ვ":"v","ზ":"z","თ":"t","ი":"i","კ":"k","ლ":"l","მ":"m","ნ":"n","ო":"o","პ":"p","ჟ":"zh","რ":"r","ს":"s","ტ":"t","უ":"u","ფ":"f","ქ":"k","ღ":"gh","ყ":"q","შ":"sh","ჩ":"ch","ც":"ts","ძ":"dz","წ":"ts","ჭ":"ch","ხ":"kh","ჯ":"j","ჰ":"h","ẞ":"SS","Ạ":"A","ạ":"a","Ả":"A","ả":"a","Ấ":"A","ấ":"a","Ầ":"A","ầ":"a","Ẩ":"A","ẩ":"a","Ẫ":"A","ẫ":"a","Ậ":"A","ậ":"a","Ắ":"A","ắ":"a","Ằ":"A","ằ":"a","Ẳ":"A","ẳ":"a","Ẵ":"A","ẵ":"a","Ặ":"A","ặ":"a","Ẹ":"E","ẹ":"e","Ẻ":"E","ẻ":"e","Ẽ":"E","ẽ":"e","Ế":"E","ế":"e","Ề":"E","ề":"e","Ể":"E","ể":"e","Ễ":"E","ễ":"e","Ệ":"E","ệ":"e","Ỉ":"I","ỉ":"i","Ị":"I","ị":"i","Ọ":"O","ọ":"o","Ỏ":"O","ỏ":"o","Ố":"O","ố":"o","Ồ":"O","ồ":"o","Ổ":"O","ổ":"o","Ỗ":"O","ỗ":"o","Ộ":"O","ộ":"o","Ớ":"O","ớ":"o","Ờ":"O","ờ":"o","Ở":"O","ở":"o","Ỡ":"O","ỡ":"o","Ợ":"O","ợ":"o","Ụ":"U","ụ":"u","Ủ":"U","ủ":"u","Ứ":"U","ứ":"u","Ừ":"U","ừ":"u","Ử":"U","ử":"u","Ữ":"U","ữ":"u","Ự":"U","ự":"u","Ỳ":"Y","ỳ":"y","Ỵ":"Y","ỵ":"y","Ỷ":"Y","ỷ":"y","Ỹ":"Y","ỹ":"y","‘":"\'","’":"\'","“":"\\\"","”":"\\\"","†":"+","•":"*","…":"...","₠":"ecu","₢":"cruzeiro","₣":"french franc","₤":"lira","₥":"mill","₦":"naira","₧":"peseta","₨":"rupee","₩":"won","₪":"new shequel","₫":"dong","€":"euro","₭":"kip","₮":"tugrik","₯":"drachma","₰":"penny","₱":"peso","₲":"guarani","₳":"austral","₴":"hryvnia","₵":"cedi","₹":"indian rupee","₽":"russian ruble","₿":"bitcoin","℠":"sm","™":"tm","∂":"d","∆":"delta","∑":"sum","∞":"infinity","♥":"love","元":"yuan","円":"yen","﷼":"rial"}');
      /* eslint-enable */

      function replace (string, options) {
        if (typeof string !== 'string') {
          throw new Error('slugify: string argument expected')
        }

        options = (typeof options === 'string')
          ? {replacement: options}
          : options || {};

        var slug = string.split('')
          .reduce(function (result, ch) {
            return result + (charMap[ch] || ch)
              // allowed
              .replace(options.remove || /[^\w\s$*_+~.()'"!\-:@]/g, '')
          }, '')
          // trim leading/trailing spaces
          .trim()
          // convert spaces
          .replace(/[-\s]+/g, options.replacement || '-');

        return options.lower ? slug.toLowerCase() : slug
      }

      replace.extend = function (customMap) {
        for (var key in customMap) {
          charMap[key] = customMap[key];
        }
      };

      return replace
    }));
    });

    function _extends() {
      _extends = Object.assign || function (target) {
        for (var i = 1; i < arguments.length; i++) {
          var source = arguments[i];

          for (var key in source) {
            if (Object.prototype.hasOwnProperty.call(source, key)) {
              target[key] = source[key];
            }
          }
        }

        return target;
      };

      return _extends.apply(this, arguments);
    }

    function _objectWithoutPropertiesLoose(source, excluded) {
      if (source == null) return {};
      var target = {};
      var sourceKeys = Object.keys(source);
      var key, i;

      for (i = 0; i < sourceKeys.length; i++) {
        key = sourceKeys[i];
        if (excluded.indexOf(key) >= 0) continue;
        target[key] = source[key];
      }

      return target;
    }

    /*
    object-assign
    (c) Sindre Sorhus
    @license MIT
    */
    /* eslint-disable no-unused-vars */
    var getOwnPropertySymbols = Object.getOwnPropertySymbols;
    var hasOwnProperty$1 = Object.prototype.hasOwnProperty;
    var propIsEnumerable = Object.prototype.propertyIsEnumerable;

    function toObject(val) {
    	if (val === null || val === undefined) {
    		throw new TypeError('Object.assign cannot be called with null or undefined');
    	}

    	return Object(val);
    }

    function shouldUseNative() {
    	try {
    		if (!Object.assign) {
    			return false;
    		}

    		// Detect buggy property enumeration order in older V8 versions.

    		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
    		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
    		test1[5] = 'de';
    		if (Object.getOwnPropertyNames(test1)[0] === '5') {
    			return false;
    		}

    		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
    		var test2 = {};
    		for (var i = 0; i < 10; i++) {
    			test2['_' + String.fromCharCode(i)] = i;
    		}
    		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
    			return test2[n];
    		});
    		if (order2.join('') !== '0123456789') {
    			return false;
    		}

    		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
    		var test3 = {};
    		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
    			test3[letter] = letter;
    		});
    		if (Object.keys(Object.assign({}, test3)).join('') !==
    				'abcdefghijklmnopqrst') {
    			return false;
    		}

    		return true;
    	} catch (err) {
    		// We don't expect any of the above to throw, but better to be safe.
    		return false;
    	}
    }

    var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
    	var from;
    	var to = toObject(target);
    	var symbols;

    	for (var s = 1; s < arguments.length; s++) {
    		from = Object(arguments[s]);

    		for (var key in from) {
    			if (hasOwnProperty$1.call(from, key)) {
    				to[key] = from[key];
    			}
    		}

    		if (getOwnPropertySymbols) {
    			symbols = getOwnPropertySymbols(from);
    			for (var i = 0; i < symbols.length; i++) {
    				if (propIsEnumerable.call(from, symbols[i])) {
    					to[symbols[i]] = from[symbols[i]];
    				}
    			}
    		}
    	}

    	return to;
    };

    /**
     * Copyright (c) 2013-present, Facebook, Inc.
     *
     * This source code is licensed under the MIT license found in the
     * LICENSE file in the root directory of this source tree.
     */

    var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

    var ReactPropTypesSecret_1 = ReactPropTypesSecret;

    var printWarning = function() {};

    {
      var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
      var loggedTypeFailures = {};

      printWarning = function(text) {
        var message = 'Warning: ' + text;
        if (typeof console !== 'undefined') {
          console.error(message);
        }
        try {
          // --- Welcome to debugging React ---
          // This error was thrown as a convenience so that you can use this stack
          // to find the callsite that caused this warning to fire.
          throw new Error(message);
        } catch (x) {}
      };
    }

    /**
     * Assert that the values match with the type specs.
     * Error messages are memorized and will only be shown once.
     *
     * @param {object} typeSpecs Map of name to a ReactPropType
     * @param {object} values Runtime values that need to be type-checked
     * @param {string} location e.g. "prop", "context", "child context"
     * @param {string} componentName Name of the component for error messages.
     * @param {?Function} getStack Returns the component stack.
     * @private
     */
    function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
      {
        for (var typeSpecName in typeSpecs) {
          if (typeSpecs.hasOwnProperty(typeSpecName)) {
            var error;
            // Prop type validation may throw. In case they do, we don't want to
            // fail the render phase where it didn't fail before. So we log it.
            // After these have been cleaned up, we'll let them throw.
            try {
              // This is intentionally an invariant that gets caught. It's the same
              // behavior as without this statement except with a better message.
              if (typeof typeSpecs[typeSpecName] !== 'function') {
                var err = Error(
                  (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
                  'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
                );
                err.name = 'Invariant Violation';
                throw err;
              }
              error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
            } catch (ex) {
              error = ex;
            }
            if (error && !(error instanceof Error)) {
              printWarning(
                (componentName || 'React class') + ': type specification of ' +
                location + ' `' + typeSpecName + '` is invalid; the type checker ' +
                'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
                'You may have forgotten to pass an argument to the type checker ' +
                'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
                'shape all require an argument).'
              );

            }
            if (error instanceof Error && !(error.message in loggedTypeFailures)) {
              // Only monitor this failure once because there tends to be a lot of the
              // same error.
              loggedTypeFailures[error.message] = true;

              var stack = getStack ? getStack() : '';

              printWarning(
                'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
              );
            }
          }
        }
      }
    }

    var checkPropTypes_1 = checkPropTypes;

    var printWarning$1 = function() {};

    {
      printWarning$1 = function(text) {
        var message = 'Warning: ' + text;
        if (typeof console !== 'undefined') {
          console.error(message);
        }
        try {
          // --- Welcome to debugging React ---
          // This error was thrown as a convenience so that you can use this stack
          // to find the callsite that caused this warning to fire.
          throw new Error(message);
        } catch (x) {}
      };
    }

    function emptyFunctionThatReturnsNull() {
      return null;
    }

    var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
      /* global Symbol */
      var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
      var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

      /**
       * Returns the iterator method function contained on the iterable object.
       *
       * Be sure to invoke the function with the iterable as context:
       *
       *     var iteratorFn = getIteratorFn(myIterable);
       *     if (iteratorFn) {
       *       var iterator = iteratorFn.call(myIterable);
       *       ...
       *     }
       *
       * @param {?object} maybeIterable
       * @return {?function}
       */
      function getIteratorFn(maybeIterable) {
        var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
        if (typeof iteratorFn === 'function') {
          return iteratorFn;
        }
      }

      /**
       * Collection of methods that allow declaration and validation of props that are
       * supplied to React components. Example usage:
       *
       *   var Props = require('ReactPropTypes');
       *   var MyArticle = React.createClass({
       *     propTypes: {
       *       // An optional string prop named "description".
       *       description: Props.string,
       *
       *       // A required enum prop named "category".
       *       category: Props.oneOf(['News','Photos']).isRequired,
       *
       *       // A prop named "dialog" that requires an instance of Dialog.
       *       dialog: Props.instanceOf(Dialog).isRequired
       *     },
       *     render: function() { ... }
       *   });
       *
       * A more formal specification of how these methods are used:
       *
       *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
       *   decl := ReactPropTypes.{type}(.isRequired)?
       *
       * Each and every declaration produces a function with the same signature. This
       * allows the creation of custom validation functions. For example:
       *
       *  var MyLink = React.createClass({
       *    propTypes: {
       *      // An optional string or URI prop named "href".
       *      href: function(props, propName, componentName) {
       *        var propValue = props[propName];
       *        if (propValue != null && typeof propValue !== 'string' &&
       *            !(propValue instanceof URI)) {
       *          return new Error(
       *            'Expected a string or an URI for ' + propName + ' in ' +
       *            componentName
       *          );
       *        }
       *      }
       *    },
       *    render: function() {...}
       *  });
       *
       * @internal
       */

      var ANONYMOUS = '<<anonymous>>';

      // Important!
      // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
      var ReactPropTypes = {
        array: createPrimitiveTypeChecker('array'),
        bool: createPrimitiveTypeChecker('boolean'),
        func: createPrimitiveTypeChecker('function'),
        number: createPrimitiveTypeChecker('number'),
        object: createPrimitiveTypeChecker('object'),
        string: createPrimitiveTypeChecker('string'),
        symbol: createPrimitiveTypeChecker('symbol'),

        any: createAnyTypeChecker(),
        arrayOf: createArrayOfTypeChecker,
        element: createElementTypeChecker(),
        instanceOf: createInstanceTypeChecker,
        node: createNodeChecker(),
        objectOf: createObjectOfTypeChecker,
        oneOf: createEnumTypeChecker,
        oneOfType: createUnionTypeChecker,
        shape: createShapeTypeChecker,
        exact: createStrictShapeTypeChecker,
      };

      /**
       * inlined Object.is polyfill to avoid requiring consumers ship their own
       * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
       */
      /*eslint-disable no-self-compare*/
      function is(x, y) {
        // SameValue algorithm
        if (x === y) {
          // Steps 1-5, 7-10
          // Steps 6.b-6.e: +0 != -0
          return x !== 0 || 1 / x === 1 / y;
        } else {
          // Step 6.a: NaN == NaN
          return x !== x && y !== y;
        }
      }
      /*eslint-enable no-self-compare*/

      /**
       * We use an Error-like object for backward compatibility as people may call
       * PropTypes directly and inspect their output. However, we don't use real
       * Errors anymore. We don't inspect their stack anyway, and creating them
       * is prohibitively expensive if they are created too often, such as what
       * happens in oneOfType() for any type before the one that matched.
       */
      function PropTypeError(message) {
        this.message = message;
        this.stack = '';
      }
      // Make `instanceof Error` still work for returned errors.
      PropTypeError.prototype = Error.prototype;

      function createChainableTypeChecker(validate) {
        {
          var manualPropTypeCallCache = {};
          var manualPropTypeWarningCount = 0;
        }
        function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
          componentName = componentName || ANONYMOUS;
          propFullName = propFullName || propName;

          if (secret !== ReactPropTypesSecret_1) {
            if (throwOnDirectAccess) {
              // New behavior only for users of `prop-types` package
              var err = new Error(
                'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
                'Use `PropTypes.checkPropTypes()` to call them. ' +
                'Read more at http://fb.me/use-check-prop-types'
              );
              err.name = 'Invariant Violation';
              throw err;
            } else if (typeof console !== 'undefined') {
              // Old behavior for people using React.PropTypes
              var cacheKey = componentName + ':' + propName;
              if (
                !manualPropTypeCallCache[cacheKey] &&
                // Avoid spamming the console because they are often not actionable except for lib authors
                manualPropTypeWarningCount < 3
              ) {
                printWarning$1(
                  'You are manually calling a React.PropTypes validation ' +
                  'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
                  'and will throw in the standalone `prop-types` package. ' +
                  'You may be seeing this warning due to a third-party PropTypes ' +
                  'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
                );
                manualPropTypeCallCache[cacheKey] = true;
                manualPropTypeWarningCount++;
              }
            }
          }
          if (props[propName] == null) {
            if (isRequired) {
              if (props[propName] === null) {
                return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
              }
              return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
            }
            return null;
          } else {
            return validate(props, propName, componentName, location, propFullName);
          }
        }

        var chainedCheckType = checkType.bind(null, false);
        chainedCheckType.isRequired = checkType.bind(null, true);

        return chainedCheckType;
      }

      function createPrimitiveTypeChecker(expectedType) {
        function validate(props, propName, componentName, location, propFullName, secret) {
          var propValue = props[propName];
          var propType = getPropType(propValue);
          if (propType !== expectedType) {
            // `propValue` being instance of, say, date/regexp, pass the 'object'
            // check, but we can offer a more precise error message here rather than
            // 'of type `object`'.
            var preciseType = getPreciseType(propValue);

            return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
          }
          return null;
        }
        return createChainableTypeChecker(validate);
      }

      function createAnyTypeChecker() {
        return createChainableTypeChecker(emptyFunctionThatReturnsNull);
      }

      function createArrayOfTypeChecker(typeChecker) {
        function validate(props, propName, componentName, location, propFullName) {
          if (typeof typeChecker !== 'function') {
            return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
          }
          var propValue = props[propName];
          if (!Array.isArray(propValue)) {
            var propType = getPropType(propValue);
            return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
          }
          for (var i = 0; i < propValue.length; i++) {
            var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
            if (error instanceof Error) {
              return error;
            }
          }
          return null;
        }
        return createChainableTypeChecker(validate);
      }

      function createElementTypeChecker() {
        function validate(props, propName, componentName, location, propFullName) {
          var propValue = props[propName];
          if (!isValidElement(propValue)) {
            var propType = getPropType(propValue);
            return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
          }
          return null;
        }
        return createChainableTypeChecker(validate);
      }

      function createInstanceTypeChecker(expectedClass) {
        function validate(props, propName, componentName, location, propFullName) {
          if (!(props[propName] instanceof expectedClass)) {
            var expectedClassName = expectedClass.name || ANONYMOUS;
            var actualClassName = getClassName(props[propName]);
            return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
          }
          return null;
        }
        return createChainableTypeChecker(validate);
      }

      function createEnumTypeChecker(expectedValues) {
        if (!Array.isArray(expectedValues)) {
          printWarning$1('Invalid argument supplied to oneOf, expected an instance of array.');
          return emptyFunctionThatReturnsNull;
        }

        function validate(props, propName, componentName, location, propFullName) {
          var propValue = props[propName];
          for (var i = 0; i < expectedValues.length; i++) {
            if (is(propValue, expectedValues[i])) {
              return null;
            }
          }

          var valuesString = JSON.stringify(expectedValues);
          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + propValue + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
        }
        return createChainableTypeChecker(validate);
      }

      function createObjectOfTypeChecker(typeChecker) {
        function validate(props, propName, componentName, location, propFullName) {
          if (typeof typeChecker !== 'function') {
            return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
          }
          var propValue = props[propName];
          var propType = getPropType(propValue);
          if (propType !== 'object') {
            return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
          }
          for (var key in propValue) {
            if (propValue.hasOwnProperty(key)) {
              var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
              if (error instanceof Error) {
                return error;
              }
            }
          }
          return null;
        }
        return createChainableTypeChecker(validate);
      }

      function createUnionTypeChecker(arrayOfTypeCheckers) {
        if (!Array.isArray(arrayOfTypeCheckers)) {
          printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.');
          return emptyFunctionThatReturnsNull;
        }

        for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
          var checker = arrayOfTypeCheckers[i];
          if (typeof checker !== 'function') {
            printWarning$1(
              'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
              'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
            );
            return emptyFunctionThatReturnsNull;
          }
        }

        function validate(props, propName, componentName, location, propFullName) {
          for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
            var checker = arrayOfTypeCheckers[i];
            if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
              return null;
            }
          }

          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
        }
        return createChainableTypeChecker(validate);
      }

      function createNodeChecker() {
        function validate(props, propName, componentName, location, propFullName) {
          if (!isNode(props[propName])) {
            return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
          }
          return null;
        }
        return createChainableTypeChecker(validate);
      }

      function createShapeTypeChecker(shapeTypes) {
        function validate(props, propName, componentName, location, propFullName) {
          var propValue = props[propName];
          var propType = getPropType(propValue);
          if (propType !== 'object') {
            return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
          }
          for (var key in shapeTypes) {
            var checker = shapeTypes[key];
            if (!checker) {
              continue;
            }
            var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
            if (error) {
              return error;
            }
          }
          return null;
        }
        return createChainableTypeChecker(validate);
      }

      function createStrictShapeTypeChecker(shapeTypes) {
        function validate(props, propName, componentName, location, propFullName) {
          var propValue = props[propName];
          var propType = getPropType(propValue);
          if (propType !== 'object') {
            return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
          }
          // We need to check all keys in case some are required but missing from
          // props.
          var allKeys = objectAssign({}, props[propName], shapeTypes);
          for (var key in allKeys) {
            var checker = shapeTypes[key];
            if (!checker) {
              return new PropTypeError(
                'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
                '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
                '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
              );
            }
            var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
            if (error) {
              return error;
            }
          }
          return null;
        }

        return createChainableTypeChecker(validate);
      }

      function isNode(propValue) {
        switch (typeof propValue) {
          case 'number':
          case 'string':
          case 'undefined':
            return true;
          case 'boolean':
            return !propValue;
          case 'object':
            if (Array.isArray(propValue)) {
              return propValue.every(isNode);
            }
            if (propValue === null || isValidElement(propValue)) {
              return true;
            }

            var iteratorFn = getIteratorFn(propValue);
            if (iteratorFn) {
              var iterator = iteratorFn.call(propValue);
              var step;
              if (iteratorFn !== propValue.entries) {
                while (!(step = iterator.next()).done) {
                  if (!isNode(step.value)) {
                    return false;
                  }
                }
              } else {
                // Iterator will provide entry [k,v] tuples rather than values.
                while (!(step = iterator.next()).done) {
                  var entry = step.value;
                  if (entry) {
                    if (!isNode(entry[1])) {
                      return false;
                    }
                  }
                }
              }
            } else {
              return false;
            }

            return true;
          default:
            return false;
        }
      }

      function isSymbol(propType, propValue) {
        // Native Symbol.
        if (propType === 'symbol') {
          return true;
        }

        // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
        if (propValue['@@toStringTag'] === 'Symbol') {
          return true;
        }

        // Fallback for non-spec compliant Symbols which are polyfilled.
        if (typeof Symbol === 'function' && propValue instanceof Symbol) {
          return true;
        }

        return false;
      }

      // Equivalent of `typeof` but with special handling for array and regexp.
      function getPropType(propValue) {
        var propType = typeof propValue;
        if (Array.isArray(propValue)) {
          return 'array';
        }
        if (propValue instanceof RegExp) {
          // Old webkits (at least until Android 4.0) return 'function' rather than
          // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
          // passes PropTypes.object.
          return 'object';
        }
        if (isSymbol(propType, propValue)) {
          return 'symbol';
        }
        return propType;
      }

      // This handles more types than `getPropType`. Only used for error messages.
      // See `createPrimitiveTypeChecker`.
      function getPreciseType(propValue) {
        if (typeof propValue === 'undefined' || propValue === null) {
          return '' + propValue;
        }
        var propType = getPropType(propValue);
        if (propType === 'object') {
          if (propValue instanceof Date) {
            return 'date';
          } else if (propValue instanceof RegExp) {
            return 'regexp';
          }
        }
        return propType;
      }

      // Returns a string that is postfixed to a warning about an invalid type.
      // For example, "undefined" or "of type array"
      function getPostfixForTypeWarning(value) {
        var type = getPreciseType(value);
        switch (type) {
          case 'array':
          case 'object':
            return 'an ' + type;
          case 'boolean':
          case 'date':
          case 'regexp':
            return 'a ' + type;
          default:
            return type;
        }
      }

      // Returns class name of the object, if any.
      function getClassName(propValue) {
        if (!propValue.constructor || !propValue.constructor.name) {
          return ANONYMOUS;
        }
        return propValue.constructor.name;
      }

      ReactPropTypes.checkPropTypes = checkPropTypes_1;
      ReactPropTypes.PropTypes = ReactPropTypes;

      return ReactPropTypes;
    };

    var propTypes = createCommonjsModule(function (module) {
    /**
     * Copyright (c) 2013-present, Facebook, Inc.
     *
     * This source code is licensed under the MIT license found in the
     * LICENSE file in the root directory of this source tree.
     */

    {
      var REACT_ELEMENT_TYPE = (typeof Symbol === 'function' &&
        Symbol.for &&
        Symbol.for('react.element')) ||
        0xeac7;

      var isValidElement = function(object) {
        return typeof object === 'object' &&
          object !== null &&
          object.$$typeof === REACT_ELEMENT_TYPE;
      };

      // By explicitly using `prop-types` you are opting into new development behavior.
      // http://fb.me/prop-types-in-prod
      var throwOnDirectAccess = true;
      module.exports = factoryWithTypeCheckers(isValidElement, throwOnDirectAccess);
    }
    });

    var classnames = createCommonjsModule(function (module) {
    /*!
      Copyright (c) 2017 Jed Watson.
      Licensed under the MIT License (MIT), see
      http://jedwatson.github.io/classnames
    */
    /* global define */

    (function () {

    	var hasOwn = {}.hasOwnProperty;

    	function classNames () {
    		var classes = [];

    		for (var i = 0; i < arguments.length; i++) {
    			var arg = arguments[i];
    			if (!arg) continue;

    			var argType = typeof arg;

    			if (argType === 'string' || argType === 'number') {
    				classes.push(arg);
    			} else if (Array.isArray(arg) && arg.length) {
    				var inner = classNames.apply(null, arg);
    				if (inner) {
    					classes.push(inner);
    				}
    			} else if (argType === 'object') {
    				for (var key in arg) {
    					if (hasOwn.call(arg, key) && arg[key]) {
    						classes.push(key);
    					}
    				}
    			}
    		}

    		return classes.join(' ');
    	}

    	if (module.exports) {
    		classNames.default = classNames;
    		module.exports = classNames;
    	} else {
    		window.classNames = classNames;
    	}
    }());
    });

    /**
     * Lodash (Custom Build) <https://lodash.com/>
     * Build: `lodash modularize exports="npm" -o ./`
     * Copyright JS Foundation and other contributors <https://js.foundation/>
     * Released under MIT license <https://lodash.com/license>
     * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
     * Copyright Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
     */

    /** `Object#toString` result references. */
    var asyncTag = '[object AsyncFunction]',
        funcTag = '[object Function]',
        genTag = '[object GeneratorFunction]',
        nullTag = '[object Null]',
        proxyTag = '[object Proxy]',
        undefinedTag = '[object Undefined]';

    /** Detect free variable `global` from Node.js. */
    var freeGlobal = typeof commonjsGlobal == 'object' && commonjsGlobal && commonjsGlobal.Object === Object && commonjsGlobal;

    /** Detect free variable `self`. */
    var freeSelf = typeof self == 'object' && self && self.Object === Object && self;

    /** Used as a reference to the global object. */
    var root = freeGlobal || freeSelf || Function('return this')();

    /** Used for built-in method references. */
    var objectProto = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$2 = objectProto.hasOwnProperty;

    /**
     * Used to resolve the
     * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
     * of values.
     */
    var nativeObjectToString = objectProto.toString;

    /** Built-in value references. */
    var Symbol$1 = root.Symbol,
        symToStringTag = Symbol$1 ? Symbol$1.toStringTag : undefined;

    /**
     * The base implementation of `getTag` without fallbacks for buggy environments.
     *
     * @private
     * @param {*} value The value to query.
     * @returns {string} Returns the `toStringTag`.
     */
    function baseGetTag(value) {
      if (value == null) {
        return value === undefined ? undefinedTag : nullTag;
      }
      return (symToStringTag && symToStringTag in Object(value))
        ? getRawTag(value)
        : objectToString(value);
    }

    /**
     * A specialized version of `baseGetTag` which ignores `Symbol.toStringTag` values.
     *
     * @private
     * @param {*} value The value to query.
     * @returns {string} Returns the raw `toStringTag`.
     */
    function getRawTag(value) {
      var isOwn = hasOwnProperty$2.call(value, symToStringTag),
          tag = value[symToStringTag];

      try {
        value[symToStringTag] = undefined;
        var unmasked = true;
      } catch (e) {}

      var result = nativeObjectToString.call(value);
      if (unmasked) {
        if (isOwn) {
          value[symToStringTag] = tag;
        } else {
          delete value[symToStringTag];
        }
      }
      return result;
    }

    /**
     * Converts `value` to a string using `Object.prototype.toString`.
     *
     * @private
     * @param {*} value The value to convert.
     * @returns {string} Returns the converted string.
     */
    function objectToString(value) {
      return nativeObjectToString.call(value);
    }

    /**
     * Checks if `value` is classified as a `Function` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a function, else `false`.
     * @example
     *
     * _.isFunction(_);
     * // => true
     *
     * _.isFunction(/abc/);
     * // => false
     */
    function isFunction(value) {
      if (!isObject(value)) {
        return false;
      }
      // The use of `Object#toString` avoids issues with the `typeof` operator
      // in Safari 9 which returns 'object' for typed arrays and other constructors.
      var tag = baseGetTag(value);
      return tag == funcTag || tag == genTag || tag == asyncTag || tag == proxyTag;
    }

    /**
     * Checks if `value` is the
     * [language type](http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-types)
     * of `Object`. (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an object, else `false`.
     * @example
     *
     * _.isObject({});
     * // => true
     *
     * _.isObject([1, 2, 3]);
     * // => true
     *
     * _.isObject(_.noop);
     * // => true
     *
     * _.isObject(null);
     * // => false
     */
    function isObject(value) {
      var type = typeof value;
      return value != null && (type == 'object' || type == 'function');
    }

    var lodash_isfunction = isFunction;

    function getScrollbarWidth() {
      var scrollDiv = document.createElement('div'); // .modal-scrollbar-measure styles // https://github.com/twbs/bootstrap/blob/v4.0.0-alpha.4/scss/_modal.scss#L106-L113

      scrollDiv.style.position = 'absolute';
      scrollDiv.style.top = '-9999px';
      scrollDiv.style.width = '50px';
      scrollDiv.style.height = '50px';
      scrollDiv.style.overflow = 'scroll';
      document.body.appendChild(scrollDiv);
      var scrollbarWidth = scrollDiv.offsetWidth - scrollDiv.clientWidth;
      document.body.removeChild(scrollDiv);
      return scrollbarWidth;
    }
    function setScrollbarWidth(padding) {
      document.body.style.paddingRight = padding > 0 ? padding + "px" : null;
    }
    function isBodyOverflowing() {
      return document.body.clientWidth < window.innerWidth;
    }
    function getOriginalBodyPadding() {
      var style = window.getComputedStyle(document.body, null);
      return parseInt(style && style.getPropertyValue('padding-right') || 0, 10);
    }
    function conditionallyUpdateScrollbar() {
      var scrollbarWidth = getScrollbarWidth(); // https://github.com/twbs/bootstrap/blob/v4.0.0-alpha.6/js/src/modal.js#L433

      var fixedContent = document.querySelectorAll('.fixed-top, .fixed-bottom, .is-fixed, .sticky-top')[0];
      var bodyPadding = fixedContent ? parseInt(fixedContent.style.paddingRight || 0, 10) : 0;

      if (isBodyOverflowing()) {
        setScrollbarWidth(bodyPadding + scrollbarWidth);
      }
    }
    var globalCssModule;
    function mapToCssModules(className, cssModule) {
      if (className === void 0) {
        className = '';
      }

      if (cssModule === void 0) {
        cssModule = globalCssModule;
      }

      if (!cssModule) return className;
      return className.split(' ').map(function (c) {
        return cssModule[c] || c;
      }).join(' ');
    }
    /**
     * Returns a new object with the key/value pairs from `obj` that are not in the array `omitKeys`.
     */

    function omit(obj, omitKeys) {
      var result = {};
      Object.keys(obj).forEach(function (key) {
        if (omitKeys.indexOf(key) === -1) {
          result[key] = obj[key];
        }
      });
      return result;
    }
    /**
     * Returns a filtered copy of an object with only the specified keys.
     */

    function pick(obj, keys) {
      var pickKeys = Array.isArray(keys) ? keys : [keys];
      var length = pickKeys.length;
      var key;
      var result = {};

      while (length > 0) {
        length -= 1;
        key = pickKeys[length];
        result[key] = obj[key];
      }

      return result;
    }
    var warned = {};
    function warnOnce(message) {
      if (!warned[message]) {
        /* istanbul ignore else */
        if (typeof console !== 'undefined') {
          console.error(message); // eslint-disable-line no-console
        }

        warned[message] = true;
      }
    }

    var Element = typeof window === 'object' && window.Element || function () {};

    function DOMElement(props, propName, componentName) {
      if (!(props[propName] instanceof Element)) {
        return new Error('Invalid prop `' + propName + '` supplied to `' + componentName + '`. Expected prop to be an instance of Element. Validation failed.');
      }
    }
    var targetPropType = propTypes.oneOfType([propTypes.string, propTypes.func, DOMElement, propTypes.shape({
      current: propTypes.any
    })]);
    var tagPropType = propTypes.oneOfType([propTypes.func, propTypes.string, propTypes.shape({
      $$typeof: propTypes.symbol,
      render: propTypes.func
    }), propTypes.arrayOf(propTypes.oneOfType([propTypes.func, propTypes.string, propTypes.shape({
      $$typeof: propTypes.symbol,
      render: propTypes.func
    })]))]);
    /* eslint key-spacing: ["error", { afterColon: true, align: "value" }] */
    // These are all setup to match what is in the bootstrap _variables.scss
    // https://github.com/twbs/bootstrap/blob/v4-dev/scss/_variables.scss

    var TransitionTimeouts = {
      Fade: 150,
      // $transition-fade
      Collapse: 350,
      // $transition-collapse
      Modal: 300,
      // $modal-transition
      Carousel: 600 // $carousel-transition

    }; // Duplicated Transition.propType keys to ensure that Reactstrap builds
    // for distribution properly exclude these keys for nested child HTML attributes
    // since `react-transition-group` removes propTypes in production builds.

    var TransitionPropTypeKeys = ['in', 'mountOnEnter', 'unmountOnExit', 'appear', 'enter', 'exit', 'timeout', 'onEnter', 'onEntering', 'onEntered', 'onExit', 'onExiting', 'onExited'];
    var TransitionStatuses = {
      ENTERING: 'entering',
      ENTERED: 'entered',
      EXITING: 'exiting',
      EXITED: 'exited'
    };
    var keyCodes = {
      esc: 27,
      space: 32,
      enter: 13,
      tab: 9,
      up: 38,
      down: 40,
      home: 36,
      end: 35,
      n: 78,
      p: 80
    };
    var PopperPlacements = ['auto-start', 'auto', 'auto-end', 'top-start', 'top', 'top-end', 'right-start', 'right', 'right-end', 'bottom-end', 'bottom', 'bottom-start', 'left-end', 'left', 'left-start'];
    var canUseDOM = !!(typeof window !== 'undefined' && window.document && window.document.createElement);
    function isReactRefObj(target) {
      if (target && typeof target === 'object') {
        return 'current' in target;
      }

      return false;
    }
    function findDOMElements(target) {
      if (isReactRefObj(target)) {
        return target.current;
      }

      if (lodash_isfunction(target)) {
        return target();
      }

      if (typeof target === 'string' && canUseDOM) {
        var selection = document.querySelectorAll(target);

        if (!selection.length) {
          selection = document.querySelectorAll("#" + target);
        }

        if (!selection.length) {
          throw new Error("The target '" + target + "' could not be identified in the dom, tip: check spelling");
        }

        return selection;
      }

      return target;
    }
    function isArrayOrNodeList(els) {
      if (els === null) {
        return false;
      }

      return Array.isArray(els) || canUseDOM && typeof els.length === 'number';
    }
    function getTarget(target) {
      var els = findDOMElements(target);

      if (isArrayOrNodeList(els)) {
        return els[0];
      }

      return els;
    }
    var focusableElements = ['a[href]', 'area[href]', 'input:not([disabled]):not([type=hidden])', 'select:not([disabled])', 'textarea:not([disabled])', 'button:not([disabled])', 'object', 'embed', '[tabindex]:not(.modal)', 'audio[controls]', 'video[controls]', '[contenteditable]:not([contenteditable="false"])'];

    var propTypes$1 = {
      tag: tagPropType,
      fluid: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$2 = {
      tag: tagPropType,
      noGutters: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object,
      form: propTypes.bool
    };

    /**
     * lodash 3.0.2 (Custom Build) <https://lodash.com/>
     * Build: `lodash modern modularize exports="npm" -o ./`
     * Copyright 2012-2015 The Dojo Foundation <http://dojofoundation.org/>
     * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
     * Copyright 2009-2015 Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
     * Available under MIT license <https://lodash.com/license>
     */

    var stringOrNumberProp = propTypes.oneOfType([propTypes.number, propTypes.string]);
    var columnProps = propTypes.oneOfType([propTypes.bool, propTypes.number, propTypes.string, propTypes.shape({
      size: propTypes.oneOfType([propTypes.bool, propTypes.number, propTypes.string]),
      order: stringOrNumberProp,
      offset: stringOrNumberProp
    })]);
    var propTypes$3 = {
      tag: tagPropType,
      xs: columnProps,
      sm: columnProps,
      md: columnProps,
      lg: columnProps,
      xl: columnProps,
      className: propTypes.string,
      cssModule: propTypes.object,
      widths: propTypes.array
    };

    var propTypes$4 = {
      light: propTypes.bool,
      dark: propTypes.bool,
      full: propTypes.bool,
      fixed: propTypes.string,
      sticky: propTypes.string,
      color: propTypes.string,
      role: propTypes.string,
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object,
      expand: propTypes.oneOfType([propTypes.bool, propTypes.string])
    };

    var propTypes$5 = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$6 = {
      tag: tagPropType,
      type: propTypes.string,
      className: propTypes.string,
      cssModule: propTypes.object,
      children: propTypes.node
    };

    var propTypes$7 = {
      tabs: propTypes.bool,
      pills: propTypes.bool,
      vertical: propTypes.oneOfType([propTypes.bool, propTypes.string]),
      horizontal: propTypes.string,
      justified: propTypes.bool,
      fill: propTypes.bool,
      navbar: propTypes.bool,
      card: propTypes.bool,
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$8 = {
      tag: tagPropType,
      active: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    function _assertThisInitialized(self) {
      if (self === void 0) {
        throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
      }

      return self;
    }

    function _inheritsLoose(subClass, superClass) {
      subClass.prototype = Object.create(superClass.prototype);
      subClass.prototype.constructor = subClass;
      subClass.__proto__ = superClass;
    }

    var propTypes$9 = {
      tag: tagPropType,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.func, propTypes.string]),
      disabled: propTypes.bool,
      active: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object,
      onClick: propTypes.func,
      href: propTypes.any
    };
    var defaultProps = {
      tag: 'a'
    };

    var NavLink =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(NavLink, _React$Component);

      function NavLink(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.onClick = _this.onClick.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = NavLink.prototype;

      _proto.onClick = function onClick(e) {
        if (this.props.disabled) {
          e.preventDefault();
          return;
        }

        if (this.props.href === '#') {
          e.preventDefault();
        }

        if (this.props.onClick) {
          this.props.onClick(e);
        }
      };

      _proto.render = function render() {
        var _this$props = this.props,
            className = _this$props.className,
            cssModule = _this$props.cssModule,
            active = _this$props.active,
            Tag = _this$props.tag,
            innerRef = _this$props.innerRef,
            attributes = _objectWithoutPropertiesLoose(_this$props, ["className", "cssModule", "active", "tag", "innerRef"]);

        var classes = mapToCssModules(classnames(className, 'nav-link', {
          disabled: attributes.disabled,
          active: active
        }), cssModule);
        return React__default.createElement(Tag, _extends({}, attributes, {
          ref: innerRef,
          onClick: this.onClick,
          className: classes
        }));
      };

      return NavLink;
    }(React__default.Component);

    NavLink.propTypes = propTypes$9;
    NavLink.defaultProps = defaultProps;

    var propTypes$a = {
      tag: tagPropType,
      listTag: tagPropType,
      className: propTypes.string,
      listClassName: propTypes.string,
      cssModule: propTypes.object,
      children: propTypes.node,
      'aria-label': propTypes.string
    };

    var propTypes$b = {
      tag: tagPropType,
      active: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$c = {
      active: propTypes.bool,
      'aria-label': propTypes.string,
      block: propTypes.bool,
      color: propTypes.string,
      disabled: propTypes.bool,
      outline: propTypes.bool,
      tag: tagPropType,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.func, propTypes.string]),
      onClick: propTypes.func,
      size: propTypes.string,
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object,
      close: propTypes.bool
    };
    var defaultProps$1 = {
      color: 'secondary',
      tag: 'button'
    };

    var Button =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Button, _React$Component);

      function Button(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.onClick = _this.onClick.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = Button.prototype;

      _proto.onClick = function onClick(e) {
        if (this.props.disabled) {
          e.preventDefault();
          return;
        }

        if (this.props.onClick) {
          this.props.onClick(e);
        }
      };

      _proto.render = function render() {
        var _this$props = this.props,
            active = _this$props.active,
            ariaLabel = _this$props['aria-label'],
            block = _this$props.block,
            className = _this$props.className,
            close = _this$props.close,
            cssModule = _this$props.cssModule,
            color = _this$props.color,
            outline = _this$props.outline,
            size = _this$props.size,
            Tag = _this$props.tag,
            innerRef = _this$props.innerRef,
            attributes = _objectWithoutPropertiesLoose(_this$props, ["active", "aria-label", "block", "className", "close", "cssModule", "color", "outline", "size", "tag", "innerRef"]);

        if (close && typeof attributes.children === 'undefined') {
          attributes.children = React__default.createElement("span", {
            "aria-hidden": true
          }, "\xD7");
        }

        var btnOutlineColor = "btn" + (outline ? '-outline' : '') + "-" + color;
        var classes = mapToCssModules(classnames(className, {
          close: close
        }, close || 'btn', close || btnOutlineColor, size ? "btn-" + size : false, block ? 'btn-block' : false, {
          active: active,
          disabled: this.props.disabled
        }), cssModule);

        if (attributes.href && Tag === 'button') {
          Tag = 'a';
        }

        var defaultAriaLabel = close ? 'Close' : null;
        return React__default.createElement(Tag, _extends({
          type: Tag === 'button' && attributes.onClick ? 'button' : undefined
        }, attributes, {
          className: classes,
          ref: innerRef,
          onClick: this.onClick,
          "aria-label": ariaLabel || defaultAriaLabel
        }));
      };

      return Button;
    }(React__default.Component);

    Button.propTypes = propTypes$c;
    Button.defaultProps = defaultProps$1;

    function _objectWithoutPropertiesLoose$1(source, excluded) {
      if (source == null) return {};
      var target = {};
      var sourceKeys = Object.keys(source);
      var key, i;

      for (i = 0; i < sourceKeys.length; i++) {
        key = sourceKeys[i];
        if (excluded.indexOf(key) >= 0) continue;
        target[key] = source[key];
      }

      return target;
    }

    var objectWithoutPropertiesLoose = _objectWithoutPropertiesLoose$1;

    var _extends_1 = createCommonjsModule(function (module) {
    function _extends() {
      module.exports = _extends = Object.assign || function (target) {
        for (var i = 1; i < arguments.length; i++) {
          var source = arguments[i];

          for (var key in source) {
            if (Object.prototype.hasOwnProperty.call(source, key)) {
              target[key] = source[key];
            }
          }
        }

        return target;
      };

      return _extends.apply(this, arguments);
    }

    module.exports = _extends;
    });

    function _inheritsLoose$1(subClass, superClass) {
      subClass.prototype = Object.create(superClass.prototype);
      subClass.prototype.constructor = subClass;
      subClass.__proto__ = superClass;
    }

    var inheritsLoose = _inheritsLoose$1;

    function _assertThisInitialized$1(self) {
      if (self === void 0) {
        throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
      }

      return self;
    }

    var assertThisInitialized = _assertThisInitialized$1;

    function _defineProperty(obj, key, value) {
      if (key in obj) {
        Object.defineProperty(obj, key, {
          value: value,
          enumerable: true,
          configurable: true,
          writable: true
        });
      } else {
        obj[key] = value;
      }

      return obj;
    }

    var defineProperty = _defineProperty;

    /**!
     * @fileOverview Kickass library to create and place poppers near their reference elements.
     * @version 1.14.4
     * @license
     * Copyright (c) 2016 Federico Zivolo and contributors
     *
     * Permission is hereby granted, free of charge, to any person obtaining a copy
     * of this software and associated documentation files (the "Software"), to deal
     * in the Software without restriction, including without limitation the rights
     * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
     * copies of the Software, and to permit persons to whom the Software is
     * furnished to do so, subject to the following conditions:
     *
     * The above copyright notice and this permission notice shall be included in all
     * copies or substantial portions of the Software.
     *
     * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
     * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
     * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
     * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
     * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
     * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
     * SOFTWARE.
     */
    var isBrowser = typeof window !== 'undefined' && typeof document !== 'undefined';

    var longerTimeoutBrowsers = ['Edge', 'Trident', 'Firefox'];
    var timeoutDuration = 0;
    for (var i = 0; i < longerTimeoutBrowsers.length; i += 1) {
      if (isBrowser && navigator.userAgent.indexOf(longerTimeoutBrowsers[i]) >= 0) {
        timeoutDuration = 1;
        break;
      }
    }

    function microtaskDebounce(fn) {
      var called = false;
      return function () {
        if (called) {
          return;
        }
        called = true;
        window.Promise.resolve().then(function () {
          called = false;
          fn();
        });
      };
    }

    function taskDebounce(fn) {
      var scheduled = false;
      return function () {
        if (!scheduled) {
          scheduled = true;
          setTimeout(function () {
            scheduled = false;
            fn();
          }, timeoutDuration);
        }
      };
    }

    var supportsMicroTasks = isBrowser && window.Promise;

    /**
    * Create a debounced version of a method, that's asynchronously deferred
    * but called in the minimum time possible.
    *
    * @method
    * @memberof Popper.Utils
    * @argument {Function} fn
    * @returns {Function}
    */
    var debounce = supportsMicroTasks ? microtaskDebounce : taskDebounce;

    /**
     * Check if the given variable is a function
     * @method
     * @memberof Popper.Utils
     * @argument {Any} functionToCheck - variable to check
     * @returns {Boolean} answer to: is a function?
     */
    function isFunction$1(functionToCheck) {
      var getType = {};
      return functionToCheck && getType.toString.call(functionToCheck) === '[object Function]';
    }

    /**
     * Get CSS computed property of the given element
     * @method
     * @memberof Popper.Utils
     * @argument {Eement} element
     * @argument {String} property
     */
    function getStyleComputedProperty(element, property) {
      if (element.nodeType !== 1) {
        return [];
      }
      // NOTE: 1 DOM access here
      var css = getComputedStyle(element, null);
      return property ? css[property] : css;
    }

    /**
     * Returns the parentNode or the host of the element
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element
     * @returns {Element} parent
     */
    function getParentNode(element) {
      if (element.nodeName === 'HTML') {
        return element;
      }
      return element.parentNode || element.host;
    }

    /**
     * Returns the scrolling parent of the given element
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element
     * @returns {Element} scroll parent
     */
    function getScrollParent(element) {
      // Return body, `getScroll` will take care to get the correct `scrollTop` from it
      if (!element) {
        return document.body;
      }

      switch (element.nodeName) {
        case 'HTML':
        case 'BODY':
          return element.ownerDocument.body;
        case '#document':
          return element.body;
      }

      // Firefox want us to check `-x` and `-y` variations as well

      var _getStyleComputedProp = getStyleComputedProperty(element),
          overflow = _getStyleComputedProp.overflow,
          overflowX = _getStyleComputedProp.overflowX,
          overflowY = _getStyleComputedProp.overflowY;

      if (/(auto|scroll|overlay)/.test(overflow + overflowY + overflowX)) {
        return element;
      }

      return getScrollParent(getParentNode(element));
    }

    var isIE11 = isBrowser && !!(window.MSInputMethodContext && document.documentMode);
    var isIE10 = isBrowser && /MSIE 10/.test(navigator.userAgent);

    /**
     * Determines if the browser is Internet Explorer
     * @method
     * @memberof Popper.Utils
     * @param {Number} version to check
     * @returns {Boolean} isIE
     */
    function isIE(version) {
      if (version === 11) {
        return isIE11;
      }
      if (version === 10) {
        return isIE10;
      }
      return isIE11 || isIE10;
    }

    /**
     * Returns the offset parent of the given element
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element
     * @returns {Element} offset parent
     */
    function getOffsetParent(element) {
      if (!element) {
        return document.documentElement;
      }

      var noOffsetParent = isIE(10) ? document.body : null;

      // NOTE: 1 DOM access here
      var offsetParent = element.offsetParent;
      // Skip hidden elements which don't have an offsetParent
      while (offsetParent === noOffsetParent && element.nextElementSibling) {
        offsetParent = (element = element.nextElementSibling).offsetParent;
      }

      var nodeName = offsetParent && offsetParent.nodeName;

      if (!nodeName || nodeName === 'BODY' || nodeName === 'HTML') {
        return element ? element.ownerDocument.documentElement : document.documentElement;
      }

      // .offsetParent will return the closest TD or TABLE in case
      // no offsetParent is present, I hate this job...
      if (['TD', 'TABLE'].indexOf(offsetParent.nodeName) !== -1 && getStyleComputedProperty(offsetParent, 'position') === 'static') {
        return getOffsetParent(offsetParent);
      }

      return offsetParent;
    }

    function isOffsetContainer(element) {
      var nodeName = element.nodeName;

      if (nodeName === 'BODY') {
        return false;
      }
      return nodeName === 'HTML' || getOffsetParent(element.firstElementChild) === element;
    }

    /**
     * Finds the root node (document, shadowDOM root) of the given element
     * @method
     * @memberof Popper.Utils
     * @argument {Element} node
     * @returns {Element} root node
     */
    function getRoot(node) {
      if (node.parentNode !== null) {
        return getRoot(node.parentNode);
      }

      return node;
    }

    /**
     * Finds the offset parent common to the two provided nodes
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element1
     * @argument {Element} element2
     * @returns {Element} common offset parent
     */
    function findCommonOffsetParent(element1, element2) {
      // This check is needed to avoid errors in case one of the elements isn't defined for any reason
      if (!element1 || !element1.nodeType || !element2 || !element2.nodeType) {
        return document.documentElement;
      }

      // Here we make sure to give as "start" the element that comes first in the DOM
      var order = element1.compareDocumentPosition(element2) & Node.DOCUMENT_POSITION_FOLLOWING;
      var start = order ? element1 : element2;
      var end = order ? element2 : element1;

      // Get common ancestor container
      var range = document.createRange();
      range.setStart(start, 0);
      range.setEnd(end, 0);
      var commonAncestorContainer = range.commonAncestorContainer;

      // Both nodes are inside #document

      if (element1 !== commonAncestorContainer && element2 !== commonAncestorContainer || start.contains(end)) {
        if (isOffsetContainer(commonAncestorContainer)) {
          return commonAncestorContainer;
        }

        return getOffsetParent(commonAncestorContainer);
      }

      // one of the nodes is inside shadowDOM, find which one
      var element1root = getRoot(element1);
      if (element1root.host) {
        return findCommonOffsetParent(element1root.host, element2);
      } else {
        return findCommonOffsetParent(element1, getRoot(element2).host);
      }
    }

    /**
     * Gets the scroll value of the given element in the given side (top and left)
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element
     * @argument {String} side `top` or `left`
     * @returns {number} amount of scrolled pixels
     */
    function getScroll(element) {
      var side = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : 'top';

      var upperSide = side === 'top' ? 'scrollTop' : 'scrollLeft';
      var nodeName = element.nodeName;

      if (nodeName === 'BODY' || nodeName === 'HTML') {
        var html = element.ownerDocument.documentElement;
        var scrollingElement = element.ownerDocument.scrollingElement || html;
        return scrollingElement[upperSide];
      }

      return element[upperSide];
    }

    /*
     * Sum or subtract the element scroll values (left and top) from a given rect object
     * @method
     * @memberof Popper.Utils
     * @param {Object} rect - Rect object you want to change
     * @param {HTMLElement} element - The element from the function reads the scroll values
     * @param {Boolean} subtract - set to true if you want to subtract the scroll values
     * @return {Object} rect - The modifier rect object
     */
    function includeScroll(rect, element) {
      var subtract = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : false;

      var scrollTop = getScroll(element, 'top');
      var scrollLeft = getScroll(element, 'left');
      var modifier = subtract ? -1 : 1;
      rect.top += scrollTop * modifier;
      rect.bottom += scrollTop * modifier;
      rect.left += scrollLeft * modifier;
      rect.right += scrollLeft * modifier;
      return rect;
    }

    /*
     * Helper to detect borders of a given element
     * @method
     * @memberof Popper.Utils
     * @param {CSSStyleDeclaration} styles
     * Result of `getStyleComputedProperty` on the given element
     * @param {String} axis - `x` or `y`
     * @return {number} borders - The borders size of the given axis
     */

    function getBordersSize(styles, axis) {
      var sideA = axis === 'x' ? 'Left' : 'Top';
      var sideB = sideA === 'Left' ? 'Right' : 'Bottom';

      return parseFloat(styles['border' + sideA + 'Width'], 10) + parseFloat(styles['border' + sideB + 'Width'], 10);
    }

    function getSize(axis, body, html, computedStyle) {
      return Math.max(body['offset' + axis], body['scroll' + axis], html['client' + axis], html['offset' + axis], html['scroll' + axis], isIE(10) ? parseInt(html['offset' + axis]) + parseInt(computedStyle['margin' + (axis === 'Height' ? 'Top' : 'Left')]) + parseInt(computedStyle['margin' + (axis === 'Height' ? 'Bottom' : 'Right')]) : 0);
    }

    function getWindowSizes(document) {
      var body = document.body;
      var html = document.documentElement;
      var computedStyle = isIE(10) && getComputedStyle(html);

      return {
        height: getSize('Height', body, html, computedStyle),
        width: getSize('Width', body, html, computedStyle)
      };
    }

    var classCallCheck = function (instance, Constructor) {
      if (!(instance instanceof Constructor)) {
        throw new TypeError("Cannot call a class as a function");
      }
    };

    var createClass = function () {
      function defineProperties(target, props) {
        for (var i = 0; i < props.length; i++) {
          var descriptor = props[i];
          descriptor.enumerable = descriptor.enumerable || false;
          descriptor.configurable = true;
          if ("value" in descriptor) descriptor.writable = true;
          Object.defineProperty(target, descriptor.key, descriptor);
        }
      }

      return function (Constructor, protoProps, staticProps) {
        if (protoProps) defineProperties(Constructor.prototype, protoProps);
        if (staticProps) defineProperties(Constructor, staticProps);
        return Constructor;
      };
    }();





    var defineProperty$1 = function (obj, key, value) {
      if (key in obj) {
        Object.defineProperty(obj, key, {
          value: value,
          enumerable: true,
          configurable: true,
          writable: true
        });
      } else {
        obj[key] = value;
      }

      return obj;
    };

    var _extends$1 = Object.assign || function (target) {
      for (var i = 1; i < arguments.length; i++) {
        var source = arguments[i];

        for (var key in source) {
          if (Object.prototype.hasOwnProperty.call(source, key)) {
            target[key] = source[key];
          }
        }
      }

      return target;
    };

    /**
     * Given element offsets, generate an output similar to getBoundingClientRect
     * @method
     * @memberof Popper.Utils
     * @argument {Object} offsets
     * @returns {Object} ClientRect like output
     */
    function getClientRect(offsets) {
      return _extends$1({}, offsets, {
        right: offsets.left + offsets.width,
        bottom: offsets.top + offsets.height
      });
    }

    /**
     * Get bounding client rect of given element
     * @method
     * @memberof Popper.Utils
     * @param {HTMLElement} element
     * @return {Object} client rect
     */
    function getBoundingClientRect(element) {
      var rect = {};

      // IE10 10 FIX: Please, don't ask, the element isn't
      // considered in DOM in some circumstances...
      // This isn't reproducible in IE10 compatibility mode of IE11
      try {
        if (isIE(10)) {
          rect = element.getBoundingClientRect();
          var scrollTop = getScroll(element, 'top');
          var scrollLeft = getScroll(element, 'left');
          rect.top += scrollTop;
          rect.left += scrollLeft;
          rect.bottom += scrollTop;
          rect.right += scrollLeft;
        } else {
          rect = element.getBoundingClientRect();
        }
      } catch (e) {}

      var result = {
        left: rect.left,
        top: rect.top,
        width: rect.right - rect.left,
        height: rect.bottom - rect.top
      };

      // subtract scrollbar size from sizes
      var sizes = element.nodeName === 'HTML' ? getWindowSizes(element.ownerDocument) : {};
      var width = sizes.width || element.clientWidth || result.right - result.left;
      var height = sizes.height || element.clientHeight || result.bottom - result.top;

      var horizScrollbar = element.offsetWidth - width;
      var vertScrollbar = element.offsetHeight - height;

      // if an hypothetical scrollbar is detected, we must be sure it's not a `border`
      // we make this check conditional for performance reasons
      if (horizScrollbar || vertScrollbar) {
        var styles = getStyleComputedProperty(element);
        horizScrollbar -= getBordersSize(styles, 'x');
        vertScrollbar -= getBordersSize(styles, 'y');

        result.width -= horizScrollbar;
        result.height -= vertScrollbar;
      }

      return getClientRect(result);
    }

    function getOffsetRectRelativeToArbitraryNode(children, parent) {
      var fixedPosition = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : false;

      var isIE10 = isIE(10);
      var isHTML = parent.nodeName === 'HTML';
      var childrenRect = getBoundingClientRect(children);
      var parentRect = getBoundingClientRect(parent);
      var scrollParent = getScrollParent(children);

      var styles = getStyleComputedProperty(parent);
      var borderTopWidth = parseFloat(styles.borderTopWidth, 10);
      var borderLeftWidth = parseFloat(styles.borderLeftWidth, 10);

      // In cases where the parent is fixed, we must ignore negative scroll in offset calc
      if (fixedPosition && isHTML) {
        parentRect.top = Math.max(parentRect.top, 0);
        parentRect.left = Math.max(parentRect.left, 0);
      }
      var offsets = getClientRect({
        top: childrenRect.top - parentRect.top - borderTopWidth,
        left: childrenRect.left - parentRect.left - borderLeftWidth,
        width: childrenRect.width,
        height: childrenRect.height
      });
      offsets.marginTop = 0;
      offsets.marginLeft = 0;

      // Subtract margins of documentElement in case it's being used as parent
      // we do this only on HTML because it's the only element that behaves
      // differently when margins are applied to it. The margins are included in
      // the box of the documentElement, in the other cases not.
      if (!isIE10 && isHTML) {
        var marginTop = parseFloat(styles.marginTop, 10);
        var marginLeft = parseFloat(styles.marginLeft, 10);

        offsets.top -= borderTopWidth - marginTop;
        offsets.bottom -= borderTopWidth - marginTop;
        offsets.left -= borderLeftWidth - marginLeft;
        offsets.right -= borderLeftWidth - marginLeft;

        // Attach marginTop and marginLeft because in some circumstances we may need them
        offsets.marginTop = marginTop;
        offsets.marginLeft = marginLeft;
      }

      if (isIE10 && !fixedPosition ? parent.contains(scrollParent) : parent === scrollParent && scrollParent.nodeName !== 'BODY') {
        offsets = includeScroll(offsets, parent);
      }

      return offsets;
    }

    function getViewportOffsetRectRelativeToArtbitraryNode(element) {
      var excludeScroll = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : false;

      var html = element.ownerDocument.documentElement;
      var relativeOffset = getOffsetRectRelativeToArbitraryNode(element, html);
      var width = Math.max(html.clientWidth, window.innerWidth || 0);
      var height = Math.max(html.clientHeight, window.innerHeight || 0);

      var scrollTop = !excludeScroll ? getScroll(html) : 0;
      var scrollLeft = !excludeScroll ? getScroll(html, 'left') : 0;

      var offset = {
        top: scrollTop - relativeOffset.top + relativeOffset.marginTop,
        left: scrollLeft - relativeOffset.left + relativeOffset.marginLeft,
        width: width,
        height: height
      };

      return getClientRect(offset);
    }

    /**
     * Check if the given element is fixed or is inside a fixed parent
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element
     * @argument {Element} customContainer
     * @returns {Boolean} answer to "isFixed?"
     */
    function isFixed(element) {
      var nodeName = element.nodeName;
      if (nodeName === 'BODY' || nodeName === 'HTML') {
        return false;
      }
      if (getStyleComputedProperty(element, 'position') === 'fixed') {
        return true;
      }
      return isFixed(getParentNode(element));
    }

    /**
     * Finds the first parent of an element that has a transformed property defined
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element
     * @returns {Element} first transformed parent or documentElement
     */

    function getFixedPositionOffsetParent(element) {
      // This check is needed to avoid errors in case one of the elements isn't defined for any reason
      if (!element || !element.parentElement || isIE()) {
        return document.documentElement;
      }
      var el = element.parentElement;
      while (el && getStyleComputedProperty(el, 'transform') === 'none') {
        el = el.parentElement;
      }
      return el || document.documentElement;
    }

    /**
     * Computed the boundaries limits and return them
     * @method
     * @memberof Popper.Utils
     * @param {HTMLElement} popper
     * @param {HTMLElement} reference
     * @param {number} padding
     * @param {HTMLElement} boundariesElement - Element used to define the boundaries
     * @param {Boolean} fixedPosition - Is in fixed position mode
     * @returns {Object} Coordinates of the boundaries
     */
    function getBoundaries(popper, reference, padding, boundariesElement) {
      var fixedPosition = arguments.length > 4 && arguments[4] !== undefined ? arguments[4] : false;

      // NOTE: 1 DOM access here

      var boundaries = { top: 0, left: 0 };
      var offsetParent = fixedPosition ? getFixedPositionOffsetParent(popper) : findCommonOffsetParent(popper, reference);

      // Handle viewport case
      if (boundariesElement === 'viewport') {
        boundaries = getViewportOffsetRectRelativeToArtbitraryNode(offsetParent, fixedPosition);
      } else {
        // Handle other cases based on DOM element used as boundaries
        var boundariesNode = void 0;
        if (boundariesElement === 'scrollParent') {
          boundariesNode = getScrollParent(getParentNode(reference));
          if (boundariesNode.nodeName === 'BODY') {
            boundariesNode = popper.ownerDocument.documentElement;
          }
        } else if (boundariesElement === 'window') {
          boundariesNode = popper.ownerDocument.documentElement;
        } else {
          boundariesNode = boundariesElement;
        }

        var offsets = getOffsetRectRelativeToArbitraryNode(boundariesNode, offsetParent, fixedPosition);

        // In case of HTML, we need a different computation
        if (boundariesNode.nodeName === 'HTML' && !isFixed(offsetParent)) {
          var _getWindowSizes = getWindowSizes(popper.ownerDocument),
              height = _getWindowSizes.height,
              width = _getWindowSizes.width;

          boundaries.top += offsets.top - offsets.marginTop;
          boundaries.bottom = height + offsets.top;
          boundaries.left += offsets.left - offsets.marginLeft;
          boundaries.right = width + offsets.left;
        } else {
          // for all the other DOM elements, this one is good
          boundaries = offsets;
        }
      }

      // Add paddings
      padding = padding || 0;
      var isPaddingNumber = typeof padding === 'number';
      boundaries.left += isPaddingNumber ? padding : padding.left || 0;
      boundaries.top += isPaddingNumber ? padding : padding.top || 0;
      boundaries.right -= isPaddingNumber ? padding : padding.right || 0;
      boundaries.bottom -= isPaddingNumber ? padding : padding.bottom || 0;

      return boundaries;
    }

    function getArea(_ref) {
      var width = _ref.width,
          height = _ref.height;

      return width * height;
    }

    /**
     * Utility used to transform the `auto` placement to the placement with more
     * available space.
     * @method
     * @memberof Popper.Utils
     * @argument {Object} data - The data object generated by update method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function computeAutoPlacement(placement, refRect, popper, reference, boundariesElement) {
      var padding = arguments.length > 5 && arguments[5] !== undefined ? arguments[5] : 0;

      if (placement.indexOf('auto') === -1) {
        return placement;
      }

      var boundaries = getBoundaries(popper, reference, padding, boundariesElement);

      var rects = {
        top: {
          width: boundaries.width,
          height: refRect.top - boundaries.top
        },
        right: {
          width: boundaries.right - refRect.right,
          height: boundaries.height
        },
        bottom: {
          width: boundaries.width,
          height: boundaries.bottom - refRect.bottom
        },
        left: {
          width: refRect.left - boundaries.left,
          height: boundaries.height
        }
      };

      var sortedAreas = Object.keys(rects).map(function (key) {
        return _extends$1({
          key: key
        }, rects[key], {
          area: getArea(rects[key])
        });
      }).sort(function (a, b) {
        return b.area - a.area;
      });

      var filteredAreas = sortedAreas.filter(function (_ref2) {
        var width = _ref2.width,
            height = _ref2.height;
        return width >= popper.clientWidth && height >= popper.clientHeight;
      });

      var computedPlacement = filteredAreas.length > 0 ? filteredAreas[0].key : sortedAreas[0].key;

      var variation = placement.split('-')[1];

      return computedPlacement + (variation ? '-' + variation : '');
    }

    /**
     * Get offsets to the reference element
     * @method
     * @memberof Popper.Utils
     * @param {Object} state
     * @param {Element} popper - the popper element
     * @param {Element} reference - the reference element (the popper will be relative to this)
     * @param {Element} fixedPosition - is in fixed position mode
     * @returns {Object} An object containing the offsets which will be applied to the popper
     */
    function getReferenceOffsets(state, popper, reference) {
      var fixedPosition = arguments.length > 3 && arguments[3] !== undefined ? arguments[3] : null;

      var commonOffsetParent = fixedPosition ? getFixedPositionOffsetParent(popper) : findCommonOffsetParent(popper, reference);
      return getOffsetRectRelativeToArbitraryNode(reference, commonOffsetParent, fixedPosition);
    }

    /**
     * Get the outer sizes of the given element (offset size + margins)
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element
     * @returns {Object} object containing width and height properties
     */
    function getOuterSizes(element) {
      var styles = getComputedStyle(element);
      var x = parseFloat(styles.marginTop) + parseFloat(styles.marginBottom);
      var y = parseFloat(styles.marginLeft) + parseFloat(styles.marginRight);
      var result = {
        width: element.offsetWidth + y,
        height: element.offsetHeight + x
      };
      return result;
    }

    /**
     * Get the opposite placement of the given one
     * @method
     * @memberof Popper.Utils
     * @argument {String} placement
     * @returns {String} flipped placement
     */
    function getOppositePlacement(placement) {
      var hash = { left: 'right', right: 'left', bottom: 'top', top: 'bottom' };
      return placement.replace(/left|right|bottom|top/g, function (matched) {
        return hash[matched];
      });
    }

    /**
     * Get offsets to the popper
     * @method
     * @memberof Popper.Utils
     * @param {Object} position - CSS position the Popper will get applied
     * @param {HTMLElement} popper - the popper element
     * @param {Object} referenceOffsets - the reference offsets (the popper will be relative to this)
     * @param {String} placement - one of the valid placement options
     * @returns {Object} popperOffsets - An object containing the offsets which will be applied to the popper
     */
    function getPopperOffsets(popper, referenceOffsets, placement) {
      placement = placement.split('-')[0];

      // Get popper node sizes
      var popperRect = getOuterSizes(popper);

      // Add position, width and height to our offsets object
      var popperOffsets = {
        width: popperRect.width,
        height: popperRect.height
      };

      // depending by the popper placement we have to compute its offsets slightly differently
      var isHoriz = ['right', 'left'].indexOf(placement) !== -1;
      var mainSide = isHoriz ? 'top' : 'left';
      var secondarySide = isHoriz ? 'left' : 'top';
      var measurement = isHoriz ? 'height' : 'width';
      var secondaryMeasurement = !isHoriz ? 'height' : 'width';

      popperOffsets[mainSide] = referenceOffsets[mainSide] + referenceOffsets[measurement] / 2 - popperRect[measurement] / 2;
      if (placement === secondarySide) {
        popperOffsets[secondarySide] = referenceOffsets[secondarySide] - popperRect[secondaryMeasurement];
      } else {
        popperOffsets[secondarySide] = referenceOffsets[getOppositePlacement(secondarySide)];
      }

      return popperOffsets;
    }

    /**
     * Mimics the `find` method of Array
     * @method
     * @memberof Popper.Utils
     * @argument {Array} arr
     * @argument prop
     * @argument value
     * @returns index or -1
     */
    function find(arr, check) {
      // use native find if supported
      if (Array.prototype.find) {
        return arr.find(check);
      }

      // use `filter` to obtain the same behavior of `find`
      return arr.filter(check)[0];
    }

    /**
     * Return the index of the matching object
     * @method
     * @memberof Popper.Utils
     * @argument {Array} arr
     * @argument prop
     * @argument value
     * @returns index or -1
     */
    function findIndex(arr, prop, value) {
      // use native findIndex if supported
      if (Array.prototype.findIndex) {
        return arr.findIndex(function (cur) {
          return cur[prop] === value;
        });
      }

      // use `find` + `indexOf` if `findIndex` isn't supported
      var match = find(arr, function (obj) {
        return obj[prop] === value;
      });
      return arr.indexOf(match);
    }

    /**
     * Loop trough the list of modifiers and run them in order,
     * each of them will then edit the data object.
     * @method
     * @memberof Popper.Utils
     * @param {dataObject} data
     * @param {Array} modifiers
     * @param {String} ends - Optional modifier name used as stopper
     * @returns {dataObject}
     */
    function runModifiers(modifiers, data, ends) {
      var modifiersToRun = ends === undefined ? modifiers : modifiers.slice(0, findIndex(modifiers, 'name', ends));

      modifiersToRun.forEach(function (modifier) {
        if (modifier['function']) {
          // eslint-disable-line dot-notation
          console.warn('`modifier.function` is deprecated, use `modifier.fn`!');
        }
        var fn = modifier['function'] || modifier.fn; // eslint-disable-line dot-notation
        if (modifier.enabled && isFunction$1(fn)) {
          // Add properties to offsets to make them a complete clientRect object
          // we do this before each modifier to make sure the previous one doesn't
          // mess with these values
          data.offsets.popper = getClientRect(data.offsets.popper);
          data.offsets.reference = getClientRect(data.offsets.reference);

          data = fn(data, modifier);
        }
      });

      return data;
    }

    /**
     * Updates the position of the popper, computing the new offsets and applying
     * the new style.<br />
     * Prefer `scheduleUpdate` over `update` because of performance reasons.
     * @method
     * @memberof Popper
     */
    function update() {
      // if popper is destroyed, don't perform any further update
      if (this.state.isDestroyed) {
        return;
      }

      var data = {
        instance: this,
        styles: {},
        arrowStyles: {},
        attributes: {},
        flipped: false,
        offsets: {}
      };

      // compute reference element offsets
      data.offsets.reference = getReferenceOffsets(this.state, this.popper, this.reference, this.options.positionFixed);

      // compute auto placement, store placement inside the data object,
      // modifiers will be able to edit `placement` if needed
      // and refer to originalPlacement to know the original value
      data.placement = computeAutoPlacement(this.options.placement, data.offsets.reference, this.popper, this.reference, this.options.modifiers.flip.boundariesElement, this.options.modifiers.flip.padding);

      // store the computed placement inside `originalPlacement`
      data.originalPlacement = data.placement;

      data.positionFixed = this.options.positionFixed;

      // compute the popper offsets
      data.offsets.popper = getPopperOffsets(this.popper, data.offsets.reference, data.placement);

      data.offsets.popper.position = this.options.positionFixed ? 'fixed' : 'absolute';

      // run the modifiers
      data = runModifiers(this.modifiers, data);

      // the first `update` will call `onCreate` callback
      // the other ones will call `onUpdate` callback
      if (!this.state.isCreated) {
        this.state.isCreated = true;
        this.options.onCreate(data);
      } else {
        this.options.onUpdate(data);
      }
    }

    /**
     * Helper used to know if the given modifier is enabled.
     * @method
     * @memberof Popper.Utils
     * @returns {Boolean}
     */
    function isModifierEnabled(modifiers, modifierName) {
      return modifiers.some(function (_ref) {
        var name = _ref.name,
            enabled = _ref.enabled;
        return enabled && name === modifierName;
      });
    }

    /**
     * Get the prefixed supported property name
     * @method
     * @memberof Popper.Utils
     * @argument {String} property (camelCase)
     * @returns {String} prefixed property (camelCase or PascalCase, depending on the vendor prefix)
     */
    function getSupportedPropertyName(property) {
      var prefixes = [false, 'ms', 'Webkit', 'Moz', 'O'];
      var upperProp = property.charAt(0).toUpperCase() + property.slice(1);

      for (var i = 0; i < prefixes.length; i++) {
        var prefix = prefixes[i];
        var toCheck = prefix ? '' + prefix + upperProp : property;
        if (typeof document.body.style[toCheck] !== 'undefined') {
          return toCheck;
        }
      }
      return null;
    }

    /**
     * Destroys the popper.
     * @method
     * @memberof Popper
     */
    function destroy() {
      this.state.isDestroyed = true;

      // touch DOM only if `applyStyle` modifier is enabled
      if (isModifierEnabled(this.modifiers, 'applyStyle')) {
        this.popper.removeAttribute('x-placement');
        this.popper.style.position = '';
        this.popper.style.top = '';
        this.popper.style.left = '';
        this.popper.style.right = '';
        this.popper.style.bottom = '';
        this.popper.style.willChange = '';
        this.popper.style[getSupportedPropertyName('transform')] = '';
      }

      this.disableEventListeners();

      // remove the popper if user explicity asked for the deletion on destroy
      // do not use `remove` because IE11 doesn't support it
      if (this.options.removeOnDestroy) {
        this.popper.parentNode.removeChild(this.popper);
      }
      return this;
    }

    /**
     * Get the window associated with the element
     * @argument {Element} element
     * @returns {Window}
     */
    function getWindow(element) {
      var ownerDocument = element.ownerDocument;
      return ownerDocument ? ownerDocument.defaultView : window;
    }

    function attachToScrollParents(scrollParent, event, callback, scrollParents) {
      var isBody = scrollParent.nodeName === 'BODY';
      var target = isBody ? scrollParent.ownerDocument.defaultView : scrollParent;
      target.addEventListener(event, callback, { passive: true });

      if (!isBody) {
        attachToScrollParents(getScrollParent(target.parentNode), event, callback, scrollParents);
      }
      scrollParents.push(target);
    }

    /**
     * Setup needed event listeners used to update the popper position
     * @method
     * @memberof Popper.Utils
     * @private
     */
    function setupEventListeners(reference, options, state, updateBound) {
      // Resize event listener on window
      state.updateBound = updateBound;
      getWindow(reference).addEventListener('resize', state.updateBound, { passive: true });

      // Scroll event listener on scroll parents
      var scrollElement = getScrollParent(reference);
      attachToScrollParents(scrollElement, 'scroll', state.updateBound, state.scrollParents);
      state.scrollElement = scrollElement;
      state.eventsEnabled = true;

      return state;
    }

    /**
     * It will add resize/scroll events and start recalculating
     * position of the popper element when they are triggered.
     * @method
     * @memberof Popper
     */
    function enableEventListeners() {
      if (!this.state.eventsEnabled) {
        this.state = setupEventListeners(this.reference, this.options, this.state, this.scheduleUpdate);
      }
    }

    /**
     * Remove event listeners used to update the popper position
     * @method
     * @memberof Popper.Utils
     * @private
     */
    function removeEventListeners(reference, state) {
      // Remove resize event listener on window
      getWindow(reference).removeEventListener('resize', state.updateBound);

      // Remove scroll event listener on scroll parents
      state.scrollParents.forEach(function (target) {
        target.removeEventListener('scroll', state.updateBound);
      });

      // Reset state
      state.updateBound = null;
      state.scrollParents = [];
      state.scrollElement = null;
      state.eventsEnabled = false;
      return state;
    }

    /**
     * It will remove resize/scroll events and won't recalculate popper position
     * when they are triggered. It also won't trigger `onUpdate` callback anymore,
     * unless you call `update` method manually.
     * @method
     * @memberof Popper
     */
    function disableEventListeners() {
      if (this.state.eventsEnabled) {
        cancelAnimationFrame(this.scheduleUpdate);
        this.state = removeEventListeners(this.reference, this.state);
      }
    }

    /**
     * Tells if a given input is a number
     * @method
     * @memberof Popper.Utils
     * @param {*} input to check
     * @return {Boolean}
     */
    function isNumeric(n) {
      return n !== '' && !isNaN(parseFloat(n)) && isFinite(n);
    }

    /**
     * Set the style to the given popper
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element - Element to apply the style to
     * @argument {Object} styles
     * Object with a list of properties and values which will be applied to the element
     */
    function setStyles(element, styles) {
      Object.keys(styles).forEach(function (prop) {
        var unit = '';
        // add unit if the value is numeric and is one of the following
        if (['width', 'height', 'top', 'right', 'bottom', 'left'].indexOf(prop) !== -1 && isNumeric(styles[prop])) {
          unit = 'px';
        }
        element.style[prop] = styles[prop] + unit;
      });
    }

    /**
     * Set the attributes to the given popper
     * @method
     * @memberof Popper.Utils
     * @argument {Element} element - Element to apply the attributes to
     * @argument {Object} styles
     * Object with a list of properties and values which will be applied to the element
     */
    function setAttributes(element, attributes) {
      Object.keys(attributes).forEach(function (prop) {
        var value = attributes[prop];
        if (value !== false) {
          element.setAttribute(prop, attributes[prop]);
        } else {
          element.removeAttribute(prop);
        }
      });
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by `update` method
     * @argument {Object} data.styles - List of style properties - values to apply to popper element
     * @argument {Object} data.attributes - List of attribute properties - values to apply to popper element
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The same data object
     */
    function applyStyle(data) {
      // any property present in `data.styles` will be applied to the popper,
      // in this way we can make the 3rd party modifiers add custom styles to it
      // Be aware, modifiers could override the properties defined in the previous
      // lines of this modifier!
      setStyles(data.instance.popper, data.styles);

      // any property present in `data.attributes` will be applied to the popper,
      // they will be set as HTML attributes of the element
      setAttributes(data.instance.popper, data.attributes);

      // if arrowElement is defined and arrowStyles has some properties
      if (data.arrowElement && Object.keys(data.arrowStyles).length) {
        setStyles(data.arrowElement, data.arrowStyles);
      }

      return data;
    }

    /**
     * Set the x-placement attribute before everything else because it could be used
     * to add margins to the popper margins needs to be calculated to get the
     * correct popper offsets.
     * @method
     * @memberof Popper.modifiers
     * @param {HTMLElement} reference - The reference element used to position the popper
     * @param {HTMLElement} popper - The HTML element used as popper
     * @param {Object} options - Popper.js options
     */
    function applyStyleOnLoad(reference, popper, options, modifierOptions, state) {
      // compute reference element offsets
      var referenceOffsets = getReferenceOffsets(state, popper, reference, options.positionFixed);

      // compute auto placement, store placement inside the data object,
      // modifiers will be able to edit `placement` if needed
      // and refer to originalPlacement to know the original value
      var placement = computeAutoPlacement(options.placement, referenceOffsets, popper, reference, options.modifiers.flip.boundariesElement, options.modifiers.flip.padding);

      popper.setAttribute('x-placement', placement);

      // Apply `position` to popper before anything else because
      // without the position applied we can't guarantee correct computations
      setStyles(popper, { position: options.positionFixed ? 'fixed' : 'absolute' });

      return options;
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by `update` method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function computeStyle(data, options) {
      var x = options.x,
          y = options.y;
      var popper = data.offsets.popper;

      // Remove this legacy support in Popper.js v2

      var legacyGpuAccelerationOption = find(data.instance.modifiers, function (modifier) {
        return modifier.name === 'applyStyle';
      }).gpuAcceleration;
      if (legacyGpuAccelerationOption !== undefined) {
        console.warn('WARNING: `gpuAcceleration` option moved to `computeStyle` modifier and will not be supported in future versions of Popper.js!');
      }
      var gpuAcceleration = legacyGpuAccelerationOption !== undefined ? legacyGpuAccelerationOption : options.gpuAcceleration;

      var offsetParent = getOffsetParent(data.instance.popper);
      var offsetParentRect = getBoundingClientRect(offsetParent);

      // Styles
      var styles = {
        position: popper.position
      };

      // Avoid blurry text by using full pixel integers.
      // For pixel-perfect positioning, top/bottom prefers rounded
      // values, while left/right prefers floored values.
      var offsets = {
        left: Math.floor(popper.left),
        top: Math.round(popper.top),
        bottom: Math.round(popper.bottom),
        right: Math.floor(popper.right)
      };

      var sideA = x === 'bottom' ? 'top' : 'bottom';
      var sideB = y === 'right' ? 'left' : 'right';

      // if gpuAcceleration is set to `true` and transform is supported,
      //  we use `translate3d` to apply the position to the popper we
      // automatically use the supported prefixed version if needed
      var prefixedProperty = getSupportedPropertyName('transform');

      // now, let's make a step back and look at this code closely (wtf?)
      // If the content of the popper grows once it's been positioned, it
      // may happen that the popper gets misplaced because of the new content
      // overflowing its reference element
      // To avoid this problem, we provide two options (x and y), which allow
      // the consumer to define the offset origin.
      // If we position a popper on top of a reference element, we can set
      // `x` to `top` to make the popper grow towards its top instead of
      // its bottom.
      var left = void 0,
          top = void 0;
      if (sideA === 'bottom') {
        // when offsetParent is <html> the positioning is relative to the bottom of the screen (excluding the scrollbar)
        // and not the bottom of the html element
        if (offsetParent.nodeName === 'HTML') {
          top = -offsetParent.clientHeight + offsets.bottom;
        } else {
          top = -offsetParentRect.height + offsets.bottom;
        }
      } else {
        top = offsets.top;
      }
      if (sideB === 'right') {
        if (offsetParent.nodeName === 'HTML') {
          left = -offsetParent.clientWidth + offsets.right;
        } else {
          left = -offsetParentRect.width + offsets.right;
        }
      } else {
        left = offsets.left;
      }
      if (gpuAcceleration && prefixedProperty) {
        styles[prefixedProperty] = 'translate3d(' + left + 'px, ' + top + 'px, 0)';
        styles[sideA] = 0;
        styles[sideB] = 0;
        styles.willChange = 'transform';
      } else {
        // othwerise, we use the standard `top`, `left`, `bottom` and `right` properties
        var invertTop = sideA === 'bottom' ? -1 : 1;
        var invertLeft = sideB === 'right' ? -1 : 1;
        styles[sideA] = top * invertTop;
        styles[sideB] = left * invertLeft;
        styles.willChange = sideA + ', ' + sideB;
      }

      // Attributes
      var attributes = {
        'x-placement': data.placement
      };

      // Update `data` attributes, styles and arrowStyles
      data.attributes = _extends$1({}, attributes, data.attributes);
      data.styles = _extends$1({}, styles, data.styles);
      data.arrowStyles = _extends$1({}, data.offsets.arrow, data.arrowStyles);

      return data;
    }

    /**
     * Helper used to know if the given modifier depends from another one.<br />
     * It checks if the needed modifier is listed and enabled.
     * @method
     * @memberof Popper.Utils
     * @param {Array} modifiers - list of modifiers
     * @param {String} requestingName - name of requesting modifier
     * @param {String} requestedName - name of requested modifier
     * @returns {Boolean}
     */
    function isModifierRequired(modifiers, requestingName, requestedName) {
      var requesting = find(modifiers, function (_ref) {
        var name = _ref.name;
        return name === requestingName;
      });

      var isRequired = !!requesting && modifiers.some(function (modifier) {
        return modifier.name === requestedName && modifier.enabled && modifier.order < requesting.order;
      });

      if (!isRequired) {
        var _requesting = '`' + requestingName + '`';
        var requested = '`' + requestedName + '`';
        console.warn(requested + ' modifier is required by ' + _requesting + ' modifier in order to work, be sure to include it before ' + _requesting + '!');
      }
      return isRequired;
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by update method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function arrow(data, options) {
      var _data$offsets$arrow;

      // arrow depends on keepTogether in order to work
      if (!isModifierRequired(data.instance.modifiers, 'arrow', 'keepTogether')) {
        return data;
      }

      var arrowElement = options.element;

      // if arrowElement is a string, suppose it's a CSS selector
      if (typeof arrowElement === 'string') {
        arrowElement = data.instance.popper.querySelector(arrowElement);

        // if arrowElement is not found, don't run the modifier
        if (!arrowElement) {
          return data;
        }
      } else {
        // if the arrowElement isn't a query selector we must check that the
        // provided DOM node is child of its popper node
        if (!data.instance.popper.contains(arrowElement)) {
          console.warn('WARNING: `arrow.element` must be child of its popper element!');
          return data;
        }
      }

      var placement = data.placement.split('-')[0];
      var _data$offsets = data.offsets,
          popper = _data$offsets.popper,
          reference = _data$offsets.reference;

      var isVertical = ['left', 'right'].indexOf(placement) !== -1;

      var len = isVertical ? 'height' : 'width';
      var sideCapitalized = isVertical ? 'Top' : 'Left';
      var side = sideCapitalized.toLowerCase();
      var altSide = isVertical ? 'left' : 'top';
      var opSide = isVertical ? 'bottom' : 'right';
      var arrowElementSize = getOuterSizes(arrowElement)[len];

      //
      // extends keepTogether behavior making sure the popper and its
      // reference have enough pixels in conjunction
      //

      // top/left side
      if (reference[opSide] - arrowElementSize < popper[side]) {
        data.offsets.popper[side] -= popper[side] - (reference[opSide] - arrowElementSize);
      }
      // bottom/right side
      if (reference[side] + arrowElementSize > popper[opSide]) {
        data.offsets.popper[side] += reference[side] + arrowElementSize - popper[opSide];
      }
      data.offsets.popper = getClientRect(data.offsets.popper);

      // compute center of the popper
      var center = reference[side] + reference[len] / 2 - arrowElementSize / 2;

      // Compute the sideValue using the updated popper offsets
      // take popper margin in account because we don't have this info available
      var css = getStyleComputedProperty(data.instance.popper);
      var popperMarginSide = parseFloat(css['margin' + sideCapitalized], 10);
      var popperBorderSide = parseFloat(css['border' + sideCapitalized + 'Width'], 10);
      var sideValue = center - data.offsets.popper[side] - popperMarginSide - popperBorderSide;

      // prevent arrowElement from being placed not contiguously to its popper
      sideValue = Math.max(Math.min(popper[len] - arrowElementSize, sideValue), 0);

      data.arrowElement = arrowElement;
      data.offsets.arrow = (_data$offsets$arrow = {}, defineProperty$1(_data$offsets$arrow, side, Math.round(sideValue)), defineProperty$1(_data$offsets$arrow, altSide, ''), _data$offsets$arrow);

      return data;
    }

    /**
     * Get the opposite placement variation of the given one
     * @method
     * @memberof Popper.Utils
     * @argument {String} placement variation
     * @returns {String} flipped placement variation
     */
    function getOppositeVariation(variation) {
      if (variation === 'end') {
        return 'start';
      } else if (variation === 'start') {
        return 'end';
      }
      return variation;
    }

    /**
     * List of accepted placements to use as values of the `placement` option.<br />
     * Valid placements are:
     * - `auto`
     * - `top`
     * - `right`
     * - `bottom`
     * - `left`
     *
     * Each placement can have a variation from this list:
     * - `-start`
     * - `-end`
     *
     * Variations are interpreted easily if you think of them as the left to right
     * written languages. Horizontally (`top` and `bottom`), `start` is left and `end`
     * is right.<br />
     * Vertically (`left` and `right`), `start` is top and `end` is bottom.
     *
     * Some valid examples are:
     * - `top-end` (on top of reference, right aligned)
     * - `right-start` (on right of reference, top aligned)
     * - `bottom` (on bottom, centered)
     * - `auto-end` (on the side with more space available, alignment depends by placement)
     *
     * @static
     * @type {Array}
     * @enum {String}
     * @readonly
     * @method placements
     * @memberof Popper
     */
    var placements = ['auto-start', 'auto', 'auto-end', 'top-start', 'top', 'top-end', 'right-start', 'right', 'right-end', 'bottom-end', 'bottom', 'bottom-start', 'left-end', 'left', 'left-start'];

    // Get rid of `auto` `auto-start` and `auto-end`
    var validPlacements = placements.slice(3);

    /**
     * Given an initial placement, returns all the subsequent placements
     * clockwise (or counter-clockwise).
     *
     * @method
     * @memberof Popper.Utils
     * @argument {String} placement - A valid placement (it accepts variations)
     * @argument {Boolean} counter - Set to true to walk the placements counterclockwise
     * @returns {Array} placements including their variations
     */
    function clockwise(placement) {
      var counter = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : false;

      var index = validPlacements.indexOf(placement);
      var arr = validPlacements.slice(index + 1).concat(validPlacements.slice(0, index));
      return counter ? arr.reverse() : arr;
    }

    var BEHAVIORS = {
      FLIP: 'flip',
      CLOCKWISE: 'clockwise',
      COUNTERCLOCKWISE: 'counterclockwise'
    };

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by update method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function flip(data, options) {
      // if `inner` modifier is enabled, we can't use the `flip` modifier
      if (isModifierEnabled(data.instance.modifiers, 'inner')) {
        return data;
      }

      if (data.flipped && data.placement === data.originalPlacement) {
        // seems like flip is trying to loop, probably there's not enough space on any of the flippable sides
        return data;
      }

      var boundaries = getBoundaries(data.instance.popper, data.instance.reference, options.padding, options.boundariesElement, data.positionFixed);

      var placement = data.placement.split('-')[0];
      var placementOpposite = getOppositePlacement(placement);
      var variation = data.placement.split('-')[1] || '';

      var flipOrder = [];

      switch (options.behavior) {
        case BEHAVIORS.FLIP:
          flipOrder = [placement, placementOpposite];
          break;
        case BEHAVIORS.CLOCKWISE:
          flipOrder = clockwise(placement);
          break;
        case BEHAVIORS.COUNTERCLOCKWISE:
          flipOrder = clockwise(placement, true);
          break;
        default:
          flipOrder = options.behavior;
      }

      flipOrder.forEach(function (step, index) {
        if (placement !== step || flipOrder.length === index + 1) {
          return data;
        }

        placement = data.placement.split('-')[0];
        placementOpposite = getOppositePlacement(placement);

        var popperOffsets = data.offsets.popper;
        var refOffsets = data.offsets.reference;

        // using floor because the reference offsets may contain decimals we are not going to consider here
        var floor = Math.floor;
        var overlapsRef = placement === 'left' && floor(popperOffsets.right) > floor(refOffsets.left) || placement === 'right' && floor(popperOffsets.left) < floor(refOffsets.right) || placement === 'top' && floor(popperOffsets.bottom) > floor(refOffsets.top) || placement === 'bottom' && floor(popperOffsets.top) < floor(refOffsets.bottom);

        var overflowsLeft = floor(popperOffsets.left) < floor(boundaries.left);
        var overflowsRight = floor(popperOffsets.right) > floor(boundaries.right);
        var overflowsTop = floor(popperOffsets.top) < floor(boundaries.top);
        var overflowsBottom = floor(popperOffsets.bottom) > floor(boundaries.bottom);

        var overflowsBoundaries = placement === 'left' && overflowsLeft || placement === 'right' && overflowsRight || placement === 'top' && overflowsTop || placement === 'bottom' && overflowsBottom;

        // flip the variation if required
        var isVertical = ['top', 'bottom'].indexOf(placement) !== -1;
        var flippedVariation = !!options.flipVariations && (isVertical && variation === 'start' && overflowsLeft || isVertical && variation === 'end' && overflowsRight || !isVertical && variation === 'start' && overflowsTop || !isVertical && variation === 'end' && overflowsBottom);

        if (overlapsRef || overflowsBoundaries || flippedVariation) {
          // this boolean to detect any flip loop
          data.flipped = true;

          if (overlapsRef || overflowsBoundaries) {
            placement = flipOrder[index + 1];
          }

          if (flippedVariation) {
            variation = getOppositeVariation(variation);
          }

          data.placement = placement + (variation ? '-' + variation : '');

          // this object contains `position`, we want to preserve it along with
          // any additional property we may add in the future
          data.offsets.popper = _extends$1({}, data.offsets.popper, getPopperOffsets(data.instance.popper, data.offsets.reference, data.placement));

          data = runModifiers(data.instance.modifiers, data, 'flip');
        }
      });
      return data;
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by update method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function keepTogether(data) {
      var _data$offsets = data.offsets,
          popper = _data$offsets.popper,
          reference = _data$offsets.reference;

      var placement = data.placement.split('-')[0];
      var floor = Math.floor;
      var isVertical = ['top', 'bottom'].indexOf(placement) !== -1;
      var side = isVertical ? 'right' : 'bottom';
      var opSide = isVertical ? 'left' : 'top';
      var measurement = isVertical ? 'width' : 'height';

      if (popper[side] < floor(reference[opSide])) {
        data.offsets.popper[opSide] = floor(reference[opSide]) - popper[measurement];
      }
      if (popper[opSide] > floor(reference[side])) {
        data.offsets.popper[opSide] = floor(reference[side]);
      }

      return data;
    }

    /**
     * Converts a string containing value + unit into a px value number
     * @function
     * @memberof {modifiers~offset}
     * @private
     * @argument {String} str - Value + unit string
     * @argument {String} measurement - `height` or `width`
     * @argument {Object} popperOffsets
     * @argument {Object} referenceOffsets
     * @returns {Number|String}
     * Value in pixels, or original string if no values were extracted
     */
    function toValue(str, measurement, popperOffsets, referenceOffsets) {
      // separate value from unit
      var split = str.match(/((?:\-|\+)?\d*\.?\d*)(.*)/);
      var value = +split[1];
      var unit = split[2];

      // If it's not a number it's an operator, I guess
      if (!value) {
        return str;
      }

      if (unit.indexOf('%') === 0) {
        var element = void 0;
        switch (unit) {
          case '%p':
            element = popperOffsets;
            break;
          case '%':
          case '%r':
          default:
            element = referenceOffsets;
        }

        var rect = getClientRect(element);
        return rect[measurement] / 100 * value;
      } else if (unit === 'vh' || unit === 'vw') {
        // if is a vh or vw, we calculate the size based on the viewport
        var size = void 0;
        if (unit === 'vh') {
          size = Math.max(document.documentElement.clientHeight, window.innerHeight || 0);
        } else {
          size = Math.max(document.documentElement.clientWidth, window.innerWidth || 0);
        }
        return size / 100 * value;
      } else {
        // if is an explicit pixel unit, we get rid of the unit and keep the value
        // if is an implicit unit, it's px, and we return just the value
        return value;
      }
    }

    /**
     * Parse an `offset` string to extrapolate `x` and `y` numeric offsets.
     * @function
     * @memberof {modifiers~offset}
     * @private
     * @argument {String} offset
     * @argument {Object} popperOffsets
     * @argument {Object} referenceOffsets
     * @argument {String} basePlacement
     * @returns {Array} a two cells array with x and y offsets in numbers
     */
    function parseOffset(offset, popperOffsets, referenceOffsets, basePlacement) {
      var offsets = [0, 0];

      // Use height if placement is left or right and index is 0 otherwise use width
      // in this way the first offset will use an axis and the second one
      // will use the other one
      var useHeight = ['right', 'left'].indexOf(basePlacement) !== -1;

      // Split the offset string to obtain a list of values and operands
      // The regex addresses values with the plus or minus sign in front (+10, -20, etc)
      var fragments = offset.split(/(\+|\-)/).map(function (frag) {
        return frag.trim();
      });

      // Detect if the offset string contains a pair of values or a single one
      // they could be separated by comma or space
      var divider = fragments.indexOf(find(fragments, function (frag) {
        return frag.search(/,|\s/) !== -1;
      }));

      if (fragments[divider] && fragments[divider].indexOf(',') === -1) {
        console.warn('Offsets separated by white space(s) are deprecated, use a comma (,) instead.');
      }

      // If divider is found, we divide the list of values and operands to divide
      // them by ofset X and Y.
      var splitRegex = /\s*,\s*|\s+/;
      var ops = divider !== -1 ? [fragments.slice(0, divider).concat([fragments[divider].split(splitRegex)[0]]), [fragments[divider].split(splitRegex)[1]].concat(fragments.slice(divider + 1))] : [fragments];

      // Convert the values with units to absolute pixels to allow our computations
      ops = ops.map(function (op, index) {
        // Most of the units rely on the orientation of the popper
        var measurement = (index === 1 ? !useHeight : useHeight) ? 'height' : 'width';
        var mergeWithPrevious = false;
        return op
        // This aggregates any `+` or `-` sign that aren't considered operators
        // e.g.: 10 + +5 => [10, +, +5]
        .reduce(function (a, b) {
          if (a[a.length - 1] === '' && ['+', '-'].indexOf(b) !== -1) {
            a[a.length - 1] = b;
            mergeWithPrevious = true;
            return a;
          } else if (mergeWithPrevious) {
            a[a.length - 1] += b;
            mergeWithPrevious = false;
            return a;
          } else {
            return a.concat(b);
          }
        }, [])
        // Here we convert the string values into number values (in px)
        .map(function (str) {
          return toValue(str, measurement, popperOffsets, referenceOffsets);
        });
      });

      // Loop trough the offsets arrays and execute the operations
      ops.forEach(function (op, index) {
        op.forEach(function (frag, index2) {
          if (isNumeric(frag)) {
            offsets[index] += frag * (op[index2 - 1] === '-' ? -1 : 1);
          }
        });
      });
      return offsets;
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by update method
     * @argument {Object} options - Modifiers configuration and options
     * @argument {Number|String} options.offset=0
     * The offset value as described in the modifier description
     * @returns {Object} The data object, properly modified
     */
    function offset(data, _ref) {
      var offset = _ref.offset;
      var placement = data.placement,
          _data$offsets = data.offsets,
          popper = _data$offsets.popper,
          reference = _data$offsets.reference;

      var basePlacement = placement.split('-')[0];

      var offsets = void 0;
      if (isNumeric(+offset)) {
        offsets = [+offset, 0];
      } else {
        offsets = parseOffset(offset, popper, reference, basePlacement);
      }

      if (basePlacement === 'left') {
        popper.top += offsets[0];
        popper.left -= offsets[1];
      } else if (basePlacement === 'right') {
        popper.top += offsets[0];
        popper.left += offsets[1];
      } else if (basePlacement === 'top') {
        popper.left += offsets[0];
        popper.top -= offsets[1];
      } else if (basePlacement === 'bottom') {
        popper.left += offsets[0];
        popper.top += offsets[1];
      }

      data.popper = popper;
      return data;
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by `update` method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function preventOverflow(data, options) {
      var boundariesElement = options.boundariesElement || getOffsetParent(data.instance.popper);

      // If offsetParent is the reference element, we really want to
      // go one step up and use the next offsetParent as reference to
      // avoid to make this modifier completely useless and look like broken
      if (data.instance.reference === boundariesElement) {
        boundariesElement = getOffsetParent(boundariesElement);
      }

      // NOTE: DOM access here
      // resets the popper's position so that the document size can be calculated excluding
      // the size of the popper element itself
      var transformProp = getSupportedPropertyName('transform');
      var popperStyles = data.instance.popper.style; // assignment to help minification
      var top = popperStyles.top,
          left = popperStyles.left,
          transform = popperStyles[transformProp];

      popperStyles.top = '';
      popperStyles.left = '';
      popperStyles[transformProp] = '';

      var boundaries = getBoundaries(data.instance.popper, data.instance.reference, options.padding, boundariesElement, data.positionFixed);

      // NOTE: DOM access here
      // restores the original style properties after the offsets have been computed
      popperStyles.top = top;
      popperStyles.left = left;
      popperStyles[transformProp] = transform;

      options.boundaries = boundaries;

      var order = options.priority;
      var popper = data.offsets.popper;

      var check = {
        primary: function primary(placement) {
          var value = popper[placement];
          if (popper[placement] < boundaries[placement] && !options.escapeWithReference) {
            value = Math.max(popper[placement], boundaries[placement]);
          }
          return defineProperty$1({}, placement, value);
        },
        secondary: function secondary(placement) {
          var mainSide = placement === 'right' ? 'left' : 'top';
          var value = popper[mainSide];
          if (popper[placement] > boundaries[placement] && !options.escapeWithReference) {
            value = Math.min(popper[mainSide], boundaries[placement] - (placement === 'right' ? popper.width : popper.height));
          }
          return defineProperty$1({}, mainSide, value);
        }
      };

      order.forEach(function (placement) {
        var side = ['left', 'top'].indexOf(placement) !== -1 ? 'primary' : 'secondary';
        popper = _extends$1({}, popper, check[side](placement));
      });

      data.offsets.popper = popper;

      return data;
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by `update` method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function shift(data) {
      var placement = data.placement;
      var basePlacement = placement.split('-')[0];
      var shiftvariation = placement.split('-')[1];

      // if shift shiftvariation is specified, run the modifier
      if (shiftvariation) {
        var _data$offsets = data.offsets,
            reference = _data$offsets.reference,
            popper = _data$offsets.popper;

        var isVertical = ['bottom', 'top'].indexOf(basePlacement) !== -1;
        var side = isVertical ? 'left' : 'top';
        var measurement = isVertical ? 'width' : 'height';

        var shiftOffsets = {
          start: defineProperty$1({}, side, reference[side]),
          end: defineProperty$1({}, side, reference[side] + reference[measurement] - popper[measurement])
        };

        data.offsets.popper = _extends$1({}, popper, shiftOffsets[shiftvariation]);
      }

      return data;
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by update method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function hide(data) {
      if (!isModifierRequired(data.instance.modifiers, 'hide', 'preventOverflow')) {
        return data;
      }

      var refRect = data.offsets.reference;
      var bound = find(data.instance.modifiers, function (modifier) {
        return modifier.name === 'preventOverflow';
      }).boundaries;

      if (refRect.bottom < bound.top || refRect.left > bound.right || refRect.top > bound.bottom || refRect.right < bound.left) {
        // Avoid unnecessary DOM access if visibility hasn't changed
        if (data.hide === true) {
          return data;
        }

        data.hide = true;
        data.attributes['x-out-of-boundaries'] = '';
      } else {
        // Avoid unnecessary DOM access if visibility hasn't changed
        if (data.hide === false) {
          return data;
        }

        data.hide = false;
        data.attributes['x-out-of-boundaries'] = false;
      }

      return data;
    }

    /**
     * @function
     * @memberof Modifiers
     * @argument {Object} data - The data object generated by `update` method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {Object} The data object, properly modified
     */
    function inner(data) {
      var placement = data.placement;
      var basePlacement = placement.split('-')[0];
      var _data$offsets = data.offsets,
          popper = _data$offsets.popper,
          reference = _data$offsets.reference;

      var isHoriz = ['left', 'right'].indexOf(basePlacement) !== -1;

      var subtractLength = ['top', 'left'].indexOf(basePlacement) === -1;

      popper[isHoriz ? 'left' : 'top'] = reference[basePlacement] - (subtractLength ? popper[isHoriz ? 'width' : 'height'] : 0);

      data.placement = getOppositePlacement(placement);
      data.offsets.popper = getClientRect(popper);

      return data;
    }

    /**
     * Modifier function, each modifier can have a function of this type assigned
     * to its `fn` property.<br />
     * These functions will be called on each update, this means that you must
     * make sure they are performant enough to avoid performance bottlenecks.
     *
     * @function ModifierFn
     * @argument {dataObject} data - The data object generated by `update` method
     * @argument {Object} options - Modifiers configuration and options
     * @returns {dataObject} The data object, properly modified
     */

    /**
     * Modifiers are plugins used to alter the behavior of your poppers.<br />
     * Popper.js uses a set of 9 modifiers to provide all the basic functionalities
     * needed by the library.
     *
     * Usually you don't want to override the `order`, `fn` and `onLoad` props.
     * All the other properties are configurations that could be tweaked.
     * @namespace modifiers
     */
    var modifiers = {
      /**
       * Modifier used to shift the popper on the start or end of its reference
       * element.<br />
       * It will read the variation of the `placement` property.<br />
       * It can be one either `-end` or `-start`.
       * @memberof modifiers
       * @inner
       */
      shift: {
        /** @prop {number} order=100 - Index used to define the order of execution */
        order: 100,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: shift
      },

      /**
       * The `offset` modifier can shift your popper on both its axis.
       *
       * It accepts the following units:
       * - `px` or unit-less, interpreted as pixels
       * - `%` or `%r`, percentage relative to the length of the reference element
       * - `%p`, percentage relative to the length of the popper element
       * - `vw`, CSS viewport width unit
       * - `vh`, CSS viewport height unit
       *
       * For length is intended the main axis relative to the placement of the popper.<br />
       * This means that if the placement is `top` or `bottom`, the length will be the
       * `width`. In case of `left` or `right`, it will be the `height`.
       *
       * You can provide a single value (as `Number` or `String`), or a pair of values
       * as `String` divided by a comma or one (or more) white spaces.<br />
       * The latter is a deprecated method because it leads to confusion and will be
       * removed in v2.<br />
       * Additionally, it accepts additions and subtractions between different units.
       * Note that multiplications and divisions aren't supported.
       *
       * Valid examples are:
       * ```
       * 10
       * '10%'
       * '10, 10'
       * '10%, 10'
       * '10 + 10%'
       * '10 - 5vh + 3%'
       * '-10px + 5vh, 5px - 6%'
       * ```
       * > **NB**: If you desire to apply offsets to your poppers in a way that may make them overlap
       * > with their reference element, unfortunately, you will have to disable the `flip` modifier.
       * > You can read more on this at this [issue](https://github.com/FezVrasta/popper.js/issues/373).
       *
       * @memberof modifiers
       * @inner
       */
      offset: {
        /** @prop {number} order=200 - Index used to define the order of execution */
        order: 200,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: offset,
        /** @prop {Number|String} offset=0
         * The offset value as described in the modifier description
         */
        offset: 0
      },

      /**
       * Modifier used to prevent the popper from being positioned outside the boundary.
       *
       * A scenario exists where the reference itself is not within the boundaries.<br />
       * We can say it has "escaped the boundaries" — or just "escaped".<br />
       * In this case we need to decide whether the popper should either:
       *
       * - detach from the reference and remain "trapped" in the boundaries, or
       * - if it should ignore the boundary and "escape with its reference"
       *
       * When `escapeWithReference` is set to`true` and reference is completely
       * outside its boundaries, the popper will overflow (or completely leave)
       * the boundaries in order to remain attached to the edge of the reference.
       *
       * @memberof modifiers
       * @inner
       */
      preventOverflow: {
        /** @prop {number} order=300 - Index used to define the order of execution */
        order: 300,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: preventOverflow,
        /**
         * @prop {Array} [priority=['left','right','top','bottom']]
         * Popper will try to prevent overflow following these priorities by default,
         * then, it could overflow on the left and on top of the `boundariesElement`
         */
        priority: ['left', 'right', 'top', 'bottom'],
        /**
         * @prop {number} padding=5
         * Amount of pixel used to define a minimum distance between the boundaries
         * and the popper. This makes sure the popper always has a little padding
         * between the edges of its container
         */
        padding: 5,
        /**
         * @prop {String|HTMLElement} boundariesElement='scrollParent'
         * Boundaries used by the modifier. Can be `scrollParent`, `window`,
         * `viewport` or any DOM element.
         */
        boundariesElement: 'scrollParent'
      },

      /**
       * Modifier used to make sure the reference and its popper stay near each other
       * without leaving any gap between the two. Especially useful when the arrow is
       * enabled and you want to ensure that it points to its reference element.
       * It cares only about the first axis. You can still have poppers with margin
       * between the popper and its reference element.
       * @memberof modifiers
       * @inner
       */
      keepTogether: {
        /** @prop {number} order=400 - Index used to define the order of execution */
        order: 400,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: keepTogether
      },

      /**
       * This modifier is used to move the `arrowElement` of the popper to make
       * sure it is positioned between the reference element and its popper element.
       * It will read the outer size of the `arrowElement` node to detect how many
       * pixels of conjunction are needed.
       *
       * It has no effect if no `arrowElement` is provided.
       * @memberof modifiers
       * @inner
       */
      arrow: {
        /** @prop {number} order=500 - Index used to define the order of execution */
        order: 500,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: arrow,
        /** @prop {String|HTMLElement} element='[x-arrow]' - Selector or node used as arrow */
        element: '[x-arrow]'
      },

      /**
       * Modifier used to flip the popper's placement when it starts to overlap its
       * reference element.
       *
       * Requires the `preventOverflow` modifier before it in order to work.
       *
       * **NOTE:** this modifier will interrupt the current update cycle and will
       * restart it if it detects the need to flip the placement.
       * @memberof modifiers
       * @inner
       */
      flip: {
        /** @prop {number} order=600 - Index used to define the order of execution */
        order: 600,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: flip,
        /**
         * @prop {String|Array} behavior='flip'
         * The behavior used to change the popper's placement. It can be one of
         * `flip`, `clockwise`, `counterclockwise` or an array with a list of valid
         * placements (with optional variations)
         */
        behavior: 'flip',
        /**
         * @prop {number} padding=5
         * The popper will flip if it hits the edges of the `boundariesElement`
         */
        padding: 5,
        /**
         * @prop {String|HTMLElement} boundariesElement='viewport'
         * The element which will define the boundaries of the popper position.
         * The popper will never be placed outside of the defined boundaries
         * (except if `keepTogether` is enabled)
         */
        boundariesElement: 'viewport'
      },

      /**
       * Modifier used to make the popper flow toward the inner of the reference element.
       * By default, when this modifier is disabled, the popper will be placed outside
       * the reference element.
       * @memberof modifiers
       * @inner
       */
      inner: {
        /** @prop {number} order=700 - Index used to define the order of execution */
        order: 700,
        /** @prop {Boolean} enabled=false - Whether the modifier is enabled or not */
        enabled: false,
        /** @prop {ModifierFn} */
        fn: inner
      },

      /**
       * Modifier used to hide the popper when its reference element is outside of the
       * popper boundaries. It will set a `x-out-of-boundaries` attribute which can
       * be used to hide with a CSS selector the popper when its reference is
       * out of boundaries.
       *
       * Requires the `preventOverflow` modifier before it in order to work.
       * @memberof modifiers
       * @inner
       */
      hide: {
        /** @prop {number} order=800 - Index used to define the order of execution */
        order: 800,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: hide
      },

      /**
       * Computes the style that will be applied to the popper element to gets
       * properly positioned.
       *
       * Note that this modifier will not touch the DOM, it just prepares the styles
       * so that `applyStyle` modifier can apply it. This separation is useful
       * in case you need to replace `applyStyle` with a custom implementation.
       *
       * This modifier has `850` as `order` value to maintain backward compatibility
       * with previous versions of Popper.js. Expect the modifiers ordering method
       * to change in future major versions of the library.
       *
       * @memberof modifiers
       * @inner
       */
      computeStyle: {
        /** @prop {number} order=850 - Index used to define the order of execution */
        order: 850,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: computeStyle,
        /**
         * @prop {Boolean} gpuAcceleration=true
         * If true, it uses the CSS 3D transformation to position the popper.
         * Otherwise, it will use the `top` and `left` properties
         */
        gpuAcceleration: true,
        /**
         * @prop {string} [x='bottom']
         * Where to anchor the X axis (`bottom` or `top`). AKA X offset origin.
         * Change this if your popper should grow in a direction different from `bottom`
         */
        x: 'bottom',
        /**
         * @prop {string} [x='left']
         * Where to anchor the Y axis (`left` or `right`). AKA Y offset origin.
         * Change this if your popper should grow in a direction different from `right`
         */
        y: 'right'
      },

      /**
       * Applies the computed styles to the popper element.
       *
       * All the DOM manipulations are limited to this modifier. This is useful in case
       * you want to integrate Popper.js inside a framework or view library and you
       * want to delegate all the DOM manipulations to it.
       *
       * Note that if you disable this modifier, you must make sure the popper element
       * has its position set to `absolute` before Popper.js can do its work!
       *
       * Just disable this modifier and define your own to achieve the desired effect.
       *
       * @memberof modifiers
       * @inner
       */
      applyStyle: {
        /** @prop {number} order=900 - Index used to define the order of execution */
        order: 900,
        /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
        enabled: true,
        /** @prop {ModifierFn} */
        fn: applyStyle,
        /** @prop {Function} */
        onLoad: applyStyleOnLoad,
        /**
         * @deprecated since version 1.10.0, the property moved to `computeStyle` modifier
         * @prop {Boolean} gpuAcceleration=true
         * If true, it uses the CSS 3D transformation to position the popper.
         * Otherwise, it will use the `top` and `left` properties
         */
        gpuAcceleration: undefined
      }
    };

    /**
     * The `dataObject` is an object containing all the information used by Popper.js.
     * This object is passed to modifiers and to the `onCreate` and `onUpdate` callbacks.
     * @name dataObject
     * @property {Object} data.instance The Popper.js instance
     * @property {String} data.placement Placement applied to popper
     * @property {String} data.originalPlacement Placement originally defined on init
     * @property {Boolean} data.flipped True if popper has been flipped by flip modifier
     * @property {Boolean} data.hide True if the reference element is out of boundaries, useful to know when to hide the popper
     * @property {HTMLElement} data.arrowElement Node used as arrow by arrow modifier
     * @property {Object} data.styles Any CSS property defined here will be applied to the popper. It expects the JavaScript nomenclature (eg. `marginBottom`)
     * @property {Object} data.arrowStyles Any CSS property defined here will be applied to the popper arrow. It expects the JavaScript nomenclature (eg. `marginBottom`)
     * @property {Object} data.boundaries Offsets of the popper boundaries
     * @property {Object} data.offsets The measurements of popper, reference and arrow elements
     * @property {Object} data.offsets.popper `top`, `left`, `width`, `height` values
     * @property {Object} data.offsets.reference `top`, `left`, `width`, `height` values
     * @property {Object} data.offsets.arrow] `top` and `left` offsets, only one of them will be different from 0
     */

    /**
     * Default options provided to Popper.js constructor.<br />
     * These can be overridden using the `options` argument of Popper.js.<br />
     * To override an option, simply pass an object with the same
     * structure of the `options` object, as the 3rd argument. For example:
     * ```
     * new Popper(ref, pop, {
     *   modifiers: {
     *     preventOverflow: { enabled: false }
     *   }
     * })
     * ```
     * @type {Object}
     * @static
     * @memberof Popper
     */
    var Defaults = {
      /**
       * Popper's placement.
       * @prop {Popper.placements} placement='bottom'
       */
      placement: 'bottom',

      /**
       * Set this to true if you want popper to position it self in 'fixed' mode
       * @prop {Boolean} positionFixed=false
       */
      positionFixed: false,

      /**
       * Whether events (resize, scroll) are initially enabled.
       * @prop {Boolean} eventsEnabled=true
       */
      eventsEnabled: true,

      /**
       * Set to true if you want to automatically remove the popper when
       * you call the `destroy` method.
       * @prop {Boolean} removeOnDestroy=false
       */
      removeOnDestroy: false,

      /**
       * Callback called when the popper is created.<br />
       * By default, it is set to no-op.<br />
       * Access Popper.js instance with `data.instance`.
       * @prop {onCreate}
       */
      onCreate: function onCreate() {},

      /**
       * Callback called when the popper is updated. This callback is not called
       * on the initialization/creation of the popper, but only on subsequent
       * updates.<br />
       * By default, it is set to no-op.<br />
       * Access Popper.js instance with `data.instance`.
       * @prop {onUpdate}
       */
      onUpdate: function onUpdate() {},

      /**
       * List of modifiers used to modify the offsets before they are applied to the popper.
       * They provide most of the functionalities of Popper.js.
       * @prop {modifiers}
       */
      modifiers: modifiers
    };

    /**
     * @callback onCreate
     * @param {dataObject} data
     */

    /**
     * @callback onUpdate
     * @param {dataObject} data
     */

    // Utils
    // Methods
    var Popper = function () {
      /**
       * Creates a new Popper.js instance.
       * @class Popper
       * @param {HTMLElement|referenceObject} reference - The reference element used to position the popper
       * @param {HTMLElement} popper - The HTML element used as the popper
       * @param {Object} options - Your custom options to override the ones defined in [Defaults](#defaults)
       * @return {Object} instance - The generated Popper.js instance
       */
      function Popper(reference, popper) {
        var _this = this;

        var options = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : {};
        classCallCheck(this, Popper);

        this.scheduleUpdate = function () {
          return requestAnimationFrame(_this.update);
        };

        // make update() debounced, so that it only runs at most once-per-tick
        this.update = debounce(this.update.bind(this));

        // with {} we create a new object with the options inside it
        this.options = _extends$1({}, Popper.Defaults, options);

        // init state
        this.state = {
          isDestroyed: false,
          isCreated: false,
          scrollParents: []
        };

        // get reference and popper elements (allow jQuery wrappers)
        this.reference = reference && reference.jquery ? reference[0] : reference;
        this.popper = popper && popper.jquery ? popper[0] : popper;

        // Deep merge modifiers options
        this.options.modifiers = {};
        Object.keys(_extends$1({}, Popper.Defaults.modifiers, options.modifiers)).forEach(function (name) {
          _this.options.modifiers[name] = _extends$1({}, Popper.Defaults.modifiers[name] || {}, options.modifiers ? options.modifiers[name] : {});
        });

        // Refactoring modifiers' list (Object => Array)
        this.modifiers = Object.keys(this.options.modifiers).map(function (name) {
          return _extends$1({
            name: name
          }, _this.options.modifiers[name]);
        })
        // sort the modifiers by order
        .sort(function (a, b) {
          return a.order - b.order;
        });

        // modifiers have the ability to execute arbitrary code when Popper.js get inited
        // such code is executed in the same order of its modifier
        // they could add new properties to their options configuration
        // BE AWARE: don't add options to `options.modifiers.name` but to `modifierOptions`!
        this.modifiers.forEach(function (modifierOptions) {
          if (modifierOptions.enabled && isFunction$1(modifierOptions.onLoad)) {
            modifierOptions.onLoad(_this.reference, _this.popper, _this.options, modifierOptions, _this.state);
          }
        });

        // fire the first update to position the popper in the right place
        this.update();

        var eventsEnabled = this.options.eventsEnabled;
        if (eventsEnabled) {
          // setup event listeners, they will take care of update the position in specific situations
          this.enableEventListeners();
        }

        this.state.eventsEnabled = eventsEnabled;
      }

      // We can't use class properties because they don't get listed in the
      // class prototype and break stuff like Sinon stubs


      createClass(Popper, [{
        key: 'update',
        value: function update$$1() {
          return update.call(this);
        }
      }, {
        key: 'destroy',
        value: function destroy$$1() {
          return destroy.call(this);
        }
      }, {
        key: 'enableEventListeners',
        value: function enableEventListeners$$1() {
          return enableEventListeners.call(this);
        }
      }, {
        key: 'disableEventListeners',
        value: function disableEventListeners$$1() {
          return disableEventListeners.call(this);
        }

        /**
         * Schedules an update. It will run on the next UI update available.
         * @method scheduleUpdate
         * @memberof Popper
         */


        /**
         * Collection of utilities useful when writing custom modifiers.
         * Starting from version 1.7, this method is available only if you
         * include `popper-utils.js` before `popper.js`.
         *
         * **DEPRECATION**: This way to access PopperUtils is deprecated
         * and will be removed in v2! Use the PopperUtils module directly instead.
         * Due to the high instability of the methods contained in Utils, we can't
         * guarantee them to follow semver. Use them at your own risk!
         * @static
         * @private
         * @type {Object}
         * @deprecated since version 1.8
         * @member Utils
         * @memberof Popper
         */

      }]);
      return Popper;
    }();

    /**
     * The `referenceObject` is an object that provides an interface compatible with Popper.js
     * and lets you use it as replacement of a real DOM node.<br />
     * You can use this method to position a popper relatively to a set of coordinates
     * in case you don't have a DOM node to use as reference.
     *
     * ```
     * new Popper(referenceObject, popperNode);
     * ```
     *
     * NB: This feature isn't supported in Internet Explorer 10.
     * @name referenceObject
     * @property {Function} data.getBoundingClientRect
     * A function that returns a set of coordinates compatible with the native `getBoundingClientRect` method.
     * @property {number} data.clientWidth
     * An ES6 getter that will return the width of the virtual reference element.
     * @property {number} data.clientHeight
     * An ES6 getter that will return the height of the virtual reference element.
     */


    Popper.Utils = (typeof window !== 'undefined' ? window : global).PopperUtils;
    Popper.placements = placements;
    Popper.Defaults = Defaults;
    //# sourceMappingURL=popper.js.map

    var key = '__global_unique_id__';

    var gud = function() {
      return commonjsGlobal[key] = (commonjsGlobal[key] || 0) + 1;
    };

    /**
     * Copyright (c) 2013-present, Facebook, Inc.
     *
     * This source code is licensed under the MIT license found in the
     * LICENSE file in the root directory of this source tree.
     *
     * 
     */

    function makeEmptyFunction(arg) {
      return function () {
        return arg;
      };
    }

    /**
     * This function accepts and discards inputs; it has no side effects. This is
     * primarily useful idiomatically for overridable function endpoints which
     * always need to be callable, since JS lacks a null-call idiom ala Cocoa.
     */
    var emptyFunction = function emptyFunction() {};

    emptyFunction.thatReturns = makeEmptyFunction;
    emptyFunction.thatReturnsFalse = makeEmptyFunction(false);
    emptyFunction.thatReturnsTrue = makeEmptyFunction(true);
    emptyFunction.thatReturnsNull = makeEmptyFunction(null);
    emptyFunction.thatReturnsThis = function () {
      return this;
    };
    emptyFunction.thatReturnsArgument = function (arg) {
      return arg;
    };

    var emptyFunction_1 = emptyFunction;

    /**
     * Similar to invariant but only logs a warning if the condition is not met.
     * This can be used to log issues in development environments in critical
     * paths. Removing the logging code for production environments will keep the
     * same logic and follow the same code paths.
     */

    var warning = emptyFunction_1;

    {
      var printWarning$2 = function printWarning(format) {
        for (var _len = arguments.length, args = Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
          args[_key - 1] = arguments[_key];
        }

        var argIndex = 0;
        var message = 'Warning: ' + format.replace(/%s/g, function () {
          return args[argIndex++];
        });
        if (typeof console !== 'undefined') {
          console.error(message);
        }
        try {
          // --- Welcome to debugging React ---
          // This error was thrown as a convenience so that you can use this stack
          // to find the callsite that caused this warning to fire.
          throw new Error(message);
        } catch (x) {}
      };

      warning = function warning(condition, format) {
        if (format === undefined) {
          throw new Error('`warning(condition, format, ...args)` requires a warning ' + 'message argument');
        }

        if (format.indexOf('Failed Composite propType: ') === 0) {
          return; // Ignore CompositeComponent proptype check.
        }

        if (!condition) {
          for (var _len2 = arguments.length, args = Array(_len2 > 2 ? _len2 - 2 : 0), _key2 = 2; _key2 < _len2; _key2++) {
            args[_key2 - 2] = arguments[_key2];
          }

          printWarning$2.apply(undefined, [format].concat(args));
        }
      };
    }

    var warning_1 = warning;

    var implementation = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;



    var _react2 = _interopRequireDefault(React__default);



    var _propTypes2 = _interopRequireDefault(propTypes);



    var _gud2 = _interopRequireDefault(gud);



    var _warning2 = _interopRequireDefault(warning_1);

    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

    function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

    function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

    var MAX_SIGNED_31_BIT_INT = 1073741823;

    // Inlined Object.is polyfill.
    // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
    function objectIs(x, y) {
      if (x === y) {
        return x !== 0 || 1 / x === 1 / y;
      } else {
        return x !== x && y !== y;
      }
    }

    function createEventEmitter(value) {
      var handlers = [];
      return {
        on: function on(handler) {
          handlers.push(handler);
        },
        off: function off(handler) {
          handlers = handlers.filter(function (h) {
            return h !== handler;
          });
        },
        get: function get() {
          return value;
        },
        set: function set(newValue, changedBits) {
          value = newValue;
          handlers.forEach(function (handler) {
            return handler(value, changedBits);
          });
        }
      };
    }

    function onlyChild(children) {
      return Array.isArray(children) ? children[0] : children;
    }

    function createReactContext(defaultValue, calculateChangedBits) {
      var _Provider$childContex, _Consumer$contextType;

      var contextProp = '__create-react-context-' + (0, _gud2.default)() + '__';

      var Provider = function (_Component) {
        _inherits(Provider, _Component);

        function Provider() {
          var _temp, _this, _ret;

          _classCallCheck(this, Provider);

          for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
            args[_key] = arguments[_key];
          }

          return _ret = (_temp = (_this = _possibleConstructorReturn(this, _Component.call.apply(_Component, [this].concat(args))), _this), _this.emitter = createEventEmitter(_this.props.value), _temp), _possibleConstructorReturn(_this, _ret);
        }

        Provider.prototype.getChildContext = function getChildContext() {
          var _ref;

          return _ref = {}, _ref[contextProp] = this.emitter, _ref;
        };

        Provider.prototype.componentWillReceiveProps = function componentWillReceiveProps(nextProps) {
          if (this.props.value !== nextProps.value) {
            var oldValue = this.props.value;
            var newValue = nextProps.value;
            var changedBits = void 0;

            if (objectIs(oldValue, newValue)) {
              changedBits = 0; // No change
            } else {
              changedBits = typeof calculateChangedBits === 'function' ? calculateChangedBits(oldValue, newValue) : MAX_SIGNED_31_BIT_INT;
              {
                (0, _warning2.default)((changedBits & MAX_SIGNED_31_BIT_INT) === changedBits, 'calculateChangedBits: Expected the return value to be a ' + '31-bit integer. Instead received: %s', changedBits);
              }

              changedBits |= 0;

              if (changedBits !== 0) {
                this.emitter.set(nextProps.value, changedBits);
              }
            }
          }
        };

        Provider.prototype.render = function render() {
          return this.props.children;
        };

        return Provider;
      }(React__default.Component);

      Provider.childContextTypes = (_Provider$childContex = {}, _Provider$childContex[contextProp] = _propTypes2.default.object.isRequired, _Provider$childContex);

      var Consumer = function (_Component2) {
        _inherits(Consumer, _Component2);

        function Consumer() {
          var _temp2, _this2, _ret2;

          _classCallCheck(this, Consumer);

          for (var _len2 = arguments.length, args = Array(_len2), _key2 = 0; _key2 < _len2; _key2++) {
            args[_key2] = arguments[_key2];
          }

          return _ret2 = (_temp2 = (_this2 = _possibleConstructorReturn(this, _Component2.call.apply(_Component2, [this].concat(args))), _this2), _this2.state = {
            value: _this2.getValue()
          }, _this2.onUpdate = function (newValue, changedBits) {
            var observedBits = _this2.observedBits | 0;
            if ((observedBits & changedBits) !== 0) {
              _this2.setState({ value: _this2.getValue() });
            }
          }, _temp2), _possibleConstructorReturn(_this2, _ret2);
        }

        Consumer.prototype.componentWillReceiveProps = function componentWillReceiveProps(nextProps) {
          var observedBits = nextProps.observedBits;

          this.observedBits = observedBits === undefined || observedBits === null ? MAX_SIGNED_31_BIT_INT // Subscribe to all changes by default
          : observedBits;
        };

        Consumer.prototype.componentDidMount = function componentDidMount() {
          if (this.context[contextProp]) {
            this.context[contextProp].on(this.onUpdate);
          }
          var observedBits = this.props.observedBits;

          this.observedBits = observedBits === undefined || observedBits === null ? MAX_SIGNED_31_BIT_INT // Subscribe to all changes by default
          : observedBits;
        };

        Consumer.prototype.componentWillUnmount = function componentWillUnmount() {
          if (this.context[contextProp]) {
            this.context[contextProp].off(this.onUpdate);
          }
        };

        Consumer.prototype.getValue = function getValue() {
          if (this.context[contextProp]) {
            return this.context[contextProp].get();
          } else {
            return defaultValue;
          }
        };

        Consumer.prototype.render = function render() {
          return onlyChild(this.props.children)(this.state.value);
        };

        return Consumer;
      }(React__default.Component);

      Consumer.contextTypes = (_Consumer$contextType = {}, _Consumer$contextType[contextProp] = _propTypes2.default.object, _Consumer$contextType);


      return {
        Provider: Provider,
        Consumer: Consumer
      };
    }

    exports.default = createReactContext;
    module.exports = exports['default'];
    });

    unwrapExports(implementation);

    var lib = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;



    var _react2 = _interopRequireDefault(React__default);



    var _implementation2 = _interopRequireDefault(implementation);

    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    exports.default = _react2.default.createContext || _implementation2.default;
    module.exports = exports['default'];
    });

    var createContext = unwrapExports(lib);

    var ManagerContext = createContext({
      setReferenceNode: undefined,
      referenceNode: undefined
    });

    var Manager =
    /*#__PURE__*/
    function (_React$Component) {
      inheritsLoose(Manager, _React$Component);

      function Manager() {
        var _this;

        _this = _React$Component.call(this) || this;

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "setReferenceNode", function (referenceNode) {
          if (!referenceNode || _this.state.context.referenceNode === referenceNode) {
            return;
          }

          _this.setState(function (_ref) {
            var context = _ref.context;
            return {
              context: _extends_1({}, context, {
                referenceNode: referenceNode
              })
            };
          });
        });

        _this.state = {
          context: {
            setReferenceNode: _this.setReferenceNode,
            referenceNode: undefined
          }
        };
        return _this;
      }

      var _proto = Manager.prototype;

      _proto.render = function render() {
        return React.createElement(ManagerContext.Provider, {
          value: this.state.context
        }, this.props.children);
      };

      return Manager;
    }(React.Component);

    /**
     * Takes an argument and if it's an array, returns the first item in the array,
     * otherwise returns the argument. Used for Preact compatibility.
     */
    var unwrapArray = function unwrapArray(arg) {
      return Array.isArray(arg) ? arg[0] : arg;
    };
    /**
     * Takes a maybe-undefined function and arbitrary args and invokes the function
     * only if it is defined.
     */

    var safeInvoke = function safeInvoke(fn) {
      if (typeof fn === "function") {
        for (var _len = arguments.length, args = new Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
          args[_key - 1] = arguments[_key];
        }

        return fn.apply(void 0, args);
      }
    };

    var initialStyle = {
      position: 'absolute',
      top: 0,
      left: 0,
      opacity: 0,
      pointerEvents: 'none'
    };
    var initialArrowStyle = {};
    var InnerPopper =
    /*#__PURE__*/
    function (_React$Component) {
      inheritsLoose(InnerPopper, _React$Component);

      function InnerPopper() {
        var _this;

        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        _this = _React$Component.call.apply(_React$Component, [this].concat(args)) || this;

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "state", {
          data: undefined,
          placement: undefined
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "popperInstance", void 0);

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "popperNode", null);

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "arrowNode", null);

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "setPopperNode", function (popperNode) {
          if (!popperNode || _this.popperNode === popperNode) return;
          safeInvoke(_this.props.innerRef, popperNode);
          _this.popperNode = popperNode;

          _this.updatePopperInstance();
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "setArrowNode", function (arrowNode) {
          _this.arrowNode = arrowNode;
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "updateStateModifier", {
          enabled: true,
          order: 900,
          fn: function fn(data) {
            var placement = data.placement;

            _this.setState({
              data: data,
              placement: placement
            });

            return data;
          }
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "getOptions", function () {
          return {
            placement: _this.props.placement,
            eventsEnabled: _this.props.eventsEnabled,
            positionFixed: _this.props.positionFixed,
            modifiers: _extends_1({}, _this.props.modifiers, {
              arrow: _extends_1({}, _this.props.modifiers && _this.props.modifiers.arrow, {
                enabled: !!_this.arrowNode,
                element: _this.arrowNode
              }),
              applyStyle: {
                enabled: false
              },
              updateStateModifier: _this.updateStateModifier
            })
          };
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "getPopperStyle", function () {
          return !_this.popperNode || !_this.state.data ? initialStyle : _extends_1({
            position: _this.state.data.offsets.popper.position
          }, _this.state.data.styles);
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "getPopperPlacement", function () {
          return !_this.state.data ? undefined : _this.state.placement;
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "getArrowStyle", function () {
          return !_this.arrowNode || !_this.state.data ? initialArrowStyle : _this.state.data.arrowStyles;
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "getOutOfBoundariesState", function () {
          return _this.state.data ? _this.state.data.hide : undefined;
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "destroyPopperInstance", function () {
          if (!_this.popperInstance) return;

          _this.popperInstance.destroy();

          _this.popperInstance = null;
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "updatePopperInstance", function () {
          _this.destroyPopperInstance();

          var _assertThisInitialize = assertThisInitialized(assertThisInitialized(_this)),
              popperNode = _assertThisInitialize.popperNode;

          var referenceElement = _this.props.referenceElement;
          if (!referenceElement || !popperNode) return;
          _this.popperInstance = new Popper(referenceElement, popperNode, _this.getOptions());
        });

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "scheduleUpdate", function () {
          if (_this.popperInstance) {
            _this.popperInstance.scheduleUpdate();
          }
        });

        return _this;
      }

      var _proto = InnerPopper.prototype;

      _proto.componentDidUpdate = function componentDidUpdate(prevProps, prevState) {
        // If the Popper.js options have changed, update the instance (destroy + create)
        if (this.props.placement !== prevProps.placement || this.props.referenceElement !== prevProps.referenceElement || this.props.positionFixed !== prevProps.positionFixed) {
          this.updatePopperInstance();
        } else if (this.props.eventsEnabled !== prevProps.eventsEnabled && this.popperInstance) {
          this.props.eventsEnabled ? this.popperInstance.enableEventListeners() : this.popperInstance.disableEventListeners();
        } // A placement difference in state means popper determined a new placement
        // apart from the props value. By the time the popper element is rendered with
        // the new position Popper has already measured it, if the place change triggers
        // a size change it will result in a misaligned popper. So we schedule an update to be sure.


        if (prevState.placement !== this.state.placement) {
          this.scheduleUpdate();
        }
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        safeInvoke(this.props.innerRef, null);
        this.destroyPopperInstance();
      };

      _proto.render = function render() {
        return unwrapArray(this.props.children)({
          ref: this.setPopperNode,
          style: this.getPopperStyle(),
          placement: this.getPopperPlacement(),
          outOfBoundaries: this.getOutOfBoundariesState(),
          scheduleUpdate: this.scheduleUpdate,
          arrowProps: {
            ref: this.setArrowNode,
            style: this.getArrowStyle()
          }
        });
      };

      return InnerPopper;
    }(React.Component);

    defineProperty(InnerPopper, "defaultProps", {
      placement: 'bottom',
      eventsEnabled: true,
      referenceElement: undefined,
      positionFixed: false
    });
    function Popper$1(_ref) {
      var referenceElement = _ref.referenceElement,
          props = objectWithoutPropertiesLoose(_ref, ["referenceElement"]);

      return React.createElement(ManagerContext.Consumer, null, function (_ref2) {
        var referenceNode = _ref2.referenceNode;
        return React.createElement(InnerPopper, _extends_1({
          referenceElement: referenceElement !== undefined ? referenceElement : referenceNode
        }, props));
      });
    }

    /**
     * Copyright (c) 2014-present, Facebook, Inc.
     *
     * This source code is licensed under the MIT license found in the
     * LICENSE file in the root directory of this source tree.
     */

    var warning$1 = function() {};

    {
      var printWarning$3 = function printWarning(format, args) {
        var len = arguments.length;
        args = new Array(len > 1 ? len - 1 : 0);
        for (var key = 1; key < len; key++) {
          args[key - 1] = arguments[key];
        }
        var argIndex = 0;
        var message = 'Warning: ' +
          format.replace(/%s/g, function() {
            return args[argIndex++];
          });
        if (typeof console !== 'undefined') {
          console.error(message);
        }
        try {
          // --- Welcome to debugging React ---
          // This error was thrown as a convenience so that you can use this stack
          // to find the callsite that caused this warning to fire.
          throw new Error(message);
        } catch (x) {}
      };

      warning$1 = function(condition, format, args) {
        var len = arguments.length;
        args = new Array(len > 2 ? len - 2 : 0);
        for (var key = 2; key < len; key++) {
          args[key - 2] = arguments[key];
        }
        if (format === undefined) {
          throw new Error(
              '`warning(condition, format, ...args)` requires a warning ' +
              'message argument'
          );
        }
        if (!condition) {
          printWarning$3.apply(null, [format].concat(args));
        }
      };
    }

    var warning_1$1 = warning$1;

    var InnerReference =
    /*#__PURE__*/
    function (_React$Component) {
      inheritsLoose(InnerReference, _React$Component);

      function InnerReference() {
        var _this;

        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        _this = _React$Component.call.apply(_React$Component, [this].concat(args)) || this;

        defineProperty(assertThisInitialized(assertThisInitialized(_this)), "refHandler", function (node) {
          safeInvoke(_this.props.innerRef, node);
          safeInvoke(_this.props.setReferenceNode, node);
        });

        return _this;
      }

      var _proto = InnerReference.prototype;

      _proto.render = function render() {
        warning_1$1(Boolean(this.props.setReferenceNode), '`Reference` should not be used outside of a `Manager` component.');
        return unwrapArray(this.props.children)({
          ref: this.refHandler
        });
      };

      return InnerReference;
    }(React.Component);

    function Reference(props) {
      return React.createElement(ManagerContext.Consumer, null, function (_ref) {
        var setReferenceNode = _ref.setReferenceNode;
        return React.createElement(InnerReference, _extends_1({
          setReferenceNode: setReferenceNode
        }, props));
      });
    }

    // Public components
     // Public types

    /**
     * DropdownContext
     * {
     *  toggle: PropTypes.func.isRequired,
     *  isOpen: PropTypes.bool.isRequired,
     *  direction: PropTypes.oneOf(['up', 'down', 'left', 'right']).isRequired,
     *  inNavbar: PropTypes.bool.isRequired,
     * }
     */

    var DropdownContext = React__default.createContext({});

    var propTypes$d = {
      disabled: propTypes.bool,
      direction: propTypes.oneOf(['up', 'down', 'left', 'right']),
      group: propTypes.bool,
      isOpen: propTypes.bool,
      nav: propTypes.bool,
      active: propTypes.bool,
      addonType: propTypes.oneOfType([propTypes.bool, propTypes.oneOf(['prepend', 'append'])]),
      size: propTypes.string,
      tag: tagPropType,
      toggle: propTypes.func,
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object,
      inNavbar: propTypes.bool,
      setActiveFromChild: propTypes.bool
    };
    var defaultProps$2 = {
      isOpen: false,
      direction: 'down',
      nav: false,
      active: false,
      addonType: false,
      inNavbar: false,
      setActiveFromChild: false
    };

    var Dropdown =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Dropdown, _React$Component);

      function Dropdown(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.addEvents = _this.addEvents.bind(_assertThisInitialized(_this));
        _this.handleDocumentClick = _this.handleDocumentClick.bind(_assertThisInitialized(_this));
        _this.handleKeyDown = _this.handleKeyDown.bind(_assertThisInitialized(_this));
        _this.removeEvents = _this.removeEvents.bind(_assertThisInitialized(_this));
        _this.toggle = _this.toggle.bind(_assertThisInitialized(_this));
        _this.containerRef = React__default.createRef();
        return _this;
      }

      var _proto = Dropdown.prototype;

      _proto.getContextValue = function getContextValue() {
        return {
          toggle: this.props.toggle,
          isOpen: this.props.isOpen,
          direction: this.props.direction === 'down' && this.props.dropup ? 'up' : this.props.direction,
          inNavbar: this.props.inNavbar
        };
      };

      _proto.componentDidMount = function componentDidMount() {
        this.handleProps();
      };

      _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
        if (this.props.isOpen !== prevProps.isOpen) {
          this.handleProps();
        }
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        this.removeEvents();
      };

      _proto.getContainer = function getContainer() {
        return this.containerRef.current;
      };

      _proto.getMenuCtrl = function getMenuCtrl() {
        if (this._$menuCtrl) return this._$menuCtrl;
        this._$menuCtrl = this.getContainer().querySelector('[aria-expanded]');
        return this._$menuCtrl;
      };

      _proto.getMenuItems = function getMenuItems() {
        return [].slice.call(this.getContainer().querySelectorAll('[role="menuitem"]'));
      };

      _proto.addEvents = function addEvents() {
        var _this2 = this;

        ['click', 'touchstart', 'keyup'].forEach(function (event) {
          return document.addEventListener(event, _this2.handleDocumentClick, true);
        });
      };

      _proto.removeEvents = function removeEvents() {
        var _this3 = this;

        ['click', 'touchstart', 'keyup'].forEach(function (event) {
          return document.removeEventListener(event, _this3.handleDocumentClick, true);
        });
      };

      _proto.handleDocumentClick = function handleDocumentClick(e) {
        if (e && (e.which === 3 || e.type === 'keyup' && e.which !== keyCodes.tab)) return;
        var container = this.getContainer();

        if (container.contains(e.target) && container !== e.target && (e.type !== 'keyup' || e.which === keyCodes.tab)) {
          return;
        }

        this.toggle(e);
      };

      _proto.handleKeyDown = function handleKeyDown(e) {
        var _this4 = this;

        if (/input|textarea/i.test(e.target.tagName) || keyCodes.tab === e.which && e.target.getAttribute('role') !== 'menuitem') {
          return;
        }

        e.preventDefault();
        if (this.props.disabled) return;

        if (this.getMenuCtrl() === e.target) {
          if (!this.props.isOpen && [keyCodes.space, keyCodes.enter, keyCodes.up, keyCodes.down].indexOf(e.which) > -1) {
            this.toggle(e);
            setTimeout(function () {
              return _this4.getMenuItems()[0].focus();
            });
          }
        }

        if (this.props.isOpen && e.target.getAttribute('role') === 'menuitem') {
          if ([keyCodes.tab, keyCodes.esc].indexOf(e.which) > -1) {
            this.toggle(e);
            this.getMenuCtrl().focus();
          } else if ([keyCodes.space, keyCodes.enter].indexOf(e.which) > -1) {
            e.target.click();
            this.getMenuCtrl().focus();
          } else if ([keyCodes.down, keyCodes.up].indexOf(e.which) > -1 || [keyCodes.n, keyCodes.p].indexOf(e.which) > -1 && e.ctrlKey) {
            var $menuitems = this.getMenuItems();
            var index = $menuitems.indexOf(e.target);

            if (keyCodes.up === e.which || keyCodes.p === e.which && e.ctrlKey) {
              index = index !== 0 ? index - 1 : $menuitems.length - 1;
            } else if (keyCodes.down === e.which || keyCodes.n === e.which && e.ctrlKey) {
              index = index === $menuitems.length - 1 ? 0 : index + 1;
            }

            $menuitems[index].focus();
          } else if (keyCodes.end === e.which) {
            var _$menuitems = this.getMenuItems();

            _$menuitems[_$menuitems.length - 1].focus();
          } else if (keyCodes.home === e.which) {
            var _$menuitems2 = this.getMenuItems();

            _$menuitems2[0].focus();
          } else if (e.which >= 48 && e.which <= 90) {
            var _$menuitems3 = this.getMenuItems();

            var charPressed = String.fromCharCode(e.which).toLowerCase();

            for (var i = 0; i < _$menuitems3.length; i += 1) {
              var firstLetter = _$menuitems3[i].textContent && _$menuitems3[i].textContent[0].toLowerCase();

              if (firstLetter === charPressed) {
                _$menuitems3[i].focus();

                break;
              }
            }
          }
        }
      };

      _proto.handleProps = function handleProps() {
        if (this.props.isOpen) {
          this.addEvents();
        } else {
          this.removeEvents();
        }
      };

      _proto.toggle = function toggle(e) {
        if (this.props.disabled) {
          return e && e.preventDefault();
        }

        return this.props.toggle(e);
      };

      _proto.render = function render() {
        var _classNames, _ref;

        var _omit = omit(this.props, ['toggle', 'disabled', 'inNavbar']),
            className = _omit.className,
            cssModule = _omit.cssModule,
            direction = _omit.direction,
            isOpen = _omit.isOpen,
            group = _omit.group,
            size = _omit.size,
            nav = _omit.nav,
            setActiveFromChild = _omit.setActiveFromChild,
            active = _omit.active,
            addonType = _omit.addonType,
            tag = _omit.tag,
            attrs = _objectWithoutPropertiesLoose(_omit, ["className", "cssModule", "direction", "isOpen", "group", "size", "nav", "setActiveFromChild", "active", "addonType", "tag"]);

        var Tag = tag || (nav ? 'li' : 'div');
        var subItemIsActive = false;

        if (setActiveFromChild) {
          React__default.Children.map(this.props.children[1].props.children, function (dropdownItem) {
            if (dropdownItem && dropdownItem.props.active) subItemIsActive = true;
          });
        }

        var classes = mapToCssModules(classnames(className, direction !== 'down' && "drop" + direction, nav && active ? 'active' : false, setActiveFromChild && subItemIsActive ? 'active' : false, (_classNames = {}, _classNames["input-group-" + addonType] = addonType, _classNames['btn-group'] = group, _classNames["btn-group-" + size] = !!size, _classNames.dropdown = !group && !addonType, _classNames.show = isOpen, _classNames['nav-item'] = nav, _classNames)), cssModule);
        return React__default.createElement(DropdownContext.Provider, {
          value: this.getContextValue()
        }, React__default.createElement(Manager, null, React__default.createElement(Tag, _extends({}, attrs, (_ref = {}, _ref[typeof Tag === 'string' ? 'ref' : 'innerRef'] = this.containerRef, _ref), {
          onKeyDown: this.handleKeyDown,
          className: classes
        }))));
      };

      return Dropdown;
    }(React__default.Component);

    Dropdown.propTypes = propTypes$d;
    Dropdown.defaultProps = defaultProps$2;

    var propTypes$e = {
      children: propTypes.node
    };

    var ButtonDropdown = function ButtonDropdown(props) {
      return React__default.createElement(Dropdown, _extends({
        group: true
      }, props));
    };

    ButtonDropdown.propTypes = propTypes$e;

    var propTypes$f = {
      tag: tagPropType,
      'aria-label': propTypes.string,
      className: propTypes.string,
      cssModule: propTypes.object,
      role: propTypes.string,
      size: propTypes.string,
      vertical: propTypes.bool
    };
    var defaultProps$3 = {
      tag: 'div',
      role: 'group'
    };

    var ButtonGroup = function ButtonGroup(props) {
      var className = props.className,
          cssModule = props.cssModule,
          size = props.size,
          vertical = props.vertical,
          Tag = props.tag,
          attributes = _objectWithoutPropertiesLoose(props, ["className", "cssModule", "size", "vertical", "tag"]);

      var classes = mapToCssModules(classnames(className, size ? 'btn-group-' + size : false, vertical ? 'btn-group-vertical' : 'btn-group'), cssModule);
      return React__default.createElement(Tag, _extends({}, attributes, {
        className: classes
      }));
    };

    ButtonGroup.propTypes = propTypes$f;
    ButtonGroup.defaultProps = defaultProps$3;

    var propTypes$g = {
      tag: tagPropType,
      'aria-label': propTypes.string,
      className: propTypes.string,
      cssModule: propTypes.object,
      role: propTypes.string
    };

    var propTypes$h = {
      children: propTypes.node,
      active: propTypes.bool,
      disabled: propTypes.bool,
      divider: propTypes.bool,
      tag: tagPropType,
      header: propTypes.bool,
      onClick: propTypes.func,
      className: propTypes.string,
      cssModule: propTypes.object,
      toggle: propTypes.bool
    };
    var defaultProps$4 = {
      tag: 'button',
      toggle: true
    };

    var DropdownItem =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(DropdownItem, _React$Component);

      function DropdownItem(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.onClick = _this.onClick.bind(_assertThisInitialized(_this));
        _this.getTabIndex = _this.getTabIndex.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = DropdownItem.prototype;

      _proto.onClick = function onClick(e) {
        if (this.props.disabled || this.props.header || this.props.divider) {
          e.preventDefault();
          return;
        }

        if (this.props.onClick) {
          this.props.onClick(e);
        }

        if (this.props.toggle) {
          this.context.toggle(e);
        }
      };

      _proto.getTabIndex = function getTabIndex() {
        if (this.props.disabled || this.props.header || this.props.divider) {
          return '-1';
        }

        return '0';
      };

      _proto.render = function render() {
        var tabIndex = this.getTabIndex();
        var role = tabIndex > -1 ? 'menuitem' : undefined;

        var _omit = omit(this.props, ['toggle']),
            className = _omit.className,
            cssModule = _omit.cssModule,
            divider = _omit.divider,
            Tag = _omit.tag,
            header = _omit.header,
            active = _omit.active,
            props = _objectWithoutPropertiesLoose(_omit, ["className", "cssModule", "divider", "tag", "header", "active"]);

        var classes = mapToCssModules(classnames(className, {
          disabled: props.disabled,
          'dropdown-item': !divider && !header,
          active: active,
          'dropdown-header': header,
          'dropdown-divider': divider
        }), cssModule);

        if (Tag === 'button') {
          if (header) {
            Tag = 'h6';
          } else if (divider) {
            Tag = 'div';
          } else if (props.href) {
            Tag = 'a';
          }
        }

        return React__default.createElement(Tag, _extends({
          type: Tag === 'button' && (props.onClick || this.props.toggle) ? 'button' : undefined
        }, props, {
          tabIndex: tabIndex,
          role: role,
          className: classes,
          onClick: this.onClick
        }));
      };

      return DropdownItem;
    }(React__default.Component);

    DropdownItem.propTypes = propTypes$h;
    DropdownItem.defaultProps = defaultProps$4;
    DropdownItem.contextType = DropdownContext;

    function _defineProperty$1(obj, key, value) {
      if (key in obj) {
        Object.defineProperty(obj, key, {
          value: value,
          enumerable: true,
          configurable: true,
          writable: true
        });
      } else {
        obj[key] = value;
      }

      return obj;
    }

    function _objectSpread(target) {
      for (var i = 1; i < arguments.length; i++) {
        var source = arguments[i] != null ? arguments[i] : {};
        var ownKeys = Object.keys(source);

        if (typeof Object.getOwnPropertySymbols === 'function') {
          ownKeys = ownKeys.concat(Object.getOwnPropertySymbols(source).filter(function (sym) {
            return Object.getOwnPropertyDescriptor(source, sym).enumerable;
          }));
        }

        ownKeys.forEach(function (key) {
          _defineProperty$1(target, key, source[key]);
        });
      }

      return target;
    }

    var propTypes$i = {
      tag: tagPropType,
      children: propTypes.node.isRequired,
      right: propTypes.bool,
      flip: propTypes.bool,
      modifiers: propTypes.object,
      className: propTypes.string,
      cssModule: propTypes.object,
      persist: propTypes.bool
    };
    var defaultProps$5 = {
      tag: 'div',
      flip: true
    };
    var noFlipModifier = {
      flip: {
        enabled: false
      }
    };
    var directionPositionMap = {
      up: 'top',
      left: 'left',
      right: 'right',
      down: 'bottom'
    };

    var DropdownMenu =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(DropdownMenu, _React$Component);

      function DropdownMenu() {
        return _React$Component.apply(this, arguments) || this;
      }

      var _proto = DropdownMenu.prototype;

      _proto.render = function render() {
        var _this = this;

        var _this$props = this.props,
            className = _this$props.className,
            cssModule = _this$props.cssModule,
            right = _this$props.right,
            tag = _this$props.tag,
            flip = _this$props.flip,
            modifiers = _this$props.modifiers,
            persist = _this$props.persist,
            attrs = _objectWithoutPropertiesLoose(_this$props, ["className", "cssModule", "right", "tag", "flip", "modifiers", "persist"]);

        var classes = mapToCssModules(classnames(className, 'dropdown-menu', {
          'dropdown-menu-right': right,
          show: this.context.isOpen
        }), cssModule);
        var Tag = tag;

        if (persist || this.context.isOpen && !this.context.inNavbar) {
          var position1 = directionPositionMap[this.context.direction] || 'bottom';
          var position2 = right ? 'end' : 'start';
          var poperPlacement = position1 + "-" + position2;
          var poperModifiers = !flip ? _objectSpread({}, modifiers, noFlipModifier) : modifiers;
          return React__default.createElement(Popper$1, {
            placement: poperPlacement,
            modifiers: poperModifiers
          }, function (_ref) {
            var ref = _ref.ref,
                style = _ref.style,
                placement = _ref.placement;
            return React__default.createElement(Tag, _extends({
              tabIndex: "-1",
              role: "menu",
              ref: ref,
              style: style
            }, attrs, {
              "aria-hidden": !_this.context.isOpen,
              className: classes,
              "x-placement": placement
            }));
          });
        }

        return React__default.createElement(Tag, _extends({
          tabIndex: "-1",
          role: "menu"
        }, attrs, {
          "aria-hidden": !this.context.isOpen,
          className: classes,
          "x-placement": attrs.placement
        }));
      };

      return DropdownMenu;
    }(React__default.Component);
    DropdownMenu.propTypes = propTypes$i;
    DropdownMenu.defaultProps = defaultProps$5;
    DropdownMenu.contextType = DropdownContext;

    var propTypes$j = {
      caret: propTypes.bool,
      color: propTypes.string,
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object,
      disabled: propTypes.bool,
      onClick: propTypes.func,
      'aria-haspopup': propTypes.bool,
      split: propTypes.bool,
      tag: tagPropType,
      nav: propTypes.bool
    };
    var defaultProps$6 = {
      'aria-haspopup': true,
      color: 'secondary'
    };

    var DropdownToggle =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(DropdownToggle, _React$Component);

      function DropdownToggle(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.onClick = _this.onClick.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = DropdownToggle.prototype;

      _proto.onClick = function onClick(e) {
        if (this.props.disabled) {
          e.preventDefault();
          return;
        }

        if (this.props.nav && !this.props.tag) {
          e.preventDefault();
        }

        if (this.props.onClick) {
          this.props.onClick(e);
        }

        this.context.toggle(e);
      };

      _proto.render = function render() {
        var _this2 = this;

        var _this$props = this.props,
            className = _this$props.className,
            color = _this$props.color,
            cssModule = _this$props.cssModule,
            caret = _this$props.caret,
            split = _this$props.split,
            nav = _this$props.nav,
            tag = _this$props.tag,
            props = _objectWithoutPropertiesLoose(_this$props, ["className", "color", "cssModule", "caret", "split", "nav", "tag"]);

        var ariaLabel = props['aria-label'] || 'Toggle Dropdown';
        var classes = mapToCssModules(classnames(className, {
          'dropdown-toggle': caret || split,
          'dropdown-toggle-split': split,
          'nav-link': nav
        }), cssModule);
        var children = props.children || React__default.createElement("span", {
          className: "sr-only"
        }, ariaLabel);
        var Tag;

        if (nav && !tag) {
          Tag = 'a';
          props.href = '#';
        } else if (!tag) {
          Tag = Button;
          props.color = color;
          props.cssModule = cssModule;
        } else {
          Tag = tag;
        }

        if (this.context.inNavbar) {
          return React__default.createElement(Tag, _extends({}, props, {
            className: classes,
            onClick: this.onClick,
            "aria-expanded": this.context.isOpen,
            children: children
          }));
        }

        return React__default.createElement(Reference, null, function (_ref) {
          var _ref2;

          var ref = _ref.ref;
          return React__default.createElement(Tag, _extends({}, props, (_ref2 = {}, _ref2[typeof Tag === 'string' ? 'ref' : 'innerRef'] = ref, _ref2), {
            className: classes,
            onClick: _this2.onClick,
            "aria-expanded": _this2.context.isOpen,
            children: children
          }));
        });
      };

      return DropdownToggle;
    }(React__default.Component);

    DropdownToggle.propTypes = propTypes$j;
    DropdownToggle.defaultProps = defaultProps$6;
    DropdownToggle.contextType = DropdownContext;

    var interopRequireDefault = createCommonjsModule(function (module) {
    function _interopRequireDefault(obj) {
      return obj && obj.__esModule ? obj : {
        "default": obj
      };
    }

    module.exports = _interopRequireDefault;
    });

    unwrapExports(interopRequireDefault);

    var hasClass_1 = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;
    exports.default = hasClass;

    function hasClass(element, className) {
      if (element.classList) return !!className && element.classList.contains(className);else return (" " + (element.className.baseVal || element.className) + " ").indexOf(" " + className + " ") !== -1;
    }

    module.exports = exports["default"];
    });

    unwrapExports(hasClass_1);

    var addClass_1 = createCommonjsModule(function (module, exports) {



    exports.__esModule = true;
    exports.default = addClass;

    var _hasClass = interopRequireDefault(hasClass_1);

    function addClass(element, className) {
      if (element.classList) element.classList.add(className);else if (!(0, _hasClass.default)(element, className)) if (typeof element.className === 'string') element.className = element.className + ' ' + className;else element.setAttribute('class', (element.className && element.className.baseVal || '') + ' ' + className);
    }

    module.exports = exports["default"];
    });

    unwrapExports(addClass_1);

    function replaceClassName(origClass, classToRemove) {
      return origClass.replace(new RegExp('(^|\\s)' + classToRemove + '(?:\\s|$)', 'g'), '$1').replace(/\s+/g, ' ').replace(/^\s*|\s*$/g, '');
    }

    var removeClass = function removeClass(element, className) {
      if (element.classList) element.classList.remove(className);else if (typeof element.className === 'string') element.className = replaceClassName(element.className, className);else element.setAttribute('class', replaceClassName(element.className && element.className.baseVal || '', className));
    };

    /**
     * Copyright (c) 2013-present, Facebook, Inc.
     *
     * This source code is licensed under the MIT license found in the
     * LICENSE file in the root directory of this source tree.
     */

    function componentWillMount() {
      // Call this.constructor.gDSFP to support sub-classes.
      var state = this.constructor.getDerivedStateFromProps(this.props, this.state);
      if (state !== null && state !== undefined) {
        this.setState(state);
      }
    }

    function componentWillReceiveProps(nextProps) {
      // Call this.constructor.gDSFP to support sub-classes.
      // Use the setState() updater to ensure state isn't stale in certain edge cases.
      function updater(prevState) {
        var state = this.constructor.getDerivedStateFromProps(nextProps, prevState);
        return state !== null && state !== undefined ? state : null;
      }
      // Binding "this" is important for shallow renderer support.
      this.setState(updater.bind(this));
    }

    function componentWillUpdate(nextProps, nextState) {
      try {
        var prevProps = this.props;
        var prevState = this.state;
        this.props = nextProps;
        this.state = nextState;
        this.__reactInternalSnapshotFlag = true;
        this.__reactInternalSnapshot = this.getSnapshotBeforeUpdate(
          prevProps,
          prevState
        );
      } finally {
        this.props = prevProps;
        this.state = prevState;
      }
    }

    // React may warn about cWM/cWRP/cWU methods being deprecated.
    // Add a flag to suppress these warnings for this special case.
    componentWillMount.__suppressDeprecationWarning = true;
    componentWillReceiveProps.__suppressDeprecationWarning = true;
    componentWillUpdate.__suppressDeprecationWarning = true;

    function polyfill(Component) {
      var prototype = Component.prototype;

      if (!prototype || !prototype.isReactComponent) {
        throw new Error('Can only polyfill class components');
      }

      if (
        typeof Component.getDerivedStateFromProps !== 'function' &&
        typeof prototype.getSnapshotBeforeUpdate !== 'function'
      ) {
        return Component;
      }

      // If new component APIs are defined, "unsafe" lifecycles won't be called.
      // Error if any of these lifecycles are present,
      // Because they would work differently between older and newer (16.3+) versions of React.
      var foundWillMountName = null;
      var foundWillReceivePropsName = null;
      var foundWillUpdateName = null;
      if (typeof prototype.componentWillMount === 'function') {
        foundWillMountName = 'componentWillMount';
      } else if (typeof prototype.UNSAFE_componentWillMount === 'function') {
        foundWillMountName = 'UNSAFE_componentWillMount';
      }
      if (typeof prototype.componentWillReceiveProps === 'function') {
        foundWillReceivePropsName = 'componentWillReceiveProps';
      } else if (typeof prototype.UNSAFE_componentWillReceiveProps === 'function') {
        foundWillReceivePropsName = 'UNSAFE_componentWillReceiveProps';
      }
      if (typeof prototype.componentWillUpdate === 'function') {
        foundWillUpdateName = 'componentWillUpdate';
      } else if (typeof prototype.UNSAFE_componentWillUpdate === 'function') {
        foundWillUpdateName = 'UNSAFE_componentWillUpdate';
      }
      if (
        foundWillMountName !== null ||
        foundWillReceivePropsName !== null ||
        foundWillUpdateName !== null
      ) {
        var componentName = Component.displayName || Component.name;
        var newApiName =
          typeof Component.getDerivedStateFromProps === 'function'
            ? 'getDerivedStateFromProps()'
            : 'getSnapshotBeforeUpdate()';

        throw Error(
          'Unsafe legacy lifecycles will not be called for components using new component APIs.\n\n' +
            componentName +
            ' uses ' +
            newApiName +
            ' but also contains the following legacy lifecycles:' +
            (foundWillMountName !== null ? '\n  ' + foundWillMountName : '') +
            (foundWillReceivePropsName !== null
              ? '\n  ' + foundWillReceivePropsName
              : '') +
            (foundWillUpdateName !== null ? '\n  ' + foundWillUpdateName : '') +
            '\n\nThe above lifecycles should be removed. Learn more about this warning here:\n' +
            'https://fb.me/react-async-component-lifecycle-hooks'
        );
      }

      // React <= 16.2 does not support static getDerivedStateFromProps.
      // As a workaround, use cWM and cWRP to invoke the new static lifecycle.
      // Newer versions of React will ignore these lifecycles if gDSFP exists.
      if (typeof Component.getDerivedStateFromProps === 'function') {
        prototype.componentWillMount = componentWillMount;
        prototype.componentWillReceiveProps = componentWillReceiveProps;
      }

      // React <= 16.2 does not support getSnapshotBeforeUpdate.
      // As a workaround, use cWU to invoke the new lifecycle.
      // Newer versions of React will ignore that lifecycle if gSBU exists.
      if (typeof prototype.getSnapshotBeforeUpdate === 'function') {
        if (typeof prototype.componentDidUpdate !== 'function') {
          throw new Error(
            'Cannot polyfill getSnapshotBeforeUpdate() for components that do not define componentDidUpdate() on the prototype'
          );
        }

        prototype.componentWillUpdate = componentWillUpdate;

        var componentDidUpdate = prototype.componentDidUpdate;

        prototype.componentDidUpdate = function componentDidUpdatePolyfill(
          prevProps,
          prevState,
          maybeSnapshot
        ) {
          // 16.3+ will not execute our will-update method;
          // It will pass a snapshot value to did-update though.
          // Older versions will require our polyfilled will-update value.
          // We need to handle both cases, but can't just check for the presence of "maybeSnapshot",
          // Because for <= 15.x versions this might be a "prevContext" object.
          // We also can't just check "__reactInternalSnapshot",
          // Because get-snapshot might return a falsy value.
          // So check for the explicit __reactInternalSnapshotFlag flag to determine behavior.
          var snapshot = this.__reactInternalSnapshotFlag
            ? this.__reactInternalSnapshot
            : maybeSnapshot;

          componentDidUpdate.call(this, prevProps, prevState, snapshot);
        };
      }

      return Component;
    }

    var reactLifecyclesCompat_es = /*#__PURE__*/Object.freeze({
        polyfill: polyfill
    });

    var PropTypes = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;
    exports.classNamesShape = exports.timeoutsShape = void 0;

    var _propTypes = _interopRequireDefault(propTypes);

    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    var timeoutsShape = _propTypes.default.oneOfType([_propTypes.default.number, _propTypes.default.shape({
      enter: _propTypes.default.number,
      exit: _propTypes.default.number,
      appear: _propTypes.default.number
    }).isRequired]);
    exports.timeoutsShape = timeoutsShape;
    var classNamesShape = _propTypes.default.oneOfType([_propTypes.default.string, _propTypes.default.shape({
      enter: _propTypes.default.string,
      exit: _propTypes.default.string,
      active: _propTypes.default.string
    }), _propTypes.default.shape({
      enter: _propTypes.default.string,
      enterDone: _propTypes.default.string,
      enterActive: _propTypes.default.string,
      exit: _propTypes.default.string,
      exitDone: _propTypes.default.string,
      exitActive: _propTypes.default.string
    })]);
    exports.classNamesShape = classNamesShape;
    });

    unwrapExports(PropTypes);
    var PropTypes_1 = PropTypes.classNamesShape;
    var PropTypes_2 = PropTypes.timeoutsShape;

    var Transition_1 = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;
    exports.default = exports.EXITING = exports.ENTERED = exports.ENTERING = exports.EXITED = exports.UNMOUNTED = void 0;

    var PropTypes$1 = _interopRequireWildcard(propTypes);

    var _react = _interopRequireDefault(React__default);

    var _reactDom = _interopRequireDefault(ReactDOM);





    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) { var desc = Object.defineProperty && Object.getOwnPropertyDescriptor ? Object.getOwnPropertyDescriptor(obj, key) : {}; if (desc.get || desc.set) { Object.defineProperty(newObj, key, desc); } else { newObj[key] = obj[key]; } } } } newObj.default = obj; return newObj; } }

    function _objectWithoutPropertiesLoose(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

    function _inheritsLoose(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }

    var UNMOUNTED = 'unmounted';
    exports.UNMOUNTED = UNMOUNTED;
    var EXITED = 'exited';
    exports.EXITED = EXITED;
    var ENTERING = 'entering';
    exports.ENTERING = ENTERING;
    var ENTERED = 'entered';
    exports.ENTERED = ENTERED;
    var EXITING = 'exiting';
    /**
     * The Transition component lets you describe a transition from one component
     * state to another _over time_ with a simple declarative API. Most commonly
     * it's used to animate the mounting and unmounting of a component, but can also
     * be used to describe in-place transition states as well.
     *
     * ---
     *
     * **Note**: `Transition` is a platform-agnostic base component. If you're using
     * transitions in CSS, you'll probably want to use
     * [`CSSTransition`](https://reactcommunity.org/react-transition-group/css-transition)
     * instead. It inherits all the features of `Transition`, but contains
     * additional features necessary to play nice with CSS transitions (hence the
     * name of the component).
     *
     * ---
     *
     * By default the `Transition` component does not alter the behavior of the
     * component it renders, it only tracks "enter" and "exit" states for the
     * components. It's up to you to give meaning and effect to those states. For
     * example we can add styles to a component when it enters or exits:
     *
     * ```jsx
     * import { Transition } from 'react-transition-group';
     *
     * const duration = 300;
     *
     * const defaultStyle = {
     *   transition: `opacity ${duration}ms ease-in-out`,
     *   opacity: 0,
     * }
     *
     * const transitionStyles = {
     *   entering: { opacity: 0 },
     *   entered:  { opacity: 1 },
     * };
     *
     * const Fade = ({ in: inProp }) => (
     *   <Transition in={inProp} timeout={duration}>
     *     {state => (
     *       <div style={{
     *         ...defaultStyle,
     *         ...transitionStyles[state]
     *       }}>
     *         I'm a fade Transition!
     *       </div>
     *     )}
     *   </Transition>
     * );
     * ```
     *
     * There are 4 main states a Transition can be in:
     *  - `'entering'`
     *  - `'entered'`
     *  - `'exiting'`
     *  - `'exited'`
     *
     * Transition state is toggled via the `in` prop. When `true` the component
     * begins the "Enter" stage. During this stage, the component will shift from
     * its current transition state, to `'entering'` for the duration of the
     * transition and then to the `'entered'` stage once it's complete. Let's take
     * the following example (we'll use the
     * [useState](https://reactjs.org/docs/hooks-reference.html#usestate) hook):
     *
     * ```jsx
     * function App() {
     *   const [inProp, setInProp] = useState(false);
     *   return (
     *     <div>
     *       <Transition in={inProp} timeout={500}>
     *         {state => (
     *           // ...
     *         )}
     *       </Transition>
     *       <button onClick={() => setInProp(true)}>
     *         Click to Enter
     *       </button>
     *     </div>
     *   );
     * }
     * ```
     *
     * When the button is clicked the component will shift to the `'entering'` state
     * and stay there for 500ms (the value of `timeout`) before it finally switches
     * to `'entered'`.
     *
     * When `in` is `false` the same thing happens except the state moves from
     * `'exiting'` to `'exited'`.
     */

    exports.EXITING = EXITING;

    var Transition =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Transition, _React$Component);

      function Transition(props, context) {
        var _this;

        _this = _React$Component.call(this, props, context) || this;
        var parentGroup = context.transitionGroup; // In the context of a TransitionGroup all enters are really appears

        var appear = parentGroup && !parentGroup.isMounting ? props.enter : props.appear;
        var initialStatus;
        _this.appearStatus = null;

        if (props.in) {
          if (appear) {
            initialStatus = EXITED;
            _this.appearStatus = ENTERING;
          } else {
            initialStatus = ENTERED;
          }
        } else {
          if (props.unmountOnExit || props.mountOnEnter) {
            initialStatus = UNMOUNTED;
          } else {
            initialStatus = EXITED;
          }
        }

        _this.state = {
          status: initialStatus
        };
        _this.nextCallback = null;
        return _this;
      }

      var _proto = Transition.prototype;

      _proto.getChildContext = function getChildContext() {
        return {
          transitionGroup: null // allows for nested Transitions

        };
      };

      Transition.getDerivedStateFromProps = function getDerivedStateFromProps(_ref, prevState) {
        var nextIn = _ref.in;

        if (nextIn && prevState.status === UNMOUNTED) {
          return {
            status: EXITED
          };
        }

        return null;
      }; // getSnapshotBeforeUpdate(prevProps) {
      //   let nextStatus = null
      //   if (prevProps !== this.props) {
      //     const { status } = this.state
      //     if (this.props.in) {
      //       if (status !== ENTERING && status !== ENTERED) {
      //         nextStatus = ENTERING
      //       }
      //     } else {
      //       if (status === ENTERING || status === ENTERED) {
      //         nextStatus = EXITING
      //       }
      //     }
      //   }
      //   return { nextStatus }
      // }


      _proto.componentDidMount = function componentDidMount() {
        this.updateStatus(true, this.appearStatus);
      };

      _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
        var nextStatus = null;

        if (prevProps !== this.props) {
          var status = this.state.status;

          if (this.props.in) {
            if (status !== ENTERING && status !== ENTERED) {
              nextStatus = ENTERING;
            }
          } else {
            if (status === ENTERING || status === ENTERED) {
              nextStatus = EXITING;
            }
          }
        }

        this.updateStatus(false, nextStatus);
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        this.cancelNextCallback();
      };

      _proto.getTimeouts = function getTimeouts() {
        var timeout = this.props.timeout;
        var exit, enter, appear;
        exit = enter = appear = timeout;

        if (timeout != null && typeof timeout !== 'number') {
          exit = timeout.exit;
          enter = timeout.enter; // TODO: remove fallback for next major

          appear = timeout.appear !== undefined ? timeout.appear : enter;
        }

        return {
          exit: exit,
          enter: enter,
          appear: appear
        };
      };

      _proto.updateStatus = function updateStatus(mounting, nextStatus) {
        if (mounting === void 0) {
          mounting = false;
        }

        if (nextStatus !== null) {
          // nextStatus will always be ENTERING or EXITING.
          this.cancelNextCallback();

          var node = _reactDom.default.findDOMNode(this);

          if (nextStatus === ENTERING) {
            this.performEnter(node, mounting);
          } else {
            this.performExit(node);
          }
        } else if (this.props.unmountOnExit && this.state.status === EXITED) {
          this.setState({
            status: UNMOUNTED
          });
        }
      };

      _proto.performEnter = function performEnter(node, mounting) {
        var _this2 = this;

        var enter = this.props.enter;
        var appearing = this.context.transitionGroup ? this.context.transitionGroup.isMounting : mounting;
        var timeouts = this.getTimeouts();
        var enterTimeout = appearing ? timeouts.appear : timeouts.enter; // no enter animation skip right to ENTERED
        // if we are mounting and running this it means appear _must_ be set

        if (!mounting && !enter) {
          this.safeSetState({
            status: ENTERED
          }, function () {
            _this2.props.onEntered(node);
          });
          return;
        }

        this.props.onEnter(node, appearing);
        this.safeSetState({
          status: ENTERING
        }, function () {
          _this2.props.onEntering(node, appearing);

          _this2.onTransitionEnd(node, enterTimeout, function () {
            _this2.safeSetState({
              status: ENTERED
            }, function () {
              _this2.props.onEntered(node, appearing);
            });
          });
        });
      };

      _proto.performExit = function performExit(node) {
        var _this3 = this;

        var exit = this.props.exit;
        var timeouts = this.getTimeouts(); // no exit animation skip right to EXITED

        if (!exit) {
          this.safeSetState({
            status: EXITED
          }, function () {
            _this3.props.onExited(node);
          });
          return;
        }

        this.props.onExit(node);
        this.safeSetState({
          status: EXITING
        }, function () {
          _this3.props.onExiting(node);

          _this3.onTransitionEnd(node, timeouts.exit, function () {
            _this3.safeSetState({
              status: EXITED
            }, function () {
              _this3.props.onExited(node);
            });
          });
        });
      };

      _proto.cancelNextCallback = function cancelNextCallback() {
        if (this.nextCallback !== null) {
          this.nextCallback.cancel();
          this.nextCallback = null;
        }
      };

      _proto.safeSetState = function safeSetState(nextState, callback) {
        // This shouldn't be necessary, but there are weird race conditions with
        // setState callbacks and unmounting in testing, so always make sure that
        // we can cancel any pending setState callbacks after we unmount.
        callback = this.setNextCallback(callback);
        this.setState(nextState, callback);
      };

      _proto.setNextCallback = function setNextCallback(callback) {
        var _this4 = this;

        var active = true;

        this.nextCallback = function (event) {
          if (active) {
            active = false;
            _this4.nextCallback = null;
            callback(event);
          }
        };

        this.nextCallback.cancel = function () {
          active = false;
        };

        return this.nextCallback;
      };

      _proto.onTransitionEnd = function onTransitionEnd(node, timeout, handler) {
        this.setNextCallback(handler);
        var doesNotHaveTimeoutOrListener = timeout == null && !this.props.addEndListener;

        if (!node || doesNotHaveTimeoutOrListener) {
          setTimeout(this.nextCallback, 0);
          return;
        }

        if (this.props.addEndListener) {
          this.props.addEndListener(node, this.nextCallback);
        }

        if (timeout != null) {
          setTimeout(this.nextCallback, timeout);
        }
      };

      _proto.render = function render() {
        var status = this.state.status;

        if (status === UNMOUNTED) {
          return null;
        }

        var _this$props = this.props,
            children = _this$props.children,
            childProps = _objectWithoutPropertiesLoose(_this$props, ["children"]); // filter props for Transtition


        delete childProps.in;
        delete childProps.mountOnEnter;
        delete childProps.unmountOnExit;
        delete childProps.appear;
        delete childProps.enter;
        delete childProps.exit;
        delete childProps.timeout;
        delete childProps.addEndListener;
        delete childProps.onEnter;
        delete childProps.onEntering;
        delete childProps.onEntered;
        delete childProps.onExit;
        delete childProps.onExiting;
        delete childProps.onExited;

        if (typeof children === 'function') {
          return children(status, childProps);
        }

        var child = _react.default.Children.only(children);

        return _react.default.cloneElement(child, childProps);
      };

      return Transition;
    }(_react.default.Component);

    Transition.contextTypes = {
      transitionGroup: PropTypes$1.object
    };
    Transition.childContextTypes = {
      transitionGroup: function transitionGroup() {}
    };
    Transition.propTypes = {
      /**
       * A `function` child can be used instead of a React element. This function is
       * called with the current transition status (`'entering'`, `'entered'`,
       * `'exiting'`, `'exited'`, `'unmounted'`), which can be used to apply context
       * specific props to a component.
       *
       * ```jsx
       * <Transition in={this.state.in} timeout={150}>
       *   {state => (
       *     <MyComponent className={`fade fade-${state}`} />
       *   )}
       * </Transition>
       * ```
       */
      children: PropTypes$1.oneOfType([PropTypes$1.func.isRequired, PropTypes$1.element.isRequired]).isRequired,

      /**
       * Show the component; triggers the enter or exit states
       */
      in: PropTypes$1.bool,

      /**
       * By default the child component is mounted immediately along with
       * the parent `Transition` component. If you want to "lazy mount" the component on the
       * first `in={true}` you can set `mountOnEnter`. After the first enter transition the component will stay
       * mounted, even on "exited", unless you also specify `unmountOnExit`.
       */
      mountOnEnter: PropTypes$1.bool,

      /**
       * By default the child component stays mounted after it reaches the `'exited'` state.
       * Set `unmountOnExit` if you'd prefer to unmount the component after it finishes exiting.
       */
      unmountOnExit: PropTypes$1.bool,

      /**
       * Normally a component is not transitioned if it is shown when the `<Transition>` component mounts.
       * If you want to transition on the first mount set `appear` to `true`, and the
       * component will transition in as soon as the `<Transition>` mounts.
       *
       * > Note: there are no specific "appear" states. `appear` only adds an additional `enter` transition.
       */
      appear: PropTypes$1.bool,

      /**
       * Enable or disable enter transitions.
       */
      enter: PropTypes$1.bool,

      /**
       * Enable or disable exit transitions.
       */
      exit: PropTypes$1.bool,

      /**
       * The duration of the transition, in milliseconds.
       * Required unless `addEndListener` is provided.
       *
       * You may specify a single timeout for all transitions:
       *
       * ```jsx
       * timeout={500}
       * ```
       *
       * or individually:
       *
       * ```jsx
       * timeout={{
       *  appear: 500,
       *  enter: 300,
       *  exit: 500,
       * }}
       * ```
       *
       * - `appear` defaults to the value of `enter`
       * - `enter` defaults to `0`
       * - `exit` defaults to `0`
       *
       * @type {number | { enter?: number, exit?: number, appear?: number }}
       */
      timeout: function timeout(props) {
        var pt = PropTypes.timeoutsShape;    if (!props.addEndListener) pt = pt.isRequired;

        for (var _len = arguments.length, args = new Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
          args[_key - 1] = arguments[_key];
        }

        return pt.apply(void 0, [props].concat(args));
      },

      /**
       * Add a custom transition end trigger. Called with the transitioning
       * DOM node and a `done` callback. Allows for more fine grained transition end
       * logic. **Note:** Timeouts are still used as a fallback if provided.
       *
       * ```jsx
       * addEndListener={(node, done) => {
       *   // use the css transitionend event to mark the finish of a transition
       *   node.addEventListener('transitionend', done, false);
       * }}
       * ```
       */
      addEndListener: PropTypes$1.func,

      /**
       * Callback fired before the "entering" status is applied. An extra parameter
       * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
       *
       * @type Function(node: HtmlElement, isAppearing: bool) -> void
       */
      onEnter: PropTypes$1.func,

      /**
       * Callback fired after the "entering" status is applied. An extra parameter
       * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
       *
       * @type Function(node: HtmlElement, isAppearing: bool)
       */
      onEntering: PropTypes$1.func,

      /**
       * Callback fired after the "entered" status is applied. An extra parameter
       * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
       *
       * @type Function(node: HtmlElement, isAppearing: bool) -> void
       */
      onEntered: PropTypes$1.func,

      /**
       * Callback fired before the "exiting" status is applied.
       *
       * @type Function(node: HtmlElement) -> void
       */
      onExit: PropTypes$1.func,

      /**
       * Callback fired after the "exiting" status is applied.
       *
       * @type Function(node: HtmlElement) -> void
       */
      onExiting: PropTypes$1.func,

      /**
       * Callback fired after the "exited" status is applied.
       *
       * @type Function(node: HtmlElement) -> void
       */
      onExited: PropTypes$1.func // Name the function so it is clearer in the documentation

    };

    function noop() {}

    Transition.defaultProps = {
      in: false,
      mountOnEnter: false,
      unmountOnExit: false,
      appear: false,
      enter: true,
      exit: true,
      onEnter: noop,
      onEntering: noop,
      onEntered: noop,
      onExit: noop,
      onExiting: noop,
      onExited: noop
    };
    Transition.UNMOUNTED = 0;
    Transition.EXITED = 1;
    Transition.ENTERING = 2;
    Transition.ENTERED = 3;
    Transition.EXITING = 4;

    var _default = (0, reactLifecyclesCompat_es.polyfill)(Transition);

    exports.default = _default;
    });

    unwrapExports(Transition_1);
    var Transition_2 = Transition_1.EXITING;
    var Transition_3 = Transition_1.ENTERED;
    var Transition_4 = Transition_1.ENTERING;
    var Transition_5 = Transition_1.EXITED;
    var Transition_6 = Transition_1.UNMOUNTED;

    var CSSTransition_1 = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;
    exports.default = void 0;

    var PropTypes$1 = _interopRequireWildcard(propTypes);

    var _addClass = _interopRequireDefault(addClass_1);

    var _removeClass = _interopRequireDefault(removeClass);

    var _react = _interopRequireDefault(React__default);

    var _Transition = _interopRequireDefault(Transition_1);



    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) { var desc = Object.defineProperty && Object.getOwnPropertyDescriptor ? Object.getOwnPropertyDescriptor(obj, key) : {}; if (desc.get || desc.set) { Object.defineProperty(newObj, key, desc); } else { newObj[key] = obj[key]; } } } } newObj.default = obj; return newObj; } }

    function _extends() { _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends.apply(this, arguments); }

    function _inheritsLoose(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }

    var addClass = function addClass(node, classes) {
      return node && classes && classes.split(' ').forEach(function (c) {
        return (0, _addClass.default)(node, c);
      });
    };

    var removeClass$1 = function removeClass(node, classes) {
      return node && classes && classes.split(' ').forEach(function (c) {
        return (0, _removeClass.default)(node, c);
      });
    };
    /**
     * A transition component inspired by the excellent
     * [ng-animate](http://www.nganimate.org/) library, you should use it if you're
     * using CSS transitions or animations. It's built upon the
     * [`Transition`](https://reactcommunity.org/react-transition-group/transition)
     * component, so it inherits all of its props.
     *
     * `CSSTransition` applies a pair of class names during the `appear`, `enter`,
     * and `exit` states of the transition. The first class is applied and then a
     * second `*-active` class in order to activate the CSSS transition. After the
     * transition, matching `*-done` class names are applied to persist the
     * transition state.
     *
     * ```jsx
     * function App() {
     *   const [inProp, setInProp] = useState(false);
     *   return (
     *     <div>
     *       <CSSTransition in={inProp} timeout={200} classNames="my-node">
     *         <div>
     *           {"I'll receive my-node-* classes"}
     *         </div>
     *       </CSSTransition>
     *       <button type="button" onClick={() => setInProp(true)}>
     *         Click to Enter
     *       </button>
     *     </div>
     *   );
     * }
     * ```
     *
     * When the `in` prop is set to `true`, the child component will first receive
     * the class `example-enter`, then the `example-enter-active` will be added in
     * the next tick. `CSSTransition` [forces a
     * reflow](https://github.com/reactjs/react-transition-group/blob/5007303e729a74be66a21c3e2205e4916821524b/src/CSSTransition.js#L208-L215)
     * between before adding the `example-enter-active`. This is an important trick
     * because it allows us to transition between `example-enter` and
     * `example-enter-active` even though they were added immediately one after
     * another. Most notably, this is what makes it possible for us to animate
     * _appearance_.
     *
     * ```css
     * .my-node-enter {
     *   opacity: 0;
     * }
     * .my-node-enter-active {
     *   opacity: 1;
     *   transition: opacity 200ms;
     * }
     * .my-node-exit {
     *   opacity: 1;
     * }
     * .my-node-exit-active {
     *   opacity: 0;
     *   transition: opacity: 200ms;
     * }
     * ```
     *
     * `*-active` classes represent which styles you want to animate **to**.
     */


    var CSSTransition =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(CSSTransition, _React$Component);

      function CSSTransition() {
        var _this;

        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        _this = _React$Component.call.apply(_React$Component, [this].concat(args)) || this;

        _this.onEnter = function (node, appearing) {
          var _this$getClassNames = _this.getClassNames(appearing ? 'appear' : 'enter'),
              className = _this$getClassNames.className;

          _this.removeClasses(node, 'exit');

          addClass(node, className);

          if (_this.props.onEnter) {
            _this.props.onEnter(node, appearing);
          }
        };

        _this.onEntering = function (node, appearing) {
          var _this$getClassNames2 = _this.getClassNames(appearing ? 'appear' : 'enter'),
              activeClassName = _this$getClassNames2.activeClassName;

          _this.reflowAndAddClass(node, activeClassName);

          if (_this.props.onEntering) {
            _this.props.onEntering(node, appearing);
          }
        };

        _this.onEntered = function (node, appearing) {
          var _this$getClassNames3 = _this.getClassNames('enter'),
              doneClassName = _this$getClassNames3.doneClassName;

          _this.removeClasses(node, appearing ? 'appear' : 'enter');

          addClass(node, doneClassName);

          if (_this.props.onEntered) {
            _this.props.onEntered(node, appearing);
          }
        };

        _this.onExit = function (node) {
          var _this$getClassNames4 = _this.getClassNames('exit'),
              className = _this$getClassNames4.className;

          _this.removeClasses(node, 'appear');

          _this.removeClasses(node, 'enter');

          addClass(node, className);

          if (_this.props.onExit) {
            _this.props.onExit(node);
          }
        };

        _this.onExiting = function (node) {
          var _this$getClassNames5 = _this.getClassNames('exit'),
              activeClassName = _this$getClassNames5.activeClassName;

          _this.reflowAndAddClass(node, activeClassName);

          if (_this.props.onExiting) {
            _this.props.onExiting(node);
          }
        };

        _this.onExited = function (node) {
          var _this$getClassNames6 = _this.getClassNames('exit'),
              doneClassName = _this$getClassNames6.doneClassName;

          _this.removeClasses(node, 'exit');

          addClass(node, doneClassName);

          if (_this.props.onExited) {
            _this.props.onExited(node);
          }
        };

        _this.getClassNames = function (type) {
          var classNames = _this.props.classNames;
          var isStringClassNames = typeof classNames === 'string';
          var prefix = isStringClassNames && classNames ? classNames + '-' : '';
          var className = isStringClassNames ? prefix + type : classNames[type];
          var activeClassName = isStringClassNames ? className + '-active' : classNames[type + 'Active'];
          var doneClassName = isStringClassNames ? className + '-done' : classNames[type + 'Done'];
          return {
            className: className,
            activeClassName: activeClassName,
            doneClassName: doneClassName
          };
        };

        return _this;
      }

      var _proto = CSSTransition.prototype;

      _proto.removeClasses = function removeClasses(node, type) {
        var _this$getClassNames7 = this.getClassNames(type),
            className = _this$getClassNames7.className,
            activeClassName = _this$getClassNames7.activeClassName,
            doneClassName = _this$getClassNames7.doneClassName;

        className && removeClass$1(node, className);
        activeClassName && removeClass$1(node, activeClassName);
        doneClassName && removeClass$1(node, doneClassName);
      };

      _proto.reflowAndAddClass = function reflowAndAddClass(node, className) {
        // This is for to force a repaint,
        // which is necessary in order to transition styles when adding a class name.
        if (className) {
          /* eslint-disable no-unused-expressions */
          node && node.scrollTop;
          /* eslint-enable no-unused-expressions */

          addClass(node, className);
        }
      };

      _proto.render = function render() {
        var props = _extends({}, this.props);

        delete props.classNames;
        return _react.default.createElement(_Transition.default, _extends({}, props, {
          onEnter: this.onEnter,
          onEntered: this.onEntered,
          onEntering: this.onEntering,
          onExit: this.onExit,
          onExiting: this.onExiting,
          onExited: this.onExited
        }));
      };

      return CSSTransition;
    }(_react.default.Component);

    CSSTransition.defaultProps = {
      classNames: ''
    };
    CSSTransition.propTypes = _extends({}, _Transition.default.propTypes, {
      /**
       * The animation classNames applied to the component as it enters, exits or has finished the transition.
       * A single name can be provided and it will be suffixed for each stage: e.g.
       *
       * `classNames="fade"` applies `fade-enter`, `fade-enter-active`, `fade-enter-done`,
       * `fade-exit`, `fade-exit-active`, `fade-exit-done`, `fade-appear`, and `fade-appear-active`.
       * Each individual classNames can also be specified independently like:
       *
       * ```js
       * classNames={{
       *  appear: 'my-appear',
       *  appearActive: 'my-active-appear',
       *  enter: 'my-enter',
       *  enterActive: 'my-active-enter',
       *  enterDone: 'my-done-enter',
       *  exit: 'my-exit',
       *  exitActive: 'my-active-exit',
       *  exitDone: 'my-done-exit',
       * }}
       * ```
       *
       * If you want to set these classes using CSS Modules:
       *
       * ```js
       * import styles from './styles.css';
       * ```
       *
       * you might want to use camelCase in your CSS file, that way could simply spread
       * them instead of listing them one by one:
       *
       * ```js
       * classNames={{ ...styles }}
       * ```
       *
       * @type {string | {
       *  appear?: string,
       *  appearActive?: string,
       *  enter?: string,
       *  enterActive?: string,
       *  enterDone?: string,
       *  exit?: string,
       *  exitActive?: string,
       *  exitDone?: string,
       * }}
       */
      classNames: PropTypes.classNamesShape,

      /**
       * A `<Transition>` callback fired immediately after the 'enter' or 'appear' class is
       * applied.
       *
       * @type Function(node: HtmlElement, isAppearing: bool)
       */
      onEnter: PropTypes$1.func,

      /**
       * A `<Transition>` callback fired immediately after the 'enter-active' or
       * 'appear-active' class is applied.
       *
       * @type Function(node: HtmlElement, isAppearing: bool)
       */
      onEntering: PropTypes$1.func,

      /**
       * A `<Transition>` callback fired immediately after the 'enter' or
       * 'appear' classes are **removed** and the `done` class is added to the DOM node.
       *
       * @type Function(node: HtmlElement, isAppearing: bool)
       */
      onEntered: PropTypes$1.func,

      /**
       * A `<Transition>` callback fired immediately after the 'exit' class is
       * applied.
       *
       * @type Function(node: HtmlElement)
       */
      onExit: PropTypes$1.func,

      /**
       * A `<Transition>` callback fired immediately after the 'exit-active' is applied.
       *
       * @type Function(node: HtmlElement)
       */
      onExiting: PropTypes$1.func,

      /**
       * A `<Transition>` callback fired immediately after the 'exit' classes
       * are **removed** and the `exit-done` class is added to the DOM node.
       *
       * @type Function(node: HtmlElement)
       */
      onExited: PropTypes$1.func
    });
    var _default = CSSTransition;
    exports.default = _default;
    module.exports = exports["default"];
    });

    unwrapExports(CSSTransition_1);

    var ChildMapping = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;
    exports.getChildMapping = getChildMapping;
    exports.mergeChildMappings = mergeChildMappings;
    exports.getInitialChildMapping = getInitialChildMapping;
    exports.getNextChildMapping = getNextChildMapping;



    /**
     * Given `this.props.children`, return an object mapping key to child.
     *
     * @param {*} children `this.props.children`
     * @return {object} Mapping of key to child
     */
    function getChildMapping(children, mapFn) {
      var mapper = function mapper(child) {
        return mapFn && (0, React__default.isValidElement)(child) ? mapFn(child) : child;
      };

      var result = Object.create(null);
      if (children) React__default.Children.map(children, function (c) {
        return c;
      }).forEach(function (child) {
        // run the map function here instead so that the key is the computed one
        result[child.key] = mapper(child);
      });
      return result;
    }
    /**
     * When you're adding or removing children some may be added or removed in the
     * same render pass. We want to show *both* since we want to simultaneously
     * animate elements in and out. This function takes a previous set of keys
     * and a new set of keys and merges them with its best guess of the correct
     * ordering. In the future we may expose some of the utilities in
     * ReactMultiChild to make this easy, but for now React itself does not
     * directly have this concept of the union of prevChildren and nextChildren
     * so we implement it here.
     *
     * @param {object} prev prev children as returned from
     * `ReactTransitionChildMapping.getChildMapping()`.
     * @param {object} next next children as returned from
     * `ReactTransitionChildMapping.getChildMapping()`.
     * @return {object} a key set that contains all keys in `prev` and all keys
     * in `next` in a reasonable order.
     */


    function mergeChildMappings(prev, next) {
      prev = prev || {};
      next = next || {};

      function getValueForKey(key) {
        return key in next ? next[key] : prev[key];
      } // For each key of `next`, the list of keys to insert before that key in
      // the combined list


      var nextKeysPending = Object.create(null);
      var pendingKeys = [];

      for (var prevKey in prev) {
        if (prevKey in next) {
          if (pendingKeys.length) {
            nextKeysPending[prevKey] = pendingKeys;
            pendingKeys = [];
          }
        } else {
          pendingKeys.push(prevKey);
        }
      }

      var i;
      var childMapping = {};

      for (var nextKey in next) {
        if (nextKeysPending[nextKey]) {
          for (i = 0; i < nextKeysPending[nextKey].length; i++) {
            var pendingNextKey = nextKeysPending[nextKey][i];
            childMapping[nextKeysPending[nextKey][i]] = getValueForKey(pendingNextKey);
          }
        }

        childMapping[nextKey] = getValueForKey(nextKey);
      } // Finally, add the keys which didn't appear before any key in `next`


      for (i = 0; i < pendingKeys.length; i++) {
        childMapping[pendingKeys[i]] = getValueForKey(pendingKeys[i]);
      }

      return childMapping;
    }

    function getProp(child, prop, props) {
      return props[prop] != null ? props[prop] : child.props[prop];
    }

    function getInitialChildMapping(props, onExited) {
      return getChildMapping(props.children, function (child) {
        return (0, React__default.cloneElement)(child, {
          onExited: onExited.bind(null, child),
          in: true,
          appear: getProp(child, 'appear', props),
          enter: getProp(child, 'enter', props),
          exit: getProp(child, 'exit', props)
        });
      });
    }

    function getNextChildMapping(nextProps, prevChildMapping, onExited) {
      var nextChildMapping = getChildMapping(nextProps.children);
      var children = mergeChildMappings(prevChildMapping, nextChildMapping);
      Object.keys(children).forEach(function (key) {
        var child = children[key];
        if (!(0, React__default.isValidElement)(child)) return;
        var hasPrev = key in prevChildMapping;
        var hasNext = key in nextChildMapping;
        var prevChild = prevChildMapping[key];
        var isLeaving = (0, React__default.isValidElement)(prevChild) && !prevChild.props.in; // item is new (entering)

        if (hasNext && (!hasPrev || isLeaving)) {
          // console.log('entering', key)
          children[key] = (0, React__default.cloneElement)(child, {
            onExited: onExited.bind(null, child),
            in: true,
            exit: getProp(child, 'exit', nextProps),
            enter: getProp(child, 'enter', nextProps)
          });
        } else if (!hasNext && hasPrev && !isLeaving) {
          // item is old (exiting)
          // console.log('leaving', key)
          children[key] = (0, React__default.cloneElement)(child, {
            in: false
          });
        } else if (hasNext && hasPrev && (0, React__default.isValidElement)(prevChild)) {
          // item hasn't changed transition states
          // copy over the last transition props;
          // console.log('unchanged', key)
          children[key] = (0, React__default.cloneElement)(child, {
            onExited: onExited.bind(null, child),
            in: prevChild.props.in,
            exit: getProp(child, 'exit', nextProps),
            enter: getProp(child, 'enter', nextProps)
          });
        }
      });
      return children;
    }
    });

    unwrapExports(ChildMapping);
    var ChildMapping_1 = ChildMapping.getChildMapping;
    var ChildMapping_2 = ChildMapping.mergeChildMappings;
    var ChildMapping_3 = ChildMapping.getInitialChildMapping;
    var ChildMapping_4 = ChildMapping.getNextChildMapping;

    var TransitionGroup_1 = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;
    exports.default = void 0;

    var _propTypes = _interopRequireDefault(propTypes);

    var _react = _interopRequireDefault(React__default);





    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    function _objectWithoutPropertiesLoose(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

    function _extends() { _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; }; return _extends.apply(this, arguments); }

    function _inheritsLoose(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }

    function _assertThisInitialized(self) { if (self === void 0) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return self; }

    var values = Object.values || function (obj) {
      return Object.keys(obj).map(function (k) {
        return obj[k];
      });
    };

    var defaultProps = {
      component: 'div',
      childFactory: function childFactory(child) {
        return child;
      }
      /**
       * The `<TransitionGroup>` component manages a set of transition components
       * (`<Transition>` and `<CSSTransition>`) in a list. Like with the transition
       * components, `<TransitionGroup>` is a state machine for managing the mounting
       * and unmounting of components over time.
       *
       * Consider the example below. As items are removed or added to the TodoList the
       * `in` prop is toggled automatically by the `<TransitionGroup>`.
       *
       * Note that `<TransitionGroup>`  does not define any animation behavior!
       * Exactly _how_ a list item animates is up to the individual transition
       * component. This means you can mix and match animations across different list
       * items.
       */

    };

    var TransitionGroup =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(TransitionGroup, _React$Component);

      function TransitionGroup(props, context) {
        var _this;

        _this = _React$Component.call(this, props, context) || this;

        var handleExited = _this.handleExited.bind(_assertThisInitialized(_assertThisInitialized(_this))); // Initial children should all be entering, dependent on appear


        _this.state = {
          handleExited: handleExited,
          firstRender: true
        };
        return _this;
      }

      var _proto = TransitionGroup.prototype;

      _proto.getChildContext = function getChildContext() {
        return {
          transitionGroup: {
            isMounting: !this.appeared
          }
        };
      };

      _proto.componentDidMount = function componentDidMount() {
        this.appeared = true;
        this.mounted = true;
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        this.mounted = false;
      };

      TransitionGroup.getDerivedStateFromProps = function getDerivedStateFromProps(nextProps, _ref) {
        var prevChildMapping = _ref.children,
            handleExited = _ref.handleExited,
            firstRender = _ref.firstRender;
        return {
          children: firstRender ? (0, ChildMapping.getInitialChildMapping)(nextProps, handleExited) : (0, ChildMapping.getNextChildMapping)(nextProps, prevChildMapping, handleExited),
          firstRender: false
        };
      };

      _proto.handleExited = function handleExited(child, node) {
        var currentChildMapping = (0, ChildMapping.getChildMapping)(this.props.children);
        if (child.key in currentChildMapping) return;

        if (child.props.onExited) {
          child.props.onExited(node);
        }

        if (this.mounted) {
          this.setState(function (state) {
            var children = _extends({}, state.children);

            delete children[child.key];
            return {
              children: children
            };
          });
        }
      };

      _proto.render = function render() {
        var _this$props = this.props,
            Component = _this$props.component,
            childFactory = _this$props.childFactory,
            props = _objectWithoutPropertiesLoose(_this$props, ["component", "childFactory"]);

        var children = values(this.state.children).map(childFactory);
        delete props.appear;
        delete props.enter;
        delete props.exit;

        if (Component === null) {
          return children;
        }

        return _react.default.createElement(Component, props, children);
      };

      return TransitionGroup;
    }(_react.default.Component);

    TransitionGroup.childContextTypes = {
      transitionGroup: _propTypes.default.object.isRequired
    };
    TransitionGroup.propTypes = {
      /**
       * `<TransitionGroup>` renders a `<div>` by default. You can change this
       * behavior by providing a `component` prop.
       * If you use React v16+ and would like to avoid a wrapping `<div>` element
       * you can pass in `component={null}`. This is useful if the wrapping div
       * borks your css styles.
       */
      component: _propTypes.default.any,

      /**
       * A set of `<Transition>` components, that are toggled `in` and out as they
       * leave. the `<TransitionGroup>` will inject specific transition props, so
       * remember to spread them through if you are wrapping the `<Transition>` as
       * with our `<Fade>` example.
       *
       * While this component is meant for multiple `Transition` or `CSSTransition`
       * children, sometimes you may want to have a single transition child with
       * content that you want to be transitioned out and in when you change it
       * (e.g. routes, images etc.) In that case you can change the `key` prop of
       * the transition child as you change its content, this will cause
       * `TransitionGroup` to transition the child out and back in.
       */
      children: _propTypes.default.node,

      /**
       * A convenience prop that enables or disables appear animations
       * for all children. Note that specifying this will override any defaults set
       * on individual children Transitions.
       */
      appear: _propTypes.default.bool,

      /**
       * A convenience prop that enables or disables enter animations
       * for all children. Note that specifying this will override any defaults set
       * on individual children Transitions.
       */
      enter: _propTypes.default.bool,

      /**
       * A convenience prop that enables or disables exit animations
       * for all children. Note that specifying this will override any defaults set
       * on individual children Transitions.
       */
      exit: _propTypes.default.bool,

      /**
       * You may need to apply reactive updates to a child as it is exiting.
       * This is generally done by using `cloneElement` however in the case of an exiting
       * child the element has already been removed and not accessible to the consumer.
       *
       * If you do need to update a child as it leaves you can provide a `childFactory`
       * to wrap every child, even the ones that are leaving.
       *
       * @type Function(child: ReactElement) -> ReactElement
       */
      childFactory: _propTypes.default.func
    };
    TransitionGroup.defaultProps = defaultProps;

    var _default = (0, reactLifecyclesCompat_es.polyfill)(TransitionGroup);

    exports.default = _default;
    module.exports = exports["default"];
    });

    unwrapExports(TransitionGroup_1);

    var ReplaceTransition_1 = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;
    exports.default = void 0;

    var _propTypes = _interopRequireDefault(propTypes);

    var _react = _interopRequireDefault(React__default);



    var _TransitionGroup = _interopRequireDefault(TransitionGroup_1);

    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    function _objectWithoutPropertiesLoose(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

    function _inheritsLoose(subClass, superClass) { subClass.prototype = Object.create(superClass.prototype); subClass.prototype.constructor = subClass; subClass.__proto__ = superClass; }

    /**
     * The `<ReplaceTransition>` component is a specialized `Transition` component
     * that animates between two children.
     *
     * ```jsx
     * <ReplaceTransition in>
     *   <Fade><div>I appear first</div></Fade>
     *   <Fade><div>I replace the above</div></Fade>
     * </ReplaceTransition>
     * ```
     */
    var ReplaceTransition =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(ReplaceTransition, _React$Component);

      function ReplaceTransition() {
        var _this;

        for (var _len = arguments.length, _args = new Array(_len), _key = 0; _key < _len; _key++) {
          _args[_key] = arguments[_key];
        }

        _this = _React$Component.call.apply(_React$Component, [this].concat(_args)) || this;

        _this.handleEnter = function () {
          for (var _len2 = arguments.length, args = new Array(_len2), _key2 = 0; _key2 < _len2; _key2++) {
            args[_key2] = arguments[_key2];
          }

          return _this.handleLifecycle('onEnter', 0, args);
        };

        _this.handleEntering = function () {
          for (var _len3 = arguments.length, args = new Array(_len3), _key3 = 0; _key3 < _len3; _key3++) {
            args[_key3] = arguments[_key3];
          }

          return _this.handleLifecycle('onEntering', 0, args);
        };

        _this.handleEntered = function () {
          for (var _len4 = arguments.length, args = new Array(_len4), _key4 = 0; _key4 < _len4; _key4++) {
            args[_key4] = arguments[_key4];
          }

          return _this.handleLifecycle('onEntered', 0, args);
        };

        _this.handleExit = function () {
          for (var _len5 = arguments.length, args = new Array(_len5), _key5 = 0; _key5 < _len5; _key5++) {
            args[_key5] = arguments[_key5];
          }

          return _this.handleLifecycle('onExit', 1, args);
        };

        _this.handleExiting = function () {
          for (var _len6 = arguments.length, args = new Array(_len6), _key6 = 0; _key6 < _len6; _key6++) {
            args[_key6] = arguments[_key6];
          }

          return _this.handleLifecycle('onExiting', 1, args);
        };

        _this.handleExited = function () {
          for (var _len7 = arguments.length, args = new Array(_len7), _key7 = 0; _key7 < _len7; _key7++) {
            args[_key7] = arguments[_key7];
          }

          return _this.handleLifecycle('onExited', 1, args);
        };

        return _this;
      }

      var _proto = ReplaceTransition.prototype;

      _proto.handleLifecycle = function handleLifecycle(handler, idx, originalArgs) {
        var _child$props;

        var children = this.props.children;

        var child = _react.default.Children.toArray(children)[idx];

        if (child.props[handler]) (_child$props = child.props)[handler].apply(_child$props, originalArgs);
        if (this.props[handler]) this.props[handler]((0, ReactDOM.findDOMNode)(this));
      };

      _proto.render = function render() {
        var _this$props = this.props,
            children = _this$props.children,
            inProp = _this$props.in,
            props = _objectWithoutPropertiesLoose(_this$props, ["children", "in"]);

        var _React$Children$toArr = _react.default.Children.toArray(children),
            first = _React$Children$toArr[0],
            second = _React$Children$toArr[1];

        delete props.onEnter;
        delete props.onEntering;
        delete props.onEntered;
        delete props.onExit;
        delete props.onExiting;
        delete props.onExited;
        return _react.default.createElement(_TransitionGroup.default, props, inProp ? _react.default.cloneElement(first, {
          key: 'first',
          onEnter: this.handleEnter,
          onEntering: this.handleEntering,
          onEntered: this.handleEntered
        }) : _react.default.cloneElement(second, {
          key: 'second',
          onEnter: this.handleExit,
          onEntering: this.handleExiting,
          onEntered: this.handleExited
        }));
      };

      return ReplaceTransition;
    }(_react.default.Component);

    ReplaceTransition.propTypes = {
      in: _propTypes.default.bool.isRequired,
      children: function children(props, propName) {
        if (_react.default.Children.count(props[propName]) !== 2) return new Error("\"" + propName + "\" must be exactly two transition components.");
        return null;
      }
    };
    var _default = ReplaceTransition;
    exports.default = _default;
    module.exports = exports["default"];
    });

    unwrapExports(ReplaceTransition_1);

    var reactTransitionGroup = createCommonjsModule(function (module) {

    var _CSSTransition = _interopRequireDefault(CSSTransition_1);

    var _ReplaceTransition = _interopRequireDefault(ReplaceTransition_1);

    var _TransitionGroup = _interopRequireDefault(TransitionGroup_1);

    var _Transition = _interopRequireDefault(Transition_1);

    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    module.exports = {
      Transition: _Transition.default,
      TransitionGroup: _TransitionGroup.default,
      ReplaceTransition: _ReplaceTransition.default,
      CSSTransition: _CSSTransition.default
    };
    });

    unwrapExports(reactTransitionGroup);
    var reactTransitionGroup_1 = reactTransitionGroup.Transition;
    var reactTransitionGroup_2 = reactTransitionGroup.TransitionGroup;
    var reactTransitionGroup_3 = reactTransitionGroup.ReplaceTransition;
    var reactTransitionGroup_4 = reactTransitionGroup.CSSTransition;

    var propTypes$k = _objectSpread({}, reactTransitionGroup_1.propTypes, {
      children: propTypes.oneOfType([propTypes.arrayOf(propTypes.node), propTypes.node]),
      tag: tagPropType,
      baseClass: propTypes.string,
      baseClassActive: propTypes.string,
      className: propTypes.string,
      cssModule: propTypes.object,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.string, propTypes.func])
    });

    var defaultProps$7 = _objectSpread({}, reactTransitionGroup_1.defaultProps, {
      tag: 'div',
      baseClass: 'fade',
      baseClassActive: 'show',
      timeout: TransitionTimeouts.Fade,
      appear: true,
      enter: true,
      exit: true,
      in: true
    });

    function Fade(props) {
      var Tag = props.tag,
          baseClass = props.baseClass,
          baseClassActive = props.baseClassActive,
          className = props.className,
          cssModule = props.cssModule,
          children = props.children,
          innerRef = props.innerRef,
          otherProps = _objectWithoutPropertiesLoose(props, ["tag", "baseClass", "baseClassActive", "className", "cssModule", "children", "innerRef"]);

      var transitionProps = pick(otherProps, TransitionPropTypeKeys);
      var childProps = omit(otherProps, TransitionPropTypeKeys);
      return React__default.createElement(reactTransitionGroup_1, transitionProps, function (status) {
        var isActive = status === 'entered';
        var classes = mapToCssModules(classnames(className, baseClass, isActive && baseClassActive), cssModule);
        return React__default.createElement(Tag, _extends({
          className: classes
        }, childProps, {
          ref: innerRef
        }), children);
      });
    }

    Fade.propTypes = propTypes$k;
    Fade.defaultProps = defaultProps$7;

    var propTypes$l = {
      color: propTypes.string,
      pill: propTypes.bool,
      tag: tagPropType,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.func, propTypes.string]),
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$m = {
      tag: tagPropType,
      inverse: propTypes.bool,
      color: propTypes.string,
      body: propTypes.bool,
      outline: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.string, propTypes.func])
    };

    var propTypes$n = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$o = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$p = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$q = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.string, propTypes.func])
    };

    var propTypes$r = {
      tag: tagPropType,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.func, propTypes.string]),
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$s = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$t = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$u = {
      tag: tagPropType,
      top: propTypes.bool,
      bottom: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$v = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var CarouselItem =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(CarouselItem, _React$Component);

      function CarouselItem(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.state = {
          startAnimation: false
        };
        _this.onEnter = _this.onEnter.bind(_assertThisInitialized(_this));
        _this.onEntering = _this.onEntering.bind(_assertThisInitialized(_this));
        _this.onExit = _this.onExit.bind(_assertThisInitialized(_this));
        _this.onExiting = _this.onExiting.bind(_assertThisInitialized(_this));
        _this.onExited = _this.onExited.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = CarouselItem.prototype;

      _proto.onEnter = function onEnter(node, isAppearing) {
        this.setState({
          startAnimation: false
        });
        this.props.onEnter(node, isAppearing);
      };

      _proto.onEntering = function onEntering(node, isAppearing) {
        // getting this variable triggers a reflow
        var offsetHeight = node.offsetHeight;
        this.setState({
          startAnimation: true
        });
        this.props.onEntering(node, isAppearing);
        return offsetHeight;
      };

      _proto.onExit = function onExit(node) {
        this.setState({
          startAnimation: false
        });
        this.props.onExit(node);
      };

      _proto.onExiting = function onExiting(node) {
        this.setState({
          startAnimation: true
        });
        node.dispatchEvent(new CustomEvent('slide.bs.carousel'));
        this.props.onExiting(node);
      };

      _proto.onExited = function onExited(node) {
        node.dispatchEvent(new CustomEvent('slid.bs.carousel'));
        this.props.onExited(node);
      };

      _proto.render = function render() {
        var _this2 = this;

        var _this$props = this.props,
            isIn = _this$props.in,
            children = _this$props.children,
            cssModule = _this$props.cssModule,
            slide = _this$props.slide,
            Tag = _this$props.tag,
            className = _this$props.className,
            transitionProps = _objectWithoutPropertiesLoose(_this$props, ["in", "children", "cssModule", "slide", "tag", "className"]);

        return React__default.createElement(reactTransitionGroup_1, _extends({}, transitionProps, {
          enter: slide,
          exit: slide,
          in: isIn,
          onEnter: this.onEnter,
          onEntering: this.onEntering,
          onExit: this.onExit,
          onExiting: this.onExiting,
          onExited: this.onExited
        }), function (status) {
          var direction = _this2.context.direction;
          var isActive = status === TransitionStatuses.ENTERED || status === TransitionStatuses.EXITING;
          var directionClassName = (status === TransitionStatuses.ENTERING || status === TransitionStatuses.EXITING) && _this2.state.startAnimation && (direction === 'right' ? 'carousel-item-left' : 'carousel-item-right');
          var orderClassName = status === TransitionStatuses.ENTERING && (direction === 'right' ? 'carousel-item-next' : 'carousel-item-prev');
          var itemClasses = mapToCssModules(classnames(className, 'carousel-item', isActive && 'active', directionClassName, orderClassName), cssModule);
          return React__default.createElement(Tag, {
            className: itemClasses
          }, children);
        });
      };

      return CarouselItem;
    }(React__default.Component);

    CarouselItem.propTypes = _objectSpread({}, reactTransitionGroup_1.propTypes, {
      tag: tagPropType,
      in: propTypes.bool,
      cssModule: propTypes.object,
      children: propTypes.node,
      slide: propTypes.bool,
      className: propTypes.string
    });
    CarouselItem.defaultProps = _objectSpread({}, reactTransitionGroup_1.defaultProps, {
      tag: 'div',
      timeout: TransitionTimeouts.Carousel,
      slide: true
    });
    CarouselItem.contextTypes = {
      direction: propTypes.string
    };

    var Carousel =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Carousel, _React$Component);

      function Carousel(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.handleKeyPress = _this.handleKeyPress.bind(_assertThisInitialized(_this));
        _this.renderItems = _this.renderItems.bind(_assertThisInitialized(_this));
        _this.hoverStart = _this.hoverStart.bind(_assertThisInitialized(_this));
        _this.hoverEnd = _this.hoverEnd.bind(_assertThisInitialized(_this));
        _this.state = {
          direction: 'right',
          indicatorClicked: false
        };
        return _this;
      }

      var _proto = Carousel.prototype;

      _proto.getChildContext = function getChildContext() {
        return {
          direction: this.state.direction
        };
      };

      _proto.componentDidMount = function componentDidMount() {
        // Set up the cycle
        if (this.props.ride === 'carousel') {
          this.setInterval();
        } // TODO: move this to the specific carousel like bootstrap. Currently it will trigger ALL carousels on the page.


        document.addEventListener('keyup', this.handleKeyPress);
      };

      _proto.componentWillReceiveProps = function componentWillReceiveProps(nextProps) {
        this.setInterval(nextProps); // Calculate the direction to turn

        if (this.props.activeIndex + 1 === nextProps.activeIndex) {
          this.setState({
            direction: 'right'
          });
        } else if (this.props.activeIndex - 1 === nextProps.activeIndex) {
          this.setState({
            direction: 'left'
          });
        } else if (this.props.activeIndex > nextProps.activeIndex) {
          this.setState({
            direction: this.state.indicatorClicked ? 'left' : 'right'
          });
        } else if (this.props.activeIndex !== nextProps.activeIndex) {
          this.setState({
            direction: this.state.indicatorClicked ? 'right' : 'left'
          });
        }

        this.setState({
          indicatorClicked: false
        });
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        this.clearInterval();
        document.removeEventListener('keyup', this.handleKeyPress);
      };

      _proto.setInterval = function (_setInterval) {
        function setInterval() {
          return _setInterval.apply(this, arguments);
        }

        setInterval.toString = function () {
          return _setInterval.toString();
        };

        return setInterval;
      }(function (props) {
        if (props === void 0) {
          props = this.props;
        }

        // make sure not to have multiple intervals going...
        this.clearInterval();

        if (props.interval) {
          this.cycleInterval = setInterval(function () {
            props.next();
          }, parseInt(props.interval, 10));
        }
      });

      _proto.clearInterval = function (_clearInterval) {
        function clearInterval() {
          return _clearInterval.apply(this, arguments);
        }

        clearInterval.toString = function () {
          return _clearInterval.toString();
        };

        return clearInterval;
      }(function () {
        clearInterval(this.cycleInterval);
      });

      _proto.hoverStart = function hoverStart() {
        if (this.props.pause === 'hover') {
          this.clearInterval();
        }

        if (this.props.mouseEnter) {
          var _this$props;

          (_this$props = this.props).mouseEnter.apply(_this$props, arguments);
        }
      };

      _proto.hoverEnd = function hoverEnd() {
        if (this.props.pause === 'hover') {
          this.setInterval();
        }

        if (this.props.mouseLeave) {
          var _this$props2;

          (_this$props2 = this.props).mouseLeave.apply(_this$props2, arguments);
        }
      };

      _proto.handleKeyPress = function handleKeyPress(evt) {
        if (this.props.keyboard) {
          if (evt.keyCode === 37) {
            this.props.previous();
          } else if (evt.keyCode === 39) {
            this.props.next();
          }
        }
      };

      _proto.renderItems = function renderItems(carouselItems, className) {
        var _this2 = this;

        var slide = this.props.slide;
        return React__default.createElement("div", {
          className: className
        }, carouselItems.map(function (item, index) {
          var isIn = index === _this2.props.activeIndex;
          return React__default.cloneElement(item, {
            in: isIn,
            slide: slide
          });
        }));
      };

      _proto.render = function render() {
        var _this3 = this;

        var _this$props3 = this.props,
            cssModule = _this$props3.cssModule,
            slide = _this$props3.slide,
            className = _this$props3.className;
        var outerClasses = mapToCssModules(classnames(className, 'carousel', slide && 'slide'), cssModule);
        var innerClasses = mapToCssModules(classnames('carousel-inner'), cssModule); // filter out booleans, null, or undefined

        var children = this.props.children.filter(function (child) {
          return child !== null && child !== undefined && typeof child !== 'boolean';
        });
        var slidesOnly = children.every(function (child) {
          return child.type === CarouselItem;
        }); // Rendering only slides

        if (slidesOnly) {
          return React__default.createElement("div", {
            className: outerClasses,
            onMouseEnter: this.hoverStart,
            onMouseLeave: this.hoverEnd
          }, this.renderItems(children, innerClasses));
        } // Rendering slides and controls


        if (children[0] instanceof Array) {
          var _carouselItems = children[0];
          var _controlLeft = children[1];
          var _controlRight = children[2];
          return React__default.createElement("div", {
            className: outerClasses,
            onMouseEnter: this.hoverStart,
            onMouseLeave: this.hoverEnd
          }, this.renderItems(_carouselItems, innerClasses), _controlLeft, _controlRight);
        } // Rendering indicators, slides and controls


        var indicators = children[0];

        var wrappedOnClick = function wrappedOnClick(e) {
          if (typeof indicators.props.onClickHandler === 'function') {
            _this3.setState({
              indicatorClicked: true
            }, function () {
              return indicators.props.onClickHandler(e);
            });
          }
        };

        var wrappedIndicators = React__default.cloneElement(indicators, {
          onClickHandler: wrappedOnClick
        });
        var carouselItems = children[1];
        var controlLeft = children[2];
        var controlRight = children[3];
        return React__default.createElement("div", {
          className: outerClasses,
          onMouseEnter: this.hoverStart,
          onMouseLeave: this.hoverEnd
        }, wrappedIndicators, this.renderItems(carouselItems, innerClasses), controlLeft, controlRight);
      };

      return Carousel;
    }(React__default.Component);

    Carousel.propTypes = {
      // the current active slide of the carousel
      activeIndex: propTypes.number,
      // a function which should advance the carousel to the next slide (via activeIndex)
      next: propTypes.func.isRequired,
      // a function which should advance the carousel to the previous slide (via activeIndex)
      previous: propTypes.func.isRequired,
      // controls if the left and right arrow keys should control the carousel
      keyboard: propTypes.bool,

      /* If set to "hover", pauses the cycling of the carousel on mouseenter and resumes the cycling of the carousel on
       * mouseleave. If set to false, hovering over the carousel won't pause it. (default: "hover")
       */
      pause: propTypes.oneOf(['hover', false]),
      // Autoplays the carousel after the user manually cycles the first item. If "carousel", autoplays the carousel on load.
      // This is how bootstrap defines it... I would prefer a bool named autoplay or something...
      ride: propTypes.oneOf(['carousel']),
      // the interval at which the carousel automatically cycles (default: 5000)
      // eslint-disable-next-line react/no-unused-prop-types
      interval: propTypes.oneOfType([propTypes.number, propTypes.string, propTypes.bool]),
      children: propTypes.array,
      // called when the mouse enters the Carousel
      mouseEnter: propTypes.func,
      // called when the mouse exits the Carousel
      mouseLeave: propTypes.func,
      // controls whether the slide animation on the Carousel works or not
      slide: propTypes.bool,
      cssModule: propTypes.object,
      className: propTypes.string
    };
    Carousel.defaultProps = {
      interval: 5000,
      pause: 'hover',
      keyboard: true,
      slide: true
    };
    Carousel.childContextTypes = {
      direction: propTypes.string
    };

    var CarouselControl = function CarouselControl(props) {
      var direction = props.direction,
          onClickHandler = props.onClickHandler,
          cssModule = props.cssModule,
          directionText = props.directionText,
          className = props.className;
      var anchorClasses = mapToCssModules(classnames(className, "carousel-control-" + direction), cssModule);
      var iconClasses = mapToCssModules(classnames("carousel-control-" + direction + "-icon"), cssModule);
      var screenReaderClasses = mapToCssModules(classnames('sr-only'), cssModule);
      return React__default.createElement("a", {
        className: anchorClasses,
        role: "button",
        tabIndex: "0",
        onClick: function onClick(e) {
          e.preventDefault();
          onClickHandler();
        }
      }, React__default.createElement("span", {
        className: iconClasses,
        "aria-hidden": "true"
      }), React__default.createElement("span", {
        className: screenReaderClasses
      }, directionText || direction));
    };

    CarouselControl.propTypes = {
      direction: propTypes.oneOf(['prev', 'next']).isRequired,
      onClickHandler: propTypes.func.isRequired,
      cssModule: propTypes.object,
      directionText: propTypes.string,
      className: propTypes.string
    };

    var CarouselIndicators = function CarouselIndicators(props) {
      var items = props.items,
          activeIndex = props.activeIndex,
          cssModule = props.cssModule,
          onClickHandler = props.onClickHandler,
          className = props.className;
      var listClasses = mapToCssModules(classnames(className, 'carousel-indicators'), cssModule);
      var indicators = items.map(function (item, idx) {
        var indicatorClasses = mapToCssModules(classnames({
          active: activeIndex === idx
        }), cssModule);
        return React__default.createElement("li", {
          key: "" + (item.key || Object.values(item).join('')),
          onClick: function onClick(e) {
            e.preventDefault();
            onClickHandler(idx);
          },
          className: indicatorClasses
        });
      });
      return React__default.createElement("ol", {
        className: listClasses
      }, indicators);
    };

    CarouselIndicators.propTypes = {
      items: propTypes.array.isRequired,
      activeIndex: propTypes.number.isRequired,
      cssModule: propTypes.object,
      onClickHandler: propTypes.func.isRequired,
      className: propTypes.string
    };

    var CarouselCaption = function CarouselCaption(props) {
      var captionHeader = props.captionHeader,
          captionText = props.captionText,
          cssModule = props.cssModule,
          className = props.className;
      var classes = mapToCssModules(classnames(className, 'carousel-caption', 'd-none', 'd-md-block'), cssModule);
      return React__default.createElement("div", {
        className: classes
      }, React__default.createElement("h3", null, captionHeader), React__default.createElement("p", null, captionText));
    };

    CarouselCaption.propTypes = {
      captionHeader: propTypes.string,
      captionText: propTypes.string.isRequired,
      cssModule: propTypes.object,
      className: propTypes.string
    };

    var propTypes$w = {
      items: propTypes.array.isRequired,
      indicators: propTypes.bool,
      controls: propTypes.bool,
      autoPlay: propTypes.bool,
      defaultActiveIndex: propTypes.number,
      activeIndex: propTypes.number,
      next: propTypes.func,
      previous: propTypes.func,
      goToIndex: propTypes.func
    };

    var propTypes$x = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$y = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$z = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$A = {
      className: propTypes.string,
      id: propTypes.oneOfType([propTypes.string, propTypes.number]).isRequired,
      type: propTypes.string.isRequired,
      label: propTypes.node,
      inline: propTypes.bool,
      valid: propTypes.bool,
      invalid: propTypes.bool,
      bsSize: propTypes.string,
      htmlFor: propTypes.string,
      cssModule: propTypes.object,
      children: propTypes.oneOfType([propTypes.node, propTypes.array, propTypes.func]),
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.string, propTypes.func])
    };

    function noop() {}

    var propTypes$B = {
      children: propTypes.node.isRequired,
      popperClassName: propTypes.string,
      placement: propTypes.string,
      placementPrefix: propTypes.string,
      arrowClassName: propTypes.string,
      hideArrow: propTypes.bool,
      tag: tagPropType,
      isOpen: propTypes.bool.isRequired,
      cssModule: propTypes.object,
      offset: propTypes.oneOfType([propTypes.string, propTypes.number]),
      fallbackPlacement: propTypes.oneOfType([propTypes.string, propTypes.array]),
      flip: propTypes.bool,
      container: targetPropType,
      target: targetPropType.isRequired,
      modifiers: propTypes.object,
      boundariesElement: propTypes.oneOfType([propTypes.string, DOMElement]),
      onClosed: propTypes.func,
      fade: propTypes.bool,
      transition: propTypes.shape(Fade.propTypes)
    };
    var defaultProps$8 = {
      boundariesElement: 'scrollParent',
      placement: 'auto',
      hideArrow: false,
      isOpen: false,
      offset: 0,
      fallbackPlacement: 'flip',
      flip: true,
      container: 'body',
      modifiers: {},
      onClosed: noop,
      fade: true,
      transition: _objectSpread({}, Fade.defaultProps)
    };

    var PopperContent =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(PopperContent, _React$Component);

      function PopperContent(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.handlePlacementChange = _this.handlePlacementChange.bind(_assertThisInitialized(_this));
        _this.setTargetNode = _this.setTargetNode.bind(_assertThisInitialized(_this));
        _this.getTargetNode = _this.getTargetNode.bind(_assertThisInitialized(_this));
        _this.getRef = _this.getRef.bind(_assertThisInitialized(_this));
        _this.onClosed = _this.onClosed.bind(_assertThisInitialized(_this));
        _this.state = {
          isOpen: props.isOpen
        };
        return _this;
      }

      PopperContent.getDerivedStateFromProps = function getDerivedStateFromProps(props, state) {
        if (props.isOpen && !state.isOpen) {
          return {
            isOpen: props.isOpen
          };
        } else return null;
      };

      var _proto = PopperContent.prototype;

      _proto.componentDidUpdate = function componentDidUpdate() {
        if (this._element && this._element.childNodes && this._element.childNodes[0] && this._element.childNodes[0].focus) {
          this._element.childNodes[0].focus();
        }
      };

      _proto.setTargetNode = function setTargetNode(node) {
        this.targetNode = node;
      };

      _proto.getTargetNode = function getTargetNode() {
        return this.targetNode;
      };

      _proto.getContainerNode = function getContainerNode() {
        return getTarget(this.props.container);
      };

      _proto.getRef = function getRef(ref) {
        this._element = ref;
      };

      _proto.handlePlacementChange = function handlePlacementChange(data) {
        if (this.state.placement !== data.placement) {
          this.setState({
            placement: data.placement
          });
        }

        return data;
      };

      _proto.onClosed = function onClosed() {
        this.props.onClosed();
        this.setState({
          isOpen: false
        });
      };

      _proto.renderChildren = function renderChildren() {
        var _this$props = this.props,
            cssModule = _this$props.cssModule,
            children = _this$props.children,
            isOpen = _this$props.isOpen,
            flip = _this$props.flip,
            target = _this$props.target,
            offset = _this$props.offset,
            fallbackPlacement = _this$props.fallbackPlacement,
            placementPrefix = _this$props.placementPrefix,
            _arrowClassName = _this$props.arrowClassName,
            hideArrow = _this$props.hideArrow,
            _popperClassName = _this$props.popperClassName,
            tag = _this$props.tag,
            container = _this$props.container,
            modifiers = _this$props.modifiers,
            boundariesElement = _this$props.boundariesElement,
            onClosed = _this$props.onClosed,
            fade = _this$props.fade,
            transition = _this$props.transition,
            attrs = _objectWithoutPropertiesLoose(_this$props, ["cssModule", "children", "isOpen", "flip", "target", "offset", "fallbackPlacement", "placementPrefix", "arrowClassName", "hideArrow", "popperClassName", "tag", "container", "modifiers", "boundariesElement", "onClosed", "fade", "transition"]);

        var arrowClassName = mapToCssModules(classnames('arrow', _arrowClassName), cssModule);
        var placement = this.state.placement || attrs.placement;
        var placementFirstPart = placement.split('-')[0];
        var popperClassName = mapToCssModules(classnames(_popperClassName, placementPrefix ? placementPrefix + "-" + placementFirstPart : placementFirstPart), this.props.cssModule);

        var extendedModifiers = _objectSpread({
          offset: {
            offset: offset
          },
          flip: {
            enabled: flip,
            behavior: fallbackPlacement
          },
          preventOverflow: {
            boundariesElement: boundariesElement
          },
          update: {
            enabled: true,
            order: 950,
            fn: this.handlePlacementChange
          }
        }, modifiers);

        var popperTransition = _objectSpread({}, Fade.defaultProps, transition, {
          baseClass: fade ? transition.baseClass : '',
          timeout: fade ? transition.timeout : 0
        });

        return React__default.createElement(Fade, _extends({}, popperTransition, attrs, {
          in: isOpen,
          onExited: this.onClosed,
          tag: tag
        }), React__default.createElement(Popper$1, {
          referenceElement: this.targetNode,
          modifiers: extendedModifiers,
          placement: placement
        }, function (_ref) {
          var ref = _ref.ref,
              style = _ref.style,
              placement = _ref.placement,
              arrowProps = _ref.arrowProps;
          return React__default.createElement("div", {
            ref: ref,
            style: style,
            className: popperClassName,
            "x-placement": placement
          }, children, !hideArrow && React__default.createElement("span", {
            ref: arrowProps.ref,
            className: arrowClassName,
            style: arrowProps.style
          }));
        }));
      };

      _proto.render = function render() {
        this.setTargetNode(getTarget(this.props.target));

        if (this.state.isOpen) {
          return this.props.container === 'inline' ? this.renderChildren() : ReactDOM.createPortal(React__default.createElement("div", {
            ref: this.getRef
          }, this.renderChildren()), this.getContainerNode());
        }

        return null;
      };

      return PopperContent;
    }(React__default.Component);

    PopperContent.propTypes = propTypes$B;
    PopperContent.defaultProps = defaultProps$8;

    var PopperTargetHelper = function PopperTargetHelper(props, context) {
      context.popperManager.setTargetNode(getTarget(props.target));
      return null;
    };

    PopperTargetHelper.contextTypes = {
      popperManager: propTypes.object.isRequired
    };
    PopperTargetHelper.propTypes = {
      target: targetPropType.isRequired
    };

    var propTypes$C = {
      placement: propTypes.oneOf(PopperPlacements),
      target: targetPropType.isRequired,
      container: targetPropType,
      isOpen: propTypes.bool,
      disabled: propTypes.bool,
      hideArrow: propTypes.bool,
      boundariesElement: propTypes.oneOfType([propTypes.string, DOMElement]),
      className: propTypes.string,
      innerClassName: propTypes.string,
      arrowClassName: propTypes.string,
      popperClassName: propTypes.string,
      cssModule: propTypes.object,
      toggle: propTypes.func,
      autohide: propTypes.bool,
      placementPrefix: propTypes.string,
      delay: propTypes.oneOfType([propTypes.shape({
        show: propTypes.number,
        hide: propTypes.number
      }), propTypes.number]),
      modifiers: propTypes.object,
      offset: propTypes.oneOfType([propTypes.string, propTypes.number]),
      innerRef: propTypes.oneOfType([propTypes.func, propTypes.string, propTypes.object]),
      trigger: propTypes.string,
      fade: propTypes.bool,
      flip: propTypes.bool
    };
    var DEFAULT_DELAYS = {
      show: 0,
      hide: 0
    };
    var defaultProps$9 = {
      isOpen: false,
      hideArrow: false,
      autohide: false,
      delay: DEFAULT_DELAYS,
      toggle: function toggle() {},
      trigger: 'click',
      fade: true
    };

    function isInDOMSubtree(element, subtreeRoot) {
      return subtreeRoot && (element === subtreeRoot || subtreeRoot.contains(element));
    }

    var TooltipPopoverWrapper =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(TooltipPopoverWrapper, _React$Component);

      function TooltipPopoverWrapper(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this._target = null;
        _this.addTargetEvents = _this.addTargetEvents.bind(_assertThisInitialized(_this));
        _this.handleDocumentClick = _this.handleDocumentClick.bind(_assertThisInitialized(_this));
        _this.removeTargetEvents = _this.removeTargetEvents.bind(_assertThisInitialized(_this));
        _this.toggle = _this.toggle.bind(_assertThisInitialized(_this));
        _this.showWithDelay = _this.showWithDelay.bind(_assertThisInitialized(_this));
        _this.hideWithDelay = _this.hideWithDelay.bind(_assertThisInitialized(_this));
        _this.onMouseOverTooltipContent = _this.onMouseOverTooltipContent.bind(_assertThisInitialized(_this));
        _this.onMouseLeaveTooltipContent = _this.onMouseLeaveTooltipContent.bind(_assertThisInitialized(_this));
        _this.show = _this.show.bind(_assertThisInitialized(_this));
        _this.hide = _this.hide.bind(_assertThisInitialized(_this));
        _this.onEscKeyDown = _this.onEscKeyDown.bind(_assertThisInitialized(_this));
        _this.getRef = _this.getRef.bind(_assertThisInitialized(_this));
        _this.onClosed = _this.onClosed.bind(_assertThisInitialized(_this));
        _this.state = {
          isOpen: props.isOpen
        };
        return _this;
      }

      var _proto = TooltipPopoverWrapper.prototype;

      _proto.componentDidMount = function componentDidMount() {
        this.updateTarget();
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        this.removeTargetEvents();
      };

      TooltipPopoverWrapper.getDerivedStateFromProps = function getDerivedStateFromProps(props, state) {
        if (props.isOpen && !state.isOpen) {
          return {
            isOpen: props.isOpen
          };
        } else return null;
      };

      _proto.onMouseOverTooltipContent = function onMouseOverTooltipContent() {
        if (this.props.trigger.indexOf('hover') > -1 && !this.props.autohide) {
          if (this._hideTimeout) {
            this.clearHideTimeout();
          }

          if (this.state.isOpen && !this.props.isOpen) {
            this.toggle();
          }
        }
      };

      _proto.onMouseLeaveTooltipContent = function onMouseLeaveTooltipContent(e) {
        if (this.props.trigger.indexOf('hover') > -1 && !this.props.autohide) {
          if (this._showTimeout) {
            this.clearShowTimeout();
          }

          e.persist();
          this._hideTimeout = setTimeout(this.hide.bind(this, e), this.getDelay('hide'));
        }
      };

      _proto.onEscKeyDown = function onEscKeyDown(e) {
        if (e.key === 'Escape') {
          this.hide(e);
        }
      };

      _proto.getRef = function getRef(ref) {
        var innerRef = this.props.innerRef;

        if (innerRef) {
          if (typeof innerRef === 'function') {
            innerRef(ref);
          } else if (typeof innerRef === 'object') {
            innerRef.current = ref;
          }
        }

        this._popover = ref;
      };

      _proto.getDelay = function getDelay(key) {
        var delay = this.props.delay;

        if (typeof delay === 'object') {
          return isNaN(delay[key]) ? DEFAULT_DELAYS[key] : delay[key];
        }

        return delay;
      };

      _proto.show = function show(e) {
        if (!this.props.isOpen) {
          this.clearShowTimeout();
          this.toggle(e);
        }
      };

      _proto.showWithDelay = function showWithDelay(e) {
        if (this._hideTimeout) {
          this.clearHideTimeout();
        }

        this._showTimeout = setTimeout(this.show.bind(this, e), this.getDelay('show'));
      };

      _proto.hide = function hide(e) {
        if (this.props.isOpen) {
          this.clearHideTimeout();
          this.toggle(e);
        }
      };

      _proto.hideWithDelay = function hideWithDelay(e) {
        if (this._showTimeout) {
          this.clearShowTimeout();
        }

        this._hideTimeout = setTimeout(this.hide.bind(this, e), this.getDelay('hide'));
      };

      _proto.clearShowTimeout = function clearShowTimeout() {
        clearTimeout(this._showTimeout);
        this._showTimeout = undefined;
      };

      _proto.clearHideTimeout = function clearHideTimeout() {
        clearTimeout(this._hideTimeout);
        this._hideTimeout = undefined;
      };

      _proto.handleDocumentClick = function handleDocumentClick(e) {
        var triggers = this.props.trigger.split(' ');

        if (triggers.indexOf('legacy') > -1 && (this.props.isOpen || isInDOMSubtree(e.target, this._target))) {
          if (this._hideTimeout) {
            this.clearHideTimeout();
          }

          if (this.props.isOpen && !isInDOMSubtree(e.target, this._popover)) {
            this.hideWithDelay(e);
          } else if (!this.props.isOpen) {
            this.showWithDelay(e);
          }
        } else if (triggers.indexOf('click') > -1 && isInDOMSubtree(e.target, this._target)) {
          if (this._hideTimeout) {
            this.clearHideTimeout();
          }

          if (!this.props.isOpen) {
            this.showWithDelay(e);
          } else {
            this.hideWithDelay(e);
          }
        }
      };

      _proto.addTargetEvents = function addTargetEvents() {
        if (this.props.trigger) {
          var triggers = this.props.trigger.split(' ');

          if (triggers.indexOf('manual') === -1) {
            if (triggers.indexOf('click') > -1 || triggers.indexOf('legacy') > -1) {
              document.addEventListener('click', this.handleDocumentClick, true);
            }

            if (this._target) {
              if (triggers.indexOf('hover') > -1) {
                this._target.addEventListener('mouseover', this.showWithDelay, true);

                this._target.addEventListener('mouseout', this.hideWithDelay, true);
              }

              if (triggers.indexOf('focus') > -1) {
                this._target.addEventListener('focusin', this.show, true);

                this._target.addEventListener('focusout', this.hide, true);
              }

              this._target.addEventListener('keydown', this.onEscKeyDown, true);
            }
          }
        }
      };

      _proto.removeTargetEvents = function removeTargetEvents() {
        if (this._target) {
          this._target.removeEventListener('mouseover', this.showWithDelay, true);

          this._target.removeEventListener('mouseout', this.hideWithDelay, true);

          this._target.removeEventListener('keydown', this.onEscKeyDown, true);

          this._target.removeEventListener('focusin', this.show, true);

          this._target.removeEventListener('focusout', this.hide, true);
        }

        document.removeEventListener('click', this.handleDocumentClick, true);
      };

      _proto.updateTarget = function updateTarget() {
        var newTarget = getTarget(this.props.target);

        if (newTarget !== this._target) {
          this.removeTargetEvents();
          this._target = newTarget;
          this.addTargetEvents();
        }
      };

      _proto.toggle = function toggle(e) {
        if (this.props.disabled) {
          return e && e.preventDefault();
        }

        return this.props.toggle(e);
      };

      _proto.onClosed = function onClosed() {
        this.setState({
          isOpen: false
        });
      };

      _proto.render = function render() {
        if (!this.state.isOpen) {
          return null;
        }

        this.updateTarget();
        var _this$props = this.props,
            className = _this$props.className,
            cssModule = _this$props.cssModule,
            innerClassName = _this$props.innerClassName,
            target = _this$props.target,
            isOpen = _this$props.isOpen,
            hideArrow = _this$props.hideArrow,
            boundariesElement = _this$props.boundariesElement,
            placement = _this$props.placement,
            placementPrefix = _this$props.placementPrefix,
            arrowClassName = _this$props.arrowClassName,
            popperClassName = _this$props.popperClassName,
            container = _this$props.container,
            modifiers = _this$props.modifiers,
            offset = _this$props.offset,
            fade = _this$props.fade,
            flip = _this$props.flip;
        var attributes = omit(this.props, Object.keys(propTypes$C));
        var popperClasses = mapToCssModules(popperClassName, cssModule);
        var classes = mapToCssModules(innerClassName, cssModule);
        return React__default.createElement(PopperContent, {
          className: className,
          target: target,
          isOpen: isOpen,
          hideArrow: hideArrow,
          boundariesElement: boundariesElement,
          placement: placement,
          placementPrefix: placementPrefix,
          arrowClassName: arrowClassName,
          popperClassName: popperClasses,
          container: container,
          modifiers: modifiers,
          offset: offset,
          cssModule: cssModule,
          onClosed: this.onClosed,
          fade: fade,
          flip: flip
        }, React__default.createElement("div", _extends({}, attributes, {
          ref: this.getRef,
          className: classes,
          role: "tooltip",
          "aria-hidden": isOpen,
          onMouseOver: this.onMouseOverTooltipContent,
          onMouseLeave: this.onMouseLeaveTooltipContent,
          onKeyDown: this.onEscKeyDown
        })));
      };

      return TooltipPopoverWrapper;
    }(React__default.Component);

    TooltipPopoverWrapper.propTypes = propTypes$C;
    TooltipPopoverWrapper.defaultProps = defaultProps$9;

    var defaultProps$a = {
      placement: 'right',
      placementPrefix: 'bs-popover',
      trigger: 'click'
    };

    var Popover = function Popover(props) {
      var popperClasses = classnames('popover', 'show');
      var classes = classnames('popover-inner', props.innerClassName);
      return React__default.createElement(TooltipPopoverWrapper, _extends({}, props, {
        popperClassName: popperClasses,
        innerClassName: classes
      }));
    };

    Popover.propTypes = propTypes$C;
    Popover.defaultProps = defaultProps$a;

    var omitKeys = ['defaultOpen'];

    var UncontrolledPopover =
    /*#__PURE__*/
    function (_Component) {
      _inheritsLoose(UncontrolledPopover, _Component);

      function UncontrolledPopover(props) {
        var _this;

        _this = _Component.call(this, props) || this;
        _this.state = {
          isOpen: props.defaultOpen || false
        };
        _this.toggle = _this.toggle.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = UncontrolledPopover.prototype;

      _proto.toggle = function toggle() {
        this.setState({
          isOpen: !this.state.isOpen
        });
      };

      _proto.render = function render() {
        return React__default.createElement(Popover, _extends({
          isOpen: this.state.isOpen,
          toggle: this.toggle
        }, omit(this.props, omitKeys)));
      };

      return UncontrolledPopover;
    }(React.Component);
    UncontrolledPopover.propTypes = _objectSpread({
      defaultOpen: propTypes.bool
    }, Popover.propTypes);

    var propTypes$D = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$E = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    /**
     * lodash (Custom Build) <https://lodash.com/>
     * Build: `lodash modularize exports="npm" -o ./`
     * Copyright jQuery Foundation and other contributors <https://jquery.org/>
     * Released under MIT license <https://lodash.com/license>
     * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
     * Copyright Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
     */

    var propTypes$F = {
      children: propTypes.node,
      bar: propTypes.bool,
      multi: propTypes.bool,
      tag: tagPropType,
      value: propTypes.oneOfType([propTypes.string, propTypes.number]),
      max: propTypes.oneOfType([propTypes.string, propTypes.number]),
      animated: propTypes.bool,
      striped: propTypes.bool,
      color: propTypes.string,
      className: propTypes.string,
      barClassName: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$G = {
      children: propTypes.node.isRequired,
      node: propTypes.any
    };

    var Portal =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Portal, _React$Component);

      function Portal() {
        return _React$Component.apply(this, arguments) || this;
      }

      var _proto = Portal.prototype;

      _proto.componentWillUnmount = function componentWillUnmount() {
        if (this.defaultNode) {
          document.body.removeChild(this.defaultNode);
        }

        this.defaultNode = null;
      };

      _proto.render = function render() {
        if (!canUseDOM) {
          return null;
        }

        if (!this.props.node && !this.defaultNode) {
          this.defaultNode = document.createElement('div');
          document.body.appendChild(this.defaultNode);
        }

        return ReactDOM.createPortal(this.props.children, this.props.node || this.defaultNode);
      };

      return Portal;
    }(React__default.Component);

    Portal.propTypes = propTypes$G;

    function noop$1() {}

    var FadePropTypes = propTypes.shape(Fade.propTypes);
    var propTypes$H = {
      isOpen: propTypes.bool,
      autoFocus: propTypes.bool,
      centered: propTypes.bool,
      scrollable: propTypes.bool,
      size: propTypes.string,
      toggle: propTypes.func,
      keyboard: propTypes.bool,
      role: propTypes.string,
      labelledBy: propTypes.string,
      backdrop: propTypes.oneOfType([propTypes.bool, propTypes.oneOf(['static'])]),
      onEnter: propTypes.func,
      onExit: propTypes.func,
      onOpened: propTypes.func,
      onClosed: propTypes.func,
      children: propTypes.node,
      className: propTypes.string,
      wrapClassName: propTypes.string,
      modalClassName: propTypes.string,
      backdropClassName: propTypes.string,
      contentClassName: propTypes.string,
      external: propTypes.node,
      fade: propTypes.bool,
      cssModule: propTypes.object,
      zIndex: propTypes.oneOfType([propTypes.number, propTypes.string]),
      backdropTransition: FadePropTypes,
      modalTransition: FadePropTypes,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.string, propTypes.func]),
      unmountOnClose: propTypes.bool,
      returnFocusAfterClose: propTypes.bool
    };
    var propsToOmit = Object.keys(propTypes$H);
    var defaultProps$b = {
      isOpen: false,
      autoFocus: true,
      centered: false,
      scrollable: false,
      role: 'dialog',
      backdrop: true,
      keyboard: true,
      zIndex: 1050,
      fade: true,
      onOpened: noop$1,
      onClosed: noop$1,
      modalTransition: {
        timeout: TransitionTimeouts.Modal
      },
      backdropTransition: {
        mountOnEnter: true,
        timeout: TransitionTimeouts.Fade // uses standard fade transition

      },
      unmountOnClose: true,
      returnFocusAfterClose: true
    };

    var Modal =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Modal, _React$Component);

      function Modal(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this._element = null;
        _this._originalBodyPadding = null;
        _this.getFocusableChildren = _this.getFocusableChildren.bind(_assertThisInitialized(_this));
        _this.handleBackdropClick = _this.handleBackdropClick.bind(_assertThisInitialized(_this));
        _this.handleBackdropMouseDown = _this.handleBackdropMouseDown.bind(_assertThisInitialized(_this));
        _this.handleEscape = _this.handleEscape.bind(_assertThisInitialized(_this));
        _this.handleTab = _this.handleTab.bind(_assertThisInitialized(_this));
        _this.onOpened = _this.onOpened.bind(_assertThisInitialized(_this));
        _this.onClosed = _this.onClosed.bind(_assertThisInitialized(_this));
        _this.manageFocusAfterClose = _this.manageFocusAfterClose.bind(_assertThisInitialized(_this));
        _this.state = {
          isOpen: props.isOpen
        };

        if (props.isOpen) {
          _this.init();
        }

        return _this;
      }

      var _proto = Modal.prototype;

      _proto.componentDidMount = function componentDidMount() {
        if (this.props.onEnter) {
          this.props.onEnter();
        }

        if (this.state.isOpen && this.props.autoFocus) {
          this.setFocus();
        }

        this._isMounted = true;
      };

      _proto.componentDidUpdate = function componentDidUpdate(prevProps, prevState) {
        if (this.props.isOpen && !prevProps.isOpen) {
          this.init();
          this.setState({
            isOpen: true
          }); // let render() renders Modal Dialog first

          return;
        } // now Modal Dialog is rendered and we can refer this._element and this._dialog


        if (this.props.autoFocus && this.state.isOpen && !prevState.isOpen) {
          this.setFocus();
        }

        if (this._element && prevProps.zIndex !== this.props.zIndex) {
          this._element.style.zIndex = this.props.zIndex;
        }
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        if (this.props.onExit) {
          this.props.onExit();
        }

        if (this._element) {
          this.destroy();

          if (this.state.isOpen) {
            this.close();
          }
        }

        this._isMounted = false;
      };

      _proto.onOpened = function onOpened(node, isAppearing) {
        this.props.onOpened();
        (this.props.modalTransition.onEntered || noop$1)(node, isAppearing);
      };

      _proto.onClosed = function onClosed(node) {
        var unmountOnClose = this.props.unmountOnClose; // so all methods get called before it is unmounted

        this.props.onClosed();
        (this.props.modalTransition.onExited || noop$1)(node);

        if (unmountOnClose) {
          this.destroy();
        }

        this.close();

        if (this._isMounted) {
          this.setState({
            isOpen: false
          });
        }
      };

      _proto.setFocus = function setFocus() {
        if (this._dialog && this._dialog.parentNode && typeof this._dialog.parentNode.focus === 'function') {
          this._dialog.parentNode.focus();
        }
      };

      _proto.getFocusableChildren = function getFocusableChildren() {
        return this._element.querySelectorAll(focusableElements.join(', '));
      };

      _proto.getFocusedChild = function getFocusedChild() {
        var currentFocus;
        var focusableChildren = this.getFocusableChildren();

        try {
          currentFocus = document.activeElement;
        } catch (err) {
          currentFocus = focusableChildren[0];
        }

        return currentFocus;
      } // not mouseUp because scrollbar fires it, shouldn't close when user scrolls
      ;

      _proto.handleBackdropClick = function handleBackdropClick(e) {
        if (e.target === this._mouseDownElement) {
          e.stopPropagation();
          if (!this.props.isOpen || this.props.backdrop !== true) return;
          var backdrop = this._dialog ? this._dialog.parentNode : null;

          if (backdrop && e.target === backdrop && this.props.toggle) {
            this.props.toggle(e);
          }
        }
      };

      _proto.handleTab = function handleTab(e) {
        if (e.which !== 9) return;
        var focusableChildren = this.getFocusableChildren();
        var totalFocusable = focusableChildren.length;
        if (totalFocusable === 0) return;
        var currentFocus = this.getFocusedChild();
        var focusedIndex = 0;

        for (var i = 0; i < totalFocusable; i += 1) {
          if (focusableChildren[i] === currentFocus) {
            focusedIndex = i;
            break;
          }
        }

        if (e.shiftKey && focusedIndex === 0) {
          e.preventDefault();
          focusableChildren[totalFocusable - 1].focus();
        } else if (!e.shiftKey && focusedIndex === totalFocusable - 1) {
          e.preventDefault();
          focusableChildren[0].focus();
        }
      };

      _proto.handleBackdropMouseDown = function handleBackdropMouseDown(e) {
        this._mouseDownElement = e.target;
      };

      _proto.handleEscape = function handleEscape(e) {
        if (this.props.isOpen && this.props.keyboard && e.keyCode === 27 && this.props.toggle) {
          e.preventDefault();
          e.stopPropagation();
          this.props.toggle(e);
        }
      };

      _proto.init = function init() {
        try {
          this._triggeringElement = document.activeElement;
        } catch (err) {
          this._triggeringElement = null;
        }

        if (!this._element) {
          this._element = document.createElement('div');

          this._element.setAttribute('tabindex', '-1');

          this._element.style.position = 'relative';
          this._element.style.zIndex = this.props.zIndex;
          document.body.appendChild(this._element);
        }

        this._originalBodyPadding = getOriginalBodyPadding();
        conditionallyUpdateScrollbar();

        if (Modal.openCount === 0) {
          document.body.className = classnames(document.body.className, mapToCssModules('modal-open', this.props.cssModule));
        }

        Modal.openCount += 1;
      };

      _proto.destroy = function destroy() {
        if (this._element) {
          document.body.removeChild(this._element);
          this._element = null;
        }

        this.manageFocusAfterClose();
      };

      _proto.manageFocusAfterClose = function manageFocusAfterClose() {
        if (this._triggeringElement) {
          var returnFocusAfterClose = this.props.returnFocusAfterClose;
          if (this._triggeringElement.focus && returnFocusAfterClose) this._triggeringElement.focus();
          this._triggeringElement = null;
        }
      };

      _proto.close = function close() {
        if (Modal.openCount <= 1) {
          var modalOpenClassName = mapToCssModules('modal-open', this.props.cssModule); // Use regex to prevent matching `modal-open` as part of a different class, e.g. `my-modal-opened`

          var modalOpenClassNameRegex = new RegExp("(^| )" + modalOpenClassName + "( |$)");
          document.body.className = document.body.className.replace(modalOpenClassNameRegex, ' ').trim();
        }

        this.manageFocusAfterClose();
        Modal.openCount = Math.max(0, Modal.openCount - 1);
        setScrollbarWidth(this._originalBodyPadding);
      };

      _proto.renderModalDialog = function renderModalDialog() {
        var _classNames,
            _this2 = this;

        var attributes = omit(this.props, propsToOmit);
        var dialogBaseClass = 'modal-dialog';
        return React__default.createElement("div", _extends({}, attributes, {
          className: mapToCssModules(classnames(dialogBaseClass, this.props.className, (_classNames = {}, _classNames["modal-" + this.props.size] = this.props.size, _classNames[dialogBaseClass + "-centered"] = this.props.centered, _classNames[dialogBaseClass + "-scrollable"] = this.props.scrollable, _classNames)), this.props.cssModule),
          role: "document",
          ref: function ref(c) {
            _this2._dialog = c;
          }
        }), React__default.createElement("div", {
          className: mapToCssModules(classnames('modal-content', this.props.contentClassName), this.props.cssModule)
        }, this.props.children));
      };

      _proto.render = function render() {
        var unmountOnClose = this.props.unmountOnClose;

        if (!!this._element && (this.state.isOpen || !unmountOnClose)) {
          var isModalHidden = !!this._element && !this.state.isOpen && !unmountOnClose;
          this._element.style.display = isModalHidden ? 'none' : 'block';
          var _this$props = this.props,
              wrapClassName = _this$props.wrapClassName,
              modalClassName = _this$props.modalClassName,
              backdropClassName = _this$props.backdropClassName,
              cssModule = _this$props.cssModule,
              isOpen = _this$props.isOpen,
              backdrop = _this$props.backdrop,
              role = _this$props.role,
              labelledBy = _this$props.labelledBy,
              external = _this$props.external,
              innerRef = _this$props.innerRef;
          var modalAttributes = {
            onClick: this.handleBackdropClick,
            onMouseDown: this.handleBackdropMouseDown,
            onKeyUp: this.handleEscape,
            onKeyDown: this.handleTab,
            style: {
              display: 'block'
            },
            'aria-labelledby': labelledBy,
            role: role,
            tabIndex: '-1'
          };
          var hasTransition = this.props.fade;

          var modalTransition = _objectSpread({}, Fade.defaultProps, this.props.modalTransition, {
            baseClass: hasTransition ? this.props.modalTransition.baseClass : '',
            timeout: hasTransition ? this.props.modalTransition.timeout : 0
          });

          var backdropTransition = _objectSpread({}, Fade.defaultProps, this.props.backdropTransition, {
            baseClass: hasTransition ? this.props.backdropTransition.baseClass : '',
            timeout: hasTransition ? this.props.backdropTransition.timeout : 0
          });

          var Backdrop = backdrop && (hasTransition ? React__default.createElement(Fade, _extends({}, backdropTransition, {
            in: isOpen && !!backdrop,
            cssModule: cssModule,
            className: mapToCssModules(classnames('modal-backdrop', backdropClassName), cssModule)
          })) : React__default.createElement("div", {
            className: mapToCssModules(classnames('modal-backdrop', 'show', backdropClassName), cssModule)
          }));
          return React__default.createElement(Portal, {
            node: this._element
          }, React__default.createElement("div", {
            className: mapToCssModules(wrapClassName)
          }, React__default.createElement(Fade, _extends({}, modalAttributes, modalTransition, {
            in: isOpen,
            onEntered: this.onOpened,
            onExited: this.onClosed,
            cssModule: cssModule,
            className: mapToCssModules(classnames('modal', modalClassName), cssModule),
            innerRef: innerRef
          }), external, this.renderModalDialog()), Backdrop));
        }

        return null;
      };

      return Modal;
    }(React__default.Component);

    Modal.propTypes = propTypes$H;
    Modal.defaultProps = defaultProps$b;
    Modal.openCount = 0;

    var propTypes$I = {
      tag: tagPropType,
      wrapTag: tagPropType,
      toggle: propTypes.func,
      className: propTypes.string,
      cssModule: propTypes.object,
      children: propTypes.node,
      closeAriaLabel: propTypes.string,
      charCode: propTypes.oneOfType([propTypes.string, propTypes.number]),
      close: propTypes.object
    };

    var propTypes$J = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$K = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var defaultProps$c = {
      placement: 'top',
      autohide: true,
      placementPrefix: 'bs-tooltip',
      trigger: 'click hover focus'
    };

    var Tooltip = function Tooltip(props) {
      var popperClasses = classnames('tooltip', 'show');
      var classes = classnames('tooltip-inner', props.innerClassName);
      return React__default.createElement(TooltipPopoverWrapper, _extends({}, props, {
        popperClassName: popperClasses,
        innerClassName: classes
      }));
    };

    Tooltip.propTypes = propTypes$C;
    Tooltip.defaultProps = defaultProps$c;

    var propTypes$L = {
      className: propTypes.string,
      cssModule: propTypes.object,
      size: propTypes.string,
      bordered: propTypes.bool,
      borderless: propTypes.bool,
      striped: propTypes.bool,
      dark: propTypes.bool,
      hover: propTypes.bool,
      responsive: propTypes.oneOfType([propTypes.bool, propTypes.string]),
      tag: tagPropType,
      responsiveTag: tagPropType,
      innerRef: propTypes.oneOfType([propTypes.func, propTypes.string, propTypes.object])
    };

    var propTypes$M = {
      tag: tagPropType,
      flush: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$N = {
      children: propTypes.node,
      inline: propTypes.bool,
      tag: tagPropType,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.func, propTypes.string]),
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$O = {
      children: propTypes.node,
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object,
      valid: propTypes.bool,
      tooltip: propTypes.bool
    };

    var propTypes$P = {
      children: propTypes.node,
      row: propTypes.bool,
      check: propTypes.bool,
      inline: propTypes.bool,
      disabled: propTypes.bool,
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$Q = {
      children: propTypes.node,
      inline: propTypes.bool,
      tag: tagPropType,
      color: propTypes.string,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$R = {
      children: propTypes.node,
      type: propTypes.string,
      size: propTypes.string,
      bsSize: propTypes.string,
      valid: propTypes.bool,
      invalid: propTypes.bool,
      tag: tagPropType,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.func, propTypes.string]),
      plaintext: propTypes.bool,
      addon: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object
    };
    var defaultProps$d = {
      type: 'text'
    };

    var Input =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Input, _React$Component);

      function Input(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.getRef = _this.getRef.bind(_assertThisInitialized(_this));
        _this.focus = _this.focus.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = Input.prototype;

      _proto.getRef = function getRef(ref) {
        if (this.props.innerRef) {
          this.props.innerRef(ref);
        }

        this.ref = ref;
      };

      _proto.focus = function focus() {
        if (this.ref) {
          this.ref.focus();
        }
      };

      _proto.render = function render() {
        var _this$props = this.props,
            className = _this$props.className,
            cssModule = _this$props.cssModule,
            type = _this$props.type,
            bsSize = _this$props.bsSize,
            valid = _this$props.valid,
            invalid = _this$props.invalid,
            tag = _this$props.tag,
            addon = _this$props.addon,
            plaintext = _this$props.plaintext,
            innerRef = _this$props.innerRef,
            attributes = _objectWithoutPropertiesLoose(_this$props, ["className", "cssModule", "type", "bsSize", "valid", "invalid", "tag", "addon", "plaintext", "innerRef"]);

        var checkInput = ['radio', 'checkbox'].indexOf(type) > -1;
        var isNotaNumber = new RegExp('\\D', 'g');
        var fileInput = type === 'file';
        var textareaInput = type === 'textarea';
        var selectInput = type === 'select';
        var Tag = tag || (selectInput || textareaInput ? type : 'input');
        var formControlClass = 'form-control';

        if (plaintext) {
          formControlClass = formControlClass + "-plaintext";
          Tag = tag || 'input';
        } else if (fileInput) {
          formControlClass = formControlClass + "-file";
        } else if (checkInput) {
          if (addon) {
            formControlClass = null;
          } else {
            formControlClass = 'form-check-input';
          }
        }

        if (attributes.size && isNotaNumber.test(attributes.size)) {
          warnOnce('Please use the prop "bsSize" instead of the "size" to bootstrap\'s input sizing.');
          bsSize = attributes.size;
          delete attributes.size;
        }

        var classes = mapToCssModules(classnames(className, invalid && 'is-invalid', valid && 'is-valid', bsSize ? "form-control-" + bsSize : false, formControlClass), cssModule);

        if (Tag === 'input' || tag && typeof tag === 'function') {
          attributes.type = type;
        }

        if (attributes.children && !(plaintext || type === 'select' || typeof Tag !== 'string' || Tag === 'select')) {
          warnOnce("Input with a type of \"" + type + "\" cannot have children. Please use \"value\"/\"defaultValue\" instead.");
          delete attributes.children;
        }

        return React__default.createElement(Tag, _extends({}, attributes, {
          ref: innerRef,
          className: classes
        }));
      };

      return Input;
    }(React__default.Component);

    Input.propTypes = propTypes$R;
    Input.defaultProps = defaultProps$d;

    var propTypes$S = {
      tag: tagPropType,
      size: propTypes.string,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$T = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$U = {
      tag: tagPropType,
      addonType: propTypes.oneOf(['prepend', 'append']).isRequired,
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$V = {
      addonType: propTypes.oneOf(['prepend', 'append']).isRequired,
      children: propTypes.node
    };

    var stringOrNumberProp$1 = propTypes.oneOfType([propTypes.number, propTypes.string]);
    var columnProps$1 = propTypes.oneOfType([propTypes.string, propTypes.number, propTypes.shape({
      size: stringOrNumberProp$1,
      order: stringOrNumberProp$1,
      offset: stringOrNumberProp$1
    })]);
    var propTypes$W = {
      children: propTypes.node,
      hidden: propTypes.bool,
      check: propTypes.bool,
      size: propTypes.string,
      for: propTypes.string,
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object,
      xs: columnProps$1,
      sm: columnProps$1,
      md: columnProps$1,
      lg: columnProps$1,
      xl: columnProps$1,
      widths: propTypes.array
    };

    var propTypes$X = {
      body: propTypes.bool,
      bottom: propTypes.bool,
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object,
      heading: propTypes.bool,
      left: propTypes.bool,
      list: propTypes.bool,
      middle: propTypes.bool,
      object: propTypes.bool,
      right: propTypes.bool,
      tag: tagPropType,
      top: propTypes.bool
    };

    var propTypes$Y = {
      children: propTypes.node,
      className: propTypes.string,
      listClassName: propTypes.string,
      cssModule: propTypes.object,
      size: propTypes.string,
      tag: tagPropType,
      listTag: tagPropType,
      'aria-label': propTypes.string
    };

    var propTypes$Z = {
      active: propTypes.bool,
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object,
      disabled: propTypes.bool,
      tag: tagPropType
    };

    var propTypes$_ = {
      'aria-label': propTypes.string,
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object,
      next: propTypes.bool,
      previous: propTypes.bool,
      first: propTypes.bool,
      last: propTypes.bool,
      tag: tagPropType
    };

    /**
     * TabContext
     * {
     *  activeTabId: PropTypes.any
     * }
     */

    var TabContext = React__default.createContext({});

    var propTypes$$ = {
      tag: tagPropType,
      activeTab: propTypes.any,
      className: propTypes.string,
      cssModule: propTypes.object
    };
    var defaultProps$e = {
      tag: 'div'
    };

    var TabContent =
    /*#__PURE__*/
    function (_Component) {
      _inheritsLoose(TabContent, _Component);

      TabContent.getDerivedStateFromProps = function getDerivedStateFromProps(nextProps, prevState) {
        if (prevState.activeTab !== nextProps.activeTab) {
          return {
            activeTab: nextProps.activeTab
          };
        }

        return null;
      };

      function TabContent(props) {
        var _this;

        _this = _Component.call(this, props) || this;
        _this.state = {
          activeTab: _this.props.activeTab
        };
        return _this;
      }

      var _proto = TabContent.prototype;

      _proto.render = function render() {
        var _this$props = this.props,
            className = _this$props.className,
            cssModule = _this$props.cssModule,
            Tag = _this$props.tag;
        var attributes = omit(this.props, Object.keys(propTypes$$));
        var classes = mapToCssModules(classnames('tab-content', className), cssModule);
        return React__default.createElement(TabContext.Provider, {
          value: {
            activeTabId: this.state.activeTab
          }
        }, React__default.createElement(Tag, _extends({}, attributes, {
          className: classes
        })));
      };

      return TabContent;
    }(React.Component);

    polyfill(TabContent);
    TabContent.propTypes = propTypes$$;
    TabContent.defaultProps = defaultProps$e;

    var propTypes$10 = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object,
      tabId: propTypes.any
    };

    var propTypes$11 = {
      tag: tagPropType,
      fluid: propTypes.bool,
      className: propTypes.string,
      cssModule: propTypes.object
    };

    var propTypes$12 = {
      children: propTypes.node,
      className: propTypes.string,
      closeClassName: propTypes.string,
      closeAriaLabel: propTypes.string,
      cssModule: propTypes.object,
      color: propTypes.string,
      fade: propTypes.bool,
      isOpen: propTypes.bool,
      toggle: propTypes.func,
      tag: tagPropType,
      transition: propTypes.shape(Fade.propTypes),
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.string, propTypes.func])
    };
    var defaultProps$f = {
      color: 'success',
      isOpen: true,
      tag: 'div',
      closeAriaLabel: 'Close',
      fade: true,
      transition: _objectSpread({}, Fade.defaultProps, {
        unmountOnExit: true
      })
    };

    function Alert(props) {
      var className = props.className,
          closeClassName = props.closeClassName,
          closeAriaLabel = props.closeAriaLabel,
          cssModule = props.cssModule,
          Tag = props.tag,
          color = props.color,
          isOpen = props.isOpen,
          toggle = props.toggle,
          children = props.children,
          transition = props.transition,
          fade = props.fade,
          innerRef = props.innerRef,
          attributes = _objectWithoutPropertiesLoose(props, ["className", "closeClassName", "closeAriaLabel", "cssModule", "tag", "color", "isOpen", "toggle", "children", "transition", "fade", "innerRef"]);

      var classes = mapToCssModules(classnames(className, 'alert', "alert-" + color, {
        'alert-dismissible': toggle
      }), cssModule);
      var closeClasses = mapToCssModules(classnames('close', closeClassName), cssModule);

      var alertTransition = _objectSpread({}, Fade.defaultProps, transition, {
        baseClass: fade ? transition.baseClass : '',
        timeout: fade ? transition.timeout : 0
      });

      return React__default.createElement(Fade, _extends({}, attributes, alertTransition, {
        tag: Tag,
        className: classes,
        in: isOpen,
        role: "alert",
        innerRef: innerRef
      }), toggle ? React__default.createElement("button", {
        type: "button",
        className: closeClasses,
        "aria-label": closeAriaLabel,
        onClick: toggle
      }, React__default.createElement("span", {
        "aria-hidden": "true"
      }, "\xD7")) : null, children);
    }

    Alert.propTypes = propTypes$12;
    Alert.defaultProps = defaultProps$f;

    var propTypes$13 = {
      children: propTypes.node,
      className: propTypes.string,
      cssModule: propTypes.object,
      fade: propTypes.bool,
      isOpen: propTypes.bool,
      tag: tagPropType,
      transition: propTypes.shape(Fade.propTypes),
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.string, propTypes.func])
    };
    var defaultProps$g = {
      isOpen: true,
      tag: 'div',
      fade: true,
      transition: _objectSpread({}, Fade.defaultProps, {
        unmountOnExit: true
      })
    };

    var propTypes$14 = {
      tag: tagPropType,
      className: propTypes.string,
      cssModule: propTypes.object,
      innerRef: propTypes.oneOfType([propTypes.object, propTypes.string, propTypes.func])
    };

    var propTypes$15 = {
      tag: tagPropType,
      icon: propTypes.oneOfType([propTypes.string, propTypes.node]),
      wrapTag: tagPropType,
      toggle: propTypes.func,
      className: propTypes.string,
      cssModule: propTypes.object,
      children: propTypes.node,
      closeAriaLabel: propTypes.string,
      charCode: propTypes.oneOfType([propTypes.string, propTypes.number]),
      close: propTypes.object
    };

    var _transitionStatusToCl;

    var propTypes$16 = _objectSpread({}, reactTransitionGroup_1.propTypes, {
      isOpen: propTypes.bool,
      children: propTypes.oneOfType([propTypes.arrayOf(propTypes.node), propTypes.node]),
      tag: tagPropType,
      className: propTypes.node,
      navbar: propTypes.bool,
      cssModule: propTypes.object,
      innerRef: propTypes.oneOfType([propTypes.func, propTypes.string, propTypes.object])
    });

    var defaultProps$h = _objectSpread({}, reactTransitionGroup_1.defaultProps, {
      isOpen: false,
      appear: false,
      enter: true,
      exit: true,
      tag: 'div',
      timeout: TransitionTimeouts.Collapse
    });

    var transitionStatusToClassHash = (_transitionStatusToCl = {}, _transitionStatusToCl[TransitionStatuses.ENTERING] = 'collapsing', _transitionStatusToCl[TransitionStatuses.ENTERED] = 'collapse show', _transitionStatusToCl[TransitionStatuses.EXITING] = 'collapsing', _transitionStatusToCl[TransitionStatuses.EXITED] = 'collapse', _transitionStatusToCl);

    var propTypes$17 = {
      tag: tagPropType,
      active: propTypes.bool,
      disabled: propTypes.bool,
      color: propTypes.string,
      action: propTypes.bool,
      className: propTypes.any,
      cssModule: propTypes.object
    };

    var propTypes$18 = {
      tag: tagPropType,
      className: propTypes.any,
      cssModule: propTypes.object
    };

    var propTypes$19 = {
      tag: tagPropType,
      className: propTypes.any,
      cssModule: propTypes.object
    };

    var omitKeys$1 = ['defaultOpen'];

    var UncontrolledButtonDropdown =
    /*#__PURE__*/
    function (_Component) {
      _inheritsLoose(UncontrolledButtonDropdown, _Component);

      function UncontrolledButtonDropdown(props) {
        var _this;

        _this = _Component.call(this, props) || this;
        _this.state = {
          isOpen: props.defaultOpen || false
        };
        _this.toggle = _this.toggle.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = UncontrolledButtonDropdown.prototype;

      _proto.toggle = function toggle() {
        this.setState({
          isOpen: !this.state.isOpen
        });
      };

      _proto.render = function render() {
        return React__default.createElement(ButtonDropdown, _extends({
          isOpen: this.state.isOpen,
          toggle: this.toggle
        }, omit(this.props, omitKeys$1)));
      };

      return UncontrolledButtonDropdown;
    }(React.Component);
    UncontrolledButtonDropdown.propTypes = _objectSpread({
      defaultOpen: propTypes.bool
    }, ButtonDropdown.propTypes);

    var propTypes$1a = {
      defaultOpen: propTypes.bool,
      toggler: propTypes.string.isRequired,
      toggleEvents: propTypes.arrayOf(propTypes.string)
    };

    var omitKeys$2 = ['defaultOpen'];

    var UncontrolledDropdown =
    /*#__PURE__*/
    function (_Component) {
      _inheritsLoose(UncontrolledDropdown, _Component);

      function UncontrolledDropdown(props) {
        var _this;

        _this = _Component.call(this, props) || this;
        _this.state = {
          isOpen: props.defaultOpen || false
        };
        _this.toggle = _this.toggle.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = UncontrolledDropdown.prototype;

      _proto.toggle = function toggle() {
        this.setState({
          isOpen: !this.state.isOpen
        });
      };

      _proto.render = function render() {
        return React__default.createElement(Dropdown, _extends({
          isOpen: this.state.isOpen,
          toggle: this.toggle
        }, omit(this.props, omitKeys$2)));
      };

      return UncontrolledDropdown;
    }(React.Component);
    UncontrolledDropdown.propTypes = _objectSpread({
      defaultOpen: propTypes.bool
    }, Dropdown.propTypes);

    var omitKeys$3 = ['defaultOpen'];

    var UncontrolledTooltip =
    /*#__PURE__*/
    function (_Component) {
      _inheritsLoose(UncontrolledTooltip, _Component);

      function UncontrolledTooltip(props) {
        var _this;

        _this = _Component.call(this, props) || this;
        _this.state = {
          isOpen: props.defaultOpen || false
        };
        _this.toggle = _this.toggle.bind(_assertThisInitialized(_this));
        return _this;
      }

      var _proto = UncontrolledTooltip.prototype;

      _proto.toggle = function toggle() {
        this.setState({
          isOpen: !this.state.isOpen
        });
      };

      _proto.render = function render() {
        return React__default.createElement(Tooltip, _extends({
          isOpen: this.state.isOpen,
          toggle: this.toggle
        }, omit(this.props, omitKeys$3)));
      };

      return UncontrolledTooltip;
    }(React.Component);
    UncontrolledTooltip.propTypes = _objectSpread({
      defaultOpen: propTypes.bool
    }, Tooltip.propTypes);

    var propTypes$1b = {
      tag: tagPropType,
      type: propTypes.string,
      size: propTypes.string,
      color: propTypes.string,
      className: propTypes.string,
      cssModule: propTypes.object,
      children: propTypes.string
    };

    /**
     * The base implementation of `_.sum` and `_.sumBy` without support for
     * iteratee shorthands.
     *
     * @private
     * @param {Array} array The array to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @returns {number} Returns the sum.
     */
    function baseSum(array, iteratee) {
      var result,
          index = -1,
          length = array.length;

      while (++index < length) {
        var current = iteratee(array[index]);
        if (current !== undefined) {
          result = result === undefined ? current : (result + current);
        }
      }
      return result;
    }

    /**
     * This method returns the first argument it receives.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Util
     * @param {*} value Any value.
     * @returns {*} Returns `value`.
     * @example
     *
     * var object = { 'a': 1 };
     *
     * console.log(_.identity(object) === object);
     * // => true
     */
    function identity(value) {
      return value;
    }

    /**
     * Computes the sum of the values in `array`.
     *
     * @static
     * @memberOf _
     * @since 3.4.0
     * @category Math
     * @param {Array} array The array to iterate over.
     * @returns {number} Returns the sum.
     * @example
     *
     * _.sum([4, 2, 8, 6]);
     * // => 20
     */
    function sum(array) {
      return (array && array.length)
        ? baseSum(array, identity)
        : 0;
    }

    /**
     * Appends the elements of `values` to `array`.
     *
     * @private
     * @param {Array} array The array to modify.
     * @param {Array} values The values to append.
     * @returns {Array} Returns `array`.
     */
    function arrayPush(array, values) {
      var index = -1,
          length = values.length,
          offset = array.length;

      while (++index < length) {
        array[offset + index] = values[index];
      }
      return array;
    }

    /** Detect free variable `global` from Node.js. */
    var freeGlobal$1 = typeof global == 'object' && global && global.Object === Object && global;

    /** Detect free variable `self`. */
    var freeSelf$1 = typeof self == 'object' && self && self.Object === Object && self;

    /** Used as a reference to the global object. */
    var root$1 = freeGlobal$1 || freeSelf$1 || Function('return this')();

    /** Built-in value references. */
    var Symbol$2 = root$1.Symbol;

    /** Used for built-in method references. */
    var objectProto$1 = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$3 = objectProto$1.hasOwnProperty;

    /**
     * Used to resolve the
     * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
     * of values.
     */
    var nativeObjectToString$1 = objectProto$1.toString;

    /** Built-in value references. */
    var symToStringTag$1 = Symbol$2 ? Symbol$2.toStringTag : undefined;

    /**
     * A specialized version of `baseGetTag` which ignores `Symbol.toStringTag` values.
     *
     * @private
     * @param {*} value The value to query.
     * @returns {string} Returns the raw `toStringTag`.
     */
    function getRawTag$1(value) {
      var isOwn = hasOwnProperty$3.call(value, symToStringTag$1),
          tag = value[symToStringTag$1];

      try {
        value[symToStringTag$1] = undefined;
        var unmasked = true;
      } catch (e) {}

      var result = nativeObjectToString$1.call(value);
      if (unmasked) {
        if (isOwn) {
          value[symToStringTag$1] = tag;
        } else {
          delete value[symToStringTag$1];
        }
      }
      return result;
    }

    /** Used for built-in method references. */
    var objectProto$2 = Object.prototype;

    /**
     * Used to resolve the
     * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
     * of values.
     */
    var nativeObjectToString$2 = objectProto$2.toString;

    /**
     * Converts `value` to a string using `Object.prototype.toString`.
     *
     * @private
     * @param {*} value The value to convert.
     * @returns {string} Returns the converted string.
     */
    function objectToString$1(value) {
      return nativeObjectToString$2.call(value);
    }

    /** `Object#toString` result references. */
    var nullTag$1 = '[object Null]',
        undefinedTag$1 = '[object Undefined]';

    /** Built-in value references. */
    var symToStringTag$2 = Symbol$2 ? Symbol$2.toStringTag : undefined;

    /**
     * The base implementation of `getTag` without fallbacks for buggy environments.
     *
     * @private
     * @param {*} value The value to query.
     * @returns {string} Returns the `toStringTag`.
     */
    function baseGetTag$1(value) {
      if (value == null) {
        return value === undefined ? undefinedTag$1 : nullTag$1;
      }
      return (symToStringTag$2 && symToStringTag$2 in Object(value))
        ? getRawTag$1(value)
        : objectToString$1(value);
    }

    /**
     * Checks if `value` is object-like. A value is object-like if it's not `null`
     * and has a `typeof` result of "object".
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is object-like, else `false`.
     * @example
     *
     * _.isObjectLike({});
     * // => true
     *
     * _.isObjectLike([1, 2, 3]);
     * // => true
     *
     * _.isObjectLike(_.noop);
     * // => false
     *
     * _.isObjectLike(null);
     * // => false
     */
    function isObjectLike(value) {
      return value != null && typeof value == 'object';
    }

    /** `Object#toString` result references. */
    var argsTag = '[object Arguments]';

    /**
     * The base implementation of `_.isArguments`.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an `arguments` object,
     */
    function baseIsArguments(value) {
      return isObjectLike(value) && baseGetTag$1(value) == argsTag;
    }

    /** Used for built-in method references. */
    var objectProto$3 = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$4 = objectProto$3.hasOwnProperty;

    /** Built-in value references. */
    var propertyIsEnumerable = objectProto$3.propertyIsEnumerable;

    /**
     * Checks if `value` is likely an `arguments` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an `arguments` object,
     *  else `false`.
     * @example
     *
     * _.isArguments(function() { return arguments; }());
     * // => true
     *
     * _.isArguments([1, 2, 3]);
     * // => false
     */
    var isArguments = baseIsArguments(function() { return arguments; }()) ? baseIsArguments : function(value) {
      return isObjectLike(value) && hasOwnProperty$4.call(value, 'callee') &&
        !propertyIsEnumerable.call(value, 'callee');
    };

    /**
     * Checks if `value` is classified as an `Array` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an array, else `false`.
     * @example
     *
     * _.isArray([1, 2, 3]);
     * // => true
     *
     * _.isArray(document.body.children);
     * // => false
     *
     * _.isArray('abc');
     * // => false
     *
     * _.isArray(_.noop);
     * // => false
     */
    var isArray = Array.isArray;

    /** Built-in value references. */
    var spreadableSymbol = Symbol$2 ? Symbol$2.isConcatSpreadable : undefined;

    /**
     * Checks if `value` is a flattenable `arguments` object or array.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is flattenable, else `false`.
     */
    function isFlattenable(value) {
      return isArray(value) || isArguments(value) ||
        !!(spreadableSymbol && value && value[spreadableSymbol]);
    }

    /**
     * The base implementation of `_.flatten` with support for restricting flattening.
     *
     * @private
     * @param {Array} array The array to flatten.
     * @param {number} depth The maximum recursion depth.
     * @param {boolean} [predicate=isFlattenable] The function invoked per iteration.
     * @param {boolean} [isStrict] Restrict to values that pass `predicate` checks.
     * @param {Array} [result=[]] The initial result value.
     * @returns {Array} Returns the new flattened array.
     */
    function baseFlatten(array, depth, predicate, isStrict, result) {
      var index = -1,
          length = array.length;

      predicate || (predicate = isFlattenable);
      result || (result = []);

      while (++index < length) {
        var value = array[index];
        if (depth > 0 && predicate(value)) {
          if (depth > 1) {
            // Recursively flatten arrays (susceptible to call stack limits).
            baseFlatten(value, depth - 1, predicate, isStrict, result);
          } else {
            arrayPush(result, value);
          }
        } else if (!isStrict) {
          result[result.length] = value;
        }
      }
      return result;
    }

    /**
     * Removes all key-value entries from the list cache.
     *
     * @private
     * @name clear
     * @memberOf ListCache
     */
    function listCacheClear() {
      this.__data__ = [];
      this.size = 0;
    }

    /**
     * Performs a
     * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * comparison between two values to determine if they are equivalent.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
     * @example
     *
     * var object = { 'a': 1 };
     * var other = { 'a': 1 };
     *
     * _.eq(object, object);
     * // => true
     *
     * _.eq(object, other);
     * // => false
     *
     * _.eq('a', 'a');
     * // => true
     *
     * _.eq('a', Object('a'));
     * // => false
     *
     * _.eq(NaN, NaN);
     * // => true
     */
    function eq(value, other) {
      return value === other || (value !== value && other !== other);
    }

    /**
     * Gets the index at which the `key` is found in `array` of key-value pairs.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {*} key The key to search for.
     * @returns {number} Returns the index of the matched value, else `-1`.
     */
    function assocIndexOf(array, key) {
      var length = array.length;
      while (length--) {
        if (eq(array[length][0], key)) {
          return length;
        }
      }
      return -1;
    }

    /** Used for built-in method references. */
    var arrayProto = Array.prototype;

    /** Built-in value references. */
    var splice = arrayProto.splice;

    /**
     * Removes `key` and its value from the list cache.
     *
     * @private
     * @name delete
     * @memberOf ListCache
     * @param {string} key The key of the value to remove.
     * @returns {boolean} Returns `true` if the entry was removed, else `false`.
     */
    function listCacheDelete(key) {
      var data = this.__data__,
          index = assocIndexOf(data, key);

      if (index < 0) {
        return false;
      }
      var lastIndex = data.length - 1;
      if (index == lastIndex) {
        data.pop();
      } else {
        splice.call(data, index, 1);
      }
      --this.size;
      return true;
    }

    /**
     * Gets the list cache value for `key`.
     *
     * @private
     * @name get
     * @memberOf ListCache
     * @param {string} key The key of the value to get.
     * @returns {*} Returns the entry value.
     */
    function listCacheGet(key) {
      var data = this.__data__,
          index = assocIndexOf(data, key);

      return index < 0 ? undefined : data[index][1];
    }

    /**
     * Checks if a list cache value for `key` exists.
     *
     * @private
     * @name has
     * @memberOf ListCache
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function listCacheHas(key) {
      return assocIndexOf(this.__data__, key) > -1;
    }

    /**
     * Sets the list cache `key` to `value`.
     *
     * @private
     * @name set
     * @memberOf ListCache
     * @param {string} key The key of the value to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns the list cache instance.
     */
    function listCacheSet(key, value) {
      var data = this.__data__,
          index = assocIndexOf(data, key);

      if (index < 0) {
        ++this.size;
        data.push([key, value]);
      } else {
        data[index][1] = value;
      }
      return this;
    }

    /**
     * Creates an list cache object.
     *
     * @private
     * @constructor
     * @param {Array} [entries] The key-value pairs to cache.
     */
    function ListCache(entries) {
      var index = -1,
          length = entries == null ? 0 : entries.length;

      this.clear();
      while (++index < length) {
        var entry = entries[index];
        this.set(entry[0], entry[1]);
      }
    }

    // Add methods to `ListCache`.
    ListCache.prototype.clear = listCacheClear;
    ListCache.prototype['delete'] = listCacheDelete;
    ListCache.prototype.get = listCacheGet;
    ListCache.prototype.has = listCacheHas;
    ListCache.prototype.set = listCacheSet;

    /**
     * Removes all key-value entries from the stack.
     *
     * @private
     * @name clear
     * @memberOf Stack
     */
    function stackClear() {
      this.__data__ = new ListCache;
      this.size = 0;
    }

    /**
     * Removes `key` and its value from the stack.
     *
     * @private
     * @name delete
     * @memberOf Stack
     * @param {string} key The key of the value to remove.
     * @returns {boolean} Returns `true` if the entry was removed, else `false`.
     */
    function stackDelete(key) {
      var data = this.__data__,
          result = data['delete'](key);

      this.size = data.size;
      return result;
    }

    /**
     * Gets the stack value for `key`.
     *
     * @private
     * @name get
     * @memberOf Stack
     * @param {string} key The key of the value to get.
     * @returns {*} Returns the entry value.
     */
    function stackGet(key) {
      return this.__data__.get(key);
    }

    /**
     * Checks if a stack value for `key` exists.
     *
     * @private
     * @name has
     * @memberOf Stack
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function stackHas(key) {
      return this.__data__.has(key);
    }

    /**
     * Checks if `value` is the
     * [language type](http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-types)
     * of `Object`. (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an object, else `false`.
     * @example
     *
     * _.isObject({});
     * // => true
     *
     * _.isObject([1, 2, 3]);
     * // => true
     *
     * _.isObject(_.noop);
     * // => true
     *
     * _.isObject(null);
     * // => false
     */
    function isObject$1(value) {
      var type = typeof value;
      return value != null && (type == 'object' || type == 'function');
    }

    /** `Object#toString` result references. */
    var asyncTag$1 = '[object AsyncFunction]',
        funcTag$1 = '[object Function]',
        genTag$1 = '[object GeneratorFunction]',
        proxyTag$1 = '[object Proxy]';

    /**
     * Checks if `value` is classified as a `Function` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a function, else `false`.
     * @example
     *
     * _.isFunction(_);
     * // => true
     *
     * _.isFunction(/abc/);
     * // => false
     */
    function isFunction$2(value) {
      if (!isObject$1(value)) {
        return false;
      }
      // The use of `Object#toString` avoids issues with the `typeof` operator
      // in Safari 9 which returns 'object' for typed arrays and other constructors.
      var tag = baseGetTag$1(value);
      return tag == funcTag$1 || tag == genTag$1 || tag == asyncTag$1 || tag == proxyTag$1;
    }

    /** Used to detect overreaching core-js shims. */
    var coreJsData = root$1['__core-js_shared__'];

    /** Used to detect methods masquerading as native. */
    var maskSrcKey = (function() {
      var uid = /[^.]+$/.exec(coreJsData && coreJsData.keys && coreJsData.keys.IE_PROTO || '');
      return uid ? ('Symbol(src)_1.' + uid) : '';
    }());

    /**
     * Checks if `func` has its source masked.
     *
     * @private
     * @param {Function} func The function to check.
     * @returns {boolean} Returns `true` if `func` is masked, else `false`.
     */
    function isMasked(func) {
      return !!maskSrcKey && (maskSrcKey in func);
    }

    /** Used for built-in method references. */
    var funcProto = Function.prototype;

    /** Used to resolve the decompiled source of functions. */
    var funcToString = funcProto.toString;

    /**
     * Converts `func` to its source code.
     *
     * @private
     * @param {Function} func The function to convert.
     * @returns {string} Returns the source code.
     */
    function toSource(func) {
      if (func != null) {
        try {
          return funcToString.call(func);
        } catch (e) {}
        try {
          return (func + '');
        } catch (e) {}
      }
      return '';
    }

    /**
     * Used to match `RegExp`
     * [syntax characters](http://ecma-international.org/ecma-262/7.0/#sec-patterns).
     */
    var reRegExpChar = /[\\^$.*+?()[\]{}|]/g;

    /** Used to detect host constructors (Safari). */
    var reIsHostCtor = /^\[object .+?Constructor\]$/;

    /** Used for built-in method references. */
    var funcProto$1 = Function.prototype,
        objectProto$4 = Object.prototype;

    /** Used to resolve the decompiled source of functions. */
    var funcToString$1 = funcProto$1.toString;

    /** Used to check objects for own properties. */
    var hasOwnProperty$5 = objectProto$4.hasOwnProperty;

    /** Used to detect if a method is native. */
    var reIsNative = RegExp('^' +
      funcToString$1.call(hasOwnProperty$5).replace(reRegExpChar, '\\$&')
      .replace(/hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g, '$1.*?') + '$'
    );

    /**
     * The base implementation of `_.isNative` without bad shim checks.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a native function,
     *  else `false`.
     */
    function baseIsNative(value) {
      if (!isObject$1(value) || isMasked(value)) {
        return false;
      }
      var pattern = isFunction$2(value) ? reIsNative : reIsHostCtor;
      return pattern.test(toSource(value));
    }

    /**
     * Gets the value at `key` of `object`.
     *
     * @private
     * @param {Object} [object] The object to query.
     * @param {string} key The key of the property to get.
     * @returns {*} Returns the property value.
     */
    function getValue(object, key) {
      return object == null ? undefined : object[key];
    }

    /**
     * Gets the native function at `key` of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {string} key The key of the method to get.
     * @returns {*} Returns the function if it's native, else `undefined`.
     */
    function getNative(object, key) {
      var value = getValue(object, key);
      return baseIsNative(value) ? value : undefined;
    }

    /* Built-in method references that are verified to be native. */
    var Map = getNative(root$1, 'Map');

    /* Built-in method references that are verified to be native. */
    var nativeCreate = getNative(Object, 'create');

    /**
     * Removes all key-value entries from the hash.
     *
     * @private
     * @name clear
     * @memberOf Hash
     */
    function hashClear() {
      this.__data__ = nativeCreate ? nativeCreate(null) : {};
      this.size = 0;
    }

    /**
     * Removes `key` and its value from the hash.
     *
     * @private
     * @name delete
     * @memberOf Hash
     * @param {Object} hash The hash to modify.
     * @param {string} key The key of the value to remove.
     * @returns {boolean} Returns `true` if the entry was removed, else `false`.
     */
    function hashDelete(key) {
      var result = this.has(key) && delete this.__data__[key];
      this.size -= result ? 1 : 0;
      return result;
    }

    /** Used to stand-in for `undefined` hash values. */
    var HASH_UNDEFINED = '__lodash_hash_undefined__';

    /** Used for built-in method references. */
    var objectProto$5 = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$6 = objectProto$5.hasOwnProperty;

    /**
     * Gets the hash value for `key`.
     *
     * @private
     * @name get
     * @memberOf Hash
     * @param {string} key The key of the value to get.
     * @returns {*} Returns the entry value.
     */
    function hashGet(key) {
      var data = this.__data__;
      if (nativeCreate) {
        var result = data[key];
        return result === HASH_UNDEFINED ? undefined : result;
      }
      return hasOwnProperty$6.call(data, key) ? data[key] : undefined;
    }

    /** Used for built-in method references. */
    var objectProto$6 = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$7 = objectProto$6.hasOwnProperty;

    /**
     * Checks if a hash value for `key` exists.
     *
     * @private
     * @name has
     * @memberOf Hash
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function hashHas(key) {
      var data = this.__data__;
      return nativeCreate ? (data[key] !== undefined) : hasOwnProperty$7.call(data, key);
    }

    /** Used to stand-in for `undefined` hash values. */
    var HASH_UNDEFINED$1 = '__lodash_hash_undefined__';

    /**
     * Sets the hash `key` to `value`.
     *
     * @private
     * @name set
     * @memberOf Hash
     * @param {string} key The key of the value to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns the hash instance.
     */
    function hashSet(key, value) {
      var data = this.__data__;
      this.size += this.has(key) ? 0 : 1;
      data[key] = (nativeCreate && value === undefined) ? HASH_UNDEFINED$1 : value;
      return this;
    }

    /**
     * Creates a hash object.
     *
     * @private
     * @constructor
     * @param {Array} [entries] The key-value pairs to cache.
     */
    function Hash(entries) {
      var index = -1,
          length = entries == null ? 0 : entries.length;

      this.clear();
      while (++index < length) {
        var entry = entries[index];
        this.set(entry[0], entry[1]);
      }
    }

    // Add methods to `Hash`.
    Hash.prototype.clear = hashClear;
    Hash.prototype['delete'] = hashDelete;
    Hash.prototype.get = hashGet;
    Hash.prototype.has = hashHas;
    Hash.prototype.set = hashSet;

    /**
     * Removes all key-value entries from the map.
     *
     * @private
     * @name clear
     * @memberOf MapCache
     */
    function mapCacheClear() {
      this.size = 0;
      this.__data__ = {
        'hash': new Hash,
        'map': new (Map || ListCache),
        'string': new Hash
      };
    }

    /**
     * Checks if `value` is suitable for use as unique object key.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is suitable, else `false`.
     */
    function isKeyable(value) {
      var type = typeof value;
      return (type == 'string' || type == 'number' || type == 'symbol' || type == 'boolean')
        ? (value !== '__proto__')
        : (value === null);
    }

    /**
     * Gets the data for `map`.
     *
     * @private
     * @param {Object} map The map to query.
     * @param {string} key The reference key.
     * @returns {*} Returns the map data.
     */
    function getMapData(map, key) {
      var data = map.__data__;
      return isKeyable(key)
        ? data[typeof key == 'string' ? 'string' : 'hash']
        : data.map;
    }

    /**
     * Removes `key` and its value from the map.
     *
     * @private
     * @name delete
     * @memberOf MapCache
     * @param {string} key The key of the value to remove.
     * @returns {boolean} Returns `true` if the entry was removed, else `false`.
     */
    function mapCacheDelete(key) {
      var result = getMapData(this, key)['delete'](key);
      this.size -= result ? 1 : 0;
      return result;
    }

    /**
     * Gets the map value for `key`.
     *
     * @private
     * @name get
     * @memberOf MapCache
     * @param {string} key The key of the value to get.
     * @returns {*} Returns the entry value.
     */
    function mapCacheGet(key) {
      return getMapData(this, key).get(key);
    }

    /**
     * Checks if a map value for `key` exists.
     *
     * @private
     * @name has
     * @memberOf MapCache
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function mapCacheHas(key) {
      return getMapData(this, key).has(key);
    }

    /**
     * Sets the map `key` to `value`.
     *
     * @private
     * @name set
     * @memberOf MapCache
     * @param {string} key The key of the value to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns the map cache instance.
     */
    function mapCacheSet(key, value) {
      var data = getMapData(this, key),
          size = data.size;

      data.set(key, value);
      this.size += data.size == size ? 0 : 1;
      return this;
    }

    /**
     * Creates a map cache object to store key-value pairs.
     *
     * @private
     * @constructor
     * @param {Array} [entries] The key-value pairs to cache.
     */
    function MapCache(entries) {
      var index = -1,
          length = entries == null ? 0 : entries.length;

      this.clear();
      while (++index < length) {
        var entry = entries[index];
        this.set(entry[0], entry[1]);
      }
    }

    // Add methods to `MapCache`.
    MapCache.prototype.clear = mapCacheClear;
    MapCache.prototype['delete'] = mapCacheDelete;
    MapCache.prototype.get = mapCacheGet;
    MapCache.prototype.has = mapCacheHas;
    MapCache.prototype.set = mapCacheSet;

    /** Used as the size to enable large array optimizations. */
    var LARGE_ARRAY_SIZE = 200;

    /**
     * Sets the stack `key` to `value`.
     *
     * @private
     * @name set
     * @memberOf Stack
     * @param {string} key The key of the value to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns the stack cache instance.
     */
    function stackSet(key, value) {
      var data = this.__data__;
      if (data instanceof ListCache) {
        var pairs = data.__data__;
        if (!Map || (pairs.length < LARGE_ARRAY_SIZE - 1)) {
          pairs.push([key, value]);
          this.size = ++data.size;
          return this;
        }
        data = this.__data__ = new MapCache(pairs);
      }
      data.set(key, value);
      this.size = data.size;
      return this;
    }

    /**
     * Creates a stack cache object to store key-value pairs.
     *
     * @private
     * @constructor
     * @param {Array} [entries] The key-value pairs to cache.
     */
    function Stack(entries) {
      var data = this.__data__ = new ListCache(entries);
      this.size = data.size;
    }

    // Add methods to `Stack`.
    Stack.prototype.clear = stackClear;
    Stack.prototype['delete'] = stackDelete;
    Stack.prototype.get = stackGet;
    Stack.prototype.has = stackHas;
    Stack.prototype.set = stackSet;

    /** Used to stand-in for `undefined` hash values. */
    var HASH_UNDEFINED$2 = '__lodash_hash_undefined__';

    /**
     * Adds `value` to the array cache.
     *
     * @private
     * @name add
     * @memberOf SetCache
     * @alias push
     * @param {*} value The value to cache.
     * @returns {Object} Returns the cache instance.
     */
    function setCacheAdd(value) {
      this.__data__.set(value, HASH_UNDEFINED$2);
      return this;
    }

    /**
     * Checks if `value` is in the array cache.
     *
     * @private
     * @name has
     * @memberOf SetCache
     * @param {*} value The value to search for.
     * @returns {number} Returns `true` if `value` is found, else `false`.
     */
    function setCacheHas(value) {
      return this.__data__.has(value);
    }

    /**
     *
     * Creates an array cache object to store unique values.
     *
     * @private
     * @constructor
     * @param {Array} [values] The values to cache.
     */
    function SetCache(values) {
      var index = -1,
          length = values == null ? 0 : values.length;

      this.__data__ = new MapCache;
      while (++index < length) {
        this.add(values[index]);
      }
    }

    // Add methods to `SetCache`.
    SetCache.prototype.add = SetCache.prototype.push = setCacheAdd;
    SetCache.prototype.has = setCacheHas;

    /**
     * A specialized version of `_.some` for arrays without support for iteratee
     * shorthands.
     *
     * @private
     * @param {Array} [array] The array to iterate over.
     * @param {Function} predicate The function invoked per iteration.
     * @returns {boolean} Returns `true` if any element passes the predicate check,
     *  else `false`.
     */
    function arraySome(array, predicate) {
      var index = -1,
          length = array == null ? 0 : array.length;

      while (++index < length) {
        if (predicate(array[index], index, array)) {
          return true;
        }
      }
      return false;
    }

    /**
     * Checks if a `cache` value for `key` exists.
     *
     * @private
     * @param {Object} cache The cache to query.
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function cacheHas(cache, key) {
      return cache.has(key);
    }

    /** Used to compose bitmasks for value comparisons. */
    var COMPARE_PARTIAL_FLAG = 1,
        COMPARE_UNORDERED_FLAG = 2;

    /**
     * A specialized version of `baseIsEqualDeep` for arrays with support for
     * partial deep comparisons.
     *
     * @private
     * @param {Array} array The array to compare.
     * @param {Array} other The other array to compare.
     * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
     * @param {Function} customizer The function to customize comparisons.
     * @param {Function} equalFunc The function to determine equivalents of values.
     * @param {Object} stack Tracks traversed `array` and `other` objects.
     * @returns {boolean} Returns `true` if the arrays are equivalent, else `false`.
     */
    function equalArrays(array, other, bitmask, customizer, equalFunc, stack) {
      var isPartial = bitmask & COMPARE_PARTIAL_FLAG,
          arrLength = array.length,
          othLength = other.length;

      if (arrLength != othLength && !(isPartial && othLength > arrLength)) {
        return false;
      }
      // Assume cyclic values are equal.
      var stacked = stack.get(array);
      if (stacked && stack.get(other)) {
        return stacked == other;
      }
      var index = -1,
          result = true,
          seen = (bitmask & COMPARE_UNORDERED_FLAG) ? new SetCache : undefined;

      stack.set(array, other);
      stack.set(other, array);

      // Ignore non-index properties.
      while (++index < arrLength) {
        var arrValue = array[index],
            othValue = other[index];

        if (customizer) {
          var compared = isPartial
            ? customizer(othValue, arrValue, index, other, array, stack)
            : customizer(arrValue, othValue, index, array, other, stack);
        }
        if (compared !== undefined) {
          if (compared) {
            continue;
          }
          result = false;
          break;
        }
        // Recursively compare arrays (susceptible to call stack limits).
        if (seen) {
          if (!arraySome(other, function(othValue, othIndex) {
                if (!cacheHas(seen, othIndex) &&
                    (arrValue === othValue || equalFunc(arrValue, othValue, bitmask, customizer, stack))) {
                  return seen.push(othIndex);
                }
              })) {
            result = false;
            break;
          }
        } else if (!(
              arrValue === othValue ||
                equalFunc(arrValue, othValue, bitmask, customizer, stack)
            )) {
          result = false;
          break;
        }
      }
      stack['delete'](array);
      stack['delete'](other);
      return result;
    }

    /** Built-in value references. */
    var Uint8Array = root$1.Uint8Array;

    /**
     * Converts `map` to its key-value pairs.
     *
     * @private
     * @param {Object} map The map to convert.
     * @returns {Array} Returns the key-value pairs.
     */
    function mapToArray(map) {
      var index = -1,
          result = Array(map.size);

      map.forEach(function(value, key) {
        result[++index] = [key, value];
      });
      return result;
    }

    /**
     * Converts `set` to an array of its values.
     *
     * @private
     * @param {Object} set The set to convert.
     * @returns {Array} Returns the values.
     */
    function setToArray(set) {
      var index = -1,
          result = Array(set.size);

      set.forEach(function(value) {
        result[++index] = value;
      });
      return result;
    }

    /** Used to compose bitmasks for value comparisons. */
    var COMPARE_PARTIAL_FLAG$1 = 1,
        COMPARE_UNORDERED_FLAG$1 = 2;

    /** `Object#toString` result references. */
    var boolTag = '[object Boolean]',
        dateTag = '[object Date]',
        errorTag = '[object Error]',
        mapTag = '[object Map]',
        numberTag = '[object Number]',
        regexpTag = '[object RegExp]',
        setTag = '[object Set]',
        stringTag = '[object String]',
        symbolTag = '[object Symbol]';

    var arrayBufferTag = '[object ArrayBuffer]',
        dataViewTag = '[object DataView]';

    /** Used to convert symbols to primitives and strings. */
    var symbolProto = Symbol$2 ? Symbol$2.prototype : undefined,
        symbolValueOf = symbolProto ? symbolProto.valueOf : undefined;

    /**
     * A specialized version of `baseIsEqualDeep` for comparing objects of
     * the same `toStringTag`.
     *
     * **Note:** This function only supports comparing values with tags of
     * `Boolean`, `Date`, `Error`, `Number`, `RegExp`, or `String`.
     *
     * @private
     * @param {Object} object The object to compare.
     * @param {Object} other The other object to compare.
     * @param {string} tag The `toStringTag` of the objects to compare.
     * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
     * @param {Function} customizer The function to customize comparisons.
     * @param {Function} equalFunc The function to determine equivalents of values.
     * @param {Object} stack Tracks traversed `object` and `other` objects.
     * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
     */
    function equalByTag(object, other, tag, bitmask, customizer, equalFunc, stack) {
      switch (tag) {
        case dataViewTag:
          if ((object.byteLength != other.byteLength) ||
              (object.byteOffset != other.byteOffset)) {
            return false;
          }
          object = object.buffer;
          other = other.buffer;

        case arrayBufferTag:
          if ((object.byteLength != other.byteLength) ||
              !equalFunc(new Uint8Array(object), new Uint8Array(other))) {
            return false;
          }
          return true;

        case boolTag:
        case dateTag:
        case numberTag:
          // Coerce booleans to `1` or `0` and dates to milliseconds.
          // Invalid dates are coerced to `NaN`.
          return eq(+object, +other);

        case errorTag:
          return object.name == other.name && object.message == other.message;

        case regexpTag:
        case stringTag:
          // Coerce regexes to strings and treat strings, primitives and objects,
          // as equal. See http://www.ecma-international.org/ecma-262/7.0/#sec-regexp.prototype.tostring
          // for more details.
          return object == (other + '');

        case mapTag:
          var convert = mapToArray;

        case setTag:
          var isPartial = bitmask & COMPARE_PARTIAL_FLAG$1;
          convert || (convert = setToArray);

          if (object.size != other.size && !isPartial) {
            return false;
          }
          // Assume cyclic values are equal.
          var stacked = stack.get(object);
          if (stacked) {
            return stacked == other;
          }
          bitmask |= COMPARE_UNORDERED_FLAG$1;

          // Recursively compare objects (susceptible to call stack limits).
          stack.set(object, other);
          var result = equalArrays(convert(object), convert(other), bitmask, customizer, equalFunc, stack);
          stack['delete'](object);
          return result;

        case symbolTag:
          if (symbolValueOf) {
            return symbolValueOf.call(object) == symbolValueOf.call(other);
          }
      }
      return false;
    }

    /**
     * The base implementation of `getAllKeys` and `getAllKeysIn` which uses
     * `keysFunc` and `symbolsFunc` to get the enumerable property names and
     * symbols of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Function} keysFunc The function to get the keys of `object`.
     * @param {Function} symbolsFunc The function to get the symbols of `object`.
     * @returns {Array} Returns the array of property names and symbols.
     */
    function baseGetAllKeys(object, keysFunc, symbolsFunc) {
      var result = keysFunc(object);
      return isArray(object) ? result : arrayPush(result, symbolsFunc(object));
    }

    /**
     * A specialized version of `_.filter` for arrays without support for
     * iteratee shorthands.
     *
     * @private
     * @param {Array} [array] The array to iterate over.
     * @param {Function} predicate The function invoked per iteration.
     * @returns {Array} Returns the new filtered array.
     */
    function arrayFilter(array, predicate) {
      var index = -1,
          length = array == null ? 0 : array.length,
          resIndex = 0,
          result = [];

      while (++index < length) {
        var value = array[index];
        if (predicate(value, index, array)) {
          result[resIndex++] = value;
        }
      }
      return result;
    }

    /**
     * This method returns a new empty array.
     *
     * @static
     * @memberOf _
     * @since 4.13.0
     * @category Util
     * @returns {Array} Returns the new empty array.
     * @example
     *
     * var arrays = _.times(2, _.stubArray);
     *
     * console.log(arrays);
     * // => [[], []]
     *
     * console.log(arrays[0] === arrays[1]);
     * // => false
     */
    function stubArray() {
      return [];
    }

    /** Used for built-in method references. */
    var objectProto$7 = Object.prototype;

    /** Built-in value references. */
    var propertyIsEnumerable$1 = objectProto$7.propertyIsEnumerable;

    /* Built-in method references for those with the same name as other `lodash` methods. */
    var nativeGetSymbols = Object.getOwnPropertySymbols;

    /**
     * Creates an array of the own enumerable symbols of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of symbols.
     */
    var getSymbols = !nativeGetSymbols ? stubArray : function(object) {
      if (object == null) {
        return [];
      }
      object = Object(object);
      return arrayFilter(nativeGetSymbols(object), function(symbol) {
        return propertyIsEnumerable$1.call(object, symbol);
      });
    };

    /**
     * The base implementation of `_.times` without support for iteratee shorthands
     * or max array length checks.
     *
     * @private
     * @param {number} n The number of times to invoke `iteratee`.
     * @param {Function} iteratee The function invoked per iteration.
     * @returns {Array} Returns the array of results.
     */
    function baseTimes(n, iteratee) {
      var index = -1,
          result = Array(n);

      while (++index < n) {
        result[index] = iteratee(index);
      }
      return result;
    }

    /**
     * This method returns `false`.
     *
     * @static
     * @memberOf _
     * @since 4.13.0
     * @category Util
     * @returns {boolean} Returns `false`.
     * @example
     *
     * _.times(2, _.stubFalse);
     * // => [false, false]
     */
    function stubFalse() {
      return false;
    }

    /** Detect free variable `exports`. */
    var freeExports = typeof exports == 'object' && exports && !exports.nodeType && exports;

    /** Detect free variable `module`. */
    var freeModule = freeExports && typeof module == 'object' && module && !module.nodeType && module;

    /** Detect the popular CommonJS extension `module.exports`. */
    var moduleExports = freeModule && freeModule.exports === freeExports;

    /** Built-in value references. */
    var Buffer = moduleExports ? root$1.Buffer : undefined;

    /* Built-in method references for those with the same name as other `lodash` methods. */
    var nativeIsBuffer = Buffer ? Buffer.isBuffer : undefined;

    /**
     * Checks if `value` is a buffer.
     *
     * @static
     * @memberOf _
     * @since 4.3.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a buffer, else `false`.
     * @example
     *
     * _.isBuffer(new Buffer(2));
     * // => true
     *
     * _.isBuffer(new Uint8Array(2));
     * // => false
     */
    var isBuffer = nativeIsBuffer || stubFalse;

    /** Used as references for various `Number` constants. */
    var MAX_SAFE_INTEGER = 9007199254740991;

    /** Used to detect unsigned integer values. */
    var reIsUint = /^(?:0|[1-9]\d*)$/;

    /**
     * Checks if `value` is a valid array-like index.
     *
     * @private
     * @param {*} value The value to check.
     * @param {number} [length=MAX_SAFE_INTEGER] The upper bounds of a valid index.
     * @returns {boolean} Returns `true` if `value` is a valid index, else `false`.
     */
    function isIndex(value, length) {
      var type = typeof value;
      length = length == null ? MAX_SAFE_INTEGER : length;

      return !!length &&
        (type == 'number' ||
          (type != 'symbol' && reIsUint.test(value))) &&
            (value > -1 && value % 1 == 0 && value < length);
    }

    /** Used as references for various `Number` constants. */
    var MAX_SAFE_INTEGER$1 = 9007199254740991;

    /**
     * Checks if `value` is a valid array-like length.
     *
     * **Note:** This method is loosely based on
     * [`ToLength`](http://ecma-international.org/ecma-262/7.0/#sec-tolength).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a valid length, else `false`.
     * @example
     *
     * _.isLength(3);
     * // => true
     *
     * _.isLength(Number.MIN_VALUE);
     * // => false
     *
     * _.isLength(Infinity);
     * // => false
     *
     * _.isLength('3');
     * // => false
     */
    function isLength(value) {
      return typeof value == 'number' &&
        value > -1 && value % 1 == 0 && value <= MAX_SAFE_INTEGER$1;
    }

    /** `Object#toString` result references. */
    var argsTag$1 = '[object Arguments]',
        arrayTag = '[object Array]',
        boolTag$1 = '[object Boolean]',
        dateTag$1 = '[object Date]',
        errorTag$1 = '[object Error]',
        funcTag$2 = '[object Function]',
        mapTag$1 = '[object Map]',
        numberTag$1 = '[object Number]',
        objectTag = '[object Object]',
        regexpTag$1 = '[object RegExp]',
        setTag$1 = '[object Set]',
        stringTag$1 = '[object String]',
        weakMapTag = '[object WeakMap]';

    var arrayBufferTag$1 = '[object ArrayBuffer]',
        dataViewTag$1 = '[object DataView]',
        float32Tag = '[object Float32Array]',
        float64Tag = '[object Float64Array]',
        int8Tag = '[object Int8Array]',
        int16Tag = '[object Int16Array]',
        int32Tag = '[object Int32Array]',
        uint8Tag = '[object Uint8Array]',
        uint8ClampedTag = '[object Uint8ClampedArray]',
        uint16Tag = '[object Uint16Array]',
        uint32Tag = '[object Uint32Array]';

    /** Used to identify `toStringTag` values of typed arrays. */
    var typedArrayTags = {};
    typedArrayTags[float32Tag] = typedArrayTags[float64Tag] =
    typedArrayTags[int8Tag] = typedArrayTags[int16Tag] =
    typedArrayTags[int32Tag] = typedArrayTags[uint8Tag] =
    typedArrayTags[uint8ClampedTag] = typedArrayTags[uint16Tag] =
    typedArrayTags[uint32Tag] = true;
    typedArrayTags[argsTag$1] = typedArrayTags[arrayTag] =
    typedArrayTags[arrayBufferTag$1] = typedArrayTags[boolTag$1] =
    typedArrayTags[dataViewTag$1] = typedArrayTags[dateTag$1] =
    typedArrayTags[errorTag$1] = typedArrayTags[funcTag$2] =
    typedArrayTags[mapTag$1] = typedArrayTags[numberTag$1] =
    typedArrayTags[objectTag] = typedArrayTags[regexpTag$1] =
    typedArrayTags[setTag$1] = typedArrayTags[stringTag$1] =
    typedArrayTags[weakMapTag] = false;

    /**
     * The base implementation of `_.isTypedArray` without Node.js optimizations.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
     */
    function baseIsTypedArray(value) {
      return isObjectLike(value) &&
        isLength(value.length) && !!typedArrayTags[baseGetTag$1(value)];
    }

    /**
     * The base implementation of `_.unary` without support for storing metadata.
     *
     * @private
     * @param {Function} func The function to cap arguments for.
     * @returns {Function} Returns the new capped function.
     */
    function baseUnary(func) {
      return function(value) {
        return func(value);
      };
    }

    /** Detect free variable `exports`. */
    var freeExports$1 = typeof exports == 'object' && exports && !exports.nodeType && exports;

    /** Detect free variable `module`. */
    var freeModule$1 = freeExports$1 && typeof module == 'object' && module && !module.nodeType && module;

    /** Detect the popular CommonJS extension `module.exports`. */
    var moduleExports$1 = freeModule$1 && freeModule$1.exports === freeExports$1;

    /** Detect free variable `process` from Node.js. */
    var freeProcess = moduleExports$1 && freeGlobal$1.process;

    /** Used to access faster Node.js helpers. */
    var nodeUtil = (function() {
      try {
        // Use `util.types` for Node.js 10+.
        var types = freeModule$1 && freeModule$1.require && freeModule$1.require('util').types;

        if (types) {
          return types;
        }

        // Legacy `process.binding('util')` for Node.js < 10.
        return freeProcess && freeProcess.binding && freeProcess.binding('util');
      } catch (e) {}
    }());

    /* Node.js helper references. */
    var nodeIsTypedArray = nodeUtil && nodeUtil.isTypedArray;

    /**
     * Checks if `value` is classified as a typed array.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
     * @example
     *
     * _.isTypedArray(new Uint8Array);
     * // => true
     *
     * _.isTypedArray([]);
     * // => false
     */
    var isTypedArray = nodeIsTypedArray ? baseUnary(nodeIsTypedArray) : baseIsTypedArray;

    /** Used for built-in method references. */
    var objectProto$8 = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$8 = objectProto$8.hasOwnProperty;

    /**
     * Creates an array of the enumerable property names of the array-like `value`.
     *
     * @private
     * @param {*} value The value to query.
     * @param {boolean} inherited Specify returning inherited property names.
     * @returns {Array} Returns the array of property names.
     */
    function arrayLikeKeys(value, inherited) {
      var isArr = isArray(value),
          isArg = !isArr && isArguments(value),
          isBuff = !isArr && !isArg && isBuffer(value),
          isType = !isArr && !isArg && !isBuff && isTypedArray(value),
          skipIndexes = isArr || isArg || isBuff || isType,
          result = skipIndexes ? baseTimes(value.length, String) : [],
          length = result.length;

      for (var key in value) {
        if ((inherited || hasOwnProperty$8.call(value, key)) &&
            !(skipIndexes && (
               // Safari 9 has enumerable `arguments.length` in strict mode.
               key == 'length' ||
               // Node.js 0.10 has enumerable non-index properties on buffers.
               (isBuff && (key == 'offset' || key == 'parent')) ||
               // PhantomJS 2 has enumerable non-index properties on typed arrays.
               (isType && (key == 'buffer' || key == 'byteLength' || key == 'byteOffset')) ||
               // Skip index properties.
               isIndex(key, length)
            ))) {
          result.push(key);
        }
      }
      return result;
    }

    /** Used for built-in method references. */
    var objectProto$9 = Object.prototype;

    /**
     * Checks if `value` is likely a prototype object.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a prototype, else `false`.
     */
    function isPrototype(value) {
      var Ctor = value && value.constructor,
          proto = (typeof Ctor == 'function' && Ctor.prototype) || objectProto$9;

      return value === proto;
    }

    /**
     * Creates a unary function that invokes `func` with its argument transformed.
     *
     * @private
     * @param {Function} func The function to wrap.
     * @param {Function} transform The argument transform.
     * @returns {Function} Returns the new function.
     */
    function overArg(func, transform) {
      return function(arg) {
        return func(transform(arg));
      };
    }

    /* Built-in method references for those with the same name as other `lodash` methods. */
    var nativeKeys = overArg(Object.keys, Object);

    /** Used for built-in method references. */
    var objectProto$a = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$9 = objectProto$a.hasOwnProperty;

    /**
     * The base implementation of `_.keys` which doesn't treat sparse arrays as dense.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names.
     */
    function baseKeys(object) {
      if (!isPrototype(object)) {
        return nativeKeys(object);
      }
      var result = [];
      for (var key in Object(object)) {
        if (hasOwnProperty$9.call(object, key) && key != 'constructor') {
          result.push(key);
        }
      }
      return result;
    }

    /**
     * Checks if `value` is array-like. A value is considered array-like if it's
     * not a function and has a `value.length` that's an integer greater than or
     * equal to `0` and less than or equal to `Number.MAX_SAFE_INTEGER`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is array-like, else `false`.
     * @example
     *
     * _.isArrayLike([1, 2, 3]);
     * // => true
     *
     * _.isArrayLike(document.body.children);
     * // => true
     *
     * _.isArrayLike('abc');
     * // => true
     *
     * _.isArrayLike(_.noop);
     * // => false
     */
    function isArrayLike(value) {
      return value != null && isLength(value.length) && !isFunction$2(value);
    }

    /**
     * Creates an array of the own enumerable property names of `object`.
     *
     * **Note:** Non-object values are coerced to objects. See the
     * [ES spec](http://ecma-international.org/ecma-262/7.0/#sec-object.keys)
     * for more details.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.keys(new Foo);
     * // => ['a', 'b'] (iteration order is not guaranteed)
     *
     * _.keys('hi');
     * // => ['0', '1']
     */
    function keys(object) {
      return isArrayLike(object) ? arrayLikeKeys(object) : baseKeys(object);
    }

    /**
     * Creates an array of own enumerable property names and symbols of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names and symbols.
     */
    function getAllKeys(object) {
      return baseGetAllKeys(object, keys, getSymbols);
    }

    /** Used to compose bitmasks for value comparisons. */
    var COMPARE_PARTIAL_FLAG$2 = 1;

    /** Used for built-in method references. */
    var objectProto$b = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$a = objectProto$b.hasOwnProperty;

    /**
     * A specialized version of `baseIsEqualDeep` for objects with support for
     * partial deep comparisons.
     *
     * @private
     * @param {Object} object The object to compare.
     * @param {Object} other The other object to compare.
     * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
     * @param {Function} customizer The function to customize comparisons.
     * @param {Function} equalFunc The function to determine equivalents of values.
     * @param {Object} stack Tracks traversed `object` and `other` objects.
     * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
     */
    function equalObjects(object, other, bitmask, customizer, equalFunc, stack) {
      var isPartial = bitmask & COMPARE_PARTIAL_FLAG$2,
          objProps = getAllKeys(object),
          objLength = objProps.length,
          othProps = getAllKeys(other),
          othLength = othProps.length;

      if (objLength != othLength && !isPartial) {
        return false;
      }
      var index = objLength;
      while (index--) {
        var key = objProps[index];
        if (!(isPartial ? key in other : hasOwnProperty$a.call(other, key))) {
          return false;
        }
      }
      // Assume cyclic values are equal.
      var stacked = stack.get(object);
      if (stacked && stack.get(other)) {
        return stacked == other;
      }
      var result = true;
      stack.set(object, other);
      stack.set(other, object);

      var skipCtor = isPartial;
      while (++index < objLength) {
        key = objProps[index];
        var objValue = object[key],
            othValue = other[key];

        if (customizer) {
          var compared = isPartial
            ? customizer(othValue, objValue, key, other, object, stack)
            : customizer(objValue, othValue, key, object, other, stack);
        }
        // Recursively compare objects (susceptible to call stack limits).
        if (!(compared === undefined
              ? (objValue === othValue || equalFunc(objValue, othValue, bitmask, customizer, stack))
              : compared
            )) {
          result = false;
          break;
        }
        skipCtor || (skipCtor = key == 'constructor');
      }
      if (result && !skipCtor) {
        var objCtor = object.constructor,
            othCtor = other.constructor;

        // Non `Object` object instances with different constructors are not equal.
        if (objCtor != othCtor &&
            ('constructor' in object && 'constructor' in other) &&
            !(typeof objCtor == 'function' && objCtor instanceof objCtor &&
              typeof othCtor == 'function' && othCtor instanceof othCtor)) {
          result = false;
        }
      }
      stack['delete'](object);
      stack['delete'](other);
      return result;
    }

    /* Built-in method references that are verified to be native. */
    var DataView = getNative(root$1, 'DataView');

    /* Built-in method references that are verified to be native. */
    var Promise$1 = getNative(root$1, 'Promise');

    /* Built-in method references that are verified to be native. */
    var Set = getNative(root$1, 'Set');

    /* Built-in method references that are verified to be native. */
    var WeakMap = getNative(root$1, 'WeakMap');

    /** `Object#toString` result references. */
    var mapTag$2 = '[object Map]',
        objectTag$1 = '[object Object]',
        promiseTag = '[object Promise]',
        setTag$2 = '[object Set]',
        weakMapTag$1 = '[object WeakMap]';

    var dataViewTag$2 = '[object DataView]';

    /** Used to detect maps, sets, and weakmaps. */
    var dataViewCtorString = toSource(DataView),
        mapCtorString = toSource(Map),
        promiseCtorString = toSource(Promise$1),
        setCtorString = toSource(Set),
        weakMapCtorString = toSource(WeakMap);

    /**
     * Gets the `toStringTag` of `value`.
     *
     * @private
     * @param {*} value The value to query.
     * @returns {string} Returns the `toStringTag`.
     */
    var getTag = baseGetTag$1;

    // Fallback for data views, maps, sets, and weak maps in IE 11 and promises in Node.js < 6.
    if ((DataView && getTag(new DataView(new ArrayBuffer(1))) != dataViewTag$2) ||
        (Map && getTag(new Map) != mapTag$2) ||
        (Promise$1 && getTag(Promise$1.resolve()) != promiseTag) ||
        (Set && getTag(new Set) != setTag$2) ||
        (WeakMap && getTag(new WeakMap) != weakMapTag$1)) {
      getTag = function(value) {
        var result = baseGetTag$1(value),
            Ctor = result == objectTag$1 ? value.constructor : undefined,
            ctorString = Ctor ? toSource(Ctor) : '';

        if (ctorString) {
          switch (ctorString) {
            case dataViewCtorString: return dataViewTag$2;
            case mapCtorString: return mapTag$2;
            case promiseCtorString: return promiseTag;
            case setCtorString: return setTag$2;
            case weakMapCtorString: return weakMapTag$1;
          }
        }
        return result;
      };
    }

    var getTag$1 = getTag;

    /** Used to compose bitmasks for value comparisons. */
    var COMPARE_PARTIAL_FLAG$3 = 1;

    /** `Object#toString` result references. */
    var argsTag$2 = '[object Arguments]',
        arrayTag$1 = '[object Array]',
        objectTag$2 = '[object Object]';

    /** Used for built-in method references. */
    var objectProto$c = Object.prototype;

    /** Used to check objects for own properties. */
    var hasOwnProperty$b = objectProto$c.hasOwnProperty;

    /**
     * A specialized version of `baseIsEqual` for arrays and objects which performs
     * deep comparisons and tracks traversed objects enabling objects with circular
     * references to be compared.
     *
     * @private
     * @param {Object} object The object to compare.
     * @param {Object} other The other object to compare.
     * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
     * @param {Function} customizer The function to customize comparisons.
     * @param {Function} equalFunc The function to determine equivalents of values.
     * @param {Object} [stack] Tracks traversed `object` and `other` objects.
     * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
     */
    function baseIsEqualDeep(object, other, bitmask, customizer, equalFunc, stack) {
      var objIsArr = isArray(object),
          othIsArr = isArray(other),
          objTag = objIsArr ? arrayTag$1 : getTag$1(object),
          othTag = othIsArr ? arrayTag$1 : getTag$1(other);

      objTag = objTag == argsTag$2 ? objectTag$2 : objTag;
      othTag = othTag == argsTag$2 ? objectTag$2 : othTag;

      var objIsObj = objTag == objectTag$2,
          othIsObj = othTag == objectTag$2,
          isSameTag = objTag == othTag;

      if (isSameTag && isBuffer(object)) {
        if (!isBuffer(other)) {
          return false;
        }
        objIsArr = true;
        objIsObj = false;
      }
      if (isSameTag && !objIsObj) {
        stack || (stack = new Stack);
        return (objIsArr || isTypedArray(object))
          ? equalArrays(object, other, bitmask, customizer, equalFunc, stack)
          : equalByTag(object, other, objTag, bitmask, customizer, equalFunc, stack);
      }
      if (!(bitmask & COMPARE_PARTIAL_FLAG$3)) {
        var objIsWrapped = objIsObj && hasOwnProperty$b.call(object, '__wrapped__'),
            othIsWrapped = othIsObj && hasOwnProperty$b.call(other, '__wrapped__');

        if (objIsWrapped || othIsWrapped) {
          var objUnwrapped = objIsWrapped ? object.value() : object,
              othUnwrapped = othIsWrapped ? other.value() : other;

          stack || (stack = new Stack);
          return equalFunc(objUnwrapped, othUnwrapped, bitmask, customizer, stack);
        }
      }
      if (!isSameTag) {
        return false;
      }
      stack || (stack = new Stack);
      return equalObjects(object, other, bitmask, customizer, equalFunc, stack);
    }

    /**
     * The base implementation of `_.isEqual` which supports partial comparisons
     * and tracks traversed objects.
     *
     * @private
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @param {boolean} bitmask The bitmask flags.
     *  1 - Unordered comparison
     *  2 - Partial comparison
     * @param {Function} [customizer] The function to customize comparisons.
     * @param {Object} [stack] Tracks traversed `value` and `other` objects.
     * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
     */
    function baseIsEqual(value, other, bitmask, customizer, stack) {
      if (value === other) {
        return true;
      }
      if (value == null || other == null || (!isObjectLike(value) && !isObjectLike(other))) {
        return value !== value && other !== other;
      }
      return baseIsEqualDeep(value, other, bitmask, customizer, baseIsEqual, stack);
    }

    /** Used to compose bitmasks for value comparisons. */
    var COMPARE_PARTIAL_FLAG$4 = 1,
        COMPARE_UNORDERED_FLAG$2 = 2;

    /**
     * The base implementation of `_.isMatch` without support for iteratee shorthands.
     *
     * @private
     * @param {Object} object The object to inspect.
     * @param {Object} source The object of property values to match.
     * @param {Array} matchData The property names, values, and compare flags to match.
     * @param {Function} [customizer] The function to customize comparisons.
     * @returns {boolean} Returns `true` if `object` is a match, else `false`.
     */
    function baseIsMatch(object, source, matchData, customizer) {
      var index = matchData.length,
          length = index,
          noCustomizer = !customizer;

      if (object == null) {
        return !length;
      }
      object = Object(object);
      while (index--) {
        var data = matchData[index];
        if ((noCustomizer && data[2])
              ? data[1] !== object[data[0]]
              : !(data[0] in object)
            ) {
          return false;
        }
      }
      while (++index < length) {
        data = matchData[index];
        var key = data[0],
            objValue = object[key],
            srcValue = data[1];

        if (noCustomizer && data[2]) {
          if (objValue === undefined && !(key in object)) {
            return false;
          }
        } else {
          var stack = new Stack;
          if (customizer) {
            var result = customizer(objValue, srcValue, key, object, source, stack);
          }
          if (!(result === undefined
                ? baseIsEqual(srcValue, objValue, COMPARE_PARTIAL_FLAG$4 | COMPARE_UNORDERED_FLAG$2, customizer, stack)
                : result
              )) {
            return false;
          }
        }
      }
      return true;
    }

    /**
     * Checks if `value` is suitable for strict equality comparisons, i.e. `===`.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` if suitable for strict
     *  equality comparisons, else `false`.
     */
    function isStrictComparable(value) {
      return value === value && !isObject$1(value);
    }

    /**
     * Gets the property names, values, and compare flags of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the match data of `object`.
     */
    function getMatchData(object) {
      var result = keys(object),
          length = result.length;

      while (length--) {
        var key = result[length],
            value = object[key];

        result[length] = [key, value, isStrictComparable(value)];
      }
      return result;
    }

    /**
     * A specialized version of `matchesProperty` for source values suitable
     * for strict equality comparisons, i.e. `===`.
     *
     * @private
     * @param {string} key The key of the property to get.
     * @param {*} srcValue The value to match.
     * @returns {Function} Returns the new spec function.
     */
    function matchesStrictComparable(key, srcValue) {
      return function(object) {
        if (object == null) {
          return false;
        }
        return object[key] === srcValue &&
          (srcValue !== undefined || (key in Object(object)));
      };
    }

    /**
     * The base implementation of `_.matches` which doesn't clone `source`.
     *
     * @private
     * @param {Object} source The object of property values to match.
     * @returns {Function} Returns the new spec function.
     */
    function baseMatches(source) {
      var matchData = getMatchData(source);
      if (matchData.length == 1 && matchData[0][2]) {
        return matchesStrictComparable(matchData[0][0], matchData[0][1]);
      }
      return function(object) {
        return object === source || baseIsMatch(object, source, matchData);
      };
    }

    /** `Object#toString` result references. */
    var symbolTag$1 = '[object Symbol]';

    /**
     * Checks if `value` is classified as a `Symbol` primitive or object.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a symbol, else `false`.
     * @example
     *
     * _.isSymbol(Symbol.iterator);
     * // => true
     *
     * _.isSymbol('abc');
     * // => false
     */
    function isSymbol(value) {
      return typeof value == 'symbol' ||
        (isObjectLike(value) && baseGetTag$1(value) == symbolTag$1);
    }

    /** Used to match property names within property paths. */
    var reIsDeepProp = /\.|\[(?:[^[\]]*|(["'])(?:(?!\1)[^\\]|\\.)*?\1)\]/,
        reIsPlainProp = /^\w*$/;

    /**
     * Checks if `value` is a property name and not a property path.
     *
     * @private
     * @param {*} value The value to check.
     * @param {Object} [object] The object to query keys on.
     * @returns {boolean} Returns `true` if `value` is a property name, else `false`.
     */
    function isKey(value, object) {
      if (isArray(value)) {
        return false;
      }
      var type = typeof value;
      if (type == 'number' || type == 'symbol' || type == 'boolean' ||
          value == null || isSymbol(value)) {
        return true;
      }
      return reIsPlainProp.test(value) || !reIsDeepProp.test(value) ||
        (object != null && value in Object(object));
    }

    /** Error message constants. */
    var FUNC_ERROR_TEXT = 'Expected a function';

    /**
     * Creates a function that memoizes the result of `func`. If `resolver` is
     * provided, it determines the cache key for storing the result based on the
     * arguments provided to the memoized function. By default, the first argument
     * provided to the memoized function is used as the map cache key. The `func`
     * is invoked with the `this` binding of the memoized function.
     *
     * **Note:** The cache is exposed as the `cache` property on the memoized
     * function. Its creation may be customized by replacing the `_.memoize.Cache`
     * constructor with one whose instances implement the
     * [`Map`](http://ecma-international.org/ecma-262/7.0/#sec-properties-of-the-map-prototype-object)
     * method interface of `clear`, `delete`, `get`, `has`, and `set`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {Function} func The function to have its output memoized.
     * @param {Function} [resolver] The function to resolve the cache key.
     * @returns {Function} Returns the new memoized function.
     * @example
     *
     * var object = { 'a': 1, 'b': 2 };
     * var other = { 'c': 3, 'd': 4 };
     *
     * var values = _.memoize(_.values);
     * values(object);
     * // => [1, 2]
     *
     * values(other);
     * // => [3, 4]
     *
     * object.a = 2;
     * values(object);
     * // => [1, 2]
     *
     * // Modify the result cache.
     * values.cache.set(object, ['a', 'b']);
     * values(object);
     * // => ['a', 'b']
     *
     * // Replace `_.memoize.Cache`.
     * _.memoize.Cache = WeakMap;
     */
    function memoize(func, resolver) {
      if (typeof func != 'function' || (resolver != null && typeof resolver != 'function')) {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      var memoized = function() {
        var args = arguments,
            key = resolver ? resolver.apply(this, args) : args[0],
            cache = memoized.cache;

        if (cache.has(key)) {
          return cache.get(key);
        }
        var result = func.apply(this, args);
        memoized.cache = cache.set(key, result) || cache;
        return result;
      };
      memoized.cache = new (memoize.Cache || MapCache);
      return memoized;
    }

    // Expose `MapCache`.
    memoize.Cache = MapCache;

    /** Used as the maximum memoize cache size. */
    var MAX_MEMOIZE_SIZE = 500;

    /**
     * A specialized version of `_.memoize` which clears the memoized function's
     * cache when it exceeds `MAX_MEMOIZE_SIZE`.
     *
     * @private
     * @param {Function} func The function to have its output memoized.
     * @returns {Function} Returns the new memoized function.
     */
    function memoizeCapped(func) {
      var result = memoize(func, function(key) {
        if (cache.size === MAX_MEMOIZE_SIZE) {
          cache.clear();
        }
        return key;
      });

      var cache = result.cache;
      return result;
    }

    /** Used to match property names within property paths. */
    var rePropName = /[^.[\]]+|\[(?:(-?\d+(?:\.\d+)?)|(["'])((?:(?!\2)[^\\]|\\.)*?)\2)\]|(?=(?:\.|\[\])(?:\.|\[\]|$))/g;

    /** Used to match backslashes in property paths. */
    var reEscapeChar = /\\(\\)?/g;

    /**
     * Converts `string` to a property path array.
     *
     * @private
     * @param {string} string The string to convert.
     * @returns {Array} Returns the property path array.
     */
    var stringToPath = memoizeCapped(function(string) {
      var result = [];
      if (string.charCodeAt(0) === 46 /* . */) {
        result.push('');
      }
      string.replace(rePropName, function(match, number, quote, subString) {
        result.push(quote ? subString.replace(reEscapeChar, '$1') : (number || match));
      });
      return result;
    });

    /**
     * A specialized version of `_.map` for arrays without support for iteratee
     * shorthands.
     *
     * @private
     * @param {Array} [array] The array to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @returns {Array} Returns the new mapped array.
     */
    function arrayMap(array, iteratee) {
      var index = -1,
          length = array == null ? 0 : array.length,
          result = Array(length);

      while (++index < length) {
        result[index] = iteratee(array[index], index, array);
      }
      return result;
    }

    /** Used as references for various `Number` constants. */
    var INFINITY = 1 / 0;

    /** Used to convert symbols to primitives and strings. */
    var symbolProto$1 = Symbol$2 ? Symbol$2.prototype : undefined,
        symbolToString = symbolProto$1 ? symbolProto$1.toString : undefined;

    /**
     * The base implementation of `_.toString` which doesn't convert nullish
     * values to empty strings.
     *
     * @private
     * @param {*} value The value to process.
     * @returns {string} Returns the string.
     */
    function baseToString(value) {
      // Exit early for strings to avoid a performance hit in some environments.
      if (typeof value == 'string') {
        return value;
      }
      if (isArray(value)) {
        // Recursively convert values (susceptible to call stack limits).
        return arrayMap(value, baseToString) + '';
      }
      if (isSymbol(value)) {
        return symbolToString ? symbolToString.call(value) : '';
      }
      var result = (value + '');
      return (result == '0' && (1 / value) == -INFINITY) ? '-0' : result;
    }

    /**
     * Converts `value` to a string. An empty string is returned for `null`
     * and `undefined` values. The sign of `-0` is preserved.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to convert.
     * @returns {string} Returns the converted string.
     * @example
     *
     * _.toString(null);
     * // => ''
     *
     * _.toString(-0);
     * // => '-0'
     *
     * _.toString([1, 2, 3]);
     * // => '1,2,3'
     */
    function toString(value) {
      return value == null ? '' : baseToString(value);
    }

    /**
     * Casts `value` to a path array if it's not one.
     *
     * @private
     * @param {*} value The value to inspect.
     * @param {Object} [object] The object to query keys on.
     * @returns {Array} Returns the cast property path array.
     */
    function castPath(value, object) {
      if (isArray(value)) {
        return value;
      }
      return isKey(value, object) ? [value] : stringToPath(toString(value));
    }

    /** Used as references for various `Number` constants. */
    var INFINITY$1 = 1 / 0;

    /**
     * Converts `value` to a string key if it's not a string or symbol.
     *
     * @private
     * @param {*} value The value to inspect.
     * @returns {string|symbol} Returns the key.
     */
    function toKey(value) {
      if (typeof value == 'string' || isSymbol(value)) {
        return value;
      }
      var result = (value + '');
      return (result == '0' && (1 / value) == -INFINITY$1) ? '-0' : result;
    }

    /**
     * The base implementation of `_.get` without support for default values.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Array|string} path The path of the property to get.
     * @returns {*} Returns the resolved value.
     */
    function baseGet(object, path) {
      path = castPath(path, object);

      var index = 0,
          length = path.length;

      while (object != null && index < length) {
        object = object[toKey(path[index++])];
      }
      return (index && index == length) ? object : undefined;
    }

    /**
     * Gets the value at `path` of `object`. If the resolved value is
     * `undefined`, the `defaultValue` is returned in its place.
     *
     * @static
     * @memberOf _
     * @since 3.7.0
     * @category Object
     * @param {Object} object The object to query.
     * @param {Array|string} path The path of the property to get.
     * @param {*} [defaultValue] The value returned for `undefined` resolved values.
     * @returns {*} Returns the resolved value.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c': 3 } }] };
     *
     * _.get(object, 'a[0].b.c');
     * // => 3
     *
     * _.get(object, ['a', '0', 'b', 'c']);
     * // => 3
     *
     * _.get(object, 'a.b.c', 'default');
     * // => 'default'
     */
    function get(object, path, defaultValue) {
      var result = object == null ? undefined : baseGet(object, path);
      return result === undefined ? defaultValue : result;
    }

    /**
     * The base implementation of `_.hasIn` without support for deep paths.
     *
     * @private
     * @param {Object} [object] The object to query.
     * @param {Array|string} key The key to check.
     * @returns {boolean} Returns `true` if `key` exists, else `false`.
     */
    function baseHasIn(object, key) {
      return object != null && key in Object(object);
    }

    /**
     * Checks if `path` exists on `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Array|string} path The path to check.
     * @param {Function} hasFunc The function to check properties.
     * @returns {boolean} Returns `true` if `path` exists, else `false`.
     */
    function hasPath(object, path, hasFunc) {
      path = castPath(path, object);

      var index = -1,
          length = path.length,
          result = false;

      while (++index < length) {
        var key = toKey(path[index]);
        if (!(result = object != null && hasFunc(object, key))) {
          break;
        }
        object = object[key];
      }
      if (result || ++index != length) {
        return result;
      }
      length = object == null ? 0 : object.length;
      return !!length && isLength(length) && isIndex(key, length) &&
        (isArray(object) || isArguments(object));
    }

    /**
     * Checks if `path` is a direct or inherited property of `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The object to query.
     * @param {Array|string} path The path to check.
     * @returns {boolean} Returns `true` if `path` exists, else `false`.
     * @example
     *
     * var object = _.create({ 'a': _.create({ 'b': 2 }) });
     *
     * _.hasIn(object, 'a');
     * // => true
     *
     * _.hasIn(object, 'a.b');
     * // => true
     *
     * _.hasIn(object, ['a', 'b']);
     * // => true
     *
     * _.hasIn(object, 'b');
     * // => false
     */
    function hasIn(object, path) {
      return object != null && hasPath(object, path, baseHasIn);
    }

    /** Used to compose bitmasks for value comparisons. */
    var COMPARE_PARTIAL_FLAG$5 = 1,
        COMPARE_UNORDERED_FLAG$3 = 2;

    /**
     * The base implementation of `_.matchesProperty` which doesn't clone `srcValue`.
     *
     * @private
     * @param {string} path The path of the property to get.
     * @param {*} srcValue The value to match.
     * @returns {Function} Returns the new spec function.
     */
    function baseMatchesProperty(path, srcValue) {
      if (isKey(path) && isStrictComparable(srcValue)) {
        return matchesStrictComparable(toKey(path), srcValue);
      }
      return function(object) {
        var objValue = get(object, path);
        return (objValue === undefined && objValue === srcValue)
          ? hasIn(object, path)
          : baseIsEqual(srcValue, objValue, COMPARE_PARTIAL_FLAG$5 | COMPARE_UNORDERED_FLAG$3);
      };
    }

    /**
     * The base implementation of `_.property` without support for deep paths.
     *
     * @private
     * @param {string} key The key of the property to get.
     * @returns {Function} Returns the new accessor function.
     */
    function baseProperty(key) {
      return function(object) {
        return object == null ? undefined : object[key];
      };
    }

    /**
     * A specialized version of `baseProperty` which supports deep paths.
     *
     * @private
     * @param {Array|string} path The path of the property to get.
     * @returns {Function} Returns the new accessor function.
     */
    function basePropertyDeep(path) {
      return function(object) {
        return baseGet(object, path);
      };
    }

    /**
     * Creates a function that returns the value at `path` of a given object.
     *
     * @static
     * @memberOf _
     * @since 2.4.0
     * @category Util
     * @param {Array|string} path The path of the property to get.
     * @returns {Function} Returns the new accessor function.
     * @example
     *
     * var objects = [
     *   { 'a': { 'b': 2 } },
     *   { 'a': { 'b': 1 } }
     * ];
     *
     * _.map(objects, _.property('a.b'));
     * // => [2, 1]
     *
     * _.map(_.sortBy(objects, _.property(['a', 'b'])), 'a.b');
     * // => [1, 2]
     */
    function property(path) {
      return isKey(path) ? baseProperty(toKey(path)) : basePropertyDeep(path);
    }

    /**
     * The base implementation of `_.iteratee`.
     *
     * @private
     * @param {*} [value=_.identity] The value to convert to an iteratee.
     * @returns {Function} Returns the iteratee.
     */
    function baseIteratee(value) {
      // Don't store the `typeof` result in a variable to avoid a JIT bug in Safari 9.
      // See https://bugs.webkit.org/show_bug.cgi?id=156034 for more details.
      if (typeof value == 'function') {
        return value;
      }
      if (value == null) {
        return identity;
      }
      if (typeof value == 'object') {
        return isArray(value)
          ? baseMatchesProperty(value[0], value[1])
          : baseMatches(value);
      }
      return property(value);
    }

    /**
     * A faster alternative to `Function#apply`, this function invokes `func`
     * with the `this` binding of `thisArg` and the arguments of `args`.
     *
     * @private
     * @param {Function} func The function to invoke.
     * @param {*} thisArg The `this` binding of `func`.
     * @param {Array} args The arguments to invoke `func` with.
     * @returns {*} Returns the result of `func`.
     */
    function apply(func, thisArg, args) {
      switch (args.length) {
        case 0: return func.call(thisArg);
        case 1: return func.call(thisArg, args[0]);
        case 2: return func.call(thisArg, args[0], args[1]);
        case 3: return func.call(thisArg, args[0], args[1], args[2]);
      }
      return func.apply(thisArg, args);
    }

    /* Built-in method references for those with the same name as other `lodash` methods. */
    var nativeMax = Math.max;

    /**
     * A specialized version of `baseRest` which transforms the rest array.
     *
     * @private
     * @param {Function} func The function to apply a rest parameter to.
     * @param {number} [start=func.length-1] The start position of the rest parameter.
     * @param {Function} transform The rest array transform.
     * @returns {Function} Returns the new function.
     */
    function overRest(func, start, transform) {
      start = nativeMax(start === undefined ? (func.length - 1) : start, 0);
      return function() {
        var args = arguments,
            index = -1,
            length = nativeMax(args.length - start, 0),
            array = Array(length);

        while (++index < length) {
          array[index] = args[start + index];
        }
        index = -1;
        var otherArgs = Array(start + 1);
        while (++index < start) {
          otherArgs[index] = args[index];
        }
        otherArgs[start] = transform(array);
        return apply(func, this, otherArgs);
      };
    }

    /**
     * Creates a function that returns `value`.
     *
     * @static
     * @memberOf _
     * @since 2.4.0
     * @category Util
     * @param {*} value The value to return from the new function.
     * @returns {Function} Returns the new constant function.
     * @example
     *
     * var objects = _.times(2, _.constant({ 'a': 1 }));
     *
     * console.log(objects);
     * // => [{ 'a': 1 }, { 'a': 1 }]
     *
     * console.log(objects[0] === objects[1]);
     * // => true
     */
    function constant(value) {
      return function() {
        return value;
      };
    }

    var defineProperty$2 = (function() {
      try {
        var func = getNative(Object, 'defineProperty');
        func({}, '', {});
        return func;
      } catch (e) {}
    }());

    /**
     * The base implementation of `setToString` without support for hot loop shorting.
     *
     * @private
     * @param {Function} func The function to modify.
     * @param {Function} string The `toString` result.
     * @returns {Function} Returns `func`.
     */
    var baseSetToString = !defineProperty$2 ? identity : function(func, string) {
      return defineProperty$2(func, 'toString', {
        'configurable': true,
        'enumerable': false,
        'value': constant(string),
        'writable': true
      });
    };

    /** Used to detect hot functions by number of calls within a span of milliseconds. */
    var HOT_COUNT = 800,
        HOT_SPAN = 16;

    /* Built-in method references for those with the same name as other `lodash` methods. */
    var nativeNow = Date.now;

    /**
     * Creates a function that'll short out and invoke `identity` instead
     * of `func` when it's called `HOT_COUNT` or more times in `HOT_SPAN`
     * milliseconds.
     *
     * @private
     * @param {Function} func The function to restrict.
     * @returns {Function} Returns the new shortable function.
     */
    function shortOut(func) {
      var count = 0,
          lastCalled = 0;

      return function() {
        var stamp = nativeNow(),
            remaining = HOT_SPAN - (stamp - lastCalled);

        lastCalled = stamp;
        if (remaining > 0) {
          if (++count >= HOT_COUNT) {
            return arguments[0];
          }
        } else {
          count = 0;
        }
        return func.apply(undefined, arguments);
      };
    }

    /**
     * Sets the `toString` method of `func` to return `string`.
     *
     * @private
     * @param {Function} func The function to modify.
     * @param {Function} string The `toString` result.
     * @returns {Function} Returns `func`.
     */
    var setToString = shortOut(baseSetToString);

    /**
     * The base implementation of `_.rest` which doesn't validate or coerce arguments.
     *
     * @private
     * @param {Function} func The function to apply a rest parameter to.
     * @param {number} [start=func.length-1] The start position of the rest parameter.
     * @returns {Function} Returns the new function.
     */
    function baseRest(func, start) {
      return setToString(overRest(func, start, identity), func + '');
    }

    /**
     * The base implementation of `_.findIndex` and `_.findLastIndex` without
     * support for iteratee shorthands.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {Function} predicate The function invoked per iteration.
     * @param {number} fromIndex The index to search from.
     * @param {boolean} [fromRight] Specify iterating from right to left.
     * @returns {number} Returns the index of the matched value, else `-1`.
     */
    function baseFindIndex(array, predicate, fromIndex, fromRight) {
      var length = array.length,
          index = fromIndex + (fromRight ? 1 : -1);

      while ((fromRight ? index-- : ++index < length)) {
        if (predicate(array[index], index, array)) {
          return index;
        }
      }
      return -1;
    }

    /**
     * The base implementation of `_.isNaN` without support for number objects.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is `NaN`, else `false`.
     */
    function baseIsNaN(value) {
      return value !== value;
    }

    /**
     * A specialized version of `_.indexOf` which performs strict equality
     * comparisons of values, i.e. `===`.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {*} value The value to search for.
     * @param {number} fromIndex The index to search from.
     * @returns {number} Returns the index of the matched value, else `-1`.
     */
    function strictIndexOf(array, value, fromIndex) {
      var index = fromIndex - 1,
          length = array.length;

      while (++index < length) {
        if (array[index] === value) {
          return index;
        }
      }
      return -1;
    }

    /**
     * The base implementation of `_.indexOf` without `fromIndex` bounds checks.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {*} value The value to search for.
     * @param {number} fromIndex The index to search from.
     * @returns {number} Returns the index of the matched value, else `-1`.
     */
    function baseIndexOf(array, value, fromIndex) {
      return value === value
        ? strictIndexOf(array, value, fromIndex)
        : baseFindIndex(array, baseIsNaN, fromIndex);
    }

    /**
     * A specialized version of `_.includes` for arrays without support for
     * specifying an index to search from.
     *
     * @private
     * @param {Array} [array] The array to inspect.
     * @param {*} target The value to search for.
     * @returns {boolean} Returns `true` if `target` is found, else `false`.
     */
    function arrayIncludes(array, value) {
      var length = array == null ? 0 : array.length;
      return !!length && baseIndexOf(array, value, 0) > -1;
    }

    /**
     * This function is like `arrayIncludes` except that it accepts a comparator.
     *
     * @private
     * @param {Array} [array] The array to inspect.
     * @param {*} target The value to search for.
     * @param {Function} comparator The comparator invoked per element.
     * @returns {boolean} Returns `true` if `target` is found, else `false`.
     */
    function arrayIncludesWith(array, value, comparator) {
      var index = -1,
          length = array == null ? 0 : array.length;

      while (++index < length) {
        if (comparator(value, array[index])) {
          return true;
        }
      }
      return false;
    }

    /**
     * This method returns `undefined`.
     *
     * @static
     * @memberOf _
     * @since 2.3.0
     * @category Util
     * @example
     *
     * _.times(2, _.noop);
     * // => [undefined, undefined]
     */
    function noop$2() {
      // No operation performed.
    }

    /** Used as references for various `Number` constants. */
    var INFINITY$2 = 1 / 0;

    /**
     * Creates a set object of `values`.
     *
     * @private
     * @param {Array} values The values to add to the set.
     * @returns {Object} Returns the new set.
     */
    var createSet = !(Set && (1 / setToArray(new Set([,-0]))[1]) == INFINITY$2) ? noop$2 : function(values) {
      return new Set(values);
    };

    /** Used as the size to enable large array optimizations. */
    var LARGE_ARRAY_SIZE$1 = 200;

    /**
     * The base implementation of `_.uniqBy` without support for iteratee shorthands.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {Function} [iteratee] The iteratee invoked per element.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new duplicate free array.
     */
    function baseUniq(array, iteratee, comparator) {
      var index = -1,
          includes = arrayIncludes,
          length = array.length,
          isCommon = true,
          result = [],
          seen = result;

      if (comparator) {
        isCommon = false;
        includes = arrayIncludesWith;
      }
      else if (length >= LARGE_ARRAY_SIZE$1) {
        var set = iteratee ? null : createSet(array);
        if (set) {
          return setToArray(set);
        }
        isCommon = false;
        includes = cacheHas;
        seen = new SetCache;
      }
      else {
        seen = iteratee ? [] : result;
      }
      outer:
      while (++index < length) {
        var value = array[index],
            computed = iteratee ? iteratee(value) : value;

        value = (comparator || value !== 0) ? value : 0;
        if (isCommon && computed === computed) {
          var seenIndex = seen.length;
          while (seenIndex--) {
            if (seen[seenIndex] === computed) {
              continue outer;
            }
          }
          if (iteratee) {
            seen.push(computed);
          }
          result.push(value);
        }
        else if (!includes(seen, computed, comparator)) {
          if (seen !== result) {
            seen.push(computed);
          }
          result.push(value);
        }
      }
      return result;
    }

    /**
     * This method is like `_.isArrayLike` except that it also checks if `value`
     * is an object.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an array-like object,
     *  else `false`.
     * @example
     *
     * _.isArrayLikeObject([1, 2, 3]);
     * // => true
     *
     * _.isArrayLikeObject(document.body.children);
     * // => true
     *
     * _.isArrayLikeObject('abc');
     * // => false
     *
     * _.isArrayLikeObject(_.noop);
     * // => false
     */
    function isArrayLikeObject(value) {
      return isObjectLike(value) && isArrayLike(value);
    }

    /**
     * Gets the last element of `array`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to query.
     * @returns {*} Returns the last element of `array`.
     * @example
     *
     * _.last([1, 2, 3]);
     * // => 3
     */
    function last(array) {
      var length = array == null ? 0 : array.length;
      return length ? array[length - 1] : undefined;
    }

    /**
     * This method is like `_.union` except that it accepts `iteratee` which is
     * invoked for each element of each `arrays` to generate the criterion by
     * which uniqueness is computed. Result values are chosen from the first
     * array in which the value occurs. The iteratee is invoked with one argument:
     * (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {Array} Returns the new array of combined values.
     * @example
     *
     * _.unionBy([2.1], [1.2, 2.3], Math.floor);
     * // => [2.1, 1.2]
     *
     * // The `_.property` iteratee shorthand.
     * _.unionBy([{ 'x': 1 }], [{ 'x': 2 }, { 'x': 1 }], 'x');
     * // => [{ 'x': 1 }, { 'x': 2 }]
     */
    var unionBy = baseRest(function(arrays) {
      var iteratee = last(arrays);
      if (isArrayLikeObject(iteratee)) {
        iteratee = undefined;
      }
      return baseUniq(baseFlatten(arrays, 1, isArrayLikeObject, true), baseIteratee(iteratee, 2));
    });

    /* Built-in method references for those with the same name as other `lodash` methods. */
    var nativeFloor = Math.floor,
        nativeRandom = Math.random;

    /**
     * The base implementation of `_.random` without support for returning
     * floating-point numbers.
     *
     * @private
     * @param {number} lower The lower bound.
     * @param {number} upper The upper bound.
     * @returns {number} Returns the random number.
     */
    function baseRandom(lower, upper) {
      return lower + nativeFloor(nativeRandom() * (upper - lower + 1));
    }

    /**
     * A specialized version of `_.sample` for arrays.
     *
     * @private
     * @param {Array} array The array to sample.
     * @returns {*} Returns the random element.
     */
    function arraySample(array) {
      var length = array.length;
      return length ? array[baseRandom(0, length - 1)] : undefined;
    }

    /**
     * The base implementation of `_.values` and `_.valuesIn` which creates an
     * array of `object` property values corresponding to the property names
     * of `props`.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Array} props The property names to get values for.
     * @returns {Object} Returns the array of property values.
     */
    function baseValues(object, props) {
      return arrayMap(props, function(key) {
        return object[key];
      });
    }

    /**
     * Creates an array of the own enumerable string keyed property values of `object`.
     *
     * **Note:** Non-object values are coerced to objects.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property values.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.values(new Foo);
     * // => [1, 2] (iteration order is not guaranteed)
     *
     * _.values('hi');
     * // => ['h', 'i']
     */
    function values(object) {
      return object == null ? [] : baseValues(object, keys(object));
    }

    /**
     * The base implementation of `_.sample`.
     *
     * @private
     * @param {Array|Object} collection The collection to sample.
     * @returns {*} Returns the random element.
     */
    function baseSample(collection) {
      return arraySample(values(collection));
    }

    /**
     * Gets a random element from `collection`.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to sample.
     * @returns {*} Returns the random element.
     * @example
     *
     * _.sample([1, 2, 3, 4]);
     * // => 2
     */
    function sample(collection) {
      var func = isArray(collection) ? arraySample : baseSample;
      return func(collection);
    }

    var defaultFormatter_1 = createCommonjsModule(function (module, exports) {

    Object.defineProperty(exports, "__esModule", {
      value: true
    });
    exports.default = defaultFormatter;



    var React = _interopRequireWildcard(React__default);

    function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj.default = obj; return newObj; } }

    function defaultFormatter(value, unit, suffix) {
      if (value !== 1) {
        unit += 's';
      }
      return value + ' ' + unit + ' ' + suffix;
    }
    });

    unwrapExports(defaultFormatter_1);

    var dateParser_1 = createCommonjsModule(function (module, exports) {

    Object.defineProperty(exports, "__esModule", {
      value: true
    });
    exports.default = dateParser;

    function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

    function _toArray(arr) { return Array.isArray(arr) ? arr : Array.from(arr); }

    function dateParser(date) {
      var parsed = new Date(date);
      if (!Number.isNaN(parsed.valueOf())) {
        return parsed;
      }

      var parts = String(date).match(/\d+/g);
      if (parts == null || parts.length <= 2) {
        return parsed;
      } else {
        var _parts$map = parts.map(function (x) {
          return parseInt(x);
        }),
            _parts$map2 = _toArray(_parts$map),
            firstP = _parts$map2[0],
            secondP = _parts$map2[1],
            restPs = _parts$map2.slice(2);

        var correctedParts = [firstP, secondP - 1].concat(_toConsumableArray(restPs));
        var isoDate = new Date(Date.UTC.apply(Date, _toConsumableArray(correctedParts)));
        return isoDate;
      }
    }
    });

    unwrapExports(dateParser_1);

    var lib$1 = createCommonjsModule(function (module, exports) {

    Object.defineProperty(exports, "__esModule", {
      value: true
    });

    var _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; };

    var _slicedToArray = function () { function sliceIterator(arr, i) { var _arr = []; var _n = true; var _d = false; var _e = undefined; try { for (var _i = arr[Symbol.iterator](), _s; !(_n = (_s = _i.next()).done); _n = true) { _arr.push(_s.value); if (i && _arr.length === i) break; } } catch (err) { _d = true; _e = err; } finally { try { if (!_n && _i["return"]) _i["return"](); } finally { if (_d) throw _e; } } return _arr; } return function (arr, i) { if (Array.isArray(arr)) { return arr; } else if (Symbol.iterator in Object(arr)) { return sliceIterator(arr, i); } else { throw new TypeError("Invalid attempt to destructure non-iterable instance"); } }; }();

    var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();



    var React = _interopRequireWildcard(React__default);



    var _defaultFormatter2 = _interopRequireDefault(defaultFormatter_1);



    var _dateParser2 = _interopRequireDefault(dateParser_1);

    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj.default = obj; return newObj; } }

    function _objectWithoutProperties(obj, keys) { var target = {}; for (var i in obj) { if (keys.indexOf(i) >= 0) continue; if (!Object.prototype.hasOwnProperty.call(obj, i)) continue; target[i] = obj[i]; } return target; }

    function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

    function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

    function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

    var Component = React.Component;


    // Just some simple constants for readability
    var MINUTE = 60;
    var HOUR = MINUTE * 60;
    var DAY = HOUR * 24;
    var WEEK = DAY * 7;
    var MONTH = DAY * 30;
    var YEAR = DAY * 365;

    var TimeAgo = function (_Component) {
      _inherits(TimeAgo, _Component);

      function TimeAgo() {
        var _ref;

        var _temp, _this, _ret;

        _classCallCheck(this, TimeAgo);

        for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        return _ret = (_temp = (_this = _possibleConstructorReturn(this, (_ref = TimeAgo.__proto__ || Object.getPrototypeOf(TimeAgo)).call.apply(_ref, [this].concat(args))), _this), _this.isStillMounted = false, _this.tick = function (refresh) {
          if (!_this.isStillMounted || !_this.props.live) {
            return;
          }

          var then = (0, _dateParser2.default)(_this.props.date).valueOf();
          if (!then) {
            console.warn('[react-timeago] Invalid Date provided');
            return;
          }

          var now = _this.props.now();
          var seconds = Math.round(Math.abs(now - then) / 1000);

          var unboundPeriod = seconds < MINUTE ? 1000 : seconds < HOUR ? 1000 * MINUTE : seconds < DAY ? 1000 * HOUR : 0;
          var period = Math.min(Math.max(unboundPeriod, _this.props.minPeriod * 1000), _this.props.maxPeriod * 1000);

          if (period) {
            if (_this.timeoutId) {
              clearTimeout(_this.timeoutId);
            }
            _this.timeoutId = setTimeout(_this.tick, period);
          }

          if (!refresh) {
            _this.forceUpdate();
          }
        }, _temp), _possibleConstructorReturn(_this, _ret);
      }

      _createClass(TimeAgo, [{
        key: 'componentDidMount',
        value: function componentDidMount() {
          this.isStillMounted = true;
          if (this.props.live) {
            this.tick(true);
          }
        }
      }, {
        key: 'componentDidUpdate',
        value: function componentDidUpdate(lastProps) {
          if (this.props.live !== lastProps.live || this.props.date !== lastProps.date) {
            if (!this.props.live && this.timeoutId) {
              clearTimeout(this.timeoutId);
            }
            this.tick();
          }
        }
      }, {
        key: 'componentWillUnmount',
        value: function componentWillUnmount() {
          this.isStillMounted = false;
          if (this.timeoutId) {
            clearTimeout(this.timeoutId);
            this.timeoutId = undefined;
          }
        }
      }, {
        key: 'render',
        value: function render() {
          /* eslint-disable no-unused-vars */
          var _props = this.props,
              date = _props.date,
              formatter = _props.formatter,
              Komponent = _props.component,
              live = _props.live,
              minPeriod = _props.minPeriod,
              maxPeriod = _props.maxPeriod,
              title = _props.title,
              now = _props.now,
              passDownProps = _objectWithoutProperties(_props, ['date', 'formatter', 'component', 'live', 'minPeriod', 'maxPeriod', 'title', 'now']);
          /* eslint-enable no-unused-vars */


          var then = (0, _dateParser2.default)(date).valueOf();
          if (!then) {
            return null;
          }
          var timeNow = now();
          var seconds = Math.round(Math.abs(timeNow - then) / 1000);
          var suffix = then < timeNow ? 'ago' : 'from now';

          var _ref2 = seconds < MINUTE ? [Math.round(seconds), 'second'] : seconds < HOUR ? [Math.round(seconds / MINUTE), 'minute'] : seconds < DAY ? [Math.round(seconds / HOUR), 'hour'] : seconds < WEEK ? [Math.round(seconds / DAY), 'day'] : seconds < MONTH ? [Math.round(seconds / WEEK), 'week'] : seconds < YEAR ? [Math.round(seconds / MONTH), 'month'] : [Math.round(seconds / YEAR), 'year'],
              _ref3 = _slicedToArray(_ref2, 2),
              value = _ref3[0],
              unit = _ref3[1];

          var passDownTitle = typeof title === 'undefined' ? typeof date === 'string' ? date : (0, _dateParser2.default)(date).toISOString().substr(0, 16).replace('T', ' ') : title;

          var spreadProps = Komponent === 'time' ? Object.assign({}, passDownProps, {
            dateTime: (0, _dateParser2.default)(date).toISOString()
          }) : passDownProps;

          var nextFormatter = _defaultFormatter2.default.bind(null, value, unit, suffix);

          return React.createElement(
            Komponent,
            _extends({}, spreadProps, { title: passDownTitle }),
            formatter(value, unit, suffix, then, nextFormatter, now)
          );
        }
      }]);

      return TimeAgo;
    }(Component);

    TimeAgo.displayName = 'TimeAgo';
    TimeAgo.defaultProps = {
      live: true,
      component: 'time',
      minPeriod: 0,
      maxPeriod: Infinity,
      formatter: _defaultFormatter2.default,
      now: function now() {
        return Date.now();
      }
    };
    exports.default = TimeAgo;
    });

    var TimeAgo = unwrapExports(lib$1);

    var implementation$1 = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;



    var _react2 = _interopRequireDefault(React__default);



    var _propTypes2 = _interopRequireDefault(propTypes);



    var _gud2 = _interopRequireDefault(gud);



    var _warning2 = _interopRequireDefault(warning_1);

    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

    function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

    function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

    var MAX_SIGNED_31_BIT_INT = 1073741823;

    // Inlined Object.is polyfill.
    // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
    function objectIs(x, y) {
      if (x === y) {
        return x !== 0 || 1 / x === 1 / y;
      } else {
        return x !== x && y !== y;
      }
    }

    function createEventEmitter(value) {
      var handlers = [];
      return {
        on: function on(handler) {
          handlers.push(handler);
        },
        off: function off(handler) {
          handlers = handlers.filter(function (h) {
            return h !== handler;
          });
        },
        get: function get() {
          return value;
        },
        set: function set(newValue, changedBits) {
          value = newValue;
          handlers.forEach(function (handler) {
            return handler(value, changedBits);
          });
        }
      };
    }

    function onlyChild(children) {
      return Array.isArray(children) ? children[0] : children;
    }

    function createReactContext(defaultValue, calculateChangedBits) {
      var _Provider$childContex, _Consumer$contextType;

      var contextProp = '__create-react-context-' + (0, _gud2.default)() + '__';

      var Provider = function (_Component) {
        _inherits(Provider, _Component);

        function Provider() {
          var _temp, _this, _ret;

          _classCallCheck(this, Provider);

          for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
            args[_key] = arguments[_key];
          }

          return _ret = (_temp = (_this = _possibleConstructorReturn(this, _Component.call.apply(_Component, [this].concat(args))), _this), _this.emitter = createEventEmitter(_this.props.value), _temp), _possibleConstructorReturn(_this, _ret);
        }

        Provider.prototype.getChildContext = function getChildContext() {
          var _ref;

          return _ref = {}, _ref[contextProp] = this.emitter, _ref;
        };

        Provider.prototype.componentWillReceiveProps = function componentWillReceiveProps(nextProps) {
          if (this.props.value !== nextProps.value) {
            var oldValue = this.props.value;
            var newValue = nextProps.value;
            var changedBits = void 0;

            if (objectIs(oldValue, newValue)) {
              changedBits = 0; // No change
            } else {
              changedBits = typeof calculateChangedBits === 'function' ? calculateChangedBits(oldValue, newValue) : MAX_SIGNED_31_BIT_INT;
              {
                (0, _warning2.default)((changedBits & MAX_SIGNED_31_BIT_INT) === changedBits, 'calculateChangedBits: Expected the return value to be a ' + '31-bit integer. Instead received: %s', changedBits);
              }

              changedBits |= 0;

              if (changedBits !== 0) {
                this.emitter.set(nextProps.value, changedBits);
              }
            }
          }
        };

        Provider.prototype.render = function render() {
          return this.props.children;
        };

        return Provider;
      }(React__default.Component);

      Provider.childContextTypes = (_Provider$childContex = {}, _Provider$childContex[contextProp] = _propTypes2.default.object.isRequired, _Provider$childContex);

      var Consumer = function (_Component2) {
        _inherits(Consumer, _Component2);

        function Consumer() {
          var _temp2, _this2, _ret2;

          _classCallCheck(this, Consumer);

          for (var _len2 = arguments.length, args = Array(_len2), _key2 = 0; _key2 < _len2; _key2++) {
            args[_key2] = arguments[_key2];
          }

          return _ret2 = (_temp2 = (_this2 = _possibleConstructorReturn(this, _Component2.call.apply(_Component2, [this].concat(args))), _this2), _this2.state = {
            value: _this2.getValue()
          }, _this2.onUpdate = function (newValue, changedBits) {
            var observedBits = _this2.observedBits | 0;
            if ((observedBits & changedBits) !== 0) {
              _this2.setState({ value: _this2.getValue() });
            }
          }, _temp2), _possibleConstructorReturn(_this2, _ret2);
        }

        Consumer.prototype.componentWillReceiveProps = function componentWillReceiveProps(nextProps) {
          var observedBits = nextProps.observedBits;

          this.observedBits = observedBits === undefined || observedBits === null ? MAX_SIGNED_31_BIT_INT // Subscribe to all changes by default
          : observedBits;
        };

        Consumer.prototype.componentDidMount = function componentDidMount() {
          if (this.context[contextProp]) {
            this.context[contextProp].on(this.onUpdate);
          }
          var observedBits = this.props.observedBits;

          this.observedBits = observedBits === undefined || observedBits === null ? MAX_SIGNED_31_BIT_INT // Subscribe to all changes by default
          : observedBits;
        };

        Consumer.prototype.componentWillUnmount = function componentWillUnmount() {
          if (this.context[contextProp]) {
            this.context[contextProp].off(this.onUpdate);
          }
        };

        Consumer.prototype.getValue = function getValue() {
          if (this.context[contextProp]) {
            return this.context[contextProp].get();
          } else {
            return defaultValue;
          }
        };

        Consumer.prototype.render = function render() {
          return onlyChild(this.props.children)(this.state.value);
        };

        return Consumer;
      }(React__default.Component);

      Consumer.contextTypes = (_Consumer$contextType = {}, _Consumer$contextType[contextProp] = _propTypes2.default.object, _Consumer$contextType);


      return {
        Provider: Provider,
        Consumer: Consumer
      };
    }

    exports.default = createReactContext;
    module.exports = exports['default'];
    });

    unwrapExports(implementation$1);

    var lib$2 = createCommonjsModule(function (module, exports) {

    exports.__esModule = true;



    var _react2 = _interopRequireDefault(React__default);



    var _implementation2 = _interopRequireDefault(implementation$1);

    function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

    exports.default = _react2.default.createContext || _implementation2.default;
    module.exports = exports['default'];
    });

    var createContext$1 = unwrapExports(lib$2);

    function warning$2(condition, message) {
      {
        if (condition) {
          return;
        }

        var text = "Warning: " + message;

        if (typeof console !== 'undefined') {
          console.warn(text);
        }

        try {
          throw Error(text);
        } catch (x) {}
      }
    }

    function isAbsolute(pathname) {
      return pathname.charAt(0) === '/';
    }

    // About 1.5x faster than the two-arg version of Array#splice()
    function spliceOne(list, index) {
      for (var i = index, k = i + 1, n = list.length; k < n; i += 1, k += 1) {
        list[i] = list[k];
      }

      list.pop();
    }

    // This implementation is based heavily on node's url.parse
    function resolvePathname(to) {
      var from = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : '';

      var toParts = to && to.split('/') || [];
      var fromParts = from && from.split('/') || [];

      var isToAbs = to && isAbsolute(to);
      var isFromAbs = from && isAbsolute(from);
      var mustEndAbs = isToAbs || isFromAbs;

      if (to && isAbsolute(to)) {
        // to is absolute
        fromParts = toParts;
      } else if (toParts.length) {
        // to is relative, drop the filename
        fromParts.pop();
        fromParts = fromParts.concat(toParts);
      }

      if (!fromParts.length) return '/';

      var hasTrailingSlash = void 0;
      if (fromParts.length) {
        var last = fromParts[fromParts.length - 1];
        hasTrailingSlash = last === '.' || last === '..' || last === '';
      } else {
        hasTrailingSlash = false;
      }

      var up = 0;
      for (var i = fromParts.length; i >= 0; i--) {
        var part = fromParts[i];

        if (part === '.') {
          spliceOne(fromParts, i);
        } else if (part === '..') {
          spliceOne(fromParts, i);
          up++;
        } else if (up) {
          spliceOne(fromParts, i);
          up--;
        }
      }

      if (!mustEndAbs) for (; up--; up) {
        fromParts.unshift('..');
      }if (mustEndAbs && fromParts[0] !== '' && (!fromParts[0] || !isAbsolute(fromParts[0]))) fromParts.unshift('');

      var result = fromParts.join('/');

      if (hasTrailingSlash && result.substr(-1) !== '/') result += '/';

      return result;
    }

    var _typeof = typeof Symbol === "function" && typeof Symbol.iterator === "symbol" ? function (obj) { return typeof obj; } : function (obj) { return obj && typeof Symbol === "function" && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj; };

    function valueEqual(a, b) {
      if (a === b) return true;

      if (a == null || b == null) return false;

      if (Array.isArray(a)) {
        return Array.isArray(b) && a.length === b.length && a.every(function (item, index) {
          return valueEqual(item, b[index]);
        });
      }

      var aType = typeof a === 'undefined' ? 'undefined' : _typeof(a);
      var bType = typeof b === 'undefined' ? 'undefined' : _typeof(b);

      if (aType !== bType) return false;

      if (aType === 'object') {
        var aValue = a.valueOf();
        var bValue = b.valueOf();

        if (aValue !== a || bValue !== b) return valueEqual(aValue, bValue);

        var aKeys = Object.keys(a);
        var bKeys = Object.keys(b);

        if (aKeys.length !== bKeys.length) return false;

        return aKeys.every(function (key) {
          return valueEqual(a[key], b[key]);
        });
      }

      return false;
    }

    var prefix = 'Invariant failed';
    function invariant(condition, message) {
      if (condition) {
        return;
      }

      {
        throw new Error(prefix + ": " + (message || ''));
      }
    }

    function addLeadingSlash(path) {
      return path.charAt(0) === '/' ? path : '/' + path;
    }
    function stripLeadingSlash(path) {
      return path.charAt(0) === '/' ? path.substr(1) : path;
    }
    function hasBasename(path, prefix) {
      return new RegExp('^' + prefix + '(\\/|\\?|#|$)', 'i').test(path);
    }
    function stripBasename(path, prefix) {
      return hasBasename(path, prefix) ? path.substr(prefix.length) : path;
    }
    function stripTrailingSlash(path) {
      return path.charAt(path.length - 1) === '/' ? path.slice(0, -1) : path;
    }
    function parsePath(path) {
      var pathname = path || '/';
      var search = '';
      var hash = '';
      var hashIndex = pathname.indexOf('#');

      if (hashIndex !== -1) {
        hash = pathname.substr(hashIndex);
        pathname = pathname.substr(0, hashIndex);
      }

      var searchIndex = pathname.indexOf('?');

      if (searchIndex !== -1) {
        search = pathname.substr(searchIndex);
        pathname = pathname.substr(0, searchIndex);
      }

      return {
        pathname: pathname,
        search: search === '?' ? '' : search,
        hash: hash === '#' ? '' : hash
      };
    }
    function createPath(location) {
      var pathname = location.pathname,
          search = location.search,
          hash = location.hash;
      var path = pathname || '/';
      if (search && search !== '?') path += search.charAt(0) === '?' ? search : "?" + search;
      if (hash && hash !== '#') path += hash.charAt(0) === '#' ? hash : "#" + hash;
      return path;
    }

    function createLocation(path, state, key, currentLocation) {
      var location;

      if (typeof path === 'string') {
        // Two-arg form: push(path, state)
        location = parsePath(path);
        location.state = state;
      } else {
        // One-arg form: push(location)
        location = _extends({}, path);
        if (location.pathname === undefined) location.pathname = '';

        if (location.search) {
          if (location.search.charAt(0) !== '?') location.search = '?' + location.search;
        } else {
          location.search = '';
        }

        if (location.hash) {
          if (location.hash.charAt(0) !== '#') location.hash = '#' + location.hash;
        } else {
          location.hash = '';
        }

        if (state !== undefined && location.state === undefined) location.state = state;
      }

      try {
        location.pathname = decodeURI(location.pathname);
      } catch (e) {
        if (e instanceof URIError) {
          throw new URIError('Pathname "' + location.pathname + '" could not be decoded. ' + 'This is likely caused by an invalid percent-encoding.');
        } else {
          throw e;
        }
      }

      if (key) location.key = key;

      if (currentLocation) {
        // Resolve incomplete/relative pathname relative to current location.
        if (!location.pathname) {
          location.pathname = currentLocation.pathname;
        } else if (location.pathname.charAt(0) !== '/') {
          location.pathname = resolvePathname(location.pathname, currentLocation.pathname);
        }
      } else {
        // When there is no prior location and pathname is empty, set it to /
        if (!location.pathname) {
          location.pathname = '/';
        }
      }

      return location;
    }
    function locationsAreEqual(a, b) {
      return a.pathname === b.pathname && a.search === b.search && a.hash === b.hash && a.key === b.key && valueEqual(a.state, b.state);
    }

    function createTransitionManager() {
      var prompt = null;

      function setPrompt(nextPrompt) {
        warning$2(prompt == null, 'A history supports only one prompt at a time');
        prompt = nextPrompt;
        return function () {
          if (prompt === nextPrompt) prompt = null;
        };
      }

      function confirmTransitionTo(location, action, getUserConfirmation, callback) {
        // TODO: If another transition starts while we're still confirming
        // the previous one, we may end up in a weird state. Figure out the
        // best way to handle this.
        if (prompt != null) {
          var result = typeof prompt === 'function' ? prompt(location, action) : prompt;

          if (typeof result === 'string') {
            if (typeof getUserConfirmation === 'function') {
              getUserConfirmation(result, callback);
            } else {
              warning$2(false, 'A history needs a getUserConfirmation function in order to use a prompt message');
              callback(true);
            }
          } else {
            // Return false from a transition hook to cancel the transition.
            callback(result !== false);
          }
        } else {
          callback(true);
        }
      }

      var listeners = [];

      function appendListener(fn) {
        var isActive = true;

        function listener() {
          if (isActive) fn.apply(void 0, arguments);
        }

        listeners.push(listener);
        return function () {
          isActive = false;
          listeners = listeners.filter(function (item) {
            return item !== listener;
          });
        };
      }

      function notifyListeners() {
        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        listeners.forEach(function (listener) {
          return listener.apply(void 0, args);
        });
      }

      return {
        setPrompt: setPrompt,
        confirmTransitionTo: confirmTransitionTo,
        appendListener: appendListener,
        notifyListeners: notifyListeners
      };
    }

    var canUseDOM$1 = !!(typeof window !== 'undefined' && window.document && window.document.createElement);
    function getConfirmation(message, callback) {
      callback(window.confirm(message)); // eslint-disable-line no-alert
    }
    /**
     * Returns true if the HTML5 history API is supported. Taken from Modernizr.
     *
     * https://github.com/Modernizr/Modernizr/blob/master/LICENSE
     * https://github.com/Modernizr/Modernizr/blob/master/feature-detects/history.js
     * changed to avoid false negatives for Windows Phones: https://github.com/reactjs/react-router/issues/586
     */

    function supportsHistory() {
      var ua = window.navigator.userAgent;
      if ((ua.indexOf('Android 2.') !== -1 || ua.indexOf('Android 4.0') !== -1) && ua.indexOf('Mobile Safari') !== -1 && ua.indexOf('Chrome') === -1 && ua.indexOf('Windows Phone') === -1) return false;
      return window.history && 'pushState' in window.history;
    }
    /**
     * Returns true if browser fires popstate on hash change.
     * IE10 and IE11 do not.
     */

    function supportsPopStateOnHashChange() {
      return window.navigator.userAgent.indexOf('Trident') === -1;
    }
    /**
     * Returns false if using go(n) with hash history causes a full page reload.
     */

    function supportsGoWithoutReloadUsingHash() {
      return window.navigator.userAgent.indexOf('Firefox') === -1;
    }
    /**
     * Returns true if a given popstate event is an extraneous WebKit event.
     * Accounts for the fact that Chrome on iOS fires real popstate events
     * containing undefined state when pressing the back button.
     */

    function isExtraneousPopstateEvent(event) {
      event.state === undefined && navigator.userAgent.indexOf('CriOS') === -1;
    }

    var PopStateEvent = 'popstate';
    var HashChangeEvent = 'hashchange';

    function getHistoryState() {
      try {
        return window.history.state || {};
      } catch (e) {
        // IE 11 sometimes throws when accessing window.history.state
        // See https://github.com/ReactTraining/history/pull/289
        return {};
      }
    }
    /**
     * Creates a history object that uses the HTML5 history API including
     * pushState, replaceState, and the popstate event.
     */


    function createBrowserHistory(props) {
      if (props === void 0) {
        props = {};
      }

      !canUseDOM$1 ? invariant(false, 'Browser history needs a DOM') : void 0;
      var globalHistory = window.history;
      var canUseHistory = supportsHistory();
      var needsHashChangeListener = !supportsPopStateOnHashChange();
      var _props = props,
          _props$forceRefresh = _props.forceRefresh,
          forceRefresh = _props$forceRefresh === void 0 ? false : _props$forceRefresh,
          _props$getUserConfirm = _props.getUserConfirmation,
          getUserConfirmation = _props$getUserConfirm === void 0 ? getConfirmation : _props$getUserConfirm,
          _props$keyLength = _props.keyLength,
          keyLength = _props$keyLength === void 0 ? 6 : _props$keyLength;
      var basename = props.basename ? stripTrailingSlash(addLeadingSlash(props.basename)) : '';

      function getDOMLocation(historyState) {
        var _ref = historyState || {},
            key = _ref.key,
            state = _ref.state;

        var _window$location = window.location,
            pathname = _window$location.pathname,
            search = _window$location.search,
            hash = _window$location.hash;
        var path = pathname + search + hash;
        warning$2(!basename || hasBasename(path, basename), 'You are attempting to use a basename on a page whose URL path does not begin ' + 'with the basename. Expected path "' + path + '" to begin with "' + basename + '".');
        if (basename) path = stripBasename(path, basename);
        return createLocation(path, state, key);
      }

      function createKey() {
        return Math.random().toString(36).substr(2, keyLength);
      }

      var transitionManager = createTransitionManager();

      function setState(nextState) {
        _extends(history, nextState);

        history.length = globalHistory.length;
        transitionManager.notifyListeners(history.location, history.action);
      }

      function handlePopState(event) {
        // Ignore extraneous popstate events in WebKit.
        if (isExtraneousPopstateEvent(event)) return;
        handlePop(getDOMLocation(event.state));
      }

      function handleHashChange() {
        handlePop(getDOMLocation(getHistoryState()));
      }

      var forceNextPop = false;

      function handlePop(location) {
        if (forceNextPop) {
          forceNextPop = false;
          setState();
        } else {
          var action = 'POP';
          transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
            if (ok) {
              setState({
                action: action,
                location: location
              });
            } else {
              revertPop(location);
            }
          });
        }
      }

      function revertPop(fromLocation) {
        var toLocation = history.location; // TODO: We could probably make this more reliable by
        // keeping a list of keys we've seen in sessionStorage.
        // Instead, we just default to 0 for keys we don't know.

        var toIndex = allKeys.indexOf(toLocation.key);
        if (toIndex === -1) toIndex = 0;
        var fromIndex = allKeys.indexOf(fromLocation.key);
        if (fromIndex === -1) fromIndex = 0;
        var delta = toIndex - fromIndex;

        if (delta) {
          forceNextPop = true;
          go(delta);
        }
      }

      var initialLocation = getDOMLocation(getHistoryState());
      var allKeys = [initialLocation.key]; // Public interface

      function createHref(location) {
        return basename + createPath(location);
      }

      function push(path, state) {
        warning$2(!(typeof path === 'object' && path.state !== undefined && state !== undefined), 'You should avoid providing a 2nd state argument to push when the 1st ' + 'argument is a location-like object that already has state; it is ignored');
        var action = 'PUSH';
        var location = createLocation(path, state, createKey(), history.location);
        transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
          if (!ok) return;
          var href = createHref(location);
          var key = location.key,
              state = location.state;

          if (canUseHistory) {
            globalHistory.pushState({
              key: key,
              state: state
            }, null, href);

            if (forceRefresh) {
              window.location.href = href;
            } else {
              var prevIndex = allKeys.indexOf(history.location.key);
              var nextKeys = allKeys.slice(0, prevIndex === -1 ? 0 : prevIndex + 1);
              nextKeys.push(location.key);
              allKeys = nextKeys;
              setState({
                action: action,
                location: location
              });
            }
          } else {
            warning$2(state === undefined, 'Browser history cannot push state in browsers that do not support HTML5 history');
            window.location.href = href;
          }
        });
      }

      function replace(path, state) {
        warning$2(!(typeof path === 'object' && path.state !== undefined && state !== undefined), 'You should avoid providing a 2nd state argument to replace when the 1st ' + 'argument is a location-like object that already has state; it is ignored');
        var action = 'REPLACE';
        var location = createLocation(path, state, createKey(), history.location);
        transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
          if (!ok) return;
          var href = createHref(location);
          var key = location.key,
              state = location.state;

          if (canUseHistory) {
            globalHistory.replaceState({
              key: key,
              state: state
            }, null, href);

            if (forceRefresh) {
              window.location.replace(href);
            } else {
              var prevIndex = allKeys.indexOf(history.location.key);
              if (prevIndex !== -1) allKeys[prevIndex] = location.key;
              setState({
                action: action,
                location: location
              });
            }
          } else {
            warning$2(state === undefined, 'Browser history cannot replace state in browsers that do not support HTML5 history');
            window.location.replace(href);
          }
        });
      }

      function go(n) {
        globalHistory.go(n);
      }

      function goBack() {
        go(-1);
      }

      function goForward() {
        go(1);
      }

      var listenerCount = 0;

      function checkDOMListeners(delta) {
        listenerCount += delta;

        if (listenerCount === 1 && delta === 1) {
          window.addEventListener(PopStateEvent, handlePopState);
          if (needsHashChangeListener) window.addEventListener(HashChangeEvent, handleHashChange);
        } else if (listenerCount === 0) {
          window.removeEventListener(PopStateEvent, handlePopState);
          if (needsHashChangeListener) window.removeEventListener(HashChangeEvent, handleHashChange);
        }
      }

      var isBlocked = false;

      function block(prompt) {
        if (prompt === void 0) {
          prompt = false;
        }

        var unblock = transitionManager.setPrompt(prompt);

        if (!isBlocked) {
          checkDOMListeners(1);
          isBlocked = true;
        }

        return function () {
          if (isBlocked) {
            isBlocked = false;
            checkDOMListeners(-1);
          }

          return unblock();
        };
      }

      function listen(listener) {
        var unlisten = transitionManager.appendListener(listener);
        checkDOMListeners(1);
        return function () {
          checkDOMListeners(-1);
          unlisten();
        };
      }

      var history = {
        length: globalHistory.length,
        action: 'POP',
        location: initialLocation,
        createHref: createHref,
        push: push,
        replace: replace,
        go: go,
        goBack: goBack,
        goForward: goForward,
        block: block,
        listen: listen
      };
      return history;
    }

    var HashChangeEvent$1 = 'hashchange';
    var HashPathCoders = {
      hashbang: {
        encodePath: function encodePath(path) {
          return path.charAt(0) === '!' ? path : '!/' + stripLeadingSlash(path);
        },
        decodePath: function decodePath(path) {
          return path.charAt(0) === '!' ? path.substr(1) : path;
        }
      },
      noslash: {
        encodePath: stripLeadingSlash,
        decodePath: addLeadingSlash
      },
      slash: {
        encodePath: addLeadingSlash,
        decodePath: addLeadingSlash
      }
    };

    function getHashPath() {
      // We can't use window.location.hash here because it's not
      // consistent across browsers - Firefox will pre-decode it!
      var href = window.location.href;
      var hashIndex = href.indexOf('#');
      return hashIndex === -1 ? '' : href.substring(hashIndex + 1);
    }

    function pushHashPath(path) {
      window.location.hash = path;
    }

    function replaceHashPath(path) {
      var hashIndex = window.location.href.indexOf('#');
      window.location.replace(window.location.href.slice(0, hashIndex >= 0 ? hashIndex : 0) + '#' + path);
    }

    function createHashHistory(props) {
      if (props === void 0) {
        props = {};
      }

      !canUseDOM$1 ? invariant(false, 'Hash history needs a DOM') : void 0;
      var globalHistory = window.history;
      var canGoWithoutReload = supportsGoWithoutReloadUsingHash();
      var _props = props,
          _props$getUserConfirm = _props.getUserConfirmation,
          getUserConfirmation = _props$getUserConfirm === void 0 ? getConfirmation : _props$getUserConfirm,
          _props$hashType = _props.hashType,
          hashType = _props$hashType === void 0 ? 'slash' : _props$hashType;
      var basename = props.basename ? stripTrailingSlash(addLeadingSlash(props.basename)) : '';
      var _HashPathCoders$hashT = HashPathCoders[hashType],
          encodePath = _HashPathCoders$hashT.encodePath,
          decodePath = _HashPathCoders$hashT.decodePath;

      function getDOMLocation() {
        var path = decodePath(getHashPath());
        warning$2(!basename || hasBasename(path, basename), 'You are attempting to use a basename on a page whose URL path does not begin ' + 'with the basename. Expected path "' + path + '" to begin with "' + basename + '".');
        if (basename) path = stripBasename(path, basename);
        return createLocation(path);
      }

      var transitionManager = createTransitionManager();

      function setState(nextState) {
        _extends(history, nextState);

        history.length = globalHistory.length;
        transitionManager.notifyListeners(history.location, history.action);
      }

      var forceNextPop = false;
      var ignorePath = null;

      function handleHashChange() {
        var path = getHashPath();
        var encodedPath = encodePath(path);

        if (path !== encodedPath) {
          // Ensure we always have a properly-encoded hash.
          replaceHashPath(encodedPath);
        } else {
          var location = getDOMLocation();
          var prevLocation = history.location;
          if (!forceNextPop && locationsAreEqual(prevLocation, location)) return; // A hashchange doesn't always == location change.

          if (ignorePath === createPath(location)) return; // Ignore this change; we already setState in push/replace.

          ignorePath = null;
          handlePop(location);
        }
      }

      function handlePop(location) {
        if (forceNextPop) {
          forceNextPop = false;
          setState();
        } else {
          var action = 'POP';
          transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
            if (ok) {
              setState({
                action: action,
                location: location
              });
            } else {
              revertPop(location);
            }
          });
        }
      }

      function revertPop(fromLocation) {
        var toLocation = history.location; // TODO: We could probably make this more reliable by
        // keeping a list of paths we've seen in sessionStorage.
        // Instead, we just default to 0 for paths we don't know.

        var toIndex = allPaths.lastIndexOf(createPath(toLocation));
        if (toIndex === -1) toIndex = 0;
        var fromIndex = allPaths.lastIndexOf(createPath(fromLocation));
        if (fromIndex === -1) fromIndex = 0;
        var delta = toIndex - fromIndex;

        if (delta) {
          forceNextPop = true;
          go(delta);
        }
      } // Ensure the hash is encoded properly before doing anything else.


      var path = getHashPath();
      var encodedPath = encodePath(path);
      if (path !== encodedPath) replaceHashPath(encodedPath);
      var initialLocation = getDOMLocation();
      var allPaths = [createPath(initialLocation)]; // Public interface

      function createHref(location) {
        return '#' + encodePath(basename + createPath(location));
      }

      function push(path, state) {
        warning$2(state === undefined, 'Hash history cannot push state; it is ignored');
        var action = 'PUSH';
        var location = createLocation(path, undefined, undefined, history.location);
        transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
          if (!ok) return;
          var path = createPath(location);
          var encodedPath = encodePath(basename + path);
          var hashChanged = getHashPath() !== encodedPath;

          if (hashChanged) {
            // We cannot tell if a hashchange was caused by a PUSH, so we'd
            // rather setState here and ignore the hashchange. The caveat here
            // is that other hash histories in the page will consider it a POP.
            ignorePath = path;
            pushHashPath(encodedPath);
            var prevIndex = allPaths.lastIndexOf(createPath(history.location));
            var nextPaths = allPaths.slice(0, prevIndex === -1 ? 0 : prevIndex + 1);
            nextPaths.push(path);
            allPaths = nextPaths;
            setState({
              action: action,
              location: location
            });
          } else {
            warning$2(false, 'Hash history cannot PUSH the same path; a new entry will not be added to the history stack');
            setState();
          }
        });
      }

      function replace(path, state) {
        warning$2(state === undefined, 'Hash history cannot replace state; it is ignored');
        var action = 'REPLACE';
        var location = createLocation(path, undefined, undefined, history.location);
        transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
          if (!ok) return;
          var path = createPath(location);
          var encodedPath = encodePath(basename + path);
          var hashChanged = getHashPath() !== encodedPath;

          if (hashChanged) {
            // We cannot tell if a hashchange was caused by a REPLACE, so we'd
            // rather setState here and ignore the hashchange. The caveat here
            // is that other hash histories in the page will consider it a POP.
            ignorePath = path;
            replaceHashPath(encodedPath);
          }

          var prevIndex = allPaths.indexOf(createPath(history.location));
          if (prevIndex !== -1) allPaths[prevIndex] = path;
          setState({
            action: action,
            location: location
          });
        });
      }

      function go(n) {
        warning$2(canGoWithoutReload, 'Hash history go(n) causes a full page reload in this browser');
        globalHistory.go(n);
      }

      function goBack() {
        go(-1);
      }

      function goForward() {
        go(1);
      }

      var listenerCount = 0;

      function checkDOMListeners(delta) {
        listenerCount += delta;

        if (listenerCount === 1 && delta === 1) {
          window.addEventListener(HashChangeEvent$1, handleHashChange);
        } else if (listenerCount === 0) {
          window.removeEventListener(HashChangeEvent$1, handleHashChange);
        }
      }

      var isBlocked = false;

      function block(prompt) {
        if (prompt === void 0) {
          prompt = false;
        }

        var unblock = transitionManager.setPrompt(prompt);

        if (!isBlocked) {
          checkDOMListeners(1);
          isBlocked = true;
        }

        return function () {
          if (isBlocked) {
            isBlocked = false;
            checkDOMListeners(-1);
          }

          return unblock();
        };
      }

      function listen(listener) {
        var unlisten = transitionManager.appendListener(listener);
        checkDOMListeners(1);
        return function () {
          checkDOMListeners(-1);
          unlisten();
        };
      }

      var history = {
        length: globalHistory.length,
        action: 'POP',
        location: initialLocation,
        createHref: createHref,
        push: push,
        replace: replace,
        go: go,
        goBack: goBack,
        goForward: goForward,
        block: block,
        listen: listen
      };
      return history;
    }

    function clamp(n, lowerBound, upperBound) {
      return Math.min(Math.max(n, lowerBound), upperBound);
    }
    /**
     * Creates a history object that stores locations in memory.
     */


    function createMemoryHistory(props) {
      if (props === void 0) {
        props = {};
      }

      var _props = props,
          getUserConfirmation = _props.getUserConfirmation,
          _props$initialEntries = _props.initialEntries,
          initialEntries = _props$initialEntries === void 0 ? ['/'] : _props$initialEntries,
          _props$initialIndex = _props.initialIndex,
          initialIndex = _props$initialIndex === void 0 ? 0 : _props$initialIndex,
          _props$keyLength = _props.keyLength,
          keyLength = _props$keyLength === void 0 ? 6 : _props$keyLength;
      var transitionManager = createTransitionManager();

      function setState(nextState) {
        _extends(history, nextState);

        history.length = history.entries.length;
        transitionManager.notifyListeners(history.location, history.action);
      }

      function createKey() {
        return Math.random().toString(36).substr(2, keyLength);
      }

      var index = clamp(initialIndex, 0, initialEntries.length - 1);
      var entries = initialEntries.map(function (entry) {
        return typeof entry === 'string' ? createLocation(entry, undefined, createKey()) : createLocation(entry, undefined, entry.key || createKey());
      }); // Public interface

      var createHref = createPath;

      function push(path, state) {
        warning$2(!(typeof path === 'object' && path.state !== undefined && state !== undefined), 'You should avoid providing a 2nd state argument to push when the 1st ' + 'argument is a location-like object that already has state; it is ignored');
        var action = 'PUSH';
        var location = createLocation(path, state, createKey(), history.location);
        transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
          if (!ok) return;
          var prevIndex = history.index;
          var nextIndex = prevIndex + 1;
          var nextEntries = history.entries.slice(0);

          if (nextEntries.length > nextIndex) {
            nextEntries.splice(nextIndex, nextEntries.length - nextIndex, location);
          } else {
            nextEntries.push(location);
          }

          setState({
            action: action,
            location: location,
            index: nextIndex,
            entries: nextEntries
          });
        });
      }

      function replace(path, state) {
        warning$2(!(typeof path === 'object' && path.state !== undefined && state !== undefined), 'You should avoid providing a 2nd state argument to replace when the 1st ' + 'argument is a location-like object that already has state; it is ignored');
        var action = 'REPLACE';
        var location = createLocation(path, state, createKey(), history.location);
        transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
          if (!ok) return;
          history.entries[history.index] = location;
          setState({
            action: action,
            location: location
          });
        });
      }

      function go(n) {
        var nextIndex = clamp(history.index + n, 0, history.entries.length - 1);
        var action = 'POP';
        var location = history.entries[nextIndex];
        transitionManager.confirmTransitionTo(location, action, getUserConfirmation, function (ok) {
          if (ok) {
            setState({
              action: action,
              location: location,
              index: nextIndex
            });
          } else {
            // Mimic the behavior of DOM histories by
            // causing a render after a cancelled POP.
            setState();
          }
        });
      }

      function goBack() {
        go(-1);
      }

      function goForward() {
        go(1);
      }

      function canGo(n) {
        var nextIndex = history.index + n;
        return nextIndex >= 0 && nextIndex < history.entries.length;
      }

      function block(prompt) {
        if (prompt === void 0) {
          prompt = false;
        }

        return transitionManager.setPrompt(prompt);
      }

      function listen(listener) {
        return transitionManager.appendListener(listener);
      }

      var history = {
        length: entries.length,
        action: 'POP',
        location: entries[index],
        index: index,
        entries: entries,
        createHref: createHref,
        push: push,
        replace: replace,
        go: go,
        goBack: goBack,
        goForward: goForward,
        canGo: canGo,
        block: block,
        listen: listen
      };
      return history;
    }

    var isarray = Array.isArray || function (arr) {
      return Object.prototype.toString.call(arr) == '[object Array]';
    };

    /**
     * Expose `pathToRegexp`.
     */
    var pathToRegexp_1 = pathToRegexp;
    var parse_1 = parse;
    var compile_1 = compile;
    var tokensToFunction_1 = tokensToFunction;
    var tokensToRegExp_1 = tokensToRegExp;

    /**
     * The main path matching regexp utility.
     *
     * @type {RegExp}
     */
    var PATH_REGEXP = new RegExp([
      // Match escaped characters that would otherwise appear in future matches.
      // This allows the user to escape special characters that won't transform.
      '(\\\\.)',
      // Match Express-style parameters and un-named parameters with a prefix
      // and optional suffixes. Matches appear as:
      //
      // "/:test(\\d+)?" => ["/", "test", "\d+", undefined, "?", undefined]
      // "/route(\\d+)"  => [undefined, undefined, undefined, "\d+", undefined, undefined]
      // "/*"            => ["/", undefined, undefined, undefined, undefined, "*"]
      '([\\/.])?(?:(?:\\:(\\w+)(?:\\(((?:\\\\.|[^\\\\()])+)\\))?|\\(((?:\\\\.|[^\\\\()])+)\\))([+*?])?|(\\*))'
    ].join('|'), 'g');

    /**
     * Parse a string for the raw tokens.
     *
     * @param  {string}  str
     * @param  {Object=} options
     * @return {!Array}
     */
    function parse (str, options) {
      var tokens = [];
      var key = 0;
      var index = 0;
      var path = '';
      var defaultDelimiter = options && options.delimiter || '/';
      var res;

      while ((res = PATH_REGEXP.exec(str)) != null) {
        var m = res[0];
        var escaped = res[1];
        var offset = res.index;
        path += str.slice(index, offset);
        index = offset + m.length;

        // Ignore already escaped sequences.
        if (escaped) {
          path += escaped[1];
          continue
        }

        var next = str[index];
        var prefix = res[2];
        var name = res[3];
        var capture = res[4];
        var group = res[5];
        var modifier = res[6];
        var asterisk = res[7];

        // Push the current path onto the tokens.
        if (path) {
          tokens.push(path);
          path = '';
        }

        var partial = prefix != null && next != null && next !== prefix;
        var repeat = modifier === '+' || modifier === '*';
        var optional = modifier === '?' || modifier === '*';
        var delimiter = res[2] || defaultDelimiter;
        var pattern = capture || group;

        tokens.push({
          name: name || key++,
          prefix: prefix || '',
          delimiter: delimiter,
          optional: optional,
          repeat: repeat,
          partial: partial,
          asterisk: !!asterisk,
          pattern: pattern ? escapeGroup(pattern) : (asterisk ? '.*' : '[^' + escapeString(delimiter) + ']+?')
        });
      }

      // Match any characters still remaining.
      if (index < str.length) {
        path += str.substr(index);
      }

      // If the path exists, push it onto the end.
      if (path) {
        tokens.push(path);
      }

      return tokens
    }

    /**
     * Compile a string to a template function for the path.
     *
     * @param  {string}             str
     * @param  {Object=}            options
     * @return {!function(Object=, Object=)}
     */
    function compile (str, options) {
      return tokensToFunction(parse(str, options))
    }

    /**
     * Prettier encoding of URI path segments.
     *
     * @param  {string}
     * @return {string}
     */
    function encodeURIComponentPretty (str) {
      return encodeURI(str).replace(/[\/?#]/g, function (c) {
        return '%' + c.charCodeAt(0).toString(16).toUpperCase()
      })
    }

    /**
     * Encode the asterisk parameter. Similar to `pretty`, but allows slashes.
     *
     * @param  {string}
     * @return {string}
     */
    function encodeAsterisk (str) {
      return encodeURI(str).replace(/[?#]/g, function (c) {
        return '%' + c.charCodeAt(0).toString(16).toUpperCase()
      })
    }

    /**
     * Expose a method for transforming tokens into the path function.
     */
    function tokensToFunction (tokens) {
      // Compile all the tokens into regexps.
      var matches = new Array(tokens.length);

      // Compile all the patterns before compilation.
      for (var i = 0; i < tokens.length; i++) {
        if (typeof tokens[i] === 'object') {
          matches[i] = new RegExp('^(?:' + tokens[i].pattern + ')$');
        }
      }

      return function (obj, opts) {
        var path = '';
        var data = obj || {};
        var options = opts || {};
        var encode = options.pretty ? encodeURIComponentPretty : encodeURIComponent;

        for (var i = 0; i < tokens.length; i++) {
          var token = tokens[i];

          if (typeof token === 'string') {
            path += token;

            continue
          }

          var value = data[token.name];
          var segment;

          if (value == null) {
            if (token.optional) {
              // Prepend partial segment prefixes.
              if (token.partial) {
                path += token.prefix;
              }

              continue
            } else {
              throw new TypeError('Expected "' + token.name + '" to be defined')
            }
          }

          if (isarray(value)) {
            if (!token.repeat) {
              throw new TypeError('Expected "' + token.name + '" to not repeat, but received `' + JSON.stringify(value) + '`')
            }

            if (value.length === 0) {
              if (token.optional) {
                continue
              } else {
                throw new TypeError('Expected "' + token.name + '" to not be empty')
              }
            }

            for (var j = 0; j < value.length; j++) {
              segment = encode(value[j]);

              if (!matches[i].test(segment)) {
                throw new TypeError('Expected all "' + token.name + '" to match "' + token.pattern + '", but received `' + JSON.stringify(segment) + '`')
              }

              path += (j === 0 ? token.prefix : token.delimiter) + segment;
            }

            continue
          }

          segment = token.asterisk ? encodeAsterisk(value) : encode(value);

          if (!matches[i].test(segment)) {
            throw new TypeError('Expected "' + token.name + '" to match "' + token.pattern + '", but received "' + segment + '"')
          }

          path += token.prefix + segment;
        }

        return path
      }
    }

    /**
     * Escape a regular expression string.
     *
     * @param  {string} str
     * @return {string}
     */
    function escapeString (str) {
      return str.replace(/([.+*?=^!:${}()[\]|\/\\])/g, '\\$1')
    }

    /**
     * Escape the capturing group by escaping special characters and meaning.
     *
     * @param  {string} group
     * @return {string}
     */
    function escapeGroup (group) {
      return group.replace(/([=!:$\/()])/g, '\\$1')
    }

    /**
     * Attach the keys as a property of the regexp.
     *
     * @param  {!RegExp} re
     * @param  {Array}   keys
     * @return {!RegExp}
     */
    function attachKeys (re, keys) {
      re.keys = keys;
      return re
    }

    /**
     * Get the flags for a regexp from the options.
     *
     * @param  {Object} options
     * @return {string}
     */
    function flags (options) {
      return options.sensitive ? '' : 'i'
    }

    /**
     * Pull out keys from a regexp.
     *
     * @param  {!RegExp} path
     * @param  {!Array}  keys
     * @return {!RegExp}
     */
    function regexpToRegexp (path, keys) {
      // Use a negative lookahead to match only capturing groups.
      var groups = path.source.match(/\((?!\?)/g);

      if (groups) {
        for (var i = 0; i < groups.length; i++) {
          keys.push({
            name: i,
            prefix: null,
            delimiter: null,
            optional: false,
            repeat: false,
            partial: false,
            asterisk: false,
            pattern: null
          });
        }
      }

      return attachKeys(path, keys)
    }

    /**
     * Transform an array into a regexp.
     *
     * @param  {!Array}  path
     * @param  {Array}   keys
     * @param  {!Object} options
     * @return {!RegExp}
     */
    function arrayToRegexp (path, keys, options) {
      var parts = [];

      for (var i = 0; i < path.length; i++) {
        parts.push(pathToRegexp(path[i], keys, options).source);
      }

      var regexp = new RegExp('(?:' + parts.join('|') + ')', flags(options));

      return attachKeys(regexp, keys)
    }

    /**
     * Create a path regexp from string input.
     *
     * @param  {string}  path
     * @param  {!Array}  keys
     * @param  {!Object} options
     * @return {!RegExp}
     */
    function stringToRegexp (path, keys, options) {
      return tokensToRegExp(parse(path, options), keys, options)
    }

    /**
     * Expose a function for taking tokens and returning a RegExp.
     *
     * @param  {!Array}          tokens
     * @param  {(Array|Object)=} keys
     * @param  {Object=}         options
     * @return {!RegExp}
     */
    function tokensToRegExp (tokens, keys, options) {
      if (!isarray(keys)) {
        options = /** @type {!Object} */ (keys || options);
        keys = [];
      }

      options = options || {};

      var strict = options.strict;
      var end = options.end !== false;
      var route = '';

      // Iterate over the tokens and create our regexp string.
      for (var i = 0; i < tokens.length; i++) {
        var token = tokens[i];

        if (typeof token === 'string') {
          route += escapeString(token);
        } else {
          var prefix = escapeString(token.prefix);
          var capture = '(?:' + token.pattern + ')';

          keys.push(token);

          if (token.repeat) {
            capture += '(?:' + prefix + capture + ')*';
          }

          if (token.optional) {
            if (!token.partial) {
              capture = '(?:' + prefix + '(' + capture + '))?';
            } else {
              capture = prefix + '(' + capture + ')?';
            }
          } else {
            capture = prefix + '(' + capture + ')';
          }

          route += capture;
        }
      }

      var delimiter = escapeString(options.delimiter || '/');
      var endsWithDelimiter = route.slice(-delimiter.length) === delimiter;

      // In non-strict mode we allow a slash at the end of match. If the path to
      // match already ends with a slash, we remove it for consistency. The slash
      // is valid at the end of a path match, not in the middle. This is important
      // in non-ending mode, where "/test/" shouldn't match "/test//route".
      if (!strict) {
        route = (endsWithDelimiter ? route.slice(0, -delimiter.length) : route) + '(?:' + delimiter + '(?=$))?';
      }

      if (end) {
        route += '$';
      } else {
        // In non-ending mode, we need the capturing groups to match as much as
        // possible by using a positive lookahead to the end or next path segment.
        route += strict && endsWithDelimiter ? '' : '(?=' + delimiter + '|$)';
      }

      return attachKeys(new RegExp('^' + route, flags(options)), keys)
    }

    /**
     * Normalize the given path string, returning a regular expression.
     *
     * An empty array can be passed in for the keys, which will hold the
     * placeholder key descriptions. For example, using `/user/:id`, `keys` will
     * contain `[{ name: 'id', delimiter: '/', optional: false, repeat: false }]`.
     *
     * @param  {(string|RegExp|Array)} path
     * @param  {(Array|Object)=}       keys
     * @param  {Object=}               options
     * @return {!RegExp}
     */
    function pathToRegexp (path, keys, options) {
      if (!isarray(keys)) {
        options = /** @type {!Object} */ (keys || options);
        keys = [];
      }

      options = options || {};

      if (path instanceof RegExp) {
        return regexpToRegexp(path, /** @type {!Array} */ (keys))
      }

      if (isarray(path)) {
        return arrayToRegexp(/** @type {!Array} */ (path), /** @type {!Array} */ (keys), options)
      }

      return stringToRegexp(/** @type {string} */ (path), /** @type {!Array} */ (keys), options)
    }
    pathToRegexp_1.parse = parse_1;
    pathToRegexp_1.compile = compile_1;
    pathToRegexp_1.tokensToFunction = tokensToFunction_1;
    pathToRegexp_1.tokensToRegExp = tokensToRegExp_1;

    var reactIs_production_min = createCommonjsModule(function (module, exports) {
    Object.defineProperty(exports,"__esModule",{value:!0});
    var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?Symbol.for("react.memo"):
    60115,r=b?Symbol.for("react.lazy"):60116;function t(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case h:return a;default:return u}}case r:case q:case d:return u}}}function v(a){return t(a)===m}exports.typeOf=t;exports.AsyncMode=l;exports.ConcurrentMode=m;exports.ContextConsumer=k;exports.ContextProvider=h;exports.Element=c;exports.ForwardRef=n;
    exports.Fragment=e;exports.Lazy=r;exports.Memo=q;exports.Portal=d;exports.Profiler=g;exports.StrictMode=f;exports.Suspense=p;exports.isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||"object"===typeof a&&null!==a&&(a.$$typeof===r||a.$$typeof===q||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n)};exports.isAsyncMode=function(a){return v(a)||t(a)===l};exports.isConcurrentMode=v;exports.isContextConsumer=function(a){return t(a)===k};
    exports.isContextProvider=function(a){return t(a)===h};exports.isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};exports.isForwardRef=function(a){return t(a)===n};exports.isFragment=function(a){return t(a)===e};exports.isLazy=function(a){return t(a)===r};exports.isMemo=function(a){return t(a)===q};exports.isPortal=function(a){return t(a)===d};exports.isProfiler=function(a){return t(a)===g};exports.isStrictMode=function(a){return t(a)===f};
    exports.isSuspense=function(a){return t(a)===p};
    });

    unwrapExports(reactIs_production_min);
    var reactIs_production_min_1 = reactIs_production_min.typeOf;
    var reactIs_production_min_2 = reactIs_production_min.AsyncMode;
    var reactIs_production_min_3 = reactIs_production_min.ConcurrentMode;
    var reactIs_production_min_4 = reactIs_production_min.ContextConsumer;
    var reactIs_production_min_5 = reactIs_production_min.ContextProvider;
    var reactIs_production_min_6 = reactIs_production_min.Element;
    var reactIs_production_min_7 = reactIs_production_min.ForwardRef;
    var reactIs_production_min_8 = reactIs_production_min.Fragment;
    var reactIs_production_min_9 = reactIs_production_min.Lazy;
    var reactIs_production_min_10 = reactIs_production_min.Memo;
    var reactIs_production_min_11 = reactIs_production_min.Portal;
    var reactIs_production_min_12 = reactIs_production_min.Profiler;
    var reactIs_production_min_13 = reactIs_production_min.StrictMode;
    var reactIs_production_min_14 = reactIs_production_min.Suspense;
    var reactIs_production_min_15 = reactIs_production_min.isValidElementType;
    var reactIs_production_min_16 = reactIs_production_min.isAsyncMode;
    var reactIs_production_min_17 = reactIs_production_min.isConcurrentMode;
    var reactIs_production_min_18 = reactIs_production_min.isContextConsumer;
    var reactIs_production_min_19 = reactIs_production_min.isContextProvider;
    var reactIs_production_min_20 = reactIs_production_min.isElement;
    var reactIs_production_min_21 = reactIs_production_min.isForwardRef;
    var reactIs_production_min_22 = reactIs_production_min.isFragment;
    var reactIs_production_min_23 = reactIs_production_min.isLazy;
    var reactIs_production_min_24 = reactIs_production_min.isMemo;
    var reactIs_production_min_25 = reactIs_production_min.isPortal;
    var reactIs_production_min_26 = reactIs_production_min.isProfiler;
    var reactIs_production_min_27 = reactIs_production_min.isStrictMode;
    var reactIs_production_min_28 = reactIs_production_min.isSuspense;

    var reactIs_development = createCommonjsModule(function (module, exports) {



    {
      (function() {

    Object.defineProperty(exports, '__esModule', { value: true });

    // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
    // nor polyfill, then a plain number is used for performance.
    var hasSymbol = typeof Symbol === 'function' && Symbol.for;

    var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
    var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
    var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
    var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
    var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
    var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
    var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace;
    var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
    var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
    var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
    var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
    var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
    var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;

    function isValidElementType(type) {
      return typeof type === 'string' || typeof type === 'function' ||
      // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
      type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE);
    }

    /**
     * Forked from fbjs/warning:
     * https://github.com/facebook/fbjs/blob/e66ba20ad5be433eb54423f2b097d829324d9de6/packages/fbjs/src/__forks__/warning.js
     *
     * Only change is we use console.warn instead of console.error,
     * and do nothing when 'console' is not supported.
     * This really simplifies the code.
     * ---
     * Similar to invariant but only logs a warning if the condition is not met.
     * This can be used to log issues in development environments in critical
     * paths. Removing the logging code for production environments will keep the
     * same logic and follow the same code paths.
     */

    var lowPriorityWarning = function () {};

    {
      var printWarning = function (format) {
        for (var _len = arguments.length, args = Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
          args[_key - 1] = arguments[_key];
        }

        var argIndex = 0;
        var message = 'Warning: ' + format.replace(/%s/g, function () {
          return args[argIndex++];
        });
        if (typeof console !== 'undefined') {
          console.warn(message);
        }
        try {
          // --- Welcome to debugging React ---
          // This error was thrown as a convenience so that you can use this stack
          // to find the callsite that caused this warning to fire.
          throw new Error(message);
        } catch (x) {}
      };

      lowPriorityWarning = function (condition, format) {
        if (format === undefined) {
          throw new Error('`lowPriorityWarning(condition, format, ...args)` requires a warning ' + 'message argument');
        }
        if (!condition) {
          for (var _len2 = arguments.length, args = Array(_len2 > 2 ? _len2 - 2 : 0), _key2 = 2; _key2 < _len2; _key2++) {
            args[_key2 - 2] = arguments[_key2];
          }

          printWarning.apply(undefined, [format].concat(args));
        }
      };
    }

    var lowPriorityWarning$1 = lowPriorityWarning;

    function typeOf(object) {
      if (typeof object === 'object' && object !== null) {
        var $$typeof = object.$$typeof;
        switch ($$typeof) {
          case REACT_ELEMENT_TYPE:
            var type = object.type;

            switch (type) {
              case REACT_ASYNC_MODE_TYPE:
              case REACT_CONCURRENT_MODE_TYPE:
              case REACT_FRAGMENT_TYPE:
              case REACT_PROFILER_TYPE:
              case REACT_STRICT_MODE_TYPE:
              case REACT_SUSPENSE_TYPE:
                return type;
              default:
                var $$typeofType = type && type.$$typeof;

                switch ($$typeofType) {
                  case REACT_CONTEXT_TYPE:
                  case REACT_FORWARD_REF_TYPE:
                  case REACT_PROVIDER_TYPE:
                    return $$typeofType;
                  default:
                    return $$typeof;
                }
            }
          case REACT_LAZY_TYPE:
          case REACT_MEMO_TYPE:
          case REACT_PORTAL_TYPE:
            return $$typeof;
        }
      }

      return undefined;
    }

    // AsyncMode is deprecated along with isAsyncMode
    var AsyncMode = REACT_ASYNC_MODE_TYPE;
    var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
    var ContextConsumer = REACT_CONTEXT_TYPE;
    var ContextProvider = REACT_PROVIDER_TYPE;
    var Element = REACT_ELEMENT_TYPE;
    var ForwardRef = REACT_FORWARD_REF_TYPE;
    var Fragment = REACT_FRAGMENT_TYPE;
    var Lazy = REACT_LAZY_TYPE;
    var Memo = REACT_MEMO_TYPE;
    var Portal = REACT_PORTAL_TYPE;
    var Profiler = REACT_PROFILER_TYPE;
    var StrictMode = REACT_STRICT_MODE_TYPE;
    var Suspense = REACT_SUSPENSE_TYPE;

    var hasWarnedAboutDeprecatedIsAsyncMode = false;

    // AsyncMode should be deprecated
    function isAsyncMode(object) {
      {
        if (!hasWarnedAboutDeprecatedIsAsyncMode) {
          hasWarnedAboutDeprecatedIsAsyncMode = true;
          lowPriorityWarning$1(false, 'The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
        }
      }
      return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
    }
    function isConcurrentMode(object) {
      return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
    }
    function isContextConsumer(object) {
      return typeOf(object) === REACT_CONTEXT_TYPE;
    }
    function isContextProvider(object) {
      return typeOf(object) === REACT_PROVIDER_TYPE;
    }
    function isElement(object) {
      return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
    }
    function isForwardRef(object) {
      return typeOf(object) === REACT_FORWARD_REF_TYPE;
    }
    function isFragment(object) {
      return typeOf(object) === REACT_FRAGMENT_TYPE;
    }
    function isLazy(object) {
      return typeOf(object) === REACT_LAZY_TYPE;
    }
    function isMemo(object) {
      return typeOf(object) === REACT_MEMO_TYPE;
    }
    function isPortal(object) {
      return typeOf(object) === REACT_PORTAL_TYPE;
    }
    function isProfiler(object) {
      return typeOf(object) === REACT_PROFILER_TYPE;
    }
    function isStrictMode(object) {
      return typeOf(object) === REACT_STRICT_MODE_TYPE;
    }
    function isSuspense(object) {
      return typeOf(object) === REACT_SUSPENSE_TYPE;
    }

    exports.typeOf = typeOf;
    exports.AsyncMode = AsyncMode;
    exports.ConcurrentMode = ConcurrentMode;
    exports.ContextConsumer = ContextConsumer;
    exports.ContextProvider = ContextProvider;
    exports.Element = Element;
    exports.ForwardRef = ForwardRef;
    exports.Fragment = Fragment;
    exports.Lazy = Lazy;
    exports.Memo = Memo;
    exports.Portal = Portal;
    exports.Profiler = Profiler;
    exports.StrictMode = StrictMode;
    exports.Suspense = Suspense;
    exports.isValidElementType = isValidElementType;
    exports.isAsyncMode = isAsyncMode;
    exports.isConcurrentMode = isConcurrentMode;
    exports.isContextConsumer = isContextConsumer;
    exports.isContextProvider = isContextProvider;
    exports.isElement = isElement;
    exports.isForwardRef = isForwardRef;
    exports.isFragment = isFragment;
    exports.isLazy = isLazy;
    exports.isMemo = isMemo;
    exports.isPortal = isPortal;
    exports.isProfiler = isProfiler;
    exports.isStrictMode = isStrictMode;
    exports.isSuspense = isSuspense;
      })();
    }
    });

    unwrapExports(reactIs_development);
    var reactIs_development_1 = reactIs_development.typeOf;
    var reactIs_development_2 = reactIs_development.AsyncMode;
    var reactIs_development_3 = reactIs_development.ConcurrentMode;
    var reactIs_development_4 = reactIs_development.ContextConsumer;
    var reactIs_development_5 = reactIs_development.ContextProvider;
    var reactIs_development_6 = reactIs_development.Element;
    var reactIs_development_7 = reactIs_development.ForwardRef;
    var reactIs_development_8 = reactIs_development.Fragment;
    var reactIs_development_9 = reactIs_development.Lazy;
    var reactIs_development_10 = reactIs_development.Memo;
    var reactIs_development_11 = reactIs_development.Portal;
    var reactIs_development_12 = reactIs_development.Profiler;
    var reactIs_development_13 = reactIs_development.StrictMode;
    var reactIs_development_14 = reactIs_development.Suspense;
    var reactIs_development_15 = reactIs_development.isValidElementType;
    var reactIs_development_16 = reactIs_development.isAsyncMode;
    var reactIs_development_17 = reactIs_development.isConcurrentMode;
    var reactIs_development_18 = reactIs_development.isContextConsumer;
    var reactIs_development_19 = reactIs_development.isContextProvider;
    var reactIs_development_20 = reactIs_development.isElement;
    var reactIs_development_21 = reactIs_development.isForwardRef;
    var reactIs_development_22 = reactIs_development.isFragment;
    var reactIs_development_23 = reactIs_development.isLazy;
    var reactIs_development_24 = reactIs_development.isMemo;
    var reactIs_development_25 = reactIs_development.isPortal;
    var reactIs_development_26 = reactIs_development.isProfiler;
    var reactIs_development_27 = reactIs_development.isStrictMode;
    var reactIs_development_28 = reactIs_development.isSuspense;

    var reactIs = createCommonjsModule(function (module) {

    {
      module.exports = reactIs_development;
    }
    });
    var reactIs_1 = reactIs.isValidElementType;

    var FORWARD_REF_STATICS = {
        '$$typeof': true,
        render: true,
        defaultProps: true,
        displayName: true,
        propTypes: true
    };

    var TYPE_STATICS = {};
    TYPE_STATICS[reactIs.ForwardRef] = FORWARD_REF_STATICS;

    // TODO: Replace with React.createContext once we can assume React 16+

    var createNamedContext = function createNamedContext(name) {
      var context = createContext$1();
      context.Provider.displayName = name + ".Provider";
      context.Consumer.displayName = name + ".Consumer";
      return context;
    };

    var context =
    /*#__PURE__*/
    createNamedContext('Router');

    /**
     * The public API for putting history on context.
     */

    var Router =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Router, _React$Component);

      Router.computeRootMatch = function computeRootMatch(pathname) {
        return {
          path: "/",
          url: "/",
          params: {},
          isExact: pathname === "/"
        };
      };

      function Router(props) {
        var _this;

        _this = _React$Component.call(this, props) || this;
        _this.state = {
          location: props.history.location
        }; // This is a bit of a hack. We have to start listening for location
        // changes here in the constructor in case there are any <Redirect>s
        // on the initial render. If there are, they will replace/push when
        // they mount and since cDM fires in children before parents, we may
        // get a new location before the <Router> is mounted.

        _this._isMounted = false;
        _this._pendingLocation = null;

        if (!props.staticContext) {
          _this.unlisten = props.history.listen(function (location) {
            if (_this._isMounted) {
              _this.setState({
                location: location
              });
            } else {
              _this._pendingLocation = location;
            }
          });
        }

        return _this;
      }

      var _proto = Router.prototype;

      _proto.componentDidMount = function componentDidMount() {
        this._isMounted = true;

        if (this._pendingLocation) {
          this.setState({
            location: this._pendingLocation
          });
        }
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        if (this.unlisten) this.unlisten();
      };

      _proto.render = function render() {
        return React__default.createElement(context.Provider, {
          children: this.props.children || null,
          value: {
            history: this.props.history,
            location: this.state.location,
            match: Router.computeRootMatch(this.state.location.pathname),
            staticContext: this.props.staticContext
          }
        });
      };

      return Router;
    }(React__default.Component);

    {
      Router.propTypes = {
        children: propTypes.node,
        history: propTypes.object.isRequired,
        staticContext: propTypes.object
      };

      Router.prototype.componentDidUpdate = function (prevProps) {
        warning$2(prevProps.history === this.props.history, "You cannot change <Router history>");
      };
    }

    /**
     * The public API for a <Router> that stores location in memory.
     */

    var MemoryRouter =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(MemoryRouter, _React$Component);

      function MemoryRouter() {
        var _this;

        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        _this = _React$Component.call.apply(_React$Component, [this].concat(args)) || this;
        _this.history = createMemoryHistory(_this.props);
        return _this;
      }

      var _proto = MemoryRouter.prototype;

      _proto.render = function render() {
        return React__default.createElement(Router, {
          history: this.history,
          children: this.props.children
        });
      };

      return MemoryRouter;
    }(React__default.Component);

    {
      MemoryRouter.propTypes = {
        initialEntries: propTypes.array,
        initialIndex: propTypes.number,
        getUserConfirmation: propTypes.func,
        keyLength: propTypes.number,
        children: propTypes.node
      };

      MemoryRouter.prototype.componentDidMount = function () {
        warning$2(!this.props.history, "<MemoryRouter> ignores the history prop. To use a custom history, " + "use `import { Router }` instead of `import { MemoryRouter as Router }`.");
      };
    }

    var Lifecycle =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Lifecycle, _React$Component);

      function Lifecycle() {
        return _React$Component.apply(this, arguments) || this;
      }

      var _proto = Lifecycle.prototype;

      _proto.componentDidMount = function componentDidMount() {
        if (this.props.onMount) this.props.onMount.call(this, this);
      };

      _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
        if (this.props.onUpdate) this.props.onUpdate.call(this, this, prevProps);
      };

      _proto.componentWillUnmount = function componentWillUnmount() {
        if (this.props.onUnmount) this.props.onUnmount.call(this, this);
      };

      _proto.render = function render() {
        return null;
      };

      return Lifecycle;
    }(React__default.Component);

    /**
     * The public API for prompting the user before navigating away from a screen.
     */

    function Prompt(_ref) {
      var message = _ref.message,
          _ref$when = _ref.when,
          when = _ref$when === void 0 ? true : _ref$when;
      return React__default.createElement(context.Consumer, null, function (context$$1) {
        !context$$1 ? invariant(false, "You should not use <Prompt> outside a <Router>") : void 0;
        if (!when || context$$1.staticContext) return null;
        var method = context$$1.history.block;
        return React__default.createElement(Lifecycle, {
          onMount: function onMount(self) {
            self.release = method(message);
          },
          onUpdate: function onUpdate(self, prevProps) {
            if (prevProps.message !== message) {
              self.release();
              self.release = method(message);
            }
          },
          onUnmount: function onUnmount(self) {
            self.release();
          },
          message: message
        });
      });
    }

    {
      var messageType = propTypes.oneOfType([propTypes.func, propTypes.string]);
      Prompt.propTypes = {
        when: propTypes.bool,
        message: messageType.isRequired
      };
    }

    var cache = {};
    var cacheLimit = 10000;
    var cacheCount = 0;

    function compilePath(path) {
      if (cache[path]) return cache[path];
      var generator = pathToRegexp_1.compile(path);

      if (cacheCount < cacheLimit) {
        cache[path] = generator;
        cacheCount++;
      }

      return generator;
    }
    /**
     * Public API for generating a URL pathname from a path and parameters.
     */


    function generatePath(path, params) {
      if (path === void 0) {
        path = "/";
      }

      if (params === void 0) {
        params = {};
      }

      return path === "/" ? path : compilePath(path)(params, {
        pretty: true
      });
    }

    /**
     * The public API for navigating programmatically with a component.
     */

    function Redirect(_ref) {
      var computedMatch = _ref.computedMatch,
          to = _ref.to,
          _ref$push = _ref.push,
          push = _ref$push === void 0 ? false : _ref$push;
      return React__default.createElement(context.Consumer, null, function (context$$1) {
        !context$$1 ? invariant(false, "You should not use <Redirect> outside a <Router>") : void 0;
        var history = context$$1.history,
            staticContext = context$$1.staticContext;
        var method = push ? history.push : history.replace;
        var location = createLocation(computedMatch ? typeof to === "string" ? generatePath(to, computedMatch.params) : _extends({}, to, {
          pathname: generatePath(to.pathname, computedMatch.params)
        }) : to); // When rendering in a static context,
        // set the new location immediately.

        if (staticContext) {
          method(location);
          return null;
        }

        return React__default.createElement(Lifecycle, {
          onMount: function onMount() {
            method(location);
          },
          onUpdate: function onUpdate(self, prevProps) {
            if (!locationsAreEqual(prevProps.to, location)) {
              method(location);
            }
          },
          to: to
        });
      });
    }

    {
      Redirect.propTypes = {
        push: propTypes.bool,
        from: propTypes.string,
        to: propTypes.oneOfType([propTypes.string, propTypes.object]).isRequired
      };
    }

    var cache$1 = {};
    var cacheLimit$1 = 10000;
    var cacheCount$1 = 0;

    function compilePath$1(path, options) {
      var cacheKey = "" + options.end + options.strict + options.sensitive;
      var pathCache = cache$1[cacheKey] || (cache$1[cacheKey] = {});
      if (pathCache[path]) return pathCache[path];
      var keys = [];
      var regexp = pathToRegexp_1(path, keys, options);
      var result = {
        regexp: regexp,
        keys: keys
      };

      if (cacheCount$1 < cacheLimit$1) {
        pathCache[path] = result;
        cacheCount$1++;
      }

      return result;
    }
    /**
     * Public API for matching a URL pathname to a path.
     */


    function matchPath(pathname, options) {
      if (options === void 0) {
        options = {};
      }

      if (typeof options === "string") options = {
        path: options
      };
      var _options = options,
          path = _options.path,
          _options$exact = _options.exact,
          exact = _options$exact === void 0 ? false : _options$exact,
          _options$strict = _options.strict,
          strict = _options$strict === void 0 ? false : _options$strict,
          _options$sensitive = _options.sensitive,
          sensitive = _options$sensitive === void 0 ? false : _options$sensitive;
      var paths = [].concat(path);
      return paths.reduce(function (matched, path) {
        if (matched) return matched;

        var _compilePath = compilePath$1(path, {
          end: exact,
          strict: strict,
          sensitive: sensitive
        }),
            regexp = _compilePath.regexp,
            keys = _compilePath.keys;

        var match = regexp.exec(pathname);
        if (!match) return null;
        var url = match[0],
            values = match.slice(1);
        var isExact = pathname === url;
        if (exact && !isExact) return null;
        return {
          path: path,
          // the path used to match
          url: path === "/" && url === "" ? "/" : url,
          // the matched portion of the URL
          isExact: isExact,
          // whether or not we matched exactly
          params: keys.reduce(function (memo, key, index) {
            memo[key.name] = values[index];
            return memo;
          }, {})
        };
      }, null);
    }

    function isEmptyChildren(children) {
      return React__default.Children.count(children) === 0;
    }
    /**
     * The public API for matching a single path and rendering.
     */


    var Route =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Route, _React$Component);

      function Route() {
        return _React$Component.apply(this, arguments) || this;
      }

      var _proto = Route.prototype;

      _proto.render = function render() {
        var _this = this;

        return React__default.createElement(context.Consumer, null, function (context$$1) {
          !context$$1 ? invariant(false, "You should not use <Route> outside a <Router>") : void 0;
          var location = _this.props.location || context$$1.location;
          var match = _this.props.computedMatch ? _this.props.computedMatch // <Switch> already computed the match for us
          : _this.props.path ? matchPath(location.pathname, _this.props) : context$$1.match;

          var props = _extends({}, context$$1, {
            location: location,
            match: match
          });

          var _this$props = _this.props,
              children = _this$props.children,
              component = _this$props.component,
              render = _this$props.render; // Preact uses an empty array as children by
          // default, so use null if that's the case.

          if (Array.isArray(children) && children.length === 0) {
            children = null;
          }

          if (typeof children === "function") {
            children = children(props);

            if (children === undefined) {
              {
                var path = _this.props.path;
                warning$2(false, "You returned `undefined` from the `children` function of " + ("<Route" + (path ? " path=\"" + path + "\"" : "") + ">, but you ") + "should have returned a React element or `null`");
              }

              children = null;
            }
          }

          return React__default.createElement(context.Provider, {
            value: props
          }, children && !isEmptyChildren(children) ? children : props.match ? component ? React__default.createElement(component, props) : render ? render(props) : null : null);
        });
      };

      return Route;
    }(React__default.Component);

    {
      Route.propTypes = {
        children: propTypes.oneOfType([propTypes.func, propTypes.node]),
        component: function component(props, propName) {
          if (props[propName] && !reactIs_1(props[propName])) {
            return new Error("Invalid prop 'component' supplied to 'Route': the prop is not a valid React component");
          }
        },
        exact: propTypes.bool,
        location: propTypes.object,
        path: propTypes.oneOfType([propTypes.string, propTypes.arrayOf(propTypes.string)]),
        render: propTypes.func,
        sensitive: propTypes.bool,
        strict: propTypes.bool
      };

      Route.prototype.componentDidMount = function () {
        warning$2(!(this.props.children && !isEmptyChildren(this.props.children) && this.props.component), "You should not use <Route component> and <Route children> in the same route; <Route component> will be ignored");
        warning$2(!(this.props.children && !isEmptyChildren(this.props.children) && this.props.render), "You should not use <Route render> and <Route children> in the same route; <Route render> will be ignored");
        warning$2(!(this.props.component && this.props.render), "You should not use <Route component> and <Route render> in the same route; <Route render> will be ignored");
      };

      Route.prototype.componentDidUpdate = function (prevProps) {
        warning$2(!(this.props.location && !prevProps.location), '<Route> elements should not change from uncontrolled to controlled (or vice versa). You initially used no "location" prop and then provided one on a subsequent render.');
        warning$2(!(!this.props.location && prevProps.location), '<Route> elements should not change from controlled to uncontrolled (or vice versa). You provided a "location" prop initially but omitted it on a subsequent render.');
      };
    }

    function addLeadingSlash$1(path) {
      return path.charAt(0) === "/" ? path : "/" + path;
    }

    function addBasename(basename, location) {
      if (!basename) return location;
      return _extends({}, location, {
        pathname: addLeadingSlash$1(basename) + location.pathname
      });
    }

    function stripBasename$1(basename, location) {
      if (!basename) return location;
      var base = addLeadingSlash$1(basename);
      if (location.pathname.indexOf(base) !== 0) return location;
      return _extends({}, location, {
        pathname: location.pathname.substr(base.length)
      });
    }

    function createURL(location) {
      return typeof location === "string" ? location : createPath(location);
    }

    function staticHandler(methodName) {
      return function () {
        invariant(false, "You cannot %s with <StaticRouter>", methodName);
      };
    }

    function noop$3() {}
    /**
     * The public top-level API for a "static" <Router>, so-called because it
     * can't actually change the current location. Instead, it just records
     * location changes in a context object. Useful mainly in testing and
     * server-rendering scenarios.
     */


    var StaticRouter =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(StaticRouter, _React$Component);

      function StaticRouter() {
        var _this;

        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        _this = _React$Component.call.apply(_React$Component, [this].concat(args)) || this;

        _this.handlePush = function (location) {
          return _this.navigateTo(location, "PUSH");
        };

        _this.handleReplace = function (location) {
          return _this.navigateTo(location, "REPLACE");
        };

        _this.handleListen = function () {
          return noop$3;
        };

        _this.handleBlock = function () {
          return noop$3;
        };

        return _this;
      }

      var _proto = StaticRouter.prototype;

      _proto.navigateTo = function navigateTo(location, action) {
        var _this$props = this.props,
            _this$props$basename = _this$props.basename,
            basename = _this$props$basename === void 0 ? "" : _this$props$basename,
            context = _this$props.context;
        context.action = action;
        context.location = addBasename(basename, createLocation(location));
        context.url = createURL(context.location);
      };

      _proto.render = function render() {
        var _this$props2 = this.props,
            _this$props2$basename = _this$props2.basename,
            basename = _this$props2$basename === void 0 ? "" : _this$props2$basename,
            _this$props2$context = _this$props2.context,
            context = _this$props2$context === void 0 ? {} : _this$props2$context,
            _this$props2$location = _this$props2.location,
            location = _this$props2$location === void 0 ? "/" : _this$props2$location,
            rest = _objectWithoutPropertiesLoose(_this$props2, ["basename", "context", "location"]);

        var history = {
          createHref: function createHref(path) {
            return addLeadingSlash$1(basename + createURL(path));
          },
          action: "POP",
          location: stripBasename$1(basename, createLocation(location)),
          push: this.handlePush,
          replace: this.handleReplace,
          go: staticHandler("go"),
          goBack: staticHandler("goBack"),
          goForward: staticHandler("goForward"),
          listen: this.handleListen,
          block: this.handleBlock
        };
        return React__default.createElement(Router, _extends({}, rest, {
          history: history,
          staticContext: context
        }));
      };

      return StaticRouter;
    }(React__default.Component);

    {
      StaticRouter.propTypes = {
        basename: propTypes.string,
        context: propTypes.object,
        location: propTypes.oneOfType([propTypes.string, propTypes.object])
      };

      StaticRouter.prototype.componentDidMount = function () {
        warning$2(!this.props.history, "<StaticRouter> ignores the history prop. To use a custom history, " + "use `import { Router }` instead of `import { StaticRouter as Router }`.");
      };
    }

    /**
     * The public API for rendering the first <Route> that matches.
     */

    var Switch =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Switch, _React$Component);

      function Switch() {
        return _React$Component.apply(this, arguments) || this;
      }

      var _proto = Switch.prototype;

      _proto.render = function render() {
        var _this = this;

        return React__default.createElement(context.Consumer, null, function (context$$1) {
          !context$$1 ? invariant(false, "You should not use <Switch> outside a <Router>") : void 0;
          var location = _this.props.location || context$$1.location;
          var element, match; // We use React.Children.forEach instead of React.Children.toArray().find()
          // here because toArray adds keys to all child elements and we do not want
          // to trigger an unmount/remount for two <Route>s that render the same
          // component at different URLs.

          React__default.Children.forEach(_this.props.children, function (child) {
            if (match == null && React__default.isValidElement(child)) {
              element = child;
              var path = child.props.path || child.props.from;
              match = path ? matchPath(location.pathname, _extends({}, child.props, {
                path: path
              })) : context$$1.match;
            }
          });
          return match ? React__default.cloneElement(element, {
            location: location,
            computedMatch: match
          }) : null;
        });
      };

      return Switch;
    }(React__default.Component);

    {
      Switch.propTypes = {
        children: propTypes.node,
        location: propTypes.object
      };

      Switch.prototype.componentDidUpdate = function (prevProps) {
        warning$2(!(this.props.location && !prevProps.location), '<Switch> elements should not change from uncontrolled to controlled (or vice versa). You initially used no "location" prop and then provided one on a subsequent render.');
        warning$2(!(!this.props.location && prevProps.location), '<Switch> elements should not change from controlled to uncontrolled (or vice versa). You provided a "location" prop initially but omitted it on a subsequent render.');
      };
    }

    {
      if (typeof window !== "undefined") {
        var global$1 = window;
        var key$1 = "__react_router_build__";
        var buildNames = {
          cjs: "CommonJS",
          esm: "ES modules",
          umd: "UMD"
        };

        if (global$1[key$1] && global$1[key$1] !== "esm") {
          var initialBuildName = buildNames[global$1[key$1]];
          var secondaryBuildName = buildNames["esm"]; // TODO: Add link to article that explains in detail how to avoid
          // loading 2 different builds.

          throw new Error("You are loading the " + secondaryBuildName + " build of React Router " + ("on a page that is already running the " + initialBuildName + " ") + "build, so things won't work right.");
        }

        global$1[key$1] = "esm";
      }
    }

    /**
     * The public API for a <Router> that uses HTML5 history.
     */

    var BrowserRouter =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(BrowserRouter, _React$Component);

      function BrowserRouter() {
        var _this;

        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        _this = _React$Component.call.apply(_React$Component, [this].concat(args)) || this;
        _this.history = createBrowserHistory(_this.props);
        return _this;
      }

      var _proto = BrowserRouter.prototype;

      _proto.render = function render() {
        return React__default.createElement(Router, {
          history: this.history,
          children: this.props.children
        });
      };

      return BrowserRouter;
    }(React__default.Component);

    {
      BrowserRouter.propTypes = {
        basename: propTypes.string,
        children: propTypes.node,
        forceRefresh: propTypes.bool,
        getUserConfirmation: propTypes.func,
        keyLength: propTypes.number
      };

      BrowserRouter.prototype.componentDidMount = function () {
        warning$2(!this.props.history, "<BrowserRouter> ignores the history prop. To use a custom history, " + "use `import { Router }` instead of `import { BrowserRouter as Router }`.");
      };
    }

    /**
     * The public API for a <Router> that uses window.location.hash.
     */

    var HashRouter =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(HashRouter, _React$Component);

      function HashRouter() {
        var _this;

        for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
          args[_key] = arguments[_key];
        }

        _this = _React$Component.call.apply(_React$Component, [this].concat(args)) || this;
        _this.history = createHashHistory(_this.props);
        return _this;
      }

      var _proto = HashRouter.prototype;

      _proto.render = function render() {
        return React__default.createElement(Router, {
          history: this.history,
          children: this.props.children
        });
      };

      return HashRouter;
    }(React__default.Component);

    {
      HashRouter.propTypes = {
        basename: propTypes.string,
        children: propTypes.node,
        getUserConfirmation: propTypes.func,
        hashType: propTypes.oneOf(["hashbang", "noslash", "slash"])
      };

      HashRouter.prototype.componentDidMount = function () {
        warning$2(!this.props.history, "<HashRouter> ignores the history prop. To use a custom history, " + "use `import { Router }` instead of `import { HashRouter as Router }`.");
      };
    }

    function isModifiedEvent(event) {
      return !!(event.metaKey || event.altKey || event.ctrlKey || event.shiftKey);
    }
    /**
     * The public API for rendering a history-aware <a>.
     */


    var Link =
    /*#__PURE__*/
    function (_React$Component) {
      _inheritsLoose(Link, _React$Component);

      function Link() {
        return _React$Component.apply(this, arguments) || this;
      }

      var _proto = Link.prototype;

      _proto.handleClick = function handleClick(event, history) {
        if (this.props.onClick) this.props.onClick(event);

        if (!event.defaultPrevented && // onClick prevented default
        event.button === 0 && ( // ignore everything but left clicks
        !this.props.target || this.props.target === "_self") && // let browser handle "target=_blank" etc.
        !isModifiedEvent(event) // ignore clicks with modifier keys
        ) {
            event.preventDefault();
            var method = this.props.replace ? history.replace : history.push;
            method(this.props.to);
          }
      };

      _proto.render = function render() {
        var _this = this;

        var _this$props = this.props,
            innerRef = _this$props.innerRef,
            replace = _this$props.replace,
            to = _this$props.to,
            rest = _objectWithoutPropertiesLoose(_this$props, ["innerRef", "replace", "to"]); // eslint-disable-line no-unused-vars


        return React__default.createElement(context.Consumer, null, function (context) {
          !context ? invariant(false, "You should not use <Link> outside a <Router>") : void 0;
          var location = typeof to === "string" ? createLocation(to, null, null, context.location) : to;
          var href = location ? context.history.createHref(location) : "";
          return React__default.createElement("a", _extends({}, rest, {
            onClick: function onClick(event) {
              return _this.handleClick(event, context.history);
            },
            href: href,
            ref: innerRef
          }));
        });
      };

      return Link;
    }(React__default.Component);

    {
      var toType = propTypes.oneOfType([propTypes.string, propTypes.object]);
      var innerRefType = propTypes.oneOfType([propTypes.string, propTypes.func, propTypes.shape({
        current: propTypes.any
      })]);
      Link.propTypes = {
        innerRef: innerRefType,
        onClick: propTypes.func,
        replace: propTypes.bool,
        target: propTypes.string,
        to: toType.isRequired
      };
    }

    function joinClassnames() {
      for (var _len = arguments.length, classnames = new Array(_len), _key = 0; _key < _len; _key++) {
        classnames[_key] = arguments[_key];
      }

      return classnames.filter(function (i) {
        return i;
      }).join(" ");
    }
    /**
     * A <Link> wrapper that knows if it's "active" or not.
     */


    function NavLink$1(_ref) {
      var _ref$ariaCurrent = _ref["aria-current"],
          ariaCurrent = _ref$ariaCurrent === void 0 ? "page" : _ref$ariaCurrent,
          _ref$activeClassName = _ref.activeClassName,
          activeClassName = _ref$activeClassName === void 0 ? "active" : _ref$activeClassName,
          activeStyle = _ref.activeStyle,
          classNameProp = _ref.className,
          exact = _ref.exact,
          isActiveProp = _ref.isActive,
          location = _ref.location,
          strict = _ref.strict,
          styleProp = _ref.style,
          to = _ref.to,
          rest = _objectWithoutPropertiesLoose(_ref, ["aria-current", "activeClassName", "activeStyle", "className", "exact", "isActive", "location", "strict", "style", "to"]);

      var path = typeof to === "object" ? to.pathname : to; // Regex taken from: https://github.com/pillarjs/path-to-regexp/blob/master/index.js#L202

      var escapedPath = path && path.replace(/([.+*?=^!:${}()[\]|/\\])/g, "\\$1");
      return React__default.createElement(Route, {
        path: escapedPath,
        exact: exact,
        strict: strict,
        location: location,
        children: function children(_ref2) {
          var location = _ref2.location,
              match = _ref2.match;
          var isActive = !!(isActiveProp ? isActiveProp(match, location) : match);
          var className = isActive ? joinClassnames(classNameProp, activeClassName) : classNameProp;
          var style = isActive ? _extends({}, styleProp, activeStyle) : styleProp;
          return React__default.createElement(Link, _extends({
            "aria-current": isActive && ariaCurrent || null,
            className: className,
            style: style,
            to: to
          }, rest));
        }
      });
    }

    {
      var ariaCurrentType = propTypes.oneOf(["page", "step", "location", "date", "time", "true"]);
      NavLink$1.propTypes = _extends({}, Link.propTypes, {
        "aria-current": ariaCurrentType,
        activeClassName: propTypes.string,
        activeStyle: propTypes.object,
        className: propTypes.string,
        exact: Route.propTypes.exact,
        isActive: propTypes.func,
        location: propTypes.object,
        strict: Route.propTypes.strict,
        style: propTypes.object
      });
    }

    var utils = createCommonjsModule(function (module, exports) {



    exports.__esModule = true;
    exports.getScrollbarWidth = getScrollbarWidth;
    exports.setScrollbarWidth = setScrollbarWidth;
    exports.isBodyOverflowing = isBodyOverflowing;
    exports.getOriginalBodyPadding = getOriginalBodyPadding;
    exports.conditionallyUpdateScrollbar = conditionallyUpdateScrollbar;
    exports.setGlobalCssModule = setGlobalCssModule;
    exports.mapToCssModules = mapToCssModules;
    exports.omit = omit;
    exports.pick = pick;
    exports.warnOnce = warnOnce;
    exports.deprecated = deprecated;
    exports.DOMElement = DOMElement;
    exports.isReactRefObj = isReactRefObj;
    exports.findDOMElements = findDOMElements;
    exports.isArrayOrNodeList = isArrayOrNodeList;
    exports.getTarget = getTarget;
    exports.addMultipleEventListeners = addMultipleEventListeners;
    exports.focusableElements = exports.defaultToggleEvents = exports.canUseDOM = exports.PopperPlacements = exports.keyCodes = exports.TransitionStatuses = exports.TransitionPropTypeKeys = exports.TransitionTimeouts = exports.tagPropType = exports.targetPropType = void 0;

    var _lodash = interopRequireDefault(lodash_isfunction);

    var _propTypes = interopRequireDefault(propTypes);

    // https://github.com/twbs/bootstrap/blob/v4.0.0-alpha.4/js/src/modal.js#L436-L443
    function getScrollbarWidth() {
      var scrollDiv = document.createElement('div'); // .modal-scrollbar-measure styles // https://github.com/twbs/bootstrap/blob/v4.0.0-alpha.4/scss/_modal.scss#L106-L113

      scrollDiv.style.position = 'absolute';
      scrollDiv.style.top = '-9999px';
      scrollDiv.style.width = '50px';
      scrollDiv.style.height = '50px';
      scrollDiv.style.overflow = 'scroll';
      document.body.appendChild(scrollDiv);
      var scrollbarWidth = scrollDiv.offsetWidth - scrollDiv.clientWidth;
      document.body.removeChild(scrollDiv);
      return scrollbarWidth;
    }

    function setScrollbarWidth(padding) {
      document.body.style.paddingRight = padding > 0 ? padding + "px" : null;
    }

    function isBodyOverflowing() {
      return document.body.clientWidth < window.innerWidth;
    }

    function getOriginalBodyPadding() {
      var style = window.getComputedStyle(document.body, null);
      return parseInt(style && style.getPropertyValue('padding-right') || 0, 10);
    }

    function conditionallyUpdateScrollbar() {
      var scrollbarWidth = getScrollbarWidth(); // https://github.com/twbs/bootstrap/blob/v4.0.0-alpha.6/js/src/modal.js#L433

      var fixedContent = document.querySelectorAll('.fixed-top, .fixed-bottom, .is-fixed, .sticky-top')[0];
      var bodyPadding = fixedContent ? parseInt(fixedContent.style.paddingRight || 0, 10) : 0;

      if (isBodyOverflowing()) {
        setScrollbarWidth(bodyPadding + scrollbarWidth);
      }
    }

    var globalCssModule;

    function setGlobalCssModule(cssModule) {
      globalCssModule = cssModule;
    }

    function mapToCssModules(className, cssModule) {
      if (className === void 0) {
        className = '';
      }

      if (cssModule === void 0) {
        cssModule = globalCssModule;
      }

      if (!cssModule) return className;
      return className.split(' ').map(function (c) {
        return cssModule[c] || c;
      }).join(' ');
    }
    /**
     * Returns a new object with the key/value pairs from `obj` that are not in the array `omitKeys`.
     */


    function omit(obj, omitKeys) {
      var result = {};
      Object.keys(obj).forEach(function (key) {
        if (omitKeys.indexOf(key) === -1) {
          result[key] = obj[key];
        }
      });
      return result;
    }
    /**
     * Returns a filtered copy of an object with only the specified keys.
     */


    function pick(obj, keys) {
      var pickKeys = Array.isArray(keys) ? keys : [keys];
      var length = pickKeys.length;
      var key;
      var result = {};

      while (length > 0) {
        length -= 1;
        key = pickKeys[length];
        result[key] = obj[key];
      }

      return result;
    }

    var warned = {};

    function warnOnce(message) {
      if (!warned[message]) {
        /* istanbul ignore else */
        if (typeof console !== 'undefined') {
          console.error(message); // eslint-disable-line no-console
        }

        warned[message] = true;
      }
    }

    function deprecated(propType, explanation) {
      return function validate(props, propName, componentName) {
        if (props[propName] !== null && typeof props[propName] !== 'undefined') {
          warnOnce("\"" + propName + "\" property of \"" + componentName + "\" has been deprecated.\n" + explanation);
        }

        for (var _len = arguments.length, rest = new Array(_len > 3 ? _len - 3 : 0), _key = 3; _key < _len; _key++) {
          rest[_key - 3] = arguments[_key];
        }

        return propType.apply(void 0, [props, propName, componentName].concat(rest));
      };
    } // Shim Element if needed (e.g. in Node environment)


    var Element = typeof window === 'object' && window.Element || function () {};

    function DOMElement(props, propName, componentName) {
      if (!(props[propName] instanceof Element)) {
        return new Error('Invalid prop `' + propName + '` supplied to `' + componentName + '`. Expected prop to be an instance of Element. Validation failed.');
      }
    }

    var targetPropType = _propTypes.default.oneOfType([_propTypes.default.string, _propTypes.default.func, DOMElement, _propTypes.default.shape({
      current: _propTypes.default.any
    })]);

    exports.targetPropType = targetPropType;

    var tagPropType = _propTypes.default.oneOfType([_propTypes.default.func, _propTypes.default.string, _propTypes.default.shape({
      $$typeof: _propTypes.default.symbol,
      render: _propTypes.default.func
    }), _propTypes.default.arrayOf(_propTypes.default.oneOfType([_propTypes.default.func, _propTypes.default.string, _propTypes.default.shape({
      $$typeof: _propTypes.default.symbol,
      render: _propTypes.default.func
    })]))]);
    /* eslint key-spacing: ["error", { afterColon: true, align: "value" }] */
    // These are all setup to match what is in the bootstrap _variables.scss
    // https://github.com/twbs/bootstrap/blob/v4-dev/scss/_variables.scss


    exports.tagPropType = tagPropType;
    var TransitionTimeouts = {
      Fade: 150,
      // $transition-fade
      Collapse: 350,
      // $transition-collapse
      Modal: 300,
      // $modal-transition
      Carousel: 600 // $carousel-transition

    }; // Duplicated Transition.propType keys to ensure that Reactstrap builds
    // for distribution properly exclude these keys for nested child HTML attributes
    // since `react-transition-group` removes propTypes in production builds.

    exports.TransitionTimeouts = TransitionTimeouts;
    var TransitionPropTypeKeys = ['in', 'mountOnEnter', 'unmountOnExit', 'appear', 'enter', 'exit', 'timeout', 'onEnter', 'onEntering', 'onEntered', 'onExit', 'onExiting', 'onExited'];
    exports.TransitionPropTypeKeys = TransitionPropTypeKeys;
    var TransitionStatuses = {
      ENTERING: 'entering',
      ENTERED: 'entered',
      EXITING: 'exiting',
      EXITED: 'exited'
    };
    exports.TransitionStatuses = TransitionStatuses;
    var keyCodes = {
      esc: 27,
      space: 32,
      enter: 13,
      tab: 9,
      up: 38,
      down: 40,
      home: 36,
      end: 35,
      n: 78,
      p: 80
    };
    exports.keyCodes = keyCodes;
    var PopperPlacements = ['auto-start', 'auto', 'auto-end', 'top-start', 'top', 'top-end', 'right-start', 'right', 'right-end', 'bottom-end', 'bottom', 'bottom-start', 'left-end', 'left', 'left-start'];
    exports.PopperPlacements = PopperPlacements;
    var canUseDOM = !!(typeof window !== 'undefined' && window.document && window.document.createElement);
    exports.canUseDOM = canUseDOM;

    function isReactRefObj(target) {
      if (target && typeof target === 'object') {
        return 'current' in target;
      }

      return false;
    }

    function findDOMElements(target) {
      if (isReactRefObj(target)) {
        return target.current;
      }

      if ((0, _lodash.default)(target)) {
        return target();
      }

      if (typeof target === 'string' && canUseDOM) {
        var selection = document.querySelectorAll(target);

        if (!selection.length) {
          selection = document.querySelectorAll("#" + target);
        }

        if (!selection.length) {
          throw new Error("The target '" + target + "' could not be identified in the dom, tip: check spelling");
        }

        return selection;
      }

      return target;
    }

    function isArrayOrNodeList(els) {
      if (els === null) {
        return false;
      }

      return Array.isArray(els) || canUseDOM && typeof els.length === 'number';
    }

    function getTarget(target) {
      var els = findDOMElements(target);

      if (isArrayOrNodeList(els)) {
        return els[0];
      }

      return els;
    }

    var defaultToggleEvents = ['touchstart', 'click'];
    exports.defaultToggleEvents = defaultToggleEvents;

    function addMultipleEventListeners(_els, handler, _events, useCapture) {
      var els = _els;

      if (!isArrayOrNodeList(els)) {
        els = [els];
      }

      var events = _events;

      if (typeof events === 'string') {
        events = events.split(/\s+/);
      }

      if (!isArrayOrNodeList(els) || typeof handler !== 'function' || !Array.isArray(events)) {
        throw new Error("\n      The first argument of this function must be DOM node or an array on DOM nodes or NodeList.\n      The second must be a function.\n      The third is a string or an array of strings that represents DOM events\n    ");
      }

      Array.prototype.forEach.call(events, function (event) {
        Array.prototype.forEach.call(els, function (el) {
          el.addEventListener(event, handler, useCapture);
        });
      });
      return function removeEvents() {
        Array.prototype.forEach.call(events, function (event) {
          Array.prototype.forEach.call(els, function (el) {
            el.removeEventListener(event, handler, useCapture);
          });
        });
      };
    }

    var focusableElements = ['a[href]', 'area[href]', 'input:not([disabled]):not([type=hidden])', 'select:not([disabled])', 'textarea:not([disabled])', 'button:not([disabled])', 'object', 'embed', '[tabindex]:not(.modal)', 'audio[controls]', 'video[controls]', '[contenteditable]:not([contenteditable="false"])'];
    exports.focusableElements = focusableElements;
    });

    unwrapExports(utils);
    var utils_1 = utils.getScrollbarWidth;
    var utils_2 = utils.setScrollbarWidth;
    var utils_3 = utils.isBodyOverflowing;
    var utils_4 = utils.getOriginalBodyPadding;
    var utils_5 = utils.conditionallyUpdateScrollbar;
    var utils_6 = utils.setGlobalCssModule;
    var utils_7 = utils.mapToCssModules;
    var utils_8 = utils.omit;
    var utils_9 = utils.pick;
    var utils_10 = utils.warnOnce;
    var utils_11 = utils.deprecated;
    var utils_12 = utils.DOMElement;
    var utils_13 = utils.isReactRefObj;
    var utils_14 = utils.findDOMElements;
    var utils_15 = utils.isArrayOrNodeList;
    var utils_16 = utils.getTarget;
    var utils_17 = utils.addMultipleEventListeners;
    var utils_18 = utils.focusableElements;
    var utils_19 = utils.defaultToggleEvents;
    var utils_20 = utils.canUseDOM;
    var utils_21 = utils.PopperPlacements;
    var utils_22 = utils.keyCodes;
    var utils_23 = utils.TransitionStatuses;
    var utils_24 = utils.TransitionPropTypeKeys;
    var utils_25 = utils.TransitionTimeouts;
    var utils_26 = utils.tagPropType;
    var utils_27 = utils.targetPropType;

    var Container_1 = createCommonjsModule(function (module, exports) {



    exports.__esModule = true;
    exports.default = void 0;

    var _extends2 = interopRequireDefault(_extends_1);

    var _objectWithoutPropertiesLoose2 = interopRequireDefault(objectWithoutPropertiesLoose);

    var _react = interopRequireDefault(React__default);

    var _propTypes = interopRequireDefault(propTypes);

    var _classnames = interopRequireDefault(classnames);



    var propTypes$1 = {
      tag: utils.tagPropType,
      fluid: _propTypes.default.bool,
      className: _propTypes.default.string,
      cssModule: _propTypes.default.object
    };
    var defaultProps = {
      tag: 'div'
    };

    var Container = function Container(props) {
      var className = props.className,
          cssModule = props.cssModule,
          fluid = props.fluid,
          Tag = props.tag,
          attributes = (0, _objectWithoutPropertiesLoose2.default)(props, ["className", "cssModule", "fluid", "tag"]);
      var classes = (0, utils.mapToCssModules)((0, _classnames.default)(className, fluid ? 'container-fluid' : 'container'), cssModule);
      return _react.default.createElement(Tag, (0, _extends2.default)({}, attributes, {
        className: classes
      }));
    };

    Container.propTypes = propTypes$1;
    Container.defaultProps = defaultProps;
    var _default = Container;
    exports.default = _default;
    });

    var Container = unwrapExports(Container_1);

    var graphsMarkdown = "# Purpose of Dijkstra's Algorithm\n\nGiven\n\n1. a directed graph §G = (V, A)§,\n2. an arc weight §l(a)§ for each arc §a in A§,\n3. a root node §s in V§,\n\nfind the shortest path from the root node to any other node.\n\n# Dijkstra's Algorithm: Implementation\n\nGiven directed graph §(V, A)§.\n\n## Auxiliary data:\n\n1. Temporary distance value for each node. §forall v in V: delta(v) in RR§\n2. Bounded priority queue §Q§ of size §|V| - 1§, containing graph nodes and\n   their distance value as\n\n## Algorithm:\n\n1. Set distance of start node §s§ to 0: §delta(s) := 0§.\n2. Set distance of all other nodes to §infty§: §forall v in V setminus {s}:\n   delta(v) := infty§\n3. Insert all nodes into priority queue §Q§.\n4. While the queue contains a node with a key/distance value less than infinite:\n    5. Extract the minimum node §v§ from the queue.\n    6. For each node §w§ which can be reached from §v§, update that node's\n       distance if is reduced by taking that path. For each outgoing arc §a =\n       (v, w) \\in A§ such that §w \\in Q§, set §delta(w) := min {delta(w),\n       delta(v) + l(a)}§\n\n# Dijkstra's Algorithm: Prerequisite\n\nThe weight of all edges must be greater or equal to zero. Given directed graph\n§(V, A)§, §\\forall a \\in A: l(a) \\ge 0§, where §l(a)§ is the length of edge §a§.\n\n# Dijkstra's Algorithm: Complexity\n\n§n = |V|§ (number of nodes)\n\n§m = |A|§ (number of arcs)\n\n§T(n)§: Worst case complexity for extraction/insertion of nodes in §Q§.\n\nWorst case complexity: §O(T(n) \\* (n + m))§\n\n## Proof\n\nEach node is extracted and inserted in Q at most once, which gives §O(T(n) \\*\nn)§.\n\nAlso, each arc §(v, w) \\in A§ is touched at most once, when §v§ is extracted\nfrom §Q§, which gives §O(T(n) \\* m)§ for all decrease-key operations.\n\n# Dijkstra's Algorithm: Heuristics\n\n1. Do not insert nodes with distance §infty§ into the queue.\n2. Early termination variant: stop when the target node has been extracted from\n   the queue.\n3. Bidirectional search: In the single-source, single-target case: Interleave\n   two searches: one from §s§ on §G§ and one from §t§ on the inverse of §G§.\n   When one node has been extracted by both searches,\n4. When performing multiple searches on same large graph:\n\n    Use heuristics 1. and 2.\n\n    Instead of initializing the distances on every search, use a version\n    counter. If the version counter does not match the current search, assume\n    §delta(v) = infty§.\n\n# Bounded Priority Queue: Methods\n\n1. insert\n2. extract minimum\n3. find minimum\n4. decrease key\n5. number\n\n# Path: Simple\n\nA path is simple if it does not meet any node more than once.\n\n# Path: Ordinary\n\nAn ordinary path in an undirected graph is a finite ordered sequence §({v_1,\nv_2}, {v_2, v_3}, ..., {v\\_(k-2), v\\_(k-2)}, {v\\_(k-2), v\\_(k-2)})§.\n\nAn ordinary path in a directed graph is a finite ordered sequence §((v_1, v_2),\n(v_2, v_3), ..., (v\\_(k-2), v\\_(k-2)), (v\\_(k-2), v\\_(k-2)))§.\n\n# Path: Generalized\n\nAlso known as a weak path.\n\nA generalized path in a directed graph is a finite sequence §((v_1, v_2), (v_2,\nv_3), ..., (v\\_(k-2), v\\_(k-2)), (v\\_(k-2), v\\_(k-2)))§, such that turning some\n(§>= 0§) of the arcs yields an ordinary path.\n\n# Graph: Reachability\n\nA node §t in V§ is _reachable_ from §s in V§ if there is a path from §s§ to §t§\nin the graph.\n\n# Path: Internal Nodes\n\nThe internal nodes of a path are all the nodes of that path except the start and\nend nodes. If the start or end nodes appear more than once on the path, they are\nalso internal nodes.\n\n# Path: Disjointedness\n\nTwo paths are **edge-disjoint**, if they have no edge in common.\n\nTwo paths are **arc-disjoint**, if they have no arc in common.\n\nTwo paths are **(internally) node-disjoint** if they have no node in common that\nis internal on either path.\n\n# Inclusion-Minimal/Maximal\n\nLet §ccS§ (read calligraphic S) be a set of (multi)sets.\n\n1. A set §S in ccS§ is **inclusion-minimal** if no other set (in §ccS§) is a\n   subset of it. (If §not EE S' in ccS setminus S: S' sub S§)\n\n2. A set §S in ccS§ is **inclusion-maximal** if no other set (in §ccS§) is a\n   proper superset of it / if it is not a proper subset of any other set (in\n   §ccS§). (If §not EE S' in ccS setminus S: S' sup S§)\n\n<!-- Let $\\mathcal{S}$ (read calligraphic S) be a set of (multi)sets.\n\n1. A set $S\\in\\mathcal{S}$ is **inclusion-minimal** (resp.\n   **inclusion-maximal**) in $\\mathcal{S}$ if $S'\\subsetneq S$ (resp.\n   $S'\\supsetneq S$) for no $S'\\in\\mathcal{S}\\setminus\\{S\\}$.\n2. A set $S\\in\\mathcal{S}$ is **cardinality-minimal** (resp.\n   **cardinality-maximal**) in $\\mathcal{S}$ if $|S'|<|S|$ (resp. $|S'|>|S|$)\n   for no $S'\\in\\mathcal{S}\\setminus\\{S\\}$. -->\n\n# Cardinality-Minimal/Maximal\n\nLet §ccS§ (read calligraphic S) be a set of (multi)sets.\n\n1. A set §S in ccS§ is **cardinality-minimal** if it has the smallest number of\n   elements of any set (in §ccS§). (§AA S' in ccS: |S| <= |S'|§)\n2. A set §S in ccS§ is **cardinality-maximal** if it has the largest number of\n   elements of any set (in §ccS§). (§AA S' in ccS: |S| >= |S'|§)\n\n# Connectedness\n\nAn **undirected graph** is said to be **connected** if every pair of nodes is\nconnected by a path.\n\nIt is §k§-connected if every pair of nodes is connected by at least §k§\n**internally node-disjoint paths**. _Connected_ means _1-connected_.\n_2-connected_ is synonmous with _biconnected_.\n\n# Weak Connectedness\n\nA **directed graph** is said to be _weakly connected_ if every pair of nodes is\nconnected by a **generalized/weak path**.\n\n# Strong Connectedness\n\nA **directed graph** is said to be _strongly connected_ if every **ordered\npair** of nodes is connected by a an **ordinary path**.\n\n# Articulation Node\n\nAn arcticulation node in a **connected undirected graph** is a node such that\nthe graph would become disconnected if it and its incident arcs were removed.\n\n# Bridge\n\nA bridge in a **connected undirected graph** is an edge such that the graph\nwould become disconnected if it were removed.\n\n# Subgraph\n\nLet §G_1 = (V_1, E_1)§ and §G_2 = (V_2, E_2)§ be two simple undirected graphs.\n\n§G_1§ is a subgraph of §G_2§ if there is §V' sube V_2§ and bijection §varphi:V_1\n-> V'§ such that §{v, w} in E_1§ implies §{varphi(v), varphi(w)} in E_2§.\n\nIf all the edges of §G_2§ defined on §V'§ are also in §G_1§, we say §G_2§ is the\ngraph **induced** by §V'§.\n\n# Spanning subgraph\n\nA spanning subgraph of an undirected or directed graph §G§ is a subgraph which\ncontains all nodes of §G§.\n\n# Graph: Simple\n\nA directed or undirected graph is simple, if:\n\n1. No node is paired with itself in §A§/§E§.\n2. The multiset §A§/§E§ is a sete. I.e., no edge is \"double\".\n\n# Arc: Lexicographically Smaller\n\nAssuming, for each node, an arbitrary but fixed ordering of outgoing arcs, an\narc §(v,w)§ preceding and arc §(v, w')§ is lexicographically smaller than §(v,\nw')§.\n\n# Path: Lexicographically Smaller\n\nLet §p§ and §p'§ be two paths that start from the same node §v in V§. Let §w§ be\nthe last common node such that the subpaths of §p§ and §p'§ are identical. If\nthe next arc of §p§ from §w§ onwards is lexicographically smaller than the next\narc of §p'§, §p§ is **lexicographically smaller** than §p'§.\n\nThe lexicograpically smallest path from §v in V§ to §w in V§ is **well defined**\nand **unique**.\n\n# Node: Lexicographically Smaller\n\n**With respect to a starting node §s in V§**, a node §v in V§ is\nlexicographically smaller than §w in V§ if the lexicographically smallest path\nfrom §s§ to §v§ is lexicographically smaller than the lexicographically smallest\npath from §s§ to §w§.\n\n# Node/Path: Lexicographical Order\n\nA node §v in V§ is lexicographically smaller than a path §p§ if §v§ does not\nbelong to §p§ and the lexicographically smallest path from the start of §p§ to\n§v§ precedes §p§.\n\nA node §v in V§ is lexicographically larger than a path §p§ if §v§ does not\nbelong to §p§ and the **lexicographically smallest** path from the start of §p§\nto §v§ succeeds §p§.\n\n# Forest\n\nA _forest_ is a **cycle-free undirected graph**.\n\nFor a forest §G = (V, E)§ Let §n = |V|§ be the number of nodes, §m = |E|§ the\nnumber of edges, and §k§ the number of trees in the forest. Then it is §m = n -\nk§.\n\nProof?\n\n# Tree\n\nA _tree_ is a **connected forest**.\n\n# Branching\n\nA _branching_ is a **cycle-free directed** graph such that the **indegree** of\neach node is zero or one.\n\n# Arborescence\n\nAn _arborescence_ is a **branching** such that **exactly one node has indegree\nzero**.\n\nFor branchings, this condition is equivalent to weak connectedness.\n\nAlso known as a **rooted tree**, the unique node with indegree zero is the\n**root**.\n\n# Head/Tail\n\nLet §G = (V, A)§ be a directed graph.\n\nFor an arc §a = (v, w) in A§, §v§ is the _tail_ of §a§, and §w§ is the _head_ of\n§a§.\n\n# Outgoing/Incoming\n\nLet §G = (V, A)§ be a directed graph.\n\nAn arc §(v, w) in A§ is an outgoing arc of §v§ and an incoming arc of §w§.\n\n# Outdegree/Indegree\n\nLet §G = (V, A)§ be a directed graph.\n\nThe outdegree of a node §v in V§ is the number of **outgoing arcs**, the\nindegree of §v§ is the number of **incoming arcs**.\n\n# Depth-First Search: Invariant/Variant\n\nGiven:\n\n1. A stack §S§ whose elements are nodes in §V§.\n2. Each node has a **current arc** §a_v in V§, which is either void or an\n   outgoing arc §a_v = (v, w)§ of §v§. (May be viewed as an iterator over the\n   list of all outgoing arcs.)\n\n**Invariant**: Before and after each iteration:\n\n1. §S§ forms a path §p§ from the start node §s§ to some other node, that is, the\n   order of the ndoes on §p§ is the order in which they appear in §S§ (start\n   node §s§ at the bottom of §S§).\n2. For each node not yet seen, the current arc is the first arc (or void if\n   outdegree = 0).\n3. For each node §v§ on §p§:\n    1. If there are arcs §(v, w) in A§ such that w is not yet seen, the current\n       arc equals or precedes the first such arc.\n    2. The subpath of §p§ from the start node §s§ to §v§ is the\n       lexicographically first §(s, v)§-path.\n4. The nodes on §p§ are seen but not finished. Let §p + a§ denote the\n   concatenation of §p§ with the current arc §a§ of the last node of §p§. The\n   nodes that lexicographically precede §p + a§ are seen and finished, and the\n   nodes that lexicographically succeed §p + a§ are neither seen nor finished.\n   (Nothing is said about the head of §a§).\n\n**Variant**: Either one node is seen for the first time or finished, or\n(inclusive) the current arc of one node is moved forward.\n\n# Breadth-First Search\n\n§Q = \"(\" ubrace(v_1, ..., v_l)\\_k, ubrace(v\\_(l+1), ... v_n)\\_(k+1) \")\"§\n";

    var optalgoMarkdown = "# Types of Algorithmic Problems\n\n1.  **Decision Problem**: is there a solution or not.\n2.  **Construction problem**: if there is a solution, construct one.\n3.  **Enumeration problem**: give all solutions.\n4.  **Optimization problem**: construct a solution that is optimal (or at least\n    nearly optimal) subject to a given objective.\n\nConstruction and optimization problems are by far the most important in\npractice.\n\nAlgorithms for decision problems are typically constructive. Construction\nproblems may be viewed as an optimization problem with all solutions having\nequal value.\n\nMany generic algorithms are applicable only to optimization problems.\n\n--> Focus on optimization problems.\n\n# Optimization Problem: Ingredients\n\n1.  Feasible inputs (a.k.a. instances). (Zulässigen Inputs/Eingaben/Instanzen)\n\n    A set §ccI§ of potential inputs.\n\n2.  Feasible outputs for a given instance.\n\n    For each §I in ccI§ a set §F_I§ of **feasible solutions**.\n\n3.  The objective.\n\n    Objective function §obj_I : F_I -> RR§ and a direction: **minimizing** or\n    **maximizing**.\n\n4.  Task:\n\n    1.  Determine whether §F_I != 0§ and,\n    2.  if so, find §x in F_I§ such that\n\n        §obj_I(x) = {(min,{obj_I(y)|y in F_I}),(max,{obj_I(y)|y in F_I}):}§\n\n# Optimization Problem: Matching\n\n1. Input: undirected graph §G = (V, E)§\n2. Feasible output: as set §M sube E§ such that no two edges in M have an\n   incident node in common. §<=>§ §M§ is called a **matching** of §G§.\n3. Objective: maximizing §#M§.\n\n# Feasible Solutions: Specification\n\n1. Typically the sets §F_I§ are specified by ground sets §S_I§ and side\n   constraints.\n2. **Side constraint**: a predicate on §S_I§.\n3. For an instance §I in ccI§, let §ccSccC_I§ denote the set of all side\n   constraints for §I§.\n4. **Feasible solution** §{x in S_I | forall c in ccSC_I : c(x) }§\n\n# Optimization Problem: TSP\n\n1. §ccI§: set of quadratic real-valued matrices §D§:\n\n    §D[i, j]§ = distance from point §i§ to point §j§.\n\n2. For an §(n x n)§-matrix §I in ccI§, §S_I§ may then be the set of all\n   quadratic 0/1-matrices §X§ of size §n§:\n\n    §X[i, j] = 1 <=> j§ follows §i§ immediately on the cycle corresponding to\n    §X§.\n\n3. Objective for matrix size n:\n\n    minimizing §sum\\_(i=1)^n sum\\_(j=1)^n D[i, j] \\* X[i, j]§\n\n# Feasibility\n\n<!-- prettier-ignore -->\n1. An instance §I in ccI§ of an algorithmic problem is called _feasible_, if\n   §F_I != 0§, otherwise _infeasible_.\n\n2) An instance §I in ccI§ of a minimization (resp. maximization) problem is\n   called _bounded_, if the objective function is bounded over §F_I§ from below\n   (resp. above), otherwise it is called unbounded.\n\n# Neighborhoods\n\n§I§: instance of an optimization problem.\n\n§F_I§ set of feasible solutions of §I§.\n\n§obj_I : F_I |-> RR§: objective function.\n\nGiven a feasible point §f in F_I§, it is useful to define a set §N_I(f)§ of\npoints which are **\"close\" is some sense** to the point §f§.\n\nA _neighborhood_ is a mapping §N_I : F_I |-> 2^(F_I)§.\n\n# Neighborhood: Exact\n\nAn optimization problem neighborhood is _exact_ **iff. every local minimum is also a global minimum**.";

    var robMarkdown = "# Denavit-Hartenberg Reference Frame Layout\n\n1. §z§ axis in rotation or linear axis.\n2. §x§-axis is perpendicular to both §z\\_(i-1)§ and §z_i§.\n\n§d_i§: distance to new origin along §z\\_(i-1)§ axis.\n\n§theta_i§: angle about §z\\_(i-1)§ to align §x\\_(i-1)§ with §x_i§.\n\n§a_i§ is the distance along the rotated §x_i§ axis.\n\n§alpha_i§ rotates about new §x_i§ axist a to align §z\\_(i-1)§ with §z_1§.\n\n# Bahn\n\nEine _Bahn_ ist eine kontinuierliche, räumliche Punktfolge, die z.B. vom TCP\n(tool center point) bei einer Bewegung durchlaufen wird.\n\n# Trajektorie\n\nEine _Trajektorie_ is eine Bahn mit zeitlicher Abhängigkeit. D.h. Position,\nGeschwindigkeit und Beschleunigung sind an jedem Punkt der Bahn im Raum gegeben.\n";

    var Gists = /** @class */ (function () {
        function Gists(
        // public readonly username: string,
        token) {
            this.token = token;
        }
        Gists.prototype.getGist = function (gist_id) {
            return fetch("https://api.github.com/gists/" +
                gist_id +
                "?" +
                querystring_4({ access_token: this.token })).then(function (r) { return r.json(); });
        };
        Gists.prototype.editGist = function (gist_id, files, fetchOptions) {
            if (fetchOptions === void 0) { fetchOptions = {}; }
            return fetch("https://api.github.com/gists/" +
                gist_id +
                "?" +
                querystring_4({ access_token: this.token }), __assign({}, fetchOptions, { method: "PATCH", body: JSON.stringify({ files: files }) })).then(function (r) { return r.json(); });
        };
        Gists.prototype.all = function (since) {
            return fetch("https://api.github.com/gists?" +
                querystring_4({ access_token: this.token, since: since })).then(function (r) { return r.json(); });
        };
        Gists.prototype.createGist = function (files, description, isPublic) {
            return fetch("https://api.github.com/gists?" +
                querystring_4({ access_token: this.token }), {
                method: "POST",
                body: JSON.stringify({ files: files, description: description, public: isPublic }),
            }).then(function (r) { return r.json(); });
        };
        return Gists;
    }());
    //# sourceMappingURL=gists.js.map

    var cardMarkdowns = {
        graphs: graphsMarkdown,
        optalgo: optalgoMarkdown,
        rob: robMarkdown,
    };
    function ilog(x) {
        console.log(x);
        return x;
    }
    var converter = new showdown.Converter({ literalMidWordUnderscores: true });
    var gs = new Gists(localStorage.getItem("learn_gisthub_token") || "");
    var saveGist;
    function getCardState(states, slug) {
        return (states[slug] || {
            level: 1,
            correct: [],
            incorrect: [],
        });
    }
    function initSaving() {
        return __awaiter(this, void 0, void 0, function () {
            var gists, saveGistInfo;
            return __generator(this, function (_a) {
                switch (_a.label) {
                    case 0: return [4 /*yield*/, gs.all()];
                    case 1:
                        gists = _a.sent();
                        saveGistInfo = gists.find(function (gist) { return gist.description === "learn saves"; });
                        if (!!saveGistInfo) return [3 /*break*/, 3];
                        console.log("Creating new gist");
                        return [4 /*yield*/, gs.createGist({ graphs: { content: "{}" } }, "learn saves", false)];
                    case 2:
                        saveGist = _a.sent();
                        return [3 /*break*/, 5];
                    case 3:
                        console.log("Found existing matching gist " + saveGistInfo.id);
                        return [4 /*yield*/, gs.getGist(saveGistInfo.id)];
                    case 4:
                        saveGist = _a.sent();
                        _a.label = 5;
                    case 5: return [2 /*return*/, saveGist];
                }
            });
        });
    }
    var saveGistPromise = initSaving();
    function b64EncodeUnicode(str) {
        // first we use encodeURIComponent to get percent-encoded UTF-8,
        // then we convert the percent encodings into raw bytes which
        // can be fed into btoa.
        return btoa(encodeURIComponent(str).replace(/%([0-9A-F]{2})/g, function toSolidBytes(match, p1) {
            return String.fromCharCode(parseInt(p1, 16));
        }));
    }
    function b64DecodeUnicode(str) {
        // Going backwards: from bytestream, to percent-encoding, to original string.
        return decodeURIComponent(atob(str)
            .split("")
            .map(function (c) {
            return "%" + ("00" + c.charCodeAt(0).toString(16)).slice(-2);
        })
            .join(""));
    }
    function updateCard(subject, card, newText) {
        var path = "content/" + subject + ".md";
        var contentURL = "https://api.github.com/repos/" +
            "NaridaL" +
            "/" +
            "learn" +
            "/contents/" +
            encodeURI(path) +
            "?" +
            querystring.stringify({ access_token: gs.token, ref: "master" });
        return fetch(contentURL, {
            cache: "no-store",
        })
            .then(function (r) { return r.json(); })
            .then(function (_a) {
            var sha = _a.sha, content = _a.content;
            var newCards = parseCards(b64DecodeUnicode(content)).map(function (c) {
                return c.slug == card.slug
                    ? {
                        title: card.title,
                        slug: card.slug,
                        content: newText,
                    }
                    : c;
            });
            var newContentContent = newCards
                .map(function (c) {
                return "# " +
                    c.title.trim() +
                    "\n\n" +
                    c.content.trim() +
                    "\n";
            })
                .join("\n");
            console.log("new content" + newContentContent);
            return Promise.all([
                fetch(contentURL + "?", {
                    method: "PUT",
                    body: JSON.stringify({
                        message: "update card " + card.title,
                        content: b64EncodeUnicode(newContentContent),
                        sha: sha,
                    }),
                }),
            ]);
        })
            .then(function (_a) {
            var newCards = _a[0];
            return newCards;
        });
    }
    function getCardsFromGitHub(subject) {
        return fetch("content/" + subject + ".md", {
            cache: "no-store",
        })
            .then(function (r) { return r.text(); })
            .then(ilog)
            .then(function (content) { return parseCards(content); });
    }
    var Card = /** @class */ (function () {
        function Card(title, slug, content) {
            this.title = title;
            this.slug = slug;
            this.content = content;
        }
        return Card;
    }());
    function parseCards(contentMarkdown) {
        var cardRegex = /^#(.*)$\s*(?:^slug:(.*)$)?([\s\S]*)/m;
        var cardTexts = contentMarkdown
            .split(/^(?=#[^#])/gm)
            .map(function (x) { return x.trim(); })
            .filter(function (x) { return x !== ""; });
        return cardTexts.map(function (text) {
            var _a = text.match(cardRegex), title = _a[1], slug = _a[2], content = _a[3];
            return new Card(title.trim(), slug ? slug.trim() : slugify(title), content.trim());
        });
    }
    var SubjectState = /** @class */ (function () {
        function SubjectState() {
            this.cards = [];
            this.cardStates = {};
            this.queue = [];
            this.viewFront = true;
        }
        return SubjectState;
    }());
    function reviveJSONSave(json) {
        console.log(json);
        var result = {};
        Object.keys(json).forEach(function (slug) {
            var _a = json[slug], correct = _a.correct, incorrect = _a.incorrect;
            result[slug] = {
                correct: correct.map(function (x) { return new Date(x); }),
                incorrect: incorrect.map(function (x) { return new Date(x); }),
                level: 0,
            };
            fixLevel(result[slug]);
        });
        return result;
    }
    function fixLevel(x) {
        if (x.incorrect.length == 0) {
            x.level = 1 + x.correct.length;
        }
        else {
            x.level =
                1 +
                    x.correct
                        .slice(x.correct.length - 4)
                        .filter(function (y) { return y > x.incorrect.last; }).length;
        }
    }
    function mergeSaves(a, b) {
        function merge(c, d) {
            c.correct = unionBy(c.correct, d.correct, function (x) { return x.getTime(); }).sort(function (a, b) { return a.valueOf() - b.valueOf(); });
            c.incorrect = unionBy(c.incorrect, d.incorrect, function (x) { return x.getTime(); }).sort(function (a, b) { return a.valueOf() - b.valueOf(); });
            fixLevel(c);
        }
        Object.keys(b).forEach(function (slug) {
            if (!a[slug]) {
                a[slug] = b[slug];
            }
            else {
                merge(a[slug], b[slug]);
            }
        });
    }
    function SubjectOverview() {
        return (React__default.createElement("ul", null, Object.keys(cardMarkdowns).map(function (subject) { return (React__default.createElement("li", { key: subject },
            React__default.createElement(Link, { to: "/" + subject }, subject))); })));
    }
    function App() {
        return (React__default.createElement(React__default.StrictMode, null,
            React__default.createElement(Container, { style: { height: "100%" } },
                React__default.createElement(Route, { exact: true, path: "/", component: SubjectOverview }),
                React__default.createElement(Route, { path: "/:subject", render: function (_a) {
                        var match = _a.match;
                        return (React__default.createElement(Subject, { subject: match.params.subject, key: match.params.subject }));
                    } }))));
    }
    var Subject = /** @class */ (function (_super) {
        __extends(Subject, _super);
        function Subject(props) {
            var _this = _super.call(this, props) || this;
            _this.state = new SubjectState();
            _this.CardCardRender = function (_a) {
                var match = _a.match;
                var _b = match.params, cardslug = _b.cardslug, subject = _b.subject;
                return (React__default.createElement(React__default.Fragment, null,
                    React__default.createElement(BackToOverview, { subject: subject }),
                    React__default.createElement(CardCard, { subject: subject, card: _this.state.cards.find(function (c) { return c.slug == cardslug; }) })));
            };
            _this.CardQuestionRender = function (_a) {
                var match = _a.match;
                var _b = match.params, subject = _b.subject, level = _b.level;
                var levelCards = _this.state.cards.filter(function (c) { return getCardState(_this.state.cardStates, c.slug).level === +level; });
                if (0 == levelCards.length) {
                    _this.state.info = "No more cards in level " + match.params.level;
                    return React__default.createElement(Redirect, { to: "/" + subject });
                }
                var testCard = sample(levelCards);
                return (React__default.createElement(CardQuestion, { card: testCard, subject: subject, onContinue: function () {
                        return _this.setState({
                            redirect: "/" +
                                subject +
                                "/learn/" +
                                match.params.level +
                                "/answer/" +
                                testCard.slug,
                        });
                    } }));
            };
            _this.EditCardRender = function (_a) {
                var match = _a.match;
                var _b = match.params, cardslug = _b.cardslug, subject = _b.subject;
                return (React__default.createElement(EditCard, { cards: _this.state.cards, subject: subject, cardslug: cardslug, key: subject + "#" + cardslug }));
            };
            _this.NewCardRender = function (_a) {
                var match = _a.match;
                var subject = match.params.subject;
                return (React__default.createElement(EditCard, { cards: _this.state.cards, subject: subject, key: subject + "#new" }));
            };
            _this.answer = function (correct, card, match) {
                var _a;
                var subject = _this.props.subject;
                var currentCardState = getCardState(_this.state.cardStates, card.slug);
                var newLevel = correct ? currentCardState.level + 1 : 1;
                var newCorrect = correct
                    ? currentCardState.correct.concat([new Date()]) : currentCardState.correct;
                var newIncorrect = correct
                    ? currentCardState.incorrect
                    : currentCardState.incorrect.concat([new Date()]);
                var newCardStates = __assign({}, _this.state.cardStates, (_a = {}, _a[card.slug] = {
                    level: newLevel,
                    correct: newCorrect,
                    incorrect: newIncorrect,
                }, _a));
                _this.saveLevels(newCardStates);
                _this.setState({
                    cardStates: newCardStates,
                    redirect: "/" + subject + "/learn/" + match.params.level,
                });
            };
            _this.saverController = new AbortController();
            _this.saveLevels = function (newLevels) {
                // this.saverController && this.saverController.abort()
                _this.saverController = new AbortController();
                var saveJSON = JSON.stringify(newLevels, function (key, value) {
                    if (value instanceof Date)
                        return value.toISOString();
                    if ("level" == key)
                        return undefined;
                    return value;
                }, "\t");
                localStorage.setItem("save_graphs", saveJSON);
                gs.editGist(saveGist.id, {
                    graphs: {
                        content: saveJSON,
                    },
                }, { signal: _this.saverController.signal })
                    .then(function () { return console.log("saved levels"); })["catch"](function (err) {
                    console.log("error?");
                    _this.setState({ error: err });
                    console.error(err);
                });
            };
            var subject = _this.props.subject;
            _this.state.cards = parseCards(cardMarkdowns[subject]);
            var localSave = localStorage.getItem("save_" + subject);
            _this.state.cardStates = localSave
                ? reviveJSONSave(JSON.parse(localSave))
                : {};
            return _this;
        }
        Subject.prototype.componentDidMount = function () {
            var _this = this;
            var subject = this.props.subject;
            getCardsFromGitHub(subject).then(function (cards) { return _this.setState({ cards: cards }); });
            if (localStorage.getItem("learn_gisthub_token")) {
                saveGistPromise
                    .then(function (gist) {
                    console.log("loaded levels from gist");
                    _this.setState(function (_a) {
                        var cardStates = _a.cardStates;
                        mergeSaves(cardStates, reviveJSONSave(gist.files[subject]
                            ? JSON.parse(gist.files[subject].content)
                            : {}));
                        console.log(cardStates);
                        return { cardStates: cardStates };
                    });
                })["catch"](console.error);
            }
            window.MathJax && MathJax.Hub.Queue(["Typeset", MathJax.Hub]);
        };
        Subject.prototype.componentDidUpdate = function () {
            MathJax.Hub.Queue(["Typeset", MathJax.Hub]);
        };
        Subject.prototype.render = function () {
            var _this = this;
            if (this.state.redirect) {
                var result = React__default.createElement(Redirect, { push: true, to: this.state.redirect });
                this.state.redirect = undefined;
                return result;
            }
            var subject = this.props.subject;
            var cards = this.state.cards;
            return (React__default.createElement("div", null,
                React__default.createElement(Route, { path: "/:subject/card/:cardslug", component: this.CardCardRender }),
                React__default.createElement(Route, { exact: true, path: "/:subject/learn/:level", component: this.CardQuestionRender }),
                React__default.createElement(Route, { exact: true, path: "/:subject/learn/:level/answer/:cardslug", render: function (_a) {
                        var match = _a.match;
                        var card = cards.find(function (c) { return c.slug == match.params.cardslug; });
                        return (React__default.createElement(CardAnswer, { card: card, subject: subject, answer: function (correct) {
                                return _this.answer(correct, card, match);
                            } }));
                    } }),
                React__default.createElement(Route, { exact: true, path: "/:subject/", render: function () {
                        var result = (React__default.createElement(CardOverview, { cards: cards, subject: subject, cardStates: _this.state.cardStates, info: _this.state.info, error: _this.state.error }));
                        _this.state.info = undefined;
                        return result;
                    } }),
                React__default.createElement(Route, { exact: true, path: "/:subject/edit/:cardslug", component: this.EditCardRender }),
                React__default.createElement(Route, { exact: true, path: "/:subject/new", component: this.NewCardRender })));
        };
        return Subject;
    }(React.Component));
    function CardCard(props) {
        var card = props.card, style = props.style, subject = props.subject, htmlAttributes = __rest(props, ["card", "style", "subject"]);
        if (!card) {
            return React__default.createElement("div", null, "card undefined");
        }
        return (React__default.createElement("div", __assign({}, htmlAttributes, { style: __assign({}, style, { padding: "4px" }) }),
            React__default.createElement("h3", { style: { textAlign: "center" } }, card.title),
            React__default.createElement(Link, { to: "/" + subject + "/edit/" + card.slug }, "Edit"),
            React__default.createElement("div", { dangerouslySetInnerHTML: {
                    __html: converter.makeHtml(card.content),
                } })));
    }
    function CardAnswer(_a) {
        var card = _a.card, answer = _a.answer, subject = _a.subject;
        return (React__default.createElement("div", { style: {
                display: "flex",
                flexDirection: "column",
                height: "100%",
            } },
            React__default.createElement(BackToOverview, { subject: subject }),
            React__default.createElement(CardCard, { subject: subject, card: card, style: { flexGrow: 1 } }),
            React__default.createElement("div", null,
                React__default.createElement(Button, { style: { width: "50%" }, color: "success", onClick: function () { return answer(true); } }, "Correct"),
                React__default.createElement(Button, { style: { width: "50%" }, color: "warning", onClick: function () { return answer(false); } }, "Incorrect"))));
    }
    var EditCardState = /** @class */ (function () {
        function EditCardState(currentContent) {
            this.currentContent = currentContent;
            this.saving = false;
            this.lastSaved = undefined;
        }
        return EditCardState;
    }());
    var EditCard = /** @class */ (function (_super) {
        __extends(EditCard, _super);
        function EditCard(props) {
            var _this = _super.call(this, props) || this;
            _this.textarea = React__default.createRef();
            _this.wrap = function (char) {
                var textarea = _this.textarea.current;
                textarea.selectionStart;
                var v = textarea.value;
                v = strSplice(v, textarea.selectionEnd, char);
                v = strSplice(v, textarea.selectionStart, char);
                var start = textarea.selectionStart + char.length;
                var end = textarea.selectionEnd + char.length;
                textarea.value = v;
                textarea.dispatchEvent(new Event("input", { bubbles: true }));
                textarea.selectionStart = start;
                textarea.selectionEnd = end;
                textarea.focus();
            };
            _this.insert = function (char) {
                var textarea = _this.textarea.current;
                var start = textarea.selectionStart + char.length;
                var end = start;
                textarea.value = strSplice(textarea.value, textarea.selectionStart, char, textarea.selectionEnd - textarea.selectionStart);
                textarea.dispatchEvent(new Event("input", { bubbles: true }));
                textarea.selectionStart = start;
                textarea.selectionEnd = end;
                textarea.focus();
            };
            _this.save = function () { return __awaiter(_this, void 0, void 0, function () {
                return __generator(this, function (_a) {
                    switch (_a.label) {
                        case 0:
                            this.setState({ saving: true });
                            return [4 /*yield*/, updateCard(this.props.subject, this.getCard(), this.state.currentContent)];
                        case 1:
                            _a.sent();
                            this.setState({ saving: false, lastSaved: new Date() });
                            return [2 /*return*/];
                    }
                });
            }); };
            _this.state = new EditCardState(_this.getCard().content);
            return _this;
        }
        EditCard.prototype.getCard = function () {
            var _this = this;
            return this.props.cards.find(function (c) { return c.slug == _this.props.cardslug; });
        };
        EditCard.prototype.render = function () {
            var _this = this;
            var subject = this.props.subject;
            var card = this.getCard();
            return (React__default.createElement("div", { style: {
                    display: "flex",
                    flexDirection: "column",
                    height: "100%",
                } },
                React__default.createElement(BackToOverview, { subject: subject }),
                React__default.createElement(Link, { to: "/" + subject + "/card/" + card.slug }, "Back to Card"),
                React__default.createElement("h1", { style: {
                        margin: "auto 8px",
                        textAlign: "center",
                    } }, card.title),
                React__default.createElement(Input, { style: {
                        flexGrow: 1,
                        minHeight: "400px",
                        fontFamily: "monospace",
                    }, type: "textarea", name: "text", id: "exampleText", value: this.state.currentContent, onChange: function (e) {
                        return _this.setState({ currentContent: e.target.value });
                    }, innerRef: this.textarea }),
                React__default.createElement(ButtonGroup, { style: { display: "flex" } },
                    React__default.createElement(Button, { color: "primary", style: { flex: 1 }, onClick: function () { return _this.wrap("§"); } }, "\u00A7"),
                    React__default.createElement(Button, { color: "primary", style: { flex: 1 }, onClick: function () { return _this.wrap("**"); } }, "**"),
                    React__default.createElement(Button, { color: "primary", style: { flex: 1 }, onClick: function () { return _this.wrap("_"); } }, "_"),
                    React__default.createElement(Button, { color: "primary", style: { flex: 1 }, onClick: function () { return _this.insert("\\"); } }, "\\")),
                React__default.createElement(Button, { onClick: this.save, disabled: this.state.saving, color: "warning" },
                    this.state.saving
                        ? "Saving..."
                        : card.content != this.state.currentContent
                            ? "Save"
                            : "Saved",
                    " ",
                    this.state.lastSaved && (React__default.createElement("span", null,
                        "(last saved",
                        " ",
                        React__default.createElement(TimeAgo, { date: this.state.lastSaved, minPeriod: 10 }),
                        ")")))));
        };
        return EditCard;
    }(React.Component));
    function CardQuestion(_a) {
        var card = _a.card, onContinue = _a.onContinue, subject = _a.subject;
        return (React__default.createElement("div", { onClick: onContinue, style: {
                flexGrow: 1,
                display: "flex",
                justifyContent: "center",
            } },
            React__default.createElement(BackToOverview, { subject: subject }),
            React__default.createElement("h1", { style: {
                    margin: "auto 8px",
                    textAlign: "center",
                } }, card.title)));
    }
    function BackToOverview(_a) {
        var subject = _a.subject;
        return React__default.createElement(Link, { to: "/" + subject }, "Back to Overview");
    }
    function CardOverview(_a) {
        var cards = _a.cards, info = _a.info, error = _a.error, cardStates = _a.cardStates, subject = _a.subject;
        var totalProgressStr = sum(cards.map(function (c) { return getCardState(cardStates, c.slug).level - 1; })) +
            "/" +
            cards.length * 4;
        return (React__default.createElement(React__default.Fragment, null,
            info && React__default.createElement(Alert, { color: "info" }, info),
            error && React__default.createElement(Alert, { color: "error" }, error),
            [1, 2, 3, 4, 5].flatMap(function (level) { return (React__default.createElement(React__default.Fragment, { key: "level" + level },
                React__default.createElement("h3", null,
                    "Level ",
                    level,
                    " -",
                    " ",
                    React__default.createElement(Link, { to: "/" + subject + "/learn/" + level }, "learn")),
                React__default.createElement("ul", null, cards
                    .filter(function (c) {
                    return getCardState(cardStates, c.slug).level ==
                        level;
                })
                    .map(function (card) {
                    var cardState = getCardState(cardStates, card.slug);
                    var correctCount = cardState.correct.length;
                    var totalCount = correctCount + cardState.incorrect.length;
                    return (React__default.createElement("li", { key: card.slug },
                        React__default.createElement(Link, { to: "/" +
                                subject +
                                "/card/" +
                                card.slug }, card.title),
                        " - ",
                        React__default.createElement("span", { style: { color: "lightgrey" } },
                            correctCount,
                            "/",
                            totalCount)));
                })))); }),
            React__default.createElement("div", null,
                "Total Progress: ",
                totalProgressStr),
            React__default.createElement(Input, { placeholder: "github API token w/ gist", onChange: function (e) {
                    return localStorage.setItem("learn_gisthub_token", e.target.value.trim());
                }, defaultValue: localStorage.getItem("learn_gisthub_token") || "" })));
    }
    function strSplice(str, index, what, deleteCount) {
        if (deleteCount === void 0) { deleteCount = 0; }
        return str.substring(0, index) + what + str.substring(index + deleteCount);
    }

    ReactDOM.render(React__default.createElement(BrowserRouter, { basename: "/learn/" },
        React__default.createElement(App, null)), document.getElementById("vcs-root"));
    //# sourceMappingURL=index.js.map

}(React, ReactDOM, showdown));
//# sourceMappingURL=bundle.js.map
