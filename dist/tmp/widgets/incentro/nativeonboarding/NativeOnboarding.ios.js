import { Dimensions, PixelRatio, TouchableOpacity, Text, View, I18nManager, StatusBar, Animated, FlatList, SafeAreaView, Image } from 'react-native';
import React, { createElement, Component, useState } from 'react';

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
function _extends() {
  _extends = Object.assign ? Object.assign.bind() : function (target) {
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

const {
  height: height$1,
  width: width$1
} = Dimensions.get("window");
const pixelRatio = PixelRatio.get();
/**
 *
 * Adjust the font size based on the screen size
 *
 * @param   {number}    size   Font size
 *
 * @return  {number} Returns adjusted font size
 */
function adjustFont(size) {
  if (pixelRatio === 2) {
    // iphone 5s and older Androids
    if (width$1 < 360) {
      return size * 0.95;
    }
    // iphone 5
    if (height$1 < 667) {
      return size;
    }
    // iphone 6-6s
    else if (height$1 >= 667 && height$1 <= 735) {
      return size * 1.15;
    }
    // older phablets
    return size * 1.25;
  }
  if (pixelRatio === 3) {
    // catch Android font scaling on small machines
    // where pixel ratio / font scale ratio => 3:3
    if (width$1 <= 360) {
      return size;
    }
    // Catch other weird android width sizings
    if (height$1 < 667) {
      return size * 1.15;
    }
    // catch in-between size Androids and scale font up
    if (height$1 >= 667 && height$1 <= 735) {
      return size * 1.2;
    }
    // catch larger devices
    // ie iphone 6s plus / 7 plus / mi note
    return size * 1.27;
  }
  if (pixelRatio === 3.5) {
    // catch Android font scaling on small machines
    // where pixel ratio / font scale ratio => 3:3
    if (width$1 <= 360) {
      return size;
    }
    // Catch other smaller android height sizings
    if (height$1 < 667) {
      return size * 1.2;
    }
    // catch in-between size Androids and scale font up
    if (height$1 >= 667 && height$1 <= 735) {
      return size * 1.25;
    }
    // catch larger phablet devices
    return size * 1.4;
  }
  // if older device ie pixelRatio !== 2 || 3 || 3.5
  return size;
}

const FilledButton = ({
  backgroundColor,
  fontSize,
  marginLeft,
  marginRight,
  textColor,
  title,
  ...props
}) => createElement(TouchableOpacity, _extends({
  style: {
    flex: 0
  },
  hitSlop: {
    top: 15,
    bottom: 15,
    left: 15,
    right: 15
  },
  containerViewStyle: {
    margin: 10
  }
}, props), createElement(Text, {
  style: {
    backgroundColor: backgroundColor,
    borderRadius: 4,
    paddingVertical: 5,
    paddingHorizontal: 16,
    color: textColor,
    fontSize: adjustFont(fontSize),
    marginLeft: marginLeft,
    marginRight: marginRight,
    overflow: "hidden"
  }
}, title));

var propTypes = {exports: {}};

var reactIs = {exports: {}};

var reactIs_development = {};

/** @license React v16.13.1
 * react-is.development.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var hasRequiredReactIs_development;

function requireReactIs_development () {
	if (hasRequiredReactIs_development) return reactIs_development;
	hasRequiredReactIs_development = 1;

	{
	  (function () {

	    // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
	    // nor polyfill, then a plain number is used for performance.
	    var hasSymbol = typeof Symbol === 'function' && Symbol.for;
	    var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
	    var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
	    var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
	    var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
	    var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
	    var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
	    var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
	    // (unstable) APIs that have been removed. Can we remove the symbols?

	    var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
	    var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
	    var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
	    var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
	    var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
	    var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
	    var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
	    var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
	    var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
	    var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
	    var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;
	    function isValidElementType(type) {
	      return typeof type === 'string' || typeof type === 'function' ||
	      // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
	      type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
	    }
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
	                  case REACT_LAZY_TYPE:
	                  case REACT_MEMO_TYPE:
	                  case REACT_PROVIDER_TYPE:
	                    return $$typeofType;
	                  default:
	                    return $$typeof;
	                }
	            }
	          case REACT_PORTAL_TYPE:
	            return $$typeof;
	        }
	      }
	      return undefined;
	    } // AsyncMode is deprecated along with isAsyncMode

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
	    var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

	    function isAsyncMode(object) {
	      {
	        if (!hasWarnedAboutDeprecatedIsAsyncMode) {
	          hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

	          console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
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
	    reactIs_development.AsyncMode = AsyncMode;
	    reactIs_development.ConcurrentMode = ConcurrentMode;
	    reactIs_development.ContextConsumer = ContextConsumer;
	    reactIs_development.ContextProvider = ContextProvider;
	    reactIs_development.Element = Element;
	    reactIs_development.ForwardRef = ForwardRef;
	    reactIs_development.Fragment = Fragment;
	    reactIs_development.Lazy = Lazy;
	    reactIs_development.Memo = Memo;
	    reactIs_development.Portal = Portal;
	    reactIs_development.Profiler = Profiler;
	    reactIs_development.StrictMode = StrictMode;
	    reactIs_development.Suspense = Suspense;
	    reactIs_development.isAsyncMode = isAsyncMode;
	    reactIs_development.isConcurrentMode = isConcurrentMode;
	    reactIs_development.isContextConsumer = isContextConsumer;
	    reactIs_development.isContextProvider = isContextProvider;
	    reactIs_development.isElement = isElement;
	    reactIs_development.isForwardRef = isForwardRef;
	    reactIs_development.isFragment = isFragment;
	    reactIs_development.isLazy = isLazy;
	    reactIs_development.isMemo = isMemo;
	    reactIs_development.isPortal = isPortal;
	    reactIs_development.isProfiler = isProfiler;
	    reactIs_development.isStrictMode = isStrictMode;
	    reactIs_development.isSuspense = isSuspense;
	    reactIs_development.isValidElementType = isValidElementType;
	    reactIs_development.typeOf = typeOf;
	  })();
	}
	return reactIs_development;
}

var hasRequiredReactIs;

function requireReactIs () {
	if (hasRequiredReactIs) return reactIs.exports;
	hasRequiredReactIs = 1;
	(function (module) {

		{
		  module.exports = requireReactIs_development();
		}
} (reactIs));
	return reactIs.exports;
}

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/

var objectAssign;
var hasRequiredObjectAssign;

function requireObjectAssign () {
	if (hasRequiredObjectAssign) return objectAssign;
	hasRequiredObjectAssign = 1;

	/* eslint-disable no-unused-vars */
	var getOwnPropertySymbols = Object.getOwnPropertySymbols;
	var hasOwnProperty = Object.prototype.hasOwnProperty;
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
	    var test1 = new String('abc'); // eslint-disable-line no-new-wrappers
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
	    if (Object.keys(Object.assign({}, test3)).join('') !== 'abcdefghijklmnopqrst') {
	      return false;
	    }
	    return true;
	  } catch (err) {
	    // We don't expect any of the above to throw, but better to be safe.
	    return false;
	  }
	}
	objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	  var from;
	  var to = toObject(target);
	  var symbols;
	  for (var s = 1; s < arguments.length; s++) {
	    from = Object(arguments[s]);
	    for (var key in from) {
	      if (hasOwnProperty.call(from, key)) {
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
	return objectAssign;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret_1;
var hasRequiredReactPropTypesSecret;

function requireReactPropTypesSecret () {
	if (hasRequiredReactPropTypesSecret) return ReactPropTypesSecret_1;
	hasRequiredReactPropTypesSecret = 1;

	var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';
	ReactPropTypesSecret_1 = ReactPropTypesSecret;
	return ReactPropTypesSecret_1;
}

var has;
var hasRequiredHas;

function requireHas () {
	if (hasRequiredHas) return has;
	hasRequiredHas = 1;
	has = Function.call.bind(Object.prototype.hasOwnProperty);
	return has;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var checkPropTypes_1;
var hasRequiredCheckPropTypes;

function requireCheckPropTypes () {
	if (hasRequiredCheckPropTypes) return checkPropTypes_1;
	hasRequiredCheckPropTypes = 1;

	var printWarning = function () {};
	{
	  var ReactPropTypesSecret = requireReactPropTypesSecret();
	  var loggedTypeFailures = {};
	  var has = requireHas();
	  printWarning = function (text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) {/**/}
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
	      if (has(typeSpecs, typeSpecName)) {
	        var error;
	        // Prop type validation may throw. In case they do, we don't want to
	        // fail the render phase where it didn't fail before. So we log it.
	        // After these have been cleaned up, we'll let them throw.
	        try {
	          // This is intentionally an invariant that gets caught. It's the same
	          // behavior as without this statement except with a better message.
	          if (typeof typeSpecs[typeSpecName] !== 'function') {
	            var err = Error((componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' + 'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.' + 'This often happens because of typos such as `PropTypes.function` instead of `PropTypes.func`.');
	            err.name = 'Invariant Violation';
	            throw err;
	          }
	          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret);
	        } catch (ex) {
	          error = ex;
	        }
	        if (error && !(error instanceof Error)) {
	          printWarning((componentName || 'React class') + ': type specification of ' + location + ' `' + typeSpecName + '` is invalid; the type checker ' + 'function must return `null` or an `Error` but returned a ' + typeof error + '. ' + 'You may have forgotten to pass an argument to the type checker ' + 'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' + 'shape all require an argument).');
	        }
	        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
	          // Only monitor this failure once because there tends to be a lot of the
	          // same error.
	          loggedTypeFailures[error.message] = true;
	          var stack = getStack ? getStack() : '';
	          printWarning('Failed ' + location + ' type: ' + error.message + (stack != null ? stack : ''));
	        }
	      }
	    }
	  }
	}

	/**
	 * Resets warning cache when testing.
	 *
	 * @private
	 */
	checkPropTypes.resetWarningCache = function () {
	  {
	    loggedTypeFailures = {};
	  }
	};
	checkPropTypes_1 = checkPropTypes;
	return checkPropTypes_1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var factoryWithTypeCheckers;
var hasRequiredFactoryWithTypeCheckers;

function requireFactoryWithTypeCheckers () {
	if (hasRequiredFactoryWithTypeCheckers) return factoryWithTypeCheckers;
	hasRequiredFactoryWithTypeCheckers = 1;

	var ReactIs = requireReactIs();
	var assign = requireObjectAssign();
	var ReactPropTypesSecret = requireReactPropTypesSecret();
	var has = requireHas();
	var checkPropTypes = requireCheckPropTypes();
	var printWarning = function () {};
	{
	  printWarning = function (text) {
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
	factoryWithTypeCheckers = function (isValidElement, throwOnDirectAccess) {
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
	    bigint: createPrimitiveTypeChecker('bigint'),
	    bool: createPrimitiveTypeChecker('boolean'),
	    func: createPrimitiveTypeChecker('function'),
	    number: createPrimitiveTypeChecker('number'),
	    object: createPrimitiveTypeChecker('object'),
	    string: createPrimitiveTypeChecker('string'),
	    symbol: createPrimitiveTypeChecker('symbol'),
	    any: createAnyTypeChecker(),
	    arrayOf: createArrayOfTypeChecker,
	    element: createElementTypeChecker(),
	    elementType: createElementTypeTypeChecker(),
	    instanceOf: createInstanceTypeChecker,
	    node: createNodeChecker(),
	    objectOf: createObjectOfTypeChecker,
	    oneOf: createEnumTypeChecker,
	    oneOfType: createUnionTypeChecker,
	    shape: createShapeTypeChecker,
	    exact: createStrictShapeTypeChecker
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
	  function PropTypeError(message, data) {
	    this.message = message;
	    this.data = data && typeof data === 'object' ? data : {};
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
	      if (secret !== ReactPropTypesSecret) {
	        if (throwOnDirectAccess) {
	          // New behavior only for users of `prop-types` package
	          var err = new Error('Calling PropTypes validators directly is not supported by the `prop-types` package. ' + 'Use `PropTypes.checkPropTypes()` to call them. ' + 'Read more at http://fb.me/use-check-prop-types');
	          err.name = 'Invariant Violation';
	          throw err;
	        } else if (typeof console !== 'undefined') {
	          // Old behavior for people using React.PropTypes
	          var cacheKey = componentName + ':' + propName;
	          if (!manualPropTypeCallCache[cacheKey] &&
	          // Avoid spamming the console because they are often not actionable except for lib authors
	          manualPropTypeWarningCount < 3) {
	            printWarning('You are manually calling a React.PropTypes validation ' + 'function for the `' + propFullName + '` prop on `' + componentName + '`. This is deprecated ' + 'and will throw in the standalone `prop-types` package. ' + 'You may be seeing this warning due to a third-party PropTypes ' + 'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.');
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
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'), {
	          expectedType: expectedType
	        });
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
	        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret);
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
	  function createElementTypeTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!ReactIs.isValidElementType(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
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
	      {
	        if (arguments.length > 1) {
	          printWarning('Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' + 'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).');
	        } else {
	          printWarning('Invalid argument supplied to oneOf, expected an array.');
	        }
	      }
	      return emptyFunctionThatReturnsNull;
	    }
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      for (var i = 0; i < expectedValues.length; i++) {
	        if (is(propValue, expectedValues[i])) {
	          return null;
	        }
	      }
	      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
	        var type = getPreciseType(value);
	        if (type === 'symbol') {
	          return String(value);
	        }
	        return value;
	      });
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
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
	        if (has(propValue, key)) {
	          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
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
	      printWarning('Invalid argument supplied to oneOfType, expected an instance of array.') ;
	      return emptyFunctionThatReturnsNull;
	    }
	    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	      var checker = arrayOfTypeCheckers[i];
	      if (typeof checker !== 'function') {
	        printWarning('Invalid argument supplied to oneOfType. Expected an array of check functions, but ' + 'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.');
	        return emptyFunctionThatReturnsNull;
	      }
	    }
	    function validate(props, propName, componentName, location, propFullName) {
	      var expectedTypes = [];
	      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	        var checker = arrayOfTypeCheckers[i];
	        var checkerResult = checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret);
	        if (checkerResult == null) {
	          return null;
	        }
	        if (checkerResult.data && has(checkerResult.data, 'expectedType')) {
	          expectedTypes.push(checkerResult.data.expectedType);
	        }
	      }
	      var expectedTypesMessage = expectedTypes.length > 0 ? ', expected one of type [' + expectedTypes.join(', ') + ']' : '';
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`' + expectedTypesMessage + '.'));
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
	  function invalidValidatorError(componentName, location, propFullName, key, type) {
	    return new PropTypeError((componentName || 'React class') + ': ' + location + ' type `' + propFullName + '.' + key + '` is invalid; ' + 'it must be a function, usually from the `prop-types` package, but received `' + type + '`.');
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
	        if (typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
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
	      // We need to check all keys in case some are required but missing from props.
	      var allKeys = assign({}, props[propName], shapeTypes);
	      for (var key in allKeys) {
	        var checker = shapeTypes[key];
	        if (has(shapeTypes, key) && typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        if (!checker) {
	          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' + '\nBad object: ' + JSON.stringify(props[propName], null, '  ') + '\nValid keys: ' + JSON.stringify(Object.keys(shapeTypes), null, '  '));
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
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

	    // falsy value can't be a Symbol
	    if (!propValue) {
	      return false;
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
	  ReactPropTypes.checkPropTypes = checkPropTypes;
	  ReactPropTypes.resetWarningCache = checkPropTypes.resetWarningCache;
	  ReactPropTypes.PropTypes = ReactPropTypes;
	  return ReactPropTypes;
	};
	return factoryWithTypeCheckers;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

{
  var ReactIs = requireReactIs();

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  propTypes.exports = requireFactoryWithTypeCheckers()(ReactIs.isElement, throwOnDirectAccess);
}

var tinycolor$1 = {exports: {}};

(function (module) {
	// TinyColor v1.4.2
	// https://github.com/bgrins/TinyColor
	// Brian Grinstead, MIT License

	(function (Math) {
	  var trimLeft = /^\s+/,
	    trimRight = /\s+$/,
	    tinyCounter = 0,
	    mathRound = Math.round,
	    mathMin = Math.min,
	    mathMax = Math.max,
	    mathRandom = Math.random;
	  function tinycolor(color, opts) {
	    color = color ? color : '';
	    opts = opts || {};

	    // If input is already a tinycolor, return itself
	    if (color instanceof tinycolor) {
	      return color;
	    }
	    // If we are called as a function, call using new instead
	    if (!(this instanceof tinycolor)) {
	      return new tinycolor(color, opts);
	    }
	    var rgb = inputToRGB(color);
	    this._originalInput = color, this._r = rgb.r, this._g = rgb.g, this._b = rgb.b, this._a = rgb.a, this._roundA = mathRound(100 * this._a) / 100, this._format = opts.format || rgb.format;
	    this._gradientType = opts.gradientType;

	    // Don't let the range of [0,255] come back in [0,1].
	    // Potentially lose a little bit of precision here, but will fix issues where
	    // .5 gets interpreted as half of the total, instead of half of 1
	    // If it was supposed to be 128, this was already taken care of by `inputToRgb`
	    if (this._r < 1) {
	      this._r = mathRound(this._r);
	    }
	    if (this._g < 1) {
	      this._g = mathRound(this._g);
	    }
	    if (this._b < 1) {
	      this._b = mathRound(this._b);
	    }
	    this._ok = rgb.ok;
	    this._tc_id = tinyCounter++;
	  }
	  tinycolor.prototype = {
	    isDark: function () {
	      return this.getBrightness() < 128;
	    },
	    isLight: function () {
	      return !this.isDark();
	    },
	    isValid: function () {
	      return this._ok;
	    },
	    getOriginalInput: function () {
	      return this._originalInput;
	    },
	    getFormat: function () {
	      return this._format;
	    },
	    getAlpha: function () {
	      return this._a;
	    },
	    getBrightness: function () {
	      //http://www.w3.org/TR/AERT#color-contrast
	      var rgb = this.toRgb();
	      return (rgb.r * 299 + rgb.g * 587 + rgb.b * 114) / 1000;
	    },
	    getLuminance: function () {
	      //http://www.w3.org/TR/2008/REC-WCAG20-20081211/#relativeluminancedef
	      var rgb = this.toRgb();
	      var RsRGB, GsRGB, BsRGB, R, G, B;
	      RsRGB = rgb.r / 255;
	      GsRGB = rgb.g / 255;
	      BsRGB = rgb.b / 255;
	      if (RsRGB <= 0.03928) {
	        R = RsRGB / 12.92;
	      } else {
	        R = Math.pow((RsRGB + 0.055) / 1.055, 2.4);
	      }
	      if (GsRGB <= 0.03928) {
	        G = GsRGB / 12.92;
	      } else {
	        G = Math.pow((GsRGB + 0.055) / 1.055, 2.4);
	      }
	      if (BsRGB <= 0.03928) {
	        B = BsRGB / 12.92;
	      } else {
	        B = Math.pow((BsRGB + 0.055) / 1.055, 2.4);
	      }
	      return 0.2126 * R + 0.7152 * G + 0.0722 * B;
	    },
	    setAlpha: function (value) {
	      this._a = boundAlpha(value);
	      this._roundA = mathRound(100 * this._a) / 100;
	      return this;
	    },
	    toHsv: function () {
	      var hsv = rgbToHsv(this._r, this._g, this._b);
	      return {
	        h: hsv.h * 360,
	        s: hsv.s,
	        v: hsv.v,
	        a: this._a
	      };
	    },
	    toHsvString: function () {
	      var hsv = rgbToHsv(this._r, this._g, this._b);
	      var h = mathRound(hsv.h * 360),
	        s = mathRound(hsv.s * 100),
	        v = mathRound(hsv.v * 100);
	      return this._a == 1 ? "hsv(" + h + ", " + s + "%, " + v + "%)" : "hsva(" + h + ", " + s + "%, " + v + "%, " + this._roundA + ")";
	    },
	    toHsl: function () {
	      var hsl = rgbToHsl(this._r, this._g, this._b);
	      return {
	        h: hsl.h * 360,
	        s: hsl.s,
	        l: hsl.l,
	        a: this._a
	      };
	    },
	    toHslString: function () {
	      var hsl = rgbToHsl(this._r, this._g, this._b);
	      var h = mathRound(hsl.h * 360),
	        s = mathRound(hsl.s * 100),
	        l = mathRound(hsl.l * 100);
	      return this._a == 1 ? "hsl(" + h + ", " + s + "%, " + l + "%)" : "hsla(" + h + ", " + s + "%, " + l + "%, " + this._roundA + ")";
	    },
	    toHex: function (allow3Char) {
	      return rgbToHex(this._r, this._g, this._b, allow3Char);
	    },
	    toHexString: function (allow3Char) {
	      return '#' + this.toHex(allow3Char);
	    },
	    toHex8: function (allow4Char) {
	      return rgbaToHex(this._r, this._g, this._b, this._a, allow4Char);
	    },
	    toHex8String: function (allow4Char) {
	      return '#' + this.toHex8(allow4Char);
	    },
	    toRgb: function () {
	      return {
	        r: mathRound(this._r),
	        g: mathRound(this._g),
	        b: mathRound(this._b),
	        a: this._a
	      };
	    },
	    toRgbString: function () {
	      return this._a == 1 ? "rgb(" + mathRound(this._r) + ", " + mathRound(this._g) + ", " + mathRound(this._b) + ")" : "rgba(" + mathRound(this._r) + ", " + mathRound(this._g) + ", " + mathRound(this._b) + ", " + this._roundA + ")";
	    },
	    toPercentageRgb: function () {
	      return {
	        r: mathRound(bound01(this._r, 255) * 100) + "%",
	        g: mathRound(bound01(this._g, 255) * 100) + "%",
	        b: mathRound(bound01(this._b, 255) * 100) + "%",
	        a: this._a
	      };
	    },
	    toPercentageRgbString: function () {
	      return this._a == 1 ? "rgb(" + mathRound(bound01(this._r, 255) * 100) + "%, " + mathRound(bound01(this._g, 255) * 100) + "%, " + mathRound(bound01(this._b, 255) * 100) + "%)" : "rgba(" + mathRound(bound01(this._r, 255) * 100) + "%, " + mathRound(bound01(this._g, 255) * 100) + "%, " + mathRound(bound01(this._b, 255) * 100) + "%, " + this._roundA + ")";
	    },
	    toName: function () {
	      if (this._a === 0) {
	        return "transparent";
	      }
	      if (this._a < 1) {
	        return false;
	      }
	      return hexNames[rgbToHex(this._r, this._g, this._b, true)] || false;
	    },
	    toFilter: function (secondColor) {
	      var hex8String = '#' + rgbaToArgbHex(this._r, this._g, this._b, this._a);
	      var secondHex8String = hex8String;
	      var gradientType = this._gradientType ? "GradientType = 1, " : "";
	      if (secondColor) {
	        var s = tinycolor(secondColor);
	        secondHex8String = '#' + rgbaToArgbHex(s._r, s._g, s._b, s._a);
	      }
	      return "progid:DXImageTransform.Microsoft.gradient(" + gradientType + "startColorstr=" + hex8String + ",endColorstr=" + secondHex8String + ")";
	    },
	    toString: function (format) {
	      var formatSet = !!format;
	      format = format || this._format;
	      var formattedString = false;
	      var hasAlpha = this._a < 1 && this._a >= 0;
	      var needsAlphaFormat = !formatSet && hasAlpha && (format === "hex" || format === "hex6" || format === "hex3" || format === "hex4" || format === "hex8" || format === "name");
	      if (needsAlphaFormat) {
	        // Special case for "transparent", all other non-alpha formats
	        // will return rgba when there is transparency.
	        if (format === "name" && this._a === 0) {
	          return this.toName();
	        }
	        return this.toRgbString();
	      }
	      if (format === "rgb") {
	        formattedString = this.toRgbString();
	      }
	      if (format === "prgb") {
	        formattedString = this.toPercentageRgbString();
	      }
	      if (format === "hex" || format === "hex6") {
	        formattedString = this.toHexString();
	      }
	      if (format === "hex3") {
	        formattedString = this.toHexString(true);
	      }
	      if (format === "hex4") {
	        formattedString = this.toHex8String(true);
	      }
	      if (format === "hex8") {
	        formattedString = this.toHex8String();
	      }
	      if (format === "name") {
	        formattedString = this.toName();
	      }
	      if (format === "hsl") {
	        formattedString = this.toHslString();
	      }
	      if (format === "hsv") {
	        formattedString = this.toHsvString();
	      }
	      return formattedString || this.toHexString();
	    },
	    clone: function () {
	      return tinycolor(this.toString());
	    },
	    _applyModification: function (fn, args) {
	      var color = fn.apply(null, [this].concat([].slice.call(args)));
	      this._r = color._r;
	      this._g = color._g;
	      this._b = color._b;
	      this.setAlpha(color._a);
	      return this;
	    },
	    lighten: function () {
	      return this._applyModification(lighten, arguments);
	    },
	    brighten: function () {
	      return this._applyModification(brighten, arguments);
	    },
	    darken: function () {
	      return this._applyModification(darken, arguments);
	    },
	    desaturate: function () {
	      return this._applyModification(desaturate, arguments);
	    },
	    saturate: function () {
	      return this._applyModification(saturate, arguments);
	    },
	    greyscale: function () {
	      return this._applyModification(greyscale, arguments);
	    },
	    spin: function () {
	      return this._applyModification(spin, arguments);
	    },
	    _applyCombination: function (fn, args) {
	      return fn.apply(null, [this].concat([].slice.call(args)));
	    },
	    analogous: function () {
	      return this._applyCombination(analogous, arguments);
	    },
	    complement: function () {
	      return this._applyCombination(complement, arguments);
	    },
	    monochromatic: function () {
	      return this._applyCombination(monochromatic, arguments);
	    },
	    splitcomplement: function () {
	      return this._applyCombination(splitcomplement, arguments);
	    },
	    triad: function () {
	      return this._applyCombination(triad, arguments);
	    },
	    tetrad: function () {
	      return this._applyCombination(tetrad, arguments);
	    }
	  };

	  // If input is an object, force 1 into "1.0" to handle ratios properly
	  // String input requires "1.0" as input, so 1 will be treated as 1
	  tinycolor.fromRatio = function (color, opts) {
	    if (typeof color == "object") {
	      var newColor = {};
	      for (var i in color) {
	        if (color.hasOwnProperty(i)) {
	          if (i === "a") {
	            newColor[i] = color[i];
	          } else {
	            newColor[i] = convertToPercentage(color[i]);
	          }
	        }
	      }
	      color = newColor;
	    }
	    return tinycolor(color, opts);
	  };

	  // Given a string or object, convert that input to RGB
	  // Possible string inputs:
	  //
	  //     "red"
	  //     "#f00" or "f00"
	  //     "#ff0000" or "ff0000"
	  //     "#ff000000" or "ff000000"
	  //     "rgb 255 0 0" or "rgb (255, 0, 0)"
	  //     "rgb 1.0 0 0" or "rgb (1, 0, 0)"
	  //     "rgba (255, 0, 0, 1)" or "rgba 255, 0, 0, 1"
	  //     "rgba (1.0, 0, 0, 1)" or "rgba 1.0, 0, 0, 1"
	  //     "hsl(0, 100%, 50%)" or "hsl 0 100% 50%"
	  //     "hsla(0, 100%, 50%, 1)" or "hsla 0 100% 50%, 1"
	  //     "hsv(0, 100%, 100%)" or "hsv 0 100% 100%"
	  //
	  function inputToRGB(color) {
	    var rgb = {
	      r: 0,
	      g: 0,
	      b: 0
	    };
	    var a = 1;
	    var s = null;
	    var v = null;
	    var l = null;
	    var ok = false;
	    var format = false;
	    if (typeof color == "string") {
	      color = stringInputToObject(color);
	    }
	    if (typeof color == "object") {
	      if (isValidCSSUnit(color.r) && isValidCSSUnit(color.g) && isValidCSSUnit(color.b)) {
	        rgb = rgbToRgb(color.r, color.g, color.b);
	        ok = true;
	        format = String(color.r).substr(-1) === "%" ? "prgb" : "rgb";
	      } else if (isValidCSSUnit(color.h) && isValidCSSUnit(color.s) && isValidCSSUnit(color.v)) {
	        s = convertToPercentage(color.s);
	        v = convertToPercentage(color.v);
	        rgb = hsvToRgb(color.h, s, v);
	        ok = true;
	        format = "hsv";
	      } else if (isValidCSSUnit(color.h) && isValidCSSUnit(color.s) && isValidCSSUnit(color.l)) {
	        s = convertToPercentage(color.s);
	        l = convertToPercentage(color.l);
	        rgb = hslToRgb(color.h, s, l);
	        ok = true;
	        format = "hsl";
	      }
	      if (color.hasOwnProperty("a")) {
	        a = color.a;
	      }
	    }
	    a = boundAlpha(a);
	    return {
	      ok: ok,
	      format: color.format || format,
	      r: mathMin(255, mathMax(rgb.r, 0)),
	      g: mathMin(255, mathMax(rgb.g, 0)),
	      b: mathMin(255, mathMax(rgb.b, 0)),
	      a: a
	    };
	  }

	  // Conversion Functions
	  // --------------------

	  // `rgbToHsl`, `rgbToHsv`, `hslToRgb`, `hsvToRgb` modified from:
	  // <http://mjijackson.com/2008/02/rgb-to-hsl-and-rgb-to-hsv-color-model-conversion-algorithms-in-javascript>

	  // `rgbToRgb`
	  // Handle bounds / percentage checking to conform to CSS color spec
	  // <http://www.w3.org/TR/css3-color/>
	  // *Assumes:* r, g, b in [0, 255] or [0, 1]
	  // *Returns:* { r, g, b } in [0, 255]
	  function rgbToRgb(r, g, b) {
	    return {
	      r: bound01(r, 255) * 255,
	      g: bound01(g, 255) * 255,
	      b: bound01(b, 255) * 255
	    };
	  }

	  // `rgbToHsl`
	  // Converts an RGB color value to HSL.
	  // *Assumes:* r, g, and b are contained in [0, 255] or [0, 1]
	  // *Returns:* { h, s, l } in [0,1]
	  function rgbToHsl(r, g, b) {
	    r = bound01(r, 255);
	    g = bound01(g, 255);
	    b = bound01(b, 255);
	    var max = mathMax(r, g, b),
	      min = mathMin(r, g, b);
	    var h,
	      s,
	      l = (max + min) / 2;
	    if (max == min) {
	      h = s = 0; // achromatic
	    } else {
	      var d = max - min;
	      s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
	      switch (max) {
	        case r:
	          h = (g - b) / d + (g < b ? 6 : 0);
	          break;
	        case g:
	          h = (b - r) / d + 2;
	          break;
	        case b:
	          h = (r - g) / d + 4;
	          break;
	      }
	      h /= 6;
	    }
	    return {
	      h: h,
	      s: s,
	      l: l
	    };
	  }

	  // `hslToRgb`
	  // Converts an HSL color value to RGB.
	  // *Assumes:* h is contained in [0, 1] or [0, 360] and s and l are contained [0, 1] or [0, 100]
	  // *Returns:* { r, g, b } in the set [0, 255]
	  function hslToRgb(h, s, l) {
	    var r, g, b;
	    h = bound01(h, 360);
	    s = bound01(s, 100);
	    l = bound01(l, 100);
	    function hue2rgb(p, q, t) {
	      if (t < 0) t += 1;
	      if (t > 1) t -= 1;
	      if (t < 1 / 6) return p + (q - p) * 6 * t;
	      if (t < 1 / 2) return q;
	      if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
	      return p;
	    }
	    if (s === 0) {
	      r = g = b = l; // achromatic
	    } else {
	      var q = l < 0.5 ? l * (1 + s) : l + s - l * s;
	      var p = 2 * l - q;
	      r = hue2rgb(p, q, h + 1 / 3);
	      g = hue2rgb(p, q, h);
	      b = hue2rgb(p, q, h - 1 / 3);
	    }
	    return {
	      r: r * 255,
	      g: g * 255,
	      b: b * 255
	    };
	  }

	  // `rgbToHsv`
	  // Converts an RGB color value to HSV
	  // *Assumes:* r, g, and b are contained in the set [0, 255] or [0, 1]
	  // *Returns:* { h, s, v } in [0,1]
	  function rgbToHsv(r, g, b) {
	    r = bound01(r, 255);
	    g = bound01(g, 255);
	    b = bound01(b, 255);
	    var max = mathMax(r, g, b),
	      min = mathMin(r, g, b);
	    var h,
	      s,
	      v = max;
	    var d = max - min;
	    s = max === 0 ? 0 : d / max;
	    if (max == min) {
	      h = 0; // achromatic
	    } else {
	      switch (max) {
	        case r:
	          h = (g - b) / d + (g < b ? 6 : 0);
	          break;
	        case g:
	          h = (b - r) / d + 2;
	          break;
	        case b:
	          h = (r - g) / d + 4;
	          break;
	      }
	      h /= 6;
	    }
	    return {
	      h: h,
	      s: s,
	      v: v
	    };
	  }

	  // `hsvToRgb`
	  // Converts an HSV color value to RGB.
	  // *Assumes:* h is contained in [0, 1] or [0, 360] and s and v are contained in [0, 1] or [0, 100]
	  // *Returns:* { r, g, b } in the set [0, 255]
	  function hsvToRgb(h, s, v) {
	    h = bound01(h, 360) * 6;
	    s = bound01(s, 100);
	    v = bound01(v, 100);
	    var i = Math.floor(h),
	      f = h - i,
	      p = v * (1 - s),
	      q = v * (1 - f * s),
	      t = v * (1 - (1 - f) * s),
	      mod = i % 6,
	      r = [v, q, p, p, t, v][mod],
	      g = [t, v, v, q, p, p][mod],
	      b = [p, p, t, v, v, q][mod];
	    return {
	      r: r * 255,
	      g: g * 255,
	      b: b * 255
	    };
	  }

	  // `rgbToHex`
	  // Converts an RGB color to hex
	  // Assumes r, g, and b are contained in the set [0, 255]
	  // Returns a 3 or 6 character hex
	  function rgbToHex(r, g, b, allow3Char) {
	    var hex = [pad2(mathRound(r).toString(16)), pad2(mathRound(g).toString(16)), pad2(mathRound(b).toString(16))];

	    // Return a 3 character hex if possible
	    if (allow3Char && hex[0].charAt(0) == hex[0].charAt(1) && hex[1].charAt(0) == hex[1].charAt(1) && hex[2].charAt(0) == hex[2].charAt(1)) {
	      return hex[0].charAt(0) + hex[1].charAt(0) + hex[2].charAt(0);
	    }
	    return hex.join("");
	  }

	  // `rgbaToHex`
	  // Converts an RGBA color plus alpha transparency to hex
	  // Assumes r, g, b are contained in the set [0, 255] and
	  // a in [0, 1]. Returns a 4 or 8 character rgba hex
	  function rgbaToHex(r, g, b, a, allow4Char) {
	    var hex = [pad2(mathRound(r).toString(16)), pad2(mathRound(g).toString(16)), pad2(mathRound(b).toString(16)), pad2(convertDecimalToHex(a))];

	    // Return a 4 character hex if possible
	    if (allow4Char && hex[0].charAt(0) == hex[0].charAt(1) && hex[1].charAt(0) == hex[1].charAt(1) && hex[2].charAt(0) == hex[2].charAt(1) && hex[3].charAt(0) == hex[3].charAt(1)) {
	      return hex[0].charAt(0) + hex[1].charAt(0) + hex[2].charAt(0) + hex[3].charAt(0);
	    }
	    return hex.join("");
	  }

	  // `rgbaToArgbHex`
	  // Converts an RGBA color to an ARGB Hex8 string
	  // Rarely used, but required for "toFilter()"
	  function rgbaToArgbHex(r, g, b, a) {
	    var hex = [pad2(convertDecimalToHex(a)), pad2(mathRound(r).toString(16)), pad2(mathRound(g).toString(16)), pad2(mathRound(b).toString(16))];
	    return hex.join("");
	  }

	  // `equals`
	  // Can be called with any tinycolor input
	  tinycolor.equals = function (color1, color2) {
	    if (!color1 || !color2) {
	      return false;
	    }
	    return tinycolor(color1).toRgbString() == tinycolor(color2).toRgbString();
	  };
	  tinycolor.random = function () {
	    return tinycolor.fromRatio({
	      r: mathRandom(),
	      g: mathRandom(),
	      b: mathRandom()
	    });
	  };

	  // Modification Functions
	  // ----------------------
	  // Thanks to less.js for some of the basics here
	  // <https://github.com/cloudhead/less.js/blob/master/lib/less/functions.js>

	  function desaturate(color, amount) {
	    amount = amount === 0 ? 0 : amount || 10;
	    var hsl = tinycolor(color).toHsl();
	    hsl.s -= amount / 100;
	    hsl.s = clamp01(hsl.s);
	    return tinycolor(hsl);
	  }
	  function saturate(color, amount) {
	    amount = amount === 0 ? 0 : amount || 10;
	    var hsl = tinycolor(color).toHsl();
	    hsl.s += amount / 100;
	    hsl.s = clamp01(hsl.s);
	    return tinycolor(hsl);
	  }
	  function greyscale(color) {
	    return tinycolor(color).desaturate(100);
	  }
	  function lighten(color, amount) {
	    amount = amount === 0 ? 0 : amount || 10;
	    var hsl = tinycolor(color).toHsl();
	    hsl.l += amount / 100;
	    hsl.l = clamp01(hsl.l);
	    return tinycolor(hsl);
	  }
	  function brighten(color, amount) {
	    amount = amount === 0 ? 0 : amount || 10;
	    var rgb = tinycolor(color).toRgb();
	    rgb.r = mathMax(0, mathMin(255, rgb.r - mathRound(255 * -(amount / 100))));
	    rgb.g = mathMax(0, mathMin(255, rgb.g - mathRound(255 * -(amount / 100))));
	    rgb.b = mathMax(0, mathMin(255, rgb.b - mathRound(255 * -(amount / 100))));
	    return tinycolor(rgb);
	  }
	  function darken(color, amount) {
	    amount = amount === 0 ? 0 : amount || 10;
	    var hsl = tinycolor(color).toHsl();
	    hsl.l -= amount / 100;
	    hsl.l = clamp01(hsl.l);
	    return tinycolor(hsl);
	  }

	  // Spin takes a positive or negative amount within [-360, 360] indicating the change of hue.
	  // Values outside of this range will be wrapped into this range.
	  function spin(color, amount) {
	    var hsl = tinycolor(color).toHsl();
	    var hue = (hsl.h + amount) % 360;
	    hsl.h = hue < 0 ? 360 + hue : hue;
	    return tinycolor(hsl);
	  }

	  // Combination Functions
	  // ---------------------
	  // Thanks to jQuery xColor for some of the ideas behind these
	  // <https://github.com/infusion/jQuery-xcolor/blob/master/jquery.xcolor.js>

	  function complement(color) {
	    var hsl = tinycolor(color).toHsl();
	    hsl.h = (hsl.h + 180) % 360;
	    return tinycolor(hsl);
	  }
	  function triad(color) {
	    var hsl = tinycolor(color).toHsl();
	    var h = hsl.h;
	    return [tinycolor(color), tinycolor({
	      h: (h + 120) % 360,
	      s: hsl.s,
	      l: hsl.l
	    }), tinycolor({
	      h: (h + 240) % 360,
	      s: hsl.s,
	      l: hsl.l
	    })];
	  }
	  function tetrad(color) {
	    var hsl = tinycolor(color).toHsl();
	    var h = hsl.h;
	    return [tinycolor(color), tinycolor({
	      h: (h + 90) % 360,
	      s: hsl.s,
	      l: hsl.l
	    }), tinycolor({
	      h: (h + 180) % 360,
	      s: hsl.s,
	      l: hsl.l
	    }), tinycolor({
	      h: (h + 270) % 360,
	      s: hsl.s,
	      l: hsl.l
	    })];
	  }
	  function splitcomplement(color) {
	    var hsl = tinycolor(color).toHsl();
	    var h = hsl.h;
	    return [tinycolor(color), tinycolor({
	      h: (h + 72) % 360,
	      s: hsl.s,
	      l: hsl.l
	    }), tinycolor({
	      h: (h + 216) % 360,
	      s: hsl.s,
	      l: hsl.l
	    })];
	  }
	  function analogous(color, results, slices) {
	    results = results || 6;
	    slices = slices || 30;
	    var hsl = tinycolor(color).toHsl();
	    var part = 360 / slices;
	    var ret = [tinycolor(color)];
	    for (hsl.h = (hsl.h - (part * results >> 1) + 720) % 360; --results;) {
	      hsl.h = (hsl.h + part) % 360;
	      ret.push(tinycolor(hsl));
	    }
	    return ret;
	  }
	  function monochromatic(color, results) {
	    results = results || 6;
	    var hsv = tinycolor(color).toHsv();
	    var h = hsv.h,
	      s = hsv.s,
	      v = hsv.v;
	    var ret = [];
	    var modification = 1 / results;
	    while (results--) {
	      ret.push(tinycolor({
	        h: h,
	        s: s,
	        v: v
	      }));
	      v = (v + modification) % 1;
	    }
	    return ret;
	  }

	  // Utility Functions
	  // ---------------------

	  tinycolor.mix = function (color1, color2, amount) {
	    amount = amount === 0 ? 0 : amount || 50;
	    var rgb1 = tinycolor(color1).toRgb();
	    var rgb2 = tinycolor(color2).toRgb();
	    var p = amount / 100;
	    var rgba = {
	      r: (rgb2.r - rgb1.r) * p + rgb1.r,
	      g: (rgb2.g - rgb1.g) * p + rgb1.g,
	      b: (rgb2.b - rgb1.b) * p + rgb1.b,
	      a: (rgb2.a - rgb1.a) * p + rgb1.a
	    };
	    return tinycolor(rgba);
	  };

	  // Readability Functions
	  // ---------------------
	  // <http://www.w3.org/TR/2008/REC-WCAG20-20081211/#contrast-ratiodef (WCAG Version 2)

	  // `contrast`
	  // Analyze the 2 colors and returns the color contrast defined by (WCAG Version 2)
	  tinycolor.readability = function (color1, color2) {
	    var c1 = tinycolor(color1);
	    var c2 = tinycolor(color2);
	    return (Math.max(c1.getLuminance(), c2.getLuminance()) + 0.05) / (Math.min(c1.getLuminance(), c2.getLuminance()) + 0.05);
	  };

	  // `isReadable`
	  // Ensure that foreground and background color combinations meet WCAG2 guidelines.
	  // The third argument is an optional Object.
	  //      the 'level' property states 'AA' or 'AAA' - if missing or invalid, it defaults to 'AA';
	  //      the 'size' property states 'large' or 'small' - if missing or invalid, it defaults to 'small'.
	  // If the entire object is absent, isReadable defaults to {level:"AA",size:"small"}.

	  // *Example*
	  //    tinycolor.isReadable("#000", "#111") => false
	  //    tinycolor.isReadable("#000", "#111",{level:"AA",size:"large"}) => false
	  tinycolor.isReadable = function (color1, color2, wcag2) {
	    var readability = tinycolor.readability(color1, color2);
	    var wcag2Parms, out;
	    out = false;
	    wcag2Parms = validateWCAG2Parms(wcag2);
	    switch (wcag2Parms.level + wcag2Parms.size) {
	      case "AAsmall":
	      case "AAAlarge":
	        out = readability >= 4.5;
	        break;
	      case "AAlarge":
	        out = readability >= 3;
	        break;
	      case "AAAsmall":
	        out = readability >= 7;
	        break;
	    }
	    return out;
	  };

	  // `mostReadable`
	  // Given a base color and a list of possible foreground or background
	  // colors for that base, returns the most readable color.
	  // Optionally returns Black or White if the most readable color is unreadable.
	  // *Example*
	  //    tinycolor.mostReadable(tinycolor.mostReadable("#123", ["#124", "#125"],{includeFallbackColors:false}).toHexString(); // "#112255"
	  //    tinycolor.mostReadable(tinycolor.mostReadable("#123", ["#124", "#125"],{includeFallbackColors:true}).toHexString();  // "#ffffff"
	  //    tinycolor.mostReadable("#a8015a", ["#faf3f3"],{includeFallbackColors:true,level:"AAA",size:"large"}).toHexString(); // "#faf3f3"
	  //    tinycolor.mostReadable("#a8015a", ["#faf3f3"],{includeFallbackColors:true,level:"AAA",size:"small"}).toHexString(); // "#ffffff"
	  tinycolor.mostReadable = function (baseColor, colorList, args) {
	    var bestColor = null;
	    var bestScore = 0;
	    var readability;
	    var includeFallbackColors, level, size;
	    args = args || {};
	    includeFallbackColors = args.includeFallbackColors;
	    level = args.level;
	    size = args.size;
	    for (var i = 0; i < colorList.length; i++) {
	      readability = tinycolor.readability(baseColor, colorList[i]);
	      if (readability > bestScore) {
	        bestScore = readability;
	        bestColor = tinycolor(colorList[i]);
	      }
	    }
	    if (tinycolor.isReadable(baseColor, bestColor, {
	      "level": level,
	      "size": size
	    }) || !includeFallbackColors) {
	      return bestColor;
	    } else {
	      args.includeFallbackColors = false;
	      return tinycolor.mostReadable(baseColor, ["#fff", "#000"], args);
	    }
	  };

	  // Big List of Colors
	  // ------------------
	  // <http://www.w3.org/TR/css3-color/#svg-color>
	  var names = tinycolor.names = {
	    aliceblue: "f0f8ff",
	    antiquewhite: "faebd7",
	    aqua: "0ff",
	    aquamarine: "7fffd4",
	    azure: "f0ffff",
	    beige: "f5f5dc",
	    bisque: "ffe4c4",
	    black: "000",
	    blanchedalmond: "ffebcd",
	    blue: "00f",
	    blueviolet: "8a2be2",
	    brown: "a52a2a",
	    burlywood: "deb887",
	    burntsienna: "ea7e5d",
	    cadetblue: "5f9ea0",
	    chartreuse: "7fff00",
	    chocolate: "d2691e",
	    coral: "ff7f50",
	    cornflowerblue: "6495ed",
	    cornsilk: "fff8dc",
	    crimson: "dc143c",
	    cyan: "0ff",
	    darkblue: "00008b",
	    darkcyan: "008b8b",
	    darkgoldenrod: "b8860b",
	    darkgray: "a9a9a9",
	    darkgreen: "006400",
	    darkgrey: "a9a9a9",
	    darkkhaki: "bdb76b",
	    darkmagenta: "8b008b",
	    darkolivegreen: "556b2f",
	    darkorange: "ff8c00",
	    darkorchid: "9932cc",
	    darkred: "8b0000",
	    darksalmon: "e9967a",
	    darkseagreen: "8fbc8f",
	    darkslateblue: "483d8b",
	    darkslategray: "2f4f4f",
	    darkslategrey: "2f4f4f",
	    darkturquoise: "00ced1",
	    darkviolet: "9400d3",
	    deeppink: "ff1493",
	    deepskyblue: "00bfff",
	    dimgray: "696969",
	    dimgrey: "696969",
	    dodgerblue: "1e90ff",
	    firebrick: "b22222",
	    floralwhite: "fffaf0",
	    forestgreen: "228b22",
	    fuchsia: "f0f",
	    gainsboro: "dcdcdc",
	    ghostwhite: "f8f8ff",
	    gold: "ffd700",
	    goldenrod: "daa520",
	    gray: "808080",
	    green: "008000",
	    greenyellow: "adff2f",
	    grey: "808080",
	    honeydew: "f0fff0",
	    hotpink: "ff69b4",
	    indianred: "cd5c5c",
	    indigo: "4b0082",
	    ivory: "fffff0",
	    khaki: "f0e68c",
	    lavender: "e6e6fa",
	    lavenderblush: "fff0f5",
	    lawngreen: "7cfc00",
	    lemonchiffon: "fffacd",
	    lightblue: "add8e6",
	    lightcoral: "f08080",
	    lightcyan: "e0ffff",
	    lightgoldenrodyellow: "fafad2",
	    lightgray: "d3d3d3",
	    lightgreen: "90ee90",
	    lightgrey: "d3d3d3",
	    lightpink: "ffb6c1",
	    lightsalmon: "ffa07a",
	    lightseagreen: "20b2aa",
	    lightskyblue: "87cefa",
	    lightslategray: "789",
	    lightslategrey: "789",
	    lightsteelblue: "b0c4de",
	    lightyellow: "ffffe0",
	    lime: "0f0",
	    limegreen: "32cd32",
	    linen: "faf0e6",
	    magenta: "f0f",
	    maroon: "800000",
	    mediumaquamarine: "66cdaa",
	    mediumblue: "0000cd",
	    mediumorchid: "ba55d3",
	    mediumpurple: "9370db",
	    mediumseagreen: "3cb371",
	    mediumslateblue: "7b68ee",
	    mediumspringgreen: "00fa9a",
	    mediumturquoise: "48d1cc",
	    mediumvioletred: "c71585",
	    midnightblue: "191970",
	    mintcream: "f5fffa",
	    mistyrose: "ffe4e1",
	    moccasin: "ffe4b5",
	    navajowhite: "ffdead",
	    navy: "000080",
	    oldlace: "fdf5e6",
	    olive: "808000",
	    olivedrab: "6b8e23",
	    orange: "ffa500",
	    orangered: "ff4500",
	    orchid: "da70d6",
	    palegoldenrod: "eee8aa",
	    palegreen: "98fb98",
	    paleturquoise: "afeeee",
	    palevioletred: "db7093",
	    papayawhip: "ffefd5",
	    peachpuff: "ffdab9",
	    peru: "cd853f",
	    pink: "ffc0cb",
	    plum: "dda0dd",
	    powderblue: "b0e0e6",
	    purple: "800080",
	    rebeccapurple: "663399",
	    red: "f00",
	    rosybrown: "bc8f8f",
	    royalblue: "4169e1",
	    saddlebrown: "8b4513",
	    salmon: "fa8072",
	    sandybrown: "f4a460",
	    seagreen: "2e8b57",
	    seashell: "fff5ee",
	    sienna: "a0522d",
	    silver: "c0c0c0",
	    skyblue: "87ceeb",
	    slateblue: "6a5acd",
	    slategray: "708090",
	    slategrey: "708090",
	    snow: "fffafa",
	    springgreen: "00ff7f",
	    steelblue: "4682b4",
	    tan: "d2b48c",
	    teal: "008080",
	    thistle: "d8bfd8",
	    tomato: "ff6347",
	    turquoise: "40e0d0",
	    violet: "ee82ee",
	    wheat: "f5deb3",
	    white: "fff",
	    whitesmoke: "f5f5f5",
	    yellow: "ff0",
	    yellowgreen: "9acd32"
	  };

	  // Make it easy to access colors via `hexNames[hex]`
	  var hexNames = tinycolor.hexNames = flip(names);

	  // Utilities
	  // ---------

	  // `{ 'name1': 'val1' }` becomes `{ 'val1': 'name1' }`
	  function flip(o) {
	    var flipped = {};
	    for (var i in o) {
	      if (o.hasOwnProperty(i)) {
	        flipped[o[i]] = i;
	      }
	    }
	    return flipped;
	  }

	  // Return a valid alpha value [0,1] with all invalid values being set to 1
	  function boundAlpha(a) {
	    a = parseFloat(a);
	    if (isNaN(a) || a < 0 || a > 1) {
	      a = 1;
	    }
	    return a;
	  }

	  // Take input from [0, n] and return it as [0, 1]
	  function bound01(n, max) {
	    if (isOnePointZero(n)) {
	      n = "100%";
	    }
	    var processPercent = isPercentage(n);
	    n = mathMin(max, mathMax(0, parseFloat(n)));

	    // Automatically convert percentage into number
	    if (processPercent) {
	      n = parseInt(n * max, 10) / 100;
	    }

	    // Handle floating point rounding errors
	    if (Math.abs(n - max) < 0.000001) {
	      return 1;
	    }

	    // Convert into [0, 1] range if it isn't already
	    return n % max / parseFloat(max);
	  }

	  // Force a number between 0 and 1
	  function clamp01(val) {
	    return mathMin(1, mathMax(0, val));
	  }

	  // Parse a base-16 hex value into a base-10 integer
	  function parseIntFromHex(val) {
	    return parseInt(val, 16);
	  }

	  // Need to handle 1.0 as 100%, since once it is a number, there is no difference between it and 1
	  // <http://stackoverflow.com/questions/7422072/javascript-how-to-detect-number-as-a-decimal-including-1-0>
	  function isOnePointZero(n) {
	    return typeof n == "string" && n.indexOf('.') != -1 && parseFloat(n) === 1;
	  }

	  // Check to see if string passed in is a percentage
	  function isPercentage(n) {
	    return typeof n === "string" && n.indexOf('%') != -1;
	  }

	  // Force a hex value to have 2 characters
	  function pad2(c) {
	    return c.length == 1 ? '0' + c : '' + c;
	  }

	  // Replace a decimal with it's percentage value
	  function convertToPercentage(n) {
	    if (n <= 1) {
	      n = n * 100 + "%";
	    }
	    return n;
	  }

	  // Converts a decimal to a hex value
	  function convertDecimalToHex(d) {
	    return Math.round(parseFloat(d) * 255).toString(16);
	  }
	  // Converts a hex value to a decimal
	  function convertHexToDecimal(h) {
	    return parseIntFromHex(h) / 255;
	  }
	  var matchers = function () {
	    // <http://www.w3.org/TR/css3-values/#integers>
	    var CSS_INTEGER = "[-\\+]?\\d+%?";

	    // <http://www.w3.org/TR/css3-values/#number-value>
	    var CSS_NUMBER = "[-\\+]?\\d*\\.\\d+%?";

	    // Allow positive/negative integer/number.  Don't capture the either/or, just the entire outcome.
	    var CSS_UNIT = "(?:" + CSS_NUMBER + ")|(?:" + CSS_INTEGER + ")";

	    // Actual matching.
	    // Parentheses and commas are optional, but not required.
	    // Whitespace can take the place of commas or opening paren
	    var PERMISSIVE_MATCH3 = "[\\s|\\(]+(" + CSS_UNIT + ")[,|\\s]+(" + CSS_UNIT + ")[,|\\s]+(" + CSS_UNIT + ")\\s*\\)?";
	    var PERMISSIVE_MATCH4 = "[\\s|\\(]+(" + CSS_UNIT + ")[,|\\s]+(" + CSS_UNIT + ")[,|\\s]+(" + CSS_UNIT + ")[,|\\s]+(" + CSS_UNIT + ")\\s*\\)?";
	    return {
	      CSS_UNIT: new RegExp(CSS_UNIT),
	      rgb: new RegExp("rgb" + PERMISSIVE_MATCH3),
	      rgba: new RegExp("rgba" + PERMISSIVE_MATCH4),
	      hsl: new RegExp("hsl" + PERMISSIVE_MATCH3),
	      hsla: new RegExp("hsla" + PERMISSIVE_MATCH4),
	      hsv: new RegExp("hsv" + PERMISSIVE_MATCH3),
	      hsva: new RegExp("hsva" + PERMISSIVE_MATCH4),
	      hex3: /^#?([0-9a-fA-F]{1})([0-9a-fA-F]{1})([0-9a-fA-F]{1})$/,
	      hex6: /^#?([0-9a-fA-F]{2})([0-9a-fA-F]{2})([0-9a-fA-F]{2})$/,
	      hex4: /^#?([0-9a-fA-F]{1})([0-9a-fA-F]{1})([0-9a-fA-F]{1})([0-9a-fA-F]{1})$/,
	      hex8: /^#?([0-9a-fA-F]{2})([0-9a-fA-F]{2})([0-9a-fA-F]{2})([0-9a-fA-F]{2})$/
	    };
	  }();

	  // `isValidCSSUnit`
	  // Take in a single string / number and check to see if it looks like a CSS unit
	  // (see `matchers` above for definition).
	  function isValidCSSUnit(color) {
	    return !!matchers.CSS_UNIT.exec(color);
	  }

	  // `stringInputToObject`
	  // Permissive string parsing.  Take in a number of formats, and output an object
	  // based on detected format.  Returns `{ r, g, b }` or `{ h, s, l }` or `{ h, s, v}`
	  function stringInputToObject(color) {
	    color = color.replace(trimLeft, '').replace(trimRight, '').toLowerCase();
	    var named = false;
	    if (names[color]) {
	      color = names[color];
	      named = true;
	    } else if (color == 'transparent') {
	      return {
	        r: 0,
	        g: 0,
	        b: 0,
	        a: 0,
	        format: "name"
	      };
	    }

	    // Try to match string input using regular expressions.
	    // Keep most of the number bounding out of this function - don't worry about [0,1] or [0,100] or [0,360]
	    // Just return an object and let the conversion functions handle that.
	    // This way the result will be the same whether the tinycolor is initialized with string or object.
	    var match;
	    if (match = matchers.rgb.exec(color)) {
	      return {
	        r: match[1],
	        g: match[2],
	        b: match[3]
	      };
	    }
	    if (match = matchers.rgba.exec(color)) {
	      return {
	        r: match[1],
	        g: match[2],
	        b: match[3],
	        a: match[4]
	      };
	    }
	    if (match = matchers.hsl.exec(color)) {
	      return {
	        h: match[1],
	        s: match[2],
	        l: match[3]
	      };
	    }
	    if (match = matchers.hsla.exec(color)) {
	      return {
	        h: match[1],
	        s: match[2],
	        l: match[3],
	        a: match[4]
	      };
	    }
	    if (match = matchers.hsv.exec(color)) {
	      return {
	        h: match[1],
	        s: match[2],
	        v: match[3]
	      };
	    }
	    if (match = matchers.hsva.exec(color)) {
	      return {
	        h: match[1],
	        s: match[2],
	        v: match[3],
	        a: match[4]
	      };
	    }
	    if (match = matchers.hex8.exec(color)) {
	      return {
	        r: parseIntFromHex(match[1]),
	        g: parseIntFromHex(match[2]),
	        b: parseIntFromHex(match[3]),
	        a: convertHexToDecimal(match[4]),
	        format: named ? "name" : "hex8"
	      };
	    }
	    if (match = matchers.hex6.exec(color)) {
	      return {
	        r: parseIntFromHex(match[1]),
	        g: parseIntFromHex(match[2]),
	        b: parseIntFromHex(match[3]),
	        format: named ? "name" : "hex"
	      };
	    }
	    if (match = matchers.hex4.exec(color)) {
	      return {
	        r: parseIntFromHex(match[1] + '' + match[1]),
	        g: parseIntFromHex(match[2] + '' + match[2]),
	        b: parseIntFromHex(match[3] + '' + match[3]),
	        a: convertHexToDecimal(match[4] + '' + match[4]),
	        format: named ? "name" : "hex8"
	      };
	    }
	    if (match = matchers.hex3.exec(color)) {
	      return {
	        r: parseIntFromHex(match[1] + '' + match[1]),
	        g: parseIntFromHex(match[2] + '' + match[2]),
	        b: parseIntFromHex(match[3] + '' + match[3]),
	        format: named ? "name" : "hex"
	      };
	    }
	    return false;
	  }
	  function validateWCAG2Parms(parms) {
	    // return valid WCAG2 parms for isReadable.
	    // If input parms are invalid, return {"level":"AA", "size":"small"}
	    var level, size;
	    parms = parms || {
	      "level": "AA",
	      "size": "small"
	    };
	    level = (parms.level || "AA").toUpperCase();
	    size = (parms.size || "small").toLowerCase();
	    if (level !== "AA" && level !== "AAA") {
	      level = "AA";
	    }
	    if (size !== "small" && size !== "large") {
	      size = "small";
	    }
	    return {
	      "level": level,
	      "size": size
	    };
	  }

	  // Node: Export function
	  if (module.exports) {
	    module.exports = tinycolor;
	  }
	  // AMD/requirejs: Define the module
	  else {
	    window.tinycolor = tinycolor;
	  }
	})(Math);
} (tinycolor$1));

var tinycolor = tinycolor$1.exports;

const Page = ({
  isLight,
  image,
  title,
  subtitle,
  width,
  height,
  containerStyles,
  imageContainerStyles,
  allowFontScaling,
  titleStyles,
  subTitleStyles
}) => {
  let titleElement = title;
  if (typeof title === 'string' || title instanceof String) {
    titleElement = /*#__PURE__*/React.createElement(View, {
      style: styles$5.padding
    }, /*#__PURE__*/React.createElement(Text, {
      allowFontScaling: allowFontScaling,
      style: [styles$5.title, isLight ? styles$5.titleLight : {}, titleStyles]
    }, title));
  }
  let subtitleElement = subtitle;
  if (typeof subtitle === 'string' || subtitle instanceof String) {
    subtitleElement = /*#__PURE__*/React.createElement(View, {
      style: styles$5.padding
    }, /*#__PURE__*/React.createElement(Text, {
      allowFontScaling: allowFontScaling,
      style: [styles$5.subtitle, isLight ? styles$5.subtitleLight : {}, subTitleStyles]
    }, subtitle));
  }
  return /*#__PURE__*/React.createElement(View, {
    style: [styles$5.container, containerStyles, {
      width,
      height
    }]
  }, /*#__PURE__*/React.createElement(View, {
    style: [styles$5.imageContainer, imageContainerStyles]
  }, image), titleElement, subtitleElement);
};
Page.propTypes = {
  isLight: propTypes.exports.bool.isRequired,
  image: propTypes.exports.element.isRequired,
  containerStyles: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  imageContainerStyles: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  title: propTypes.exports.oneOfType([propTypes.exports.string, propTypes.exports.element]).isRequired,
  subtitle: propTypes.exports.oneOfType([propTypes.exports.string, propTypes.exports.element]).isRequired,
  allowFontScaling: propTypes.exports.bool,
  titleStyles: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  subTitleStyles: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  width: propTypes.exports.number.isRequired,
  height: propTypes.exports.number.isRequired
};
Page.defaultProps = {
  containerStyles: null,
  imageContainerStyles: null,
  allowFontScaling: true,
  titleStyles: null,
  subTitleStyles: null
};
const {
  width,
  height
} = Dimensions.get('window');
const potrait = height > width;
const styles$5 = {
  container: {
    flex: 1,
    flexDirection: 'column',
    alignItems: 'center',
    justifyContent: potrait ? 'center' : 'flex-start',
    paddingTop: potrait ? 0 : 10
  },
  imageContainer: {
    flex: 0,
    paddingBottom: potrait ? 60 : 10,
    alignItems: 'center',
    width: '100%'
  },
  padding: {
    paddingHorizontal: 10
  },
  title: {
    textAlign: 'center',
    fontSize: 26,
    color: '#fff',
    paddingBottom: 15
  },
  titleLight: {
    color: '#000'
  },
  subtitle: {
    textAlign: 'center',
    fontSize: 16,
    color: 'rgba(255, 255, 255, 0.7)'
  },
  subtitleLight: {
    color: 'rgba(0, 0, 0, 0.7)'
  }
};

const Dots = ({
  isLight,
  numPages,
  currentPage,
  Dot
}) => /*#__PURE__*/React.createElement(View, {
  style: styles$4.container
}, [...Array(numPages)].map((_, index) => /*#__PURE__*/React.createElement(Dot, {
  key: index,
  selected: index === currentPage,
  isLight: isLight
})));
Dots.propTypes = {
  isLight: propTypes.exports.bool.isRequired,
  numPages: propTypes.exports.number.isRequired,
  currentPage: propTypes.exports.number.isRequired,
  Dot: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]).isRequired
};
const styles$4 = {
  container: {
    flex: 0,
    flexDirection: I18nManager.isRTL && "ios" === 'ios' ? 'row-reverse' : 'row',
    alignItems: 'center'
  }
};

const Pagination = ({
  numPages,
  currentPage,
  isLight,
  bottomBarHeight,
  bottomBarColor,
  controlStatusBar,
  showSkip,
  showNext,
  showDone,
  onNext,
  onSkip,
  onDone,
  skipLabel,
  nextLabel,
  allowFontScaling,
  SkipButtonComponent,
  NextButtonComponent,
  DoneButtonComponent,
  DotComponent
}) => {
  const isLastPage = I18nManager.isRTL && "ios" == 'ios' ? currentPage === 0 : currentPage + 1 === numPages;
  const SkipButtonFinal = showSkip && !isLastPage && /*#__PURE__*/React.createElement(SkipButtonComponent, {
    isLight: isLight,
    skipLabel: skipLabel,
    allowFontScaling: allowFontScaling,
    onPress: () => {
      if (typeof onSkip === 'function') {
        if (controlStatusBar) {
          StatusBar.setBarStyle('default', true);
        }
        onSkip();
      }
    }
  });
  const NextButtonFinal = showNext && !isLastPage && /*#__PURE__*/React.createElement(NextButtonComponent, {
    nextLabel: nextLabel,
    allowFontScaling: allowFontScaling,
    isLight: isLight,
    onPress: onNext
  });
  const DoneButtonFinal = showDone && isLastPage && /*#__PURE__*/React.createElement(DoneButtonComponent, {
    isLight: isLight,
    allowFontScaling: allowFontScaling,
    onPress: () => {
      if (typeof onDone === 'function') {
        if (controlStatusBar) {
          StatusBar.setBarStyle('default', true);
        }
        onDone();
      }
    }
  });
  return /*#__PURE__*/React.createElement(View, {
    style: {
      height: bottomBarHeight,
      backgroundColor: bottomBarColor,
      ...styles$3.container
    }
  }, /*#__PURE__*/React.createElement(View, {
    style: styles$3.buttonLeft
  }, SkipButtonFinal), /*#__PURE__*/React.createElement(Dots, {
    isLight: isLight,
    numPages: numPages,
    currentPage: currentPage,
    Dot: DotComponent,
    style: styles$3.dots
  }), /*#__PURE__*/React.createElement(View, {
    style: styles$3.buttonRight
  }, NextButtonFinal, DoneButtonFinal));
};
Pagination.propTypes = {
  numPages: propTypes.exports.number.isRequired,
  currentPage: propTypes.exports.number.isRequired,
  isLight: propTypes.exports.bool.isRequired,
  bottomBarHeight: propTypes.exports.number.isRequired,
  bottomBarColor: propTypes.exports.string.isRequired,
  showNext: propTypes.exports.bool.isRequired,
  showSkip: propTypes.exports.bool.isRequired,
  showDone: propTypes.exports.bool.isRequired,
  onNext: propTypes.exports.func.isRequired,
  onSkip: propTypes.exports.func,
  onDone: propTypes.exports.func,
  allowFontScaling: propTypes.exports.bool,
  skipLabel: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.string]).isRequired,
  nextLabel: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.string]).isRequired,
  SkipButtonComponent: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]).isRequired,
  DoneButtonComponent: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]).isRequired,
  NextButtonComponent: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]).isRequired,
  DotComponent: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]).isRequired
};
const styles$3 = {
  container: {
    paddingHorizontal: 0,
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center'
  },
  buttonLeft: {
    width: 200,
    flexShrink: 1,
    alignItems: 'flex-start'
  },
  buttonRight: {
    width: 200,
    flexShrink: 1,
    alignItems: 'flex-end'
  },
  dots: {
    flexShrink: 0
  }
};

const Dot = ({
  isLight,
  selected
}) => {
  let backgroundColor;
  if (isLight) {
    backgroundColor = selected ? 'rgba(0, 0, 0, 0.8)' : 'rgba(0, 0, 0, 0.3)';
  } else {
    backgroundColor = selected ? '#fff' : 'rgba(255, 255, 255, 0.5)';
  }
  return /*#__PURE__*/React.createElement(View, {
    style: {
      ...styles$2.dot,
      backgroundColor
    }
  });
};
Dot.propTypes = {
  isLight: propTypes.exports.bool.isRequired,
  selected: propTypes.exports.bool.isRequired
};
const styles$2 = {
  dot: {
    width: 6,
    height: 6,
    borderRadius: 3,
    marginHorizontal: 3
  }
};

const TextButton$1 = ({
  size,
  onPress,
  textStyle,
  allowFontScaling,
  style,
  children
}) => /*#__PURE__*/React.createElement(View, {
  style: {
    flex: 0,
    paddingHorizontal: 10,
    ...style
  }
}, /*#__PURE__*/React.createElement(TouchableOpacity, {
  style: {
    flex: 0
  },
  onPress: onPress,
  hitSlop: {
    top: 15,
    bottom: 15,
    left: 15,
    right: 15
  }
}, /*#__PURE__*/React.createElement(Text, {
  allowFontScaling: allowFontScaling,
  style: {
    fontSize: size / 2.5,
    ...textStyle
  }
}, children)));
TextButton$1.propTypes = {
  size: propTypes.exports.number.isRequired,
  onPress: propTypes.exports.func.isRequired,
  textStyle: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  allowFontScaling: propTypes.exports.bool
};
TextButton$1.defaultProps = {
  textStyle: null,
  allowFontScaling: true
};

const BUTTON_SIZE = 40;
const MARGIN_RIGHT = 10;
const MARGIN_LEFT = 10;
const getDefaultStyle = isLight => ({
  color: isLight ? 'rgba(0, 0, 0, 0.8)' : '#fff'
});

const SkipButton = ({
  skipLabel,
  isLight,
  ...rest
}) => /*#__PURE__*/React.createElement(TextButton$1, _extends({
  size: BUTTON_SIZE,
  style: {
    marginLeft: MARGIN_LEFT
  },
  textStyle: getDefaultStyle(isLight)
}, rest), skipLabel);

const NextButton = ({
  nextLabel,
  isLight,
  ...rest
}) => /*#__PURE__*/React.createElement(TextButton$1, _extends({
  size: BUTTON_SIZE,
  style: {
    marginRight: MARGIN_RIGHT
  },
  textStyle: getDefaultStyle(isLight)
}, rest), nextLabel);

const SymbolButton = ({
  size,
  onPress,
  style,
  textStyle,
  children
}) => /*#__PURE__*/React.createElement(View, {
  style: {
    height: size,
    width: size,
    justifyContent: 'center',
    alignItems: 'center',
    ...style
  }
}, /*#__PURE__*/React.createElement(TouchableOpacity, {
  style: {
    flex: 1,
    justifyContent: 'center',
    alignItems: 'center'
  },
  onPress: onPress,
  hitSlop: {
    top: 15,
    bottom: 15,
    left: 15,
    right: 15
  }
}, /*#__PURE__*/React.createElement(Text, {
  allowFontScaling: false,
  style: {
    textAlign: 'center',
    fontSize: size / 1.7,
    ...textStyle
  }
}, children)));
SymbolButton.propTypes = {
  size: propTypes.exports.number.isRequired,
  onPress: propTypes.exports.func.isRequired,
  style: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  textStyle: propTypes.exports.shape({
    style: propTypes.exports.any
  })
};
SymbolButton.defaultProps = {
  style: null,
  textStyle: null
};

class DoneButton extends React.Component {
  constructor(...args) {
    super(...args);
    _defineProperty(this, "state", {
      fadeAnim: new Animated.Value(0)
    });
  }
  componentDidMount() {
    setTimeout(() => {
      Animated.timing(this.state.fadeAnim, {
        toValue: 1,
        duration: 1000,
        useNativeDriver: true
      }).start();
    }, 1000);
  }
  render() {
    const {
      isLight,
      ...rest
    } = this.props;
    const {
      fadeAnim
    } = this.state;
    return /*#__PURE__*/React.createElement(Animated.View, {
      style: {
        opacity: fadeAnim
      }
    }, /*#__PURE__*/React.createElement(SymbolButton, _extends({
      size: BUTTON_SIZE,
      textStyle: getDefaultStyle(isLight),
      style: {
        borderRadius: BUTTON_SIZE / 2,
        backgroundColor: 'rgba(255, 255, 255, 0.10)',
        margin: MARGIN_RIGHT
      }
    }, rest), "\u2713"));
  }
}

// hotfix: https://github.com/facebook/react-native/issues/16710
const itemVisibleHotfix = {
  itemVisiblePercentThreshold: 100
};
class Onboarding extends Component {
  constructor(props) {
    super(props);
    _defineProperty(this, "onSwipePageChange", ({
      viewableItems
    }) => {
      if (!viewableItems[0] || this.state.currentPage === viewableItems[0].index) return;
      this.setState(state => {
        this.props.pageIndexCallback && this.props.pageIndexCallback(viewableItems[0].index);
        return {
          previousPage: state.currentPage,
          currentPage: viewableItems[0].index,
          backgroundColorAnim: new Animated.Value(0)
        };
      });
    });
    _defineProperty(this, "goNext", () => {
      this.flatList.scrollToIndex({
        animated: true,
        index: I18nManager.isRTL && "ios" == 'ios' ? this.state.currentPage - 1 : this.state.currentPage + 1
      });
    });
    _defineProperty(this, "goToPage", (index, animated = true) => {
      this.flatList.scrollToIndex({
        index,
        animated
      });
    });
    _defineProperty(this, "_onLayout", () => {
      const {
        width,
        height
      } = Dimensions.get('window');
      this.setState({
        width,
        height
      });
    });
    _defineProperty(this, "keyExtractor", (item, index) => index.toString());
    _defineProperty(this, "renderItem", ({
      item
    }) => {
      const {
        image,
        title,
        subtitle,
        backgroundColor
      } = item;
      const isLight = tinycolor(backgroundColor).getBrightness() > 180;
      const {
        containerStyles,
        imageContainerStyles,
        allowFontScalingText,
        titleStyles,
        subTitleStyles
      } = this.props;
      return /*#__PURE__*/React.createElement(Page, {
        isLight: isLight,
        image: image,
        title: title,
        subtitle: subtitle,
        width: this.state.width || Dimensions.get('window').width,
        height: this.state.height || Dimensions.get('window').height,
        containerStyles: containerStyles,
        imageContainerStyles: imageContainerStyles,
        allowFontScaling: allowFontScalingText,
        titleStyles: Object.assign({}, titleStyles || {}, item.titleStyles || {}),
        subTitleStyles: Object.assign({}, subTitleStyles || {}, item.subTitleStyles || {})
      });
    });
    this.state = {
      currentPage: 0,
      previousPage: null,
      width: null,
      height: null,
      backgroundColorAnim: new Animated.Value(0)
    };
  }
  componentDidUpdate() {
    Animated.timing(this.state.backgroundColorAnim, {
      toValue: 1,
      duration: this.props.transitionAnimationDuration,
      useNativeDriver: false
    }).start();
  }
  render() {
    const {
      pages,
      alterBottomColor,
      bottomBarHeight,
      bottomBarColor,
      controlStatusBar,
      showSkip,
      showNext,
      showDone,
      showPagination,
      onSkip,
      onDone,
      skipLabel,
      nextLabel,
      allowFontScalingButtons,
      SkipButtonComponent,
      DoneButtonComponent,
      NextButtonComponent,
      DotComponent,
      flatlistProps,
      skipToPage
    } = this.props;
    const currentPage = pages[this.state.currentPage];
    const currentBackgroundColor = currentPage.backgroundColor;
    const isLight = tinycolor(currentBackgroundColor).getBrightness() > 180;
    const barStyle = isLight ? 'dark-content' : 'light-content';
    const bottomBarHighlight = alterBottomColor !== undefined ? alterBottomColor : this.props.bottomBarHighlight;
    let backgroundColor = currentBackgroundColor;
    if (this.state.previousPage !== null && pages[this.state.previousPage] !== undefined) {
      const previousBackgroundColor = pages[this.state.previousPage].backgroundColor;
      backgroundColor = this.state.backgroundColorAnim.interpolate({
        inputRange: [0, 1],
        outputRange: [previousBackgroundColor, currentBackgroundColor]
      });
    }
    if (alterBottomColor !== undefined) {
      console.warn('The prop alterBottomColor on react-native-onboarding-swiper is deprecated and will be removed soon. Use `bottomBarHighlight` instead.');
    }
    const skipFun = skipToPage != null ? () => {
      this.flatList.scrollToIndex({
        animated: true,
        index: skipToPage
      });
    } : onSkip;
    return /*#__PURE__*/React.createElement(Animated.View, {
      onLayout: this._onLayout,
      style: {
        flex: 1,
        backgroundColor,
        justifyContent: 'center'
      }
    }, controlStatusBar && /*#__PURE__*/React.createElement(StatusBar, {
      barStyle: barStyle
    }), /*#__PURE__*/React.createElement(FlatList, _extends({
      ref: list => {
        this.flatList = list;
      },
      data: pages,
      pagingEnabled: true,
      horizontal: true,
      showsHorizontalScrollIndicator: false,
      renderItem: this.renderItem,
      keyExtractor: this.keyExtractor,
      onViewableItemsChanged: this.onSwipePageChange,
      viewabilityConfig: itemVisibleHotfix,
      initialNumToRender: 1,
      extraData: this.state.width // ensure that the list re-renders on orientation change
    }, flatlistProps)), showPagination && /*#__PURE__*/React.createElement(SafeAreaView, {
      style: bottomBarHighlight ? styles$1.overlay : {}
    }, /*#__PURE__*/React.createElement(Pagination, {
      isLight: isLight,
      bottomBarHeight: bottomBarHeight,
      bottomBarColor: bottomBarColor,
      showSkip: showSkip,
      showNext: showNext,
      showDone: showDone,
      numPages: pages.length,
      currentPage: this.state.currentPage,
      controlStatusBar: controlStatusBar,
      onSkip: skipFun,
      onDone: onDone,
      onNext: this.goNext,
      skipLabel: skipLabel,
      nextLabel: nextLabel,
      allowFontScaling: allowFontScalingButtons,
      SkipButtonComponent: SkipButtonComponent,
      DoneButtonComponent: DoneButtonComponent,
      NextButtonComponent: NextButtonComponent,
      DotComponent: DotComponent
    })));
  }
}
Onboarding.propTypes = {
  pages: propTypes.exports.arrayOf(propTypes.exports.shape({
    backgroundColor: propTypes.exports.string.isRequired,
    image: propTypes.exports.element.isRequired,
    title: propTypes.exports.oneOfType([propTypes.exports.string, propTypes.exports.element, propTypes.exports.func]).isRequired,
    subtitle: propTypes.exports.oneOfType([propTypes.exports.string, propTypes.exports.element]).isRequired
  })).isRequired,
  bottomBarHighlight: propTypes.exports.bool,
  bottomBarHeight: propTypes.exports.number,
  bottomBarColor: propTypes.exports.string,
  controlStatusBar: propTypes.exports.bool,
  showSkip: propTypes.exports.bool,
  showNext: propTypes.exports.bool,
  showDone: propTypes.exports.bool,
  showPagination: propTypes.exports.bool,
  onSkip: propTypes.exports.func,
  onDone: propTypes.exports.func,
  skipLabel: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.string]),
  nextLabel: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.string]),
  SkipButtonComponent: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]),
  DoneButtonComponent: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]),
  NextButtonComponent: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]),
  DotComponent: propTypes.exports.oneOfType([propTypes.exports.element, propTypes.exports.func]),
  containerStyles: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  imageContainerStyles: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  allowFontScalingText: propTypes.exports.bool,
  allowFontScalingButtons: propTypes.exports.bool,
  titleStyles: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  subTitleStyles: propTypes.exports.shape({
    style: propTypes.exports.any
  }),
  transitionAnimationDuration: propTypes.exports.number,
  skipToPage: propTypes.exports.number,
  pageIndexCallback: propTypes.exports.func
};
Onboarding.defaultProps = {
  bottomBarHighlight: true,
  bottomBarHeight: 60,
  bottomBarColor: 'transparent',
  controlStatusBar: true,
  showPagination: true,
  showSkip: true,
  showNext: true,
  showDone: true,
  skipLabel: 'Skip',
  nextLabel: 'Next',
  onSkip: null,
  onDone: null,
  SkipButtonComponent: SkipButton,
  DoneButtonComponent: DoneButton,
  NextButtonComponent: NextButton,
  DotComponent: Dot,
  containerStyles: null,
  imageContainerStyles: null,
  allowFontScalingText: true,
  allowFontScalingButtons: true,
  titleStyles: null,
  subTitleStyles: null,
  transitionAnimationDuration: 500,
  skipToPage: null,
  pageIndexCallback: null
};
const styles$1 = {
  overlay: {
    backgroundColor: 'rgba(0, 0, 0, 0.1)'
  }
};

const TextButton = ({
  fontSize,
  marginLeft,
  marginRight,
  textColor,
  title,
  ...props
}) => createElement(TouchableOpacity, _extends({
  style: {
    flex: 0
  },
  hitSlop: {
    top: 15,
    bottom: 15,
    left: 15,
    right: 15
  },
  containerViewStyle: {
    margin: 10
  }
}, props), createElement(Text, {
  style: {
    color: textColor,
    fontSize: adjustFont(fontSize),
    marginLeft: marginLeft,
    marginRight: marginRight
  }
}, title));

const spacing = {
  smallest: 4,
  smaller: 8,
  small: 10,
  regular: 16,
  large: 24,
  larger: 30,
  largest: 40
};

// based on https://github.com/jfilter/react-native-onboarding-swiper

const windowWidth = Dimensions.get('window').width;
const styles = {
  container: {
    height: '100%',
    width: '100%',
    zIndex: 10
  },
  onboarding: {
    justifyContent: 'center'
  },
  title: {
    color: '#4B4B4B',
    fontSize: 30,
    fontWeight: '400',
    textAlign: 'left',
    width: windowWidth - spacing.regular * 2
  },
  subTitle: {
    color: '#4B4B4B',
    fontSize: 16,
    lineHeight: 16 * 1.5,
    textAlign: 'left',
    width: windowWidth - spacing.regular * 2
  },
  image: {
    margin: 0,
    padding: 0,
    resizeMode: 'contain',
    maxWidth: windowWidth - spacing.regular * 2
  },
  imageContainer: {
    paddingBottom: spacing.regular,
    height: 'auto',
    width: 'auto'
  }
};
function NativeOnboarding({
  bottombarHighlight,
  bottombarTextColor,
  currentPageDotColor,
  doneButtonColor,
  doneButtonText,
  dotColor,
  doneAction,
  doneText,
  nextText,
  pages,
  showSkip,
  skipAction,
  skipText
}) {
  const onboardingPages = [];
  const [currentPage, setCurrentPage] = useState(0);
  const Square = ({
    selected
  }) => {
    const backgroundColor = selected ? currentPageDotColor : 'transparent';
    const borderColor = selected ? 'transparent' : dotColor;
    return createElement(View, {
      style: {
        borderRadius: 20,
        borderWidth: 1,
        width: 8,
        height: 8,
        marginHorizontal: 3,
        backgroundColor,
        borderColor
      }
    });
  };
  const Skip = ({
    ...props
  }) => createElement(TextButton, _extends({
    title: skipText,
    textColor: bottombarTextColor,
    marginLeft: spacing.regular,
    fontSize: 14
  }, props));
  const Next = ({
    ...props
  }) => createElement(TextButton, _extends({
    title: nextText,
    textColor: bottombarTextColor,
    marginRight: spacing.regular,
    fontSize: 14
  }, props));
  const Done = ({
    ...props
  }) => createElement(FilledButton, _extends({
    backgroundColor: doneButtonColor,
    title: doneText,
    textColor: doneButtonText,
    marginRight: spacing.regular,
    fontSize: 14
  }, props));
  function actionButton() {
    if (doneAction && doneAction.canExecute) {
      doneAction.execute();
    }
  }
  function skipButton() {
    if (skipAction && skipAction.canExecute) {
      setCurrentPage(0);
      skipAction.execute();
    }
  }
  pages.map(page => onboardingPages.push({
    backgroundColor: page.pageBackground || 'transparent',
    title: page.pageTitle || '',
    subtitle: page.pageSubTitle || '',
    image: createElement(Image, {
      source: Number(page.pageImage.value),
      style: [styles.image, {
        height: page.pageImageSize
      }]
    })
  }));
  return createElement(View, {
    style: styles.container
  }, createElement(Onboarding, {
    allowFontScalingText: false,
    bottomBarHighlight: bottombarHighlight,
    currentPage: currentPage,
    SkipButtonComponent: Skip,
    DotComponent: Square,
    NextButtonComponent: Next,
    DoneButtonComponent: Done,
    onSkip: skipAction && skipButton,
    onDone: doneAction && actionButton,
    pages: onboardingPages,
    transitionAnimationDuration: 200,
    titleStyles: styles.title,
    imageContainerStyles: styles.imageContainer,
    subTitleStyles: styles.subTitle,
    containerStyles: styles.onboarding,
    showSkip: showSkip
  }));
}

export { NativeOnboarding };
