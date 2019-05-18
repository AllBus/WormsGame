(function(){
'use strict';
/* Scala.js runtime support
 * Copyright 2013 LAMP/EPFL
 * Author: Sébastien Doeraene
 */

/* ---------------------------------- *
 * The top-level Scala.js environment *
 * ---------------------------------- */

// Where to send exports



// TODO Do not use global object detection, and rather export with actual `var` declarations
var $e = (typeof global === "object" && global && global["Object"] === Object) ? global : this;
// #3036 - convince GCC that $e must not be dce'ed away
this["__ScalaJSWorkaroundToRetainExportsInGCC"] = $e;


// Linking info - must be in sync with scala.scalajs.runtime.LinkingInfo
var $linkingInfo = {
  "semantics": {




    "asInstanceOfs": 1,








    "arrayIndexOutOfBounds": 1,










    "moduleInit": 2,





    "strictFloats": false,




    "productionMode": false

  },



  "assumingES6": false,

  "linkerVersion": "1.0.0-M6",
  "globalThis": this
};
Object["freeze"]($linkingInfo);
Object["freeze"]($linkingInfo["semantics"]);

// Snapshots of builtins and polyfills






var $imul = Math["imul"] || (function(a, b) {
  // See https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Math/imul
  var ah = (a >>> 16) & 0xffff;
  var al = a & 0xffff;
  var bh = (b >>> 16) & 0xffff;
  var bl = b & 0xffff;
  // the shift by 0 fixes the sign on the high part
  // the final |0 converts the unsigned value into a signed value
  return ((al * bl) + (((ah * bl + al * bh) << 16) >>> 0) | 0);
});

var $fround = Math["fround"] ||













































  (function(v) {
    return +v;
  });


var $clz32 = Math["clz32"] || (function(i) {
  // See Hacker's Delight, Section 5-3
  if (i === 0) return 32;
  var r = 1;
  if ((i & 0xffff0000) === 0) { i <<= 16; r += 16; };
  if ((i & 0xff000000) === 0) { i <<= 8; r += 8; };
  if ((i & 0xf0000000) === 0) { i <<= 4; r += 4; };
  if ((i & 0xc0000000) === 0) { i <<= 2; r += 2; };
  return r + (i >> 31);
});



// Cached instance of RuntimeLong for 0L
var $L0;


// identityHashCode support
var $lastIDHash = 0; // last value attributed to an id hash code



var $idHashCodeMap = typeof WeakMap !== "undefined" ? new WeakMap() : null;


// Core mechanism

function $makeIsArrayOfPrimitive(primitiveData) {
  return function(obj, depth) {
    return !!(obj && obj.$classData &&
      (obj.$classData.arrayDepth === depth) &&
      (obj.$classData.arrayBase === primitiveData));
  }
};


function $makeAsArrayOfPrimitive(isInstanceOfFunction, arrayEncodedName) {
  return function(obj, depth) {
    if (isInstanceOfFunction(obj, depth) || (obj === null))
      return obj;
    else
      $throwArrayCastException(obj, arrayEncodedName, depth);
  }
};


/** Encode a property name for runtime manipulation
  *  Usage:
  *    env.propertyName({someProp:0})
  *  Returns:
  *    "someProp"
  *  Useful when the property is renamed by a global optimizer (like Closure)
  *  but we must still get hold of a string of that name for runtime
  * reflection.
  */
function $propertyName(obj) {
  for (var prop in obj)
    return prop;
};

// Boxed Char











function $Char(c) {
  this.c = c;
};
$Char.prototype.toString = (function() {
  return String["fromCharCode"](this.c);
});


// Runtime functions

function $isScalaJSObject(obj) {
  return !!(obj && obj.$classData);
};


function $throwClassCastException(instance, classFullName) {




  throw new $c_sjsr_UndefinedBehaviorError().init___jl_Throwable(
    new $c_jl_ClassCastException().init___T(
      instance + " is not an instance of " + classFullName));

};

function $throwArrayCastException(instance, classArrayEncodedName, depth) {
  for (; depth; --depth)
    classArrayEncodedName = "[" + classArrayEncodedName;
  $throwClassCastException(instance, classArrayEncodedName);
};



function $throwArrayIndexOutOfBoundsException(i) {
  var msg = (i === null) ? null : ("" + i);



  throw new $c_sjsr_UndefinedBehaviorError().init___jl_Throwable(
    new $c_jl_ArrayIndexOutOfBoundsException().init___T(msg));

};


function $noIsInstance(instance) {
  throw new TypeError(
    "Cannot call isInstance() on a Class representing a raw JS trait/object");
};

function $makeNativeArrayWrapper(arrayClassData, nativeArray) {
  return new arrayClassData.constr(nativeArray);
};

function $newArrayObject(arrayClassData, lengths) {
  return $newArrayObjectInternal(arrayClassData, lengths, 0);
};

function $newArrayObjectInternal(arrayClassData, lengths, lengthIndex) {
  var result = new arrayClassData.constr(lengths[lengthIndex]);

  if (lengthIndex < lengths.length-1) {
    var subArrayClassData = arrayClassData.componentData;
    var subLengthIndex = lengthIndex+1;
    var underlying = result.u;
    for (var i = 0; i < underlying.length; i++) {
      underlying[i] = $newArrayObjectInternal(
        subArrayClassData, lengths, subLengthIndex);
    }
  }

  return result;
};

function $objectGetClass(instance) {
  switch (typeof instance) {
    case "string":
      return $d_T.getClassOf();
    case "number": {
      var v = instance | 0;
      if (v === instance) { // is the value integral?
        if ($isByte(v))
          return $d_jl_Byte.getClassOf();
        else if ($isShort(v))
          return $d_jl_Short.getClassOf();
        else
          return $d_jl_Integer.getClassOf();
      } else {
        if ($isFloat(instance))
          return $d_jl_Float.getClassOf();
        else
          return $d_jl_Double.getClassOf();
      }
    }
    case "boolean":
      return $d_jl_Boolean.getClassOf();
    case "undefined":
      return $d_sr_BoxedUnit.getClassOf();
    default:
      if (instance === null)
        return instance.getClass__jl_Class();

      else if ($is_sjsr_RuntimeLong(instance))



        return $d_jl_Long.getClassOf();
      else if ($isChar(instance))
        return $d_jl_Character.getClassOf();
      else if ($isScalaJSObject(instance))
        return instance.$classData.getClassOf();
      else
        return null; // Exception?
  }
};

function $dp_toString__T(instance) {
  if (instance === void 0)
    return "undefined";
  else
    return instance.toString();
};

function $dp_getClass__jl_Class(instance) {
  return $objectGetClass(instance);
};

function $dp_clone__O(instance) {
  if ($isScalaJSObject(instance) || (instance === null))
    return instance.clone__O();
  else
    throw new $c_jl_CloneNotSupportedException().init___();
};

function $dp_notify__V(instance) {
  // final and no-op in java.lang.Object
  if (instance === null)
    instance.notify__V();
};

function $dp_notifyAll__V(instance) {
  // final and no-op in java.lang.Object
  if (instance === null)
    instance.notifyAll__V();
};

function $dp_finalize__V(instance) {
  if ($isScalaJSObject(instance) || (instance === null))
    instance.finalize__V();
  // else no-op
};

function $dp_equals__O__Z(instance, rhs) {
  if ($isScalaJSObject(instance) || (instance === null))
    return instance.equals__O__Z(rhs);
  else if (typeof instance === "number")
    return $f_jl_Double__equals__O__Z(instance, rhs);




  else if ($isChar(instance))
    return $f_jl_Character__equals__O__Z(instance, rhs);
  else
    return instance === rhs;
};

function $dp_hashCode__I(instance) {
  switch (typeof instance) {
    case "string":
      return $f_T__hashCode__I(instance);
    case "number":
      return $f_jl_Double__hashCode__I(instance);
    case "boolean":
      return $f_jl_Boolean__hashCode__I(instance);
    case "undefined":
      return $f_sr_BoxedUnit__hashCode__I(instance);
    default:
      if ($isScalaJSObject(instance) || instance === null)
        return instance.hashCode__I();




      else if ($isChar(instance))
        return $f_jl_Character__hashCode__I(instance);
      else
        return $systemIdentityHashCode(instance);
  }
};

function $dp_compareTo__O__I(instance, rhs) {
  switch (typeof instance) {
    case "string":
      return $f_T__compareTo__O__I(instance, rhs);
    case "number":
      return $f_jl_Double__compareTo__O__I(instance, rhs);
    case "boolean":
      return $f_jl_Boolean__compareTo__O__I(instance, rhs);
    default:
      if ($isChar(instance))
        return $f_jl_Character__compareTo__O__I(instance, rhs);




      else
        return instance.compareTo__O__I(rhs);
  }
};

function $dp_length__I(instance) {
  if (typeof(instance) === "string")
    return $f_T__length__I(instance);
  else
    return instance.length__I();
};

function $dp_charAt__I__C(instance, index) {
  if (typeof(instance) === "string")
    return $f_T__charAt__I__C(instance, index);
  else
    return instance.charAt__I__C(index);
};

function $dp_subSequence__I__I__jl_CharSequence(instance, start, end) {
  if (typeof(instance) === "string")
    return $f_T__subSequence__I__I__jl_CharSequence(instance, start, end);
  else
    return instance.subSequence__I__I__jl_CharSequence(start, end);
};

function $dp_byteValue__B(instance) {
  if (typeof instance === "number")
    return $f_jl_Double__byteValue__B(instance);




  else
    return instance.byteValue__B();
};
function $dp_shortValue__S(instance) {
  if (typeof instance === "number")
    return $f_jl_Double__shortValue__S(instance);




  else
    return instance.shortValue__S();
};
function $dp_intValue__I(instance) {
  if (typeof instance === "number")
    return $f_jl_Double__intValue__I(instance);




  else
    return instance.intValue__I();
};
function $dp_longValue__J(instance) {
  if (typeof instance === "number")
    return $f_jl_Double__longValue__J(instance);




  else
    return instance.longValue__J();
};
function $dp_floatValue__F(instance) {
  if (typeof instance === "number")
    return $f_jl_Double__floatValue__F(instance);




  else
    return instance.floatValue__F();
};
function $dp_doubleValue__D(instance) {
  if (typeof instance === "number")
    return $f_jl_Double__doubleValue__D(instance);




  else
    return instance.doubleValue__D();
};

function $doubleToInt(x) {
  return (x > 2147483647) ? (2147483647) : ((x < -2147483648) ? -2147483648 : (x | 0));
};




















/** Instantiates a JS object with variadic arguments to the constructor. */
function $newJSObjectWithVarargs(ctor, args) {
  // This basically emulates the ECMAScript specification for 'new'.
  var instance = Object["create"](ctor.prototype);
  var result = ctor["apply"](instance, args);
  switch (typeof result) {
    case "string": case "number": case "boolean": case "undefined": case "symbol":
      return instance;
    default:
      return result === null ? instance : result;
  }
};

function $resolveSuperRef(superClass, propName) {
  var getPrototypeOf = Object["getPrototypeOf"];
  var getOwnPropertyDescriptor = Object["getOwnPropertyDescriptor"];

  var superProto = superClass.prototype;
  while (superProto !== null) {
    var desc = getOwnPropertyDescriptor(superProto, propName);
    if (desc !== void 0)
      return desc;
    superProto = getPrototypeOf(superProto);
  }

  return void 0;
};

function $superGet(superClass, self, propName) {
  var desc = $resolveSuperRef(superClass, propName);
  if (desc !== void 0) {
    var getter = desc["get"];
    if (getter !== void 0)
      return getter["call"](self);
    else
      return desc["value"];
  }
  return void 0;
};

function $superSet(superClass, self, propName, value) {
  var desc = $resolveSuperRef(superClass, propName);
  if (desc !== void 0) {
    var setter = desc["set"];
    if (setter !== void 0) {
      setter["call"](self, value);
      return void 0;
    }
  }
  throw new TypeError("super has no setter '" + propName + "'.");
};







function $systemArraycopy(src, srcPos, dest, destPos, length) {
  var srcu = src.u;
  var destu = dest.u;


  if (srcPos < 0 || destPos < 0 || length < 0 ||
      (srcPos > ((srcu.length - length) | 0)) ||
      (destPos > ((destu.length - length) | 0))) {
    $throwArrayIndexOutOfBoundsException(null);
  }


  if (srcu !== destu || destPos < srcPos || (((srcPos + length) | 0) < destPos)) {
    for (var i = 0; i < length; i = (i + 1) | 0)
      destu[(destPos + i) | 0] = srcu[(srcPos + i) | 0];
  } else {
    for (var i = (length - 1) | 0; i >= 0; i = (i - 1) | 0)
      destu[(destPos + i) | 0] = srcu[(srcPos + i) | 0];
  }
};

var $systemIdentityHashCode =

  ($idHashCodeMap !== null) ?

  (function(obj) {
    switch (typeof obj) {
      case "string": case "number": case "bigint": case "boolean": case "undefined":
        return $dp_hashCode__I(obj);
      default:
        if (obj === null) {
          return 0;
        } else {
          var hash = $idHashCodeMap["get"](obj);
          if (hash === void 0) {
            hash = ($lastIDHash + 1) | 0;
            $lastIDHash = hash;
            $idHashCodeMap["set"](obj, hash);
          }
          return hash;
        }
    }

  }) :
  (function(obj) {
    switch (typeof obj) {
      case "string": case "number": case "bigint": case "boolean": case "undefined":
        return $dp_hashCode__I(obj);
      default:
        if ($isScalaJSObject(obj)) {
          var hash = obj["$idHashCode$0"];
          if (hash !== void 0) {
            return hash;
          } else if (!Object["isSealed"](obj)) {
            hash = ($lastIDHash + 1) | 0;
            $lastIDHash = hash;
            obj["$idHashCode$0"] = hash;
            return hash;
          } else {
            return 42;
          }
        } else if (obj === null) {
          return 0;
        } else {
          return 42;
        }
    }

  });

// is/as for hijacked boxed classes (the non-trivial ones)

function $isChar(v) {
  return v instanceof $Char;
};

function $isByte(v) {
  return typeof v === "number" && (v << 24 >> 24) === v && 1/v !== 1/-0;
};

function $isShort(v) {
  return typeof v === "number" && (v << 16 >> 16) === v && 1/v !== 1/-0;
};

function $isInt(v) {
  return typeof v === "number" && (v | 0) === v && 1/v !== 1/-0;
};







function $isFloat(v) {



  return typeof v === "number";

};


function $asUnit(v) {
  if (v === void 0 || v === null)
    return v;
  else
    $throwClassCastException(v, "scala.runtime.BoxedUnit");
};

function $asBoolean(v) {
  if (typeof v === "boolean" || v === null)
    return v;
  else
    $throwClassCastException(v, "java.lang.Boolean");
};

function $asChar(v) {
  if (v instanceof $Char || v === null)
    return v;
  else
    $throwClassCastException(v, "java.lang.Character");
};

function $asByte(v) {
  if ($isByte(v) || v === null)
    return v;
  else
    $throwClassCastException(v, "java.lang.Byte");
};

function $asShort(v) {
  if ($isShort(v) || v === null)
    return v;
  else
    $throwClassCastException(v, "java.lang.Short");
};

function $asInt(v) {
  if ($isInt(v) || v === null)
    return v;
  else
    $throwClassCastException(v, "java.lang.Integer");
};










function $asFloat(v) {
  if ($isFloat(v) || v === null)
    return v;
  else
    $throwClassCastException(v, "java.lang.Float");
};

function $asDouble(v) {
  if (typeof v === "number" || v === null)
    return v;
  else
    $throwClassCastException(v, "java.lang.Double");
};


// Boxes

function $bC(c) {
  return new $Char(c);
}
var $bC0 = $bC(0);

// Unboxes


function $uZ(value) {
  return !!$asBoolean(value);
};
function $uC(value) {
  return null === value ? 0 : $asChar(value).c;
};
function $uB(value) {
  return $asByte(value) | 0;
};
function $uS(value) {
  return $asShort(value) | 0;
};
function $uI(value) {
  return $asInt(value) | 0;
};
function $uJ(value) {



  return null === value ? $L0 : $as_sjsr_RuntimeLong(value);

};
function $uF(value) {
  /* Here, it is fine to use + instead of fround, because asFloat already
   * ensures that the result is either null or a float.
   */
  return +$asFloat(value);
};
function $uD(value) {
  return +$asDouble(value);
};













// TypeArray conversions

function $byteArray2TypedArray(value) { return new Int8Array(value.u); };
function $shortArray2TypedArray(value) { return new Int16Array(value.u); };
function $charArray2TypedArray(value) { return new Uint16Array(value.u); };
function $intArray2TypedArray(value) { return new Int32Array(value.u); };
function $floatArray2TypedArray(value) { return new Float32Array(value.u); };
function $doubleArray2TypedArray(value) { return new Float64Array(value.u); };

function $typedArray2ByteArray(value) {
  var arrayClassData = $d_B.getArrayOf();
  return new arrayClassData.constr(new Int8Array(value));
};
function $typedArray2ShortArray(value) {
  var arrayClassData = $d_S.getArrayOf();
  return new arrayClassData.constr(new Int16Array(value));
};
function $typedArray2CharArray(value) {
  var arrayClassData = $d_C.getArrayOf();
  return new arrayClassData.constr(new Uint16Array(value));
};
function $typedArray2IntArray(value) {
  var arrayClassData = $d_I.getArrayOf();
  return new arrayClassData.constr(new Int32Array(value));
};
function $typedArray2FloatArray(value) {
  var arrayClassData = $d_F.getArrayOf();
  return new arrayClassData.constr(new Float32Array(value));
};
function $typedArray2DoubleArray(value) {
  var arrayClassData = $d_D.getArrayOf();
  return new arrayClassData.constr(new Float64Array(value));
};

// TypeData class


/** @constructor */
function $TypeData() {




  // Runtime support
  this.constr = void 0;
  this.parentData = void 0;
  this.ancestors = null;
  this.componentData = null;
  this.arrayBase = null;
  this.arrayDepth = 0;
  this.zero = null;
  this.arrayEncodedName = "";
  this._classOf = void 0;
  this._arrayOf = void 0;
  this.isArrayOf = void 0;

  // java.lang.Class support
  this["name"] = "";
  this["isPrimitive"] = false;
  this["isInterface"] = false;
  this["isArrayClass"] = false;
  this["isRawJSType"] = false;
  this["isInstance"] = void 0;
};


$TypeData.prototype.initPrim = function(



    zero, arrayEncodedName, displayName) {
  // Runtime support
  this.ancestors = {};
  this.componentData = null;
  this.zero = zero;
  this.arrayEncodedName = arrayEncodedName;
  this.isArrayOf = function(obj, depth) { return false; };

  // java.lang.Class support
  this["name"] = displayName;
  this["isPrimitive"] = true;
  this["isInstance"] = function(obj) { return false; };

  return this;
};


$TypeData.prototype.initClass = function(



    internalNameObj, isInterface, fullName,
    ancestors, isRawJSType, parentData, isInstance, isArrayOf) {
  var internalName = $propertyName(internalNameObj);

  isInstance = isInstance || function(obj) {
    return !!(obj && obj.$classData && obj.$classData.ancestors[internalName]);
  };

  isArrayOf = isArrayOf || function(obj, depth) {
    return !!(obj && obj.$classData && (obj.$classData.arrayDepth === depth)
      && obj.$classData.arrayBase.ancestors[internalName])
  };

  // Runtime support
  this.parentData = parentData;
  this.ancestors = ancestors;
  this.arrayEncodedName = "L"+fullName+";";
  this.isArrayOf = isArrayOf;

  // java.lang.Class support
  this["name"] = fullName;
  this["isInterface"] = isInterface;
  this["isRawJSType"] = !!isRawJSType;
  this["isInstance"] = isInstance;

  return this;
};


$TypeData.prototype.initArray = function(



    componentData) {
  // The constructor




  // The zero for the Long runtime representation
  // is a special case here, since the class has not
  // been defined yet when this constructor is called.
  var componentZero0 = componentData.zero;
  var componentZero = (componentZero0 == "longZero") ? $L0 : componentZero0;



  /** @constructor */
  var ArrayClass = function(arg) {
    if (typeof(arg) === "number") {
      // arg is the length of the array
      this.u = new Array(arg);
      for (var i = 0; i < arg; i++)
        this.u[i] = componentZero;
    } else {
      // arg is a native array that we wrap
      this.u = arg;
    }
  }
  ArrayClass.prototype = new $h_O;
  ArrayClass.prototype.constructor = ArrayClass;


  ArrayClass.prototype.get = function(i) {
    if (i < 0 || i >= this.u.length)
      $throwArrayIndexOutOfBoundsException(i);
    return this.u[i];
  };
  ArrayClass.prototype.set = function(i, v) {
    if (i < 0 || i >= this.u.length)
      $throwArrayIndexOutOfBoundsException(i);
    this.u[i] = v;
  };


  ArrayClass.prototype.clone__O = function() {
    if (this.u instanceof Array)
      return new ArrayClass(this.u["slice"](0));
    else
      // The underlying Array is a TypedArray
      return new ArrayClass(new this.u.constructor(this.u));
  };






































  ArrayClass.prototype.$classData = this;

  // Don't generate reflective call proxies. The compiler special cases
  // reflective calls to methods on scala.Array

  // The data

  var encodedName = "[" + componentData.arrayEncodedName;
  var componentBase = componentData.arrayBase || componentData;
  var arrayDepth = componentData.arrayDepth + 1;

  var isInstance = function(obj) {
    return componentBase.isArrayOf(obj, arrayDepth);
  }

  // Runtime support
  this.constr = ArrayClass;
  this.parentData = $d_O;
  this.ancestors = {O: 1, jl_Cloneable: 1, Ljava_io_Serializable: 1};
  this.componentData = componentData;
  this.arrayBase = componentBase;
  this.arrayDepth = arrayDepth;
  this.zero = null;
  this.arrayEncodedName = encodedName;
  this._classOf = undefined;
  this._arrayOf = undefined;
  this.isArrayOf = undefined;

  // java.lang.Class support
  this["name"] = encodedName;
  this["isPrimitive"] = false;
  this["isInterface"] = false;
  this["isArrayClass"] = true;
  this["isInstance"] = isInstance;

  return this;
};


$TypeData.prototype.getClassOf = function() {



  if (!this._classOf)
    this._classOf = new $c_jl_Class(this);
  return this._classOf;
};


$TypeData.prototype.getArrayOf = function() {



  if (!this._arrayOf)
    this._arrayOf = new $TypeData().initArray(this);
  return this._arrayOf;
};

// java.lang.Class support


$TypeData.prototype["isAssignableFrom"] = function(that) {



  if (this["isPrimitive"] || that["isPrimitive"]) {
    return this === that;
  } else {
    var thatFakeInstance;
    if (that === $d_T)
      thatFakeInstance = "some string";
    else if (that === $d_jl_Boolean)
      thatFakeInstance = false;
    else if (that === $d_jl_Byte ||
             that === $d_jl_Short ||
             that === $d_jl_Integer ||
             that === $d_jl_Float ||
             that === $d_jl_Double)
      thatFakeInstance = 0;
    else if (that === $d_jl_Long)



      thatFakeInstance = $L0;

    else if (that === $d_sr_BoxedUnit)
      thatFakeInstance = void 0;
    else
      thatFakeInstance = {$classData: that};
    return this["isInstance"](thatFakeInstance);
  }
};


$TypeData.prototype["getSuperclass"] = function() {



  return this.parentData ? this.parentData.getClassOf() : null;
};


$TypeData.prototype["getComponentType"] = function() {



  return this.componentData ? this.componentData.getClassOf() : null;
};


$TypeData.prototype["newArrayOfThisClass"] = function(lengths) {



  var arrayClassData = this;
  for (var i = 0; i < lengths.length; i++)
    arrayClassData = arrayClassData.getArrayOf();
  return $newArrayObject(arrayClassData, lengths);
};




// Create primitive types

var $d_V = new $TypeData().initPrim(undefined, "V", "void");
var $d_Z = new $TypeData().initPrim(false, "Z", "boolean");
var $d_C = new $TypeData().initPrim(0, "C", "char");
var $d_B = new $TypeData().initPrim(0, "B", "byte");
var $d_S = new $TypeData().initPrim(0, "S", "short");
var $d_I = new $TypeData().initPrim(0, "I", "int");



var $d_J = new $TypeData().initPrim("longZero", "J", "long");

var $d_F = new $TypeData().initPrim(0.0, "F", "float");
var $d_D = new $TypeData().initPrim(0.0, "D", "double");

// Instance tests for array of primitives

var $isArrayOf_Z = $makeIsArrayOfPrimitive($d_Z);
$d_Z.isArrayOf = $isArrayOf_Z;

var $isArrayOf_C = $makeIsArrayOfPrimitive($d_C);
$d_C.isArrayOf = $isArrayOf_C;

var $isArrayOf_B = $makeIsArrayOfPrimitive($d_B);
$d_B.isArrayOf = $isArrayOf_B;

var $isArrayOf_S = $makeIsArrayOfPrimitive($d_S);
$d_S.isArrayOf = $isArrayOf_S;

var $isArrayOf_I = $makeIsArrayOfPrimitive($d_I);
$d_I.isArrayOf = $isArrayOf_I;

var $isArrayOf_J = $makeIsArrayOfPrimitive($d_J);
$d_J.isArrayOf = $isArrayOf_J;

var $isArrayOf_F = $makeIsArrayOfPrimitive($d_F);
$d_F.isArrayOf = $isArrayOf_F;

var $isArrayOf_D = $makeIsArrayOfPrimitive($d_D);
$d_D.isArrayOf = $isArrayOf_D;


// asInstanceOfs for array of primitives
var $asArrayOf_Z = $makeAsArrayOfPrimitive($isArrayOf_Z, "Z");
var $asArrayOf_C = $makeAsArrayOfPrimitive($isArrayOf_C, "C");
var $asArrayOf_B = $makeAsArrayOfPrimitive($isArrayOf_B, "B");
var $asArrayOf_S = $makeAsArrayOfPrimitive($isArrayOf_S, "S");
var $asArrayOf_I = $makeAsArrayOfPrimitive($isArrayOf_I, "I");
var $asArrayOf_J = $makeAsArrayOfPrimitive($isArrayOf_J, "J");
var $asArrayOf_F = $makeAsArrayOfPrimitive($isArrayOf_F, "F");
var $asArrayOf_D = $makeAsArrayOfPrimitive($isArrayOf_D, "D");

function $is_F0(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.F0)))
}
function $as_F0(obj) {
  return (($is_F0(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.Function0"))
}
function $isArrayOf_F0(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.F0)))
}
function $asArrayOf_F0(obj, depth) {
  return (($isArrayOf_F0(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.Function0;", depth))
}
function $f_Lcom_kos_wormpad_WormGameConst__$$init$__V($thiz) {
  $thiz.LEVEL$undWORM$undHEALTH$undSPEED$undUPDATE$1 = 0.1;
  $thiz.ENERGY$undBURGER$1 = 12;
  $thiz.ENERGY$undBOMB$1 = (-25);
  $thiz.RANDOM$undBURGER$1 = 100;
  $thiz.RANDOM$undBOMB$1 = 300;
  $thiz.RANDOM$undHIDE$undEAT$1 = 200;
  $thiz.GAME$undBOARD$1 = new $c_Lcom_kos_wormpad_geometry_RectF((-2000.0), (-1000.0), 2000.0, 1000.0)
}
function $f_Lcom_kos_wormpad_game_WormTextures__$$init$__V($thiz) {
  $thiz.backgroundPath$1 = "images/background/";
  $thiz.heroesPath$1 = "images/heroes/";
  $thiz.imgCloud$1 = $m_Lcom_kos_wormpad_game_helpers_JSHelper$().loadImage__T__Lorg_scalajs_dom_raw_HTMLImageElement(($thiz.backgroundPath$1 + "cloud.svg"));
  var this$4 = $m_sci_Seq$();
  var array = [new $c_Lcom_kos_wormpad_game_BackgroundLayer(($thiz.backgroundPath$1 + "earth_layer2.svg"), 940.0, 200.0, 0.0, 230.0, (-0.065), 0.01), new $c_Lcom_kos_wormpad_game_BackgroundLayer(($thiz.backgroundPath$1 + "earth_layer2.svg"), 940.0, 200.0, 0.0, 200.0, (-0.125), 0.01), new $c_Lcom_kos_wormpad_game_BackgroundLayer(($thiz.backgroundPath$1 + "earth_layer1.svg"), 940.0, 200.0, 0.0, 150.0, (-0.25), 0.1)];
  var elems = new $c_sjsr_WrappedVarArgs(array);
  $thiz.imgLayers$1 = $as_sci_Seq(this$4.from__sc_IterableOnce__sc_SeqOps(elems));
  var this$53 = $m_s_Predef$().Map$3;
  var array$1 = [new $c_T2(0, "none"), new $c_T2(101, "bomb"), new $c_T2(201, "burger"), new $c_T2(202, "king_burger"), new $c_T2(301, "capsule"), new $c_T2(302, "capsule_worm"), new $c_T2(303, "capsule_white"), new $c_T2(401, "cloud"), new $c_T2(501, "meteor_rain"), new $c_T2(601, "mirage"), new $c_T2(602, "underground_lak"), new $c_T2(701, "ship_with_burger"), new $c_T2(801, "povar"), new $c_T2(901, "worm"), new $c_T2(902, "worm_tail")];
  var elems$1 = new $c_sjsr_WrappedVarArgs(array$1);
  $thiz.com$kos$wormpad$game$WormTextures$$texNames$1 = this$53.from__sc_IterableOnce__sci_Map(elems$1);
  var this$57 = $m_sci_Seq$();
  var array$2 = [0, 101, 201, 202, 301, 302, 303, 401, 501, 601, 602, 701, 801, 901, 902];
  var elems$2 = new $c_sjsr_WrappedVarArgs(array$2);
  var jsx$1 = $as_sc_IterableOnceOps(this$57.from__sc_IterableOnce__sc_SeqOps(elems$2).map__F1__O(new $c_sjsr_AnonFunction1((function($this) {
    return (function(heroKind$2) {
      var heroKind = $uI(heroKind$2);
      return $f_Lcom_kos_wormpad_game_WormTextures__createHeroTex__I__T2($this, heroKind)
    })
  })($thiz))));
  var this$59 = $m_s_Predef$$eq$colon$eq$();
  $thiz.heroTextures$1 = jsx$1.toMap__s_Predef$$less$colon$less__sci_Map(this$59.singleton$1);
  $thiz.cloudWidth$1 = 440;
  $thiz.cloudHeight$1 = 220
}
function $f_Lcom_kos_wormpad_game_WormTextures__createHeroTex__I__T2($thiz, heroKind) {
  var y = new $c_Lcom_kos_wormpad_game_HeroTexture(((("" + $thiz.heroesPath$1) + $thiz.com$kos$wormpad$game$WormTextures$$texNames$1.apply__O__O(heroKind)) + ".svg"));
  return new $c_T2(heroKind, y)
}
/** @constructor */
function $c_O() {
  /*<skip>*/
}
/** @constructor */
function $h_O() {
  /*<skip>*/
}
$h_O.prototype = $c_O.prototype;
$c_O.prototype.init___ = (function() {
  return this
});
$c_O.prototype.equals__O__Z = (function(that) {
  return (this === that)
});
$c_O.prototype.toString__T = (function() {
  var jsx$1 = $objectGetClass(this).getName__T();
  var i = this.hashCode__I();
  return ((jsx$1 + "@") + $as_T($uD((i >>> 0)).toString(16)))
});
$c_O.prototype.hashCode__I = (function() {
  return $systemIdentityHashCode(this)
});
$c_O.prototype.toString = (function() {
  return this.toString__T()
});
function $is_O(obj) {
  return (obj !== null)
}
function $as_O(obj) {
  return obj
}
function $isArrayOf_O(obj, depth) {
  var data = (obj && obj.$classData);
  if ((!data)) {
    return false
  } else {
    var arrayDepth = (data.arrayDepth || 0);
    return ((!(arrayDepth < depth)) && ((arrayDepth > depth) || (!data.arrayBase.isPrimitive)))
  }
}
function $asArrayOf_O(obj, depth) {
  return (($isArrayOf_O(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.Object;", depth))
}
var $d_O = new $TypeData().initClass({
  O: 0
}, false, "java.lang.Object", {
  O: 1
}, (void 0), (void 0), $is_O, $isArrayOf_O);
$c_O.prototype.$classData = $d_O;
function $is_sc_IterableOnce(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_IterableOnce)))
}
function $as_sc_IterableOnce(obj) {
  return (($is_sc_IterableOnce(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.IterableOnce"))
}
function $isArrayOf_sc_IterableOnce(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_IterableOnce)))
}
function $asArrayOf_sc_IterableOnce(obj, depth) {
  return (($isArrayOf_sc_IterableOnce(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.IterableOnce;", depth))
}
function $f_sc_IterableOnceOps__exists__F1__Z($thiz, p) {
  var res = false;
  var it = $as_sc_IterableOnce($thiz).iterator__sc_Iterator();
  while (((!res) && it.hasNext__Z())) {
    res = $uZ(p.apply__O__O(it.next__O()))
  };
  return res
}
function $f_sc_IterableOnceOps__isEmpty__Z($thiz) {
  return (!$as_sc_IterableOnce($thiz).iterator__sc_Iterator().hasNext__Z())
}
function $f_sc_IterableOnceOps__mkString__T__T__T__T($thiz, start, sep, end) {
  if ($thiz.isEmpty__Z()) {
    return (("" + start) + end)
  } else {
    var this$1 = $thiz.addString__scm_StringBuilder__T__T__T__scm_StringBuilder(new $c_scm_StringBuilder().init___(), start, sep, end);
    return this$1.underlying$4.java$lang$StringBuilder$$content$f
  }
}
function $f_sc_IterableOnceOps__forall__F1__Z($thiz, p) {
  var res = true;
  var it = $as_sc_IterableOnce($thiz).iterator__sc_Iterator();
  while ((res && it.hasNext__Z())) {
    res = $uZ(p.apply__O__O(it.next__O()))
  };
  return res
}
function $f_sc_IterableOnceOps__foreach__F1__V($thiz, f) {
  var it = $as_sc_IterableOnce($thiz).iterator__sc_Iterator();
  while (it.hasNext__Z()) {
    f.apply__O__O(it.next__O())
  }
}
function $f_sc_IterableOnceOps__foldLeft__O__F2__O($thiz, z, op) {
  var result = z;
  var it = $as_sc_IterableOnce($thiz).iterator__sc_Iterator();
  while (it.hasNext__Z()) {
    result = op.apply__O__O__O(result, it.next__O())
  };
  return result
}
function $f_sc_IterableOnceOps__copyToArray__O__I__I($thiz, xs, start) {
  var xsLen = $m_sr_ScalaRunTime$().array$undlength__O__I(xs);
  var it = $as_sc_IterableOnce($thiz).iterator__sc_Iterator();
  var i = start;
  while (((i < xsLen) && it.hasNext__Z())) {
    $m_sr_ScalaRunTime$().array$undupdate__O__I__O__V(xs, i, it.next__O());
    i = ((1 + i) | 0)
  };
  return ((i - start) | 0)
}
function $f_sc_IterableOnceOps__size__I($thiz) {
  if (($thiz.knownSize__I() >= 0)) {
    return $thiz.knownSize__I()
  } else {
    var it = $as_sc_IterableOnce($thiz).iterator__sc_Iterator();
    var len = 0;
    while (it.hasNext__Z()) {
      len = ((1 + len) | 0);
      it.next__O()
    };
    return len
  }
}
function $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder($thiz, b, start, sep, end) {
  var jsb = b.underlying$4;
  if (($uI(start.length) !== 0)) {
    jsb.java$lang$StringBuilder$$content$f = (("" + jsb.java$lang$StringBuilder$$content$f) + start)
  };
  var it = $as_sc_IterableOnce($thiz).iterator__sc_Iterator();
  if (it.hasNext__Z()) {
    var obj = it.next__O();
    jsb.java$lang$StringBuilder$$content$f = (("" + jsb.java$lang$StringBuilder$$content$f) + obj);
    while (it.hasNext__Z()) {
      jsb.java$lang$StringBuilder$$content$f = (("" + jsb.java$lang$StringBuilder$$content$f) + sep);
      var obj$1 = it.next__O();
      jsb.java$lang$StringBuilder$$content$f = (("" + jsb.java$lang$StringBuilder$$content$f) + obj$1)
    }
  };
  if (($uI(end.length) !== 0)) {
    jsb.java$lang$StringBuilder$$content$f = (("" + jsb.java$lang$StringBuilder$$content$f) + end)
  };
  return b
}
function $f_sc_IterableOnceOps__toArray__s_reflect_ClassTag__O($thiz, evidence$2) {
  if (($thiz.knownSize__I() >= 0)) {
    var destination = evidence$2.newArray__I__O($thiz.knownSize__I());
    $thiz.copyToArray__O__I__I(destination, 0);
    return destination
  } else {
    var this$1 = $m_scm_ArrayBuffer$().from__sc_IterableOnce__scm_ArrayBuffer($as_sc_IterableOnce($thiz));
    return $f_sc_IterableOnceOps__toArray__s_reflect_ClassTag__O(this$1, evidence$2)
  }
}
function $f_sc_IterableOnceOps__sum__s_math_Numeric__O($thiz, num) {
  return $thiz.foldLeft__O__F2__O(0, new $c_sjsr_AnonFunction2((function($this, num$1) {
    return (function(x$2, y$2) {
      var x = $uI(x$2);
      var y = $uI(y$2);
      return $f_s_math_Numeric$IntIsIntegral__plus__I__I__I(num$1, x, y)
    })
  })($thiz, num)))
}
function $is_sc_IterableOnceOps(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_IterableOnceOps)))
}
function $as_sc_IterableOnceOps(obj) {
  return (($is_sc_IterableOnceOps(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.IterableOnceOps"))
}
function $isArrayOf_sc_IterableOnceOps(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_IterableOnceOps)))
}
function $asArrayOf_sc_IterableOnceOps(obj, depth) {
  return (($isArrayOf_sc_IterableOnceOps(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.IterableOnceOps;", depth))
}
function $f_scg_BitOperations$Int__unsignedCompare__I__I__Z($thiz, i, j) {
  return (((i < j) !== (i < 0)) !== (j < 0))
}
function $f_sci_VectorPointer__copyOf__AO__AO($thiz, a) {
  var copy = $newArrayObject($d_O.getArrayOf(), [a.u.length]);
  $systemArraycopy(a, 0, copy, 0, a.u.length);
  return copy
}
function $f_sci_VectorPointer__preClean__I__V($thiz, depth) {
  $thiz.depth$und$eq__I__V(depth);
  var x1 = (((-1) + depth) | 0);
  switch (x1) {
    case 0: {
      $thiz.display1$und$eq__AO__V(null);
      $thiz.display2$und$eq__AO__V(null);
      $thiz.display3$und$eq__AO__V(null);
      $thiz.display4$und$eq__AO__V(null);
      $thiz.display5$und$eq__AO__V(null);
      break
    }
    case 1: {
      $thiz.display2$und$eq__AO__V(null);
      $thiz.display3$und$eq__AO__V(null);
      $thiz.display4$und$eq__AO__V(null);
      $thiz.display5$und$eq__AO__V(null);
      break
    }
    case 2: {
      $thiz.display3$und$eq__AO__V(null);
      $thiz.display4$und$eq__AO__V(null);
      $thiz.display5$und$eq__AO__V(null);
      break
    }
    case 3: {
      $thiz.display4$und$eq__AO__V(null);
      $thiz.display5$und$eq__AO__V(null);
      break
    }
    case 4: {
      $thiz.display5$und$eq__AO__V(null);
      break
    }
    case 5: {
      break
    }
    default: {
      throw new $c_s_MatchError(x1)
    }
  }
}
function $f_sci_VectorPointer__gotoNextBlockStart__I__I__V($thiz, index, xor) {
  if ((xor < 1024)) {
    $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get((31 & ((index >>> 5) | 0))), 1))
  } else if ((xor < 32768)) {
    $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((index >>> 10) | 0))), 1));
    $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get(0), 1))
  } else if ((xor < 1048576)) {
    $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get((31 & ((index >>> 15) | 0))), 1));
    $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get(0), 1));
    $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get(0), 1))
  } else if ((xor < 33554432)) {
    $thiz.display3$und$eq__AO__V($asArrayOf_O($thiz.display4__AO().get((31 & ((index >>> 20) | 0))), 1));
    $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get(0), 1));
    $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get(0), 1));
    $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get(0), 1))
  } else if ((xor < 1073741824)) {
    $thiz.display4$und$eq__AO__V($asArrayOf_O($thiz.display5__AO().get((31 & ((index >>> 25) | 0))), 1));
    $thiz.display3$und$eq__AO__V($asArrayOf_O($thiz.display4__AO().get(0), 1));
    $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get(0), 1));
    $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get(0), 1));
    $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get(0), 1))
  } else {
    throw new $c_jl_IllegalArgumentException().init___()
  }
}
function $f_sci_VectorPointer__gotoFreshPosWritable1__I__I__I__V($thiz, oldIndex, newIndex, xor) {
  $f_sci_VectorPointer__stabilize__I__V($thiz, oldIndex);
  $f_sci_VectorPointer__gotoFreshPosWritable0__I__I__I__V($thiz, oldIndex, newIndex, xor)
}
function $f_sci_VectorPointer__getElem__I__I__O($thiz, index, xor) {
  if ((xor < 32)) {
    return $thiz.display0__AO().get((31 & index))
  } else if ((xor < 1024)) {
    return $asArrayOf_O($thiz.display1__AO().get((31 & ((index >>> 5) | 0))), 1).get((31 & index))
  } else if ((xor < 32768)) {
    return $asArrayOf_O($asArrayOf_O($thiz.display2__AO().get((31 & ((index >>> 10) | 0))), 1).get((31 & ((index >>> 5) | 0))), 1).get((31 & index))
  } else if ((xor < 1048576)) {
    return $asArrayOf_O($asArrayOf_O($asArrayOf_O($thiz.display3__AO().get((31 & ((index >>> 15) | 0))), 1).get((31 & ((index >>> 10) | 0))), 1).get((31 & ((index >>> 5) | 0))), 1).get((31 & index))
  } else if ((xor < 33554432)) {
    return $asArrayOf_O($asArrayOf_O($asArrayOf_O($asArrayOf_O($thiz.display4__AO().get((31 & ((index >>> 20) | 0))), 1).get((31 & ((index >>> 15) | 0))), 1).get((31 & ((index >>> 10) | 0))), 1).get((31 & ((index >>> 5) | 0))), 1).get((31 & index))
  } else if ((xor < 1073741824)) {
    return $asArrayOf_O($asArrayOf_O($asArrayOf_O($asArrayOf_O($asArrayOf_O($thiz.display5__AO().get((31 & ((index >>> 25) | 0))), 1).get((31 & ((index >>> 20) | 0))), 1).get((31 & ((index >>> 15) | 0))), 1).get((31 & ((index >>> 10) | 0))), 1).get((31 & ((index >>> 5) | 0))), 1).get((31 & index))
  } else {
    throw new $c_jl_IllegalArgumentException().init___()
  }
}
function $f_sci_VectorPointer__gotoFreshPosWritable0__I__I__I__V($thiz, oldIndex, newIndex, xor) {
  if ((xor >= 32)) {
    if ((xor < 1024)) {
      if (($thiz.depth__I() === 1)) {
        $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
        $thiz.display1__AO().set((31 & ((oldIndex >>> 5) | 0)), $thiz.display0__AO());
        $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
      };
      $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
    } else if ((xor < 32768)) {
      if (($thiz.depth__I() === 2)) {
        $thiz.display2$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
        $thiz.display2__AO().set((31 & ((oldIndex >>> 10) | 0)), $thiz.display1__AO());
        $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
      };
      $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((newIndex >>> 10) | 0))), 1));
      if (($thiz.display1__AO() === null)) {
        $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
    } else if ((xor < 1048576)) {
      if (($thiz.depth__I() === 3)) {
        $thiz.display3$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
        $thiz.display3__AO().set((31 & ((oldIndex >>> 15) | 0)), $thiz.display2__AO());
        $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
      };
      $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get((31 & ((newIndex >>> 15) | 0))), 1));
      if (($thiz.display2__AO() === null)) {
        $thiz.display2$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((newIndex >>> 10) | 0))), 1));
      if (($thiz.display1__AO() === null)) {
        $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
    } else if ((xor < 33554432)) {
      if (($thiz.depth__I() === 4)) {
        $thiz.display4$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
        $thiz.display4__AO().set((31 & ((oldIndex >>> 20) | 0)), $thiz.display3__AO());
        $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
      };
      $thiz.display3$und$eq__AO__V($asArrayOf_O($thiz.display4__AO().get((31 & ((newIndex >>> 20) | 0))), 1));
      if (($thiz.display3__AO() === null)) {
        $thiz.display3$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get((31 & ((newIndex >>> 15) | 0))), 1));
      if (($thiz.display2__AO() === null)) {
        $thiz.display2$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((newIndex >>> 10) | 0))), 1));
      if (($thiz.display1__AO() === null)) {
        $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
    } else if ((xor < 1073741824)) {
      if (($thiz.depth__I() === 5)) {
        $thiz.display5$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
        $thiz.display5__AO().set((31 & ((oldIndex >>> 25) | 0)), $thiz.display4__AO());
        $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
      };
      $thiz.display4$und$eq__AO__V($asArrayOf_O($thiz.display5__AO().get((31 & ((newIndex >>> 25) | 0))), 1));
      if (($thiz.display4__AO() === null)) {
        $thiz.display4$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display3$und$eq__AO__V($asArrayOf_O($thiz.display4__AO().get((31 & ((newIndex >>> 20) | 0))), 1));
      if (($thiz.display3__AO() === null)) {
        $thiz.display3$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get((31 & ((newIndex >>> 15) | 0))), 1));
      if (($thiz.display2__AO() === null)) {
        $thiz.display2$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((newIndex >>> 10) | 0))), 1));
      if (($thiz.display1__AO() === null)) {
        $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
      };
      $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]))
    } else {
      throw new $c_jl_IllegalArgumentException().init___()
    }
  }
}
function $f_sci_VectorPointer__gotoPosWritable1__I__I__I__V($thiz, oldIndex, newIndex, xor) {
  if ((xor < 32)) {
    var a = $thiz.display0__AO();
    $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a))
  } else if ((xor < 1024)) {
    var a$1 = $thiz.display1__AO();
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$1));
    $thiz.display1__AO().set((31 & ((oldIndex >>> 5) | 0)), $thiz.display0__AO());
    var array = $thiz.display1__AO();
    var index = (31 & ((newIndex >>> 5) | 0));
    $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array, index))
  } else if ((xor < 32768)) {
    var a$2 = $thiz.display1__AO();
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$2));
    var a$3 = $thiz.display2__AO();
    $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$3));
    $thiz.display1__AO().set((31 & ((oldIndex >>> 5) | 0)), $thiz.display0__AO());
    $thiz.display2__AO().set((31 & ((oldIndex >>> 10) | 0)), $thiz.display1__AO());
    var array$1 = $thiz.display2__AO();
    var index$1 = (31 & ((newIndex >>> 10) | 0));
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$1, index$1));
    var array$2 = $thiz.display1__AO();
    var index$2 = (31 & ((newIndex >>> 5) | 0));
    $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$2, index$2))
  } else if ((xor < 1048576)) {
    var a$4 = $thiz.display1__AO();
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$4));
    var a$5 = $thiz.display2__AO();
    $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$5));
    var a$6 = $thiz.display3__AO();
    $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$6));
    $thiz.display1__AO().set((31 & ((oldIndex >>> 5) | 0)), $thiz.display0__AO());
    $thiz.display2__AO().set((31 & ((oldIndex >>> 10) | 0)), $thiz.display1__AO());
    $thiz.display3__AO().set((31 & ((oldIndex >>> 15) | 0)), $thiz.display2__AO());
    var array$3 = $thiz.display3__AO();
    var index$3 = (31 & ((newIndex >>> 15) | 0));
    $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$3, index$3));
    var array$4 = $thiz.display2__AO();
    var index$4 = (31 & ((newIndex >>> 10) | 0));
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$4, index$4));
    var array$5 = $thiz.display1__AO();
    var index$5 = (31 & ((newIndex >>> 5) | 0));
    $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$5, index$5))
  } else if ((xor < 33554432)) {
    var a$7 = $thiz.display1__AO();
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$7));
    var a$8 = $thiz.display2__AO();
    $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$8));
    var a$9 = $thiz.display3__AO();
    $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$9));
    var a$10 = $thiz.display4__AO();
    $thiz.display4$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$10));
    $thiz.display1__AO().set((31 & ((oldIndex >>> 5) | 0)), $thiz.display0__AO());
    $thiz.display2__AO().set((31 & ((oldIndex >>> 10) | 0)), $thiz.display1__AO());
    $thiz.display3__AO().set((31 & ((oldIndex >>> 15) | 0)), $thiz.display2__AO());
    $thiz.display4__AO().set((31 & ((oldIndex >>> 20) | 0)), $thiz.display3__AO());
    var array$6 = $thiz.display4__AO();
    var index$6 = (31 & ((newIndex >>> 20) | 0));
    $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$6, index$6));
    var array$7 = $thiz.display3__AO();
    var index$7 = (31 & ((newIndex >>> 15) | 0));
    $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$7, index$7));
    var array$8 = $thiz.display2__AO();
    var index$8 = (31 & ((newIndex >>> 10) | 0));
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$8, index$8));
    var array$9 = $thiz.display1__AO();
    var index$9 = (31 & ((newIndex >>> 5) | 0));
    $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$9, index$9))
  } else if ((xor < 1073741824)) {
    var a$11 = $thiz.display1__AO();
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$11));
    var a$12 = $thiz.display2__AO();
    $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$12));
    var a$13 = $thiz.display3__AO();
    $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$13));
    var a$14 = $thiz.display4__AO();
    $thiz.display4$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$14));
    var a$15 = $thiz.display5__AO();
    $thiz.display5$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$15));
    $thiz.display1__AO().set((31 & ((oldIndex >>> 5) | 0)), $thiz.display0__AO());
    $thiz.display2__AO().set((31 & ((oldIndex >>> 10) | 0)), $thiz.display1__AO());
    $thiz.display3__AO().set((31 & ((oldIndex >>> 15) | 0)), $thiz.display2__AO());
    $thiz.display4__AO().set((31 & ((oldIndex >>> 20) | 0)), $thiz.display3__AO());
    $thiz.display5__AO().set((31 & ((oldIndex >>> 25) | 0)), $thiz.display4__AO());
    var array$10 = $thiz.display5__AO();
    var index$10 = (31 & ((newIndex >>> 25) | 0));
    $thiz.display4$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$10, index$10));
    var array$11 = $thiz.display4__AO();
    var index$11 = (31 & ((newIndex >>> 20) | 0));
    $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$11, index$11));
    var array$12 = $thiz.display3__AO();
    var index$12 = (31 & ((newIndex >>> 15) | 0));
    $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$12, index$12));
    var array$13 = $thiz.display2__AO();
    var index$13 = (31 & ((newIndex >>> 10) | 0));
    $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$13, index$13));
    var array$14 = $thiz.display1__AO();
    var index$14 = (31 & ((newIndex >>> 5) | 0));
    $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$14, index$14))
  } else {
    throw new $c_jl_IllegalArgumentException().init___()
  }
}
function $f_sci_VectorPointer__copyRange__AO__I__I__AO($thiz, array, oldLeft, newLeft) {
  var elems = $newArrayObject($d_O.getArrayOf(), [32]);
  $systemArraycopy(array, oldLeft, elems, newLeft, ((32 - ((newLeft > oldLeft) ? newLeft : oldLeft)) | 0));
  return elems
}
function $f_sci_VectorPointer__gotoPos__I__I__V($thiz, index, xor) {
  if ((xor >= 32)) {
    if ((xor < 1024)) {
      $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get((31 & ((index >>> 5) | 0))), 1))
    } else if ((xor < 32768)) {
      $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((index >>> 10) | 0))), 1));
      $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get((31 & ((index >>> 5) | 0))), 1))
    } else if ((xor < 1048576)) {
      $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get((31 & ((index >>> 15) | 0))), 1));
      $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((index >>> 10) | 0))), 1));
      $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get((31 & ((index >>> 5) | 0))), 1))
    } else if ((xor < 33554432)) {
      $thiz.display3$und$eq__AO__V($asArrayOf_O($thiz.display4__AO().get((31 & ((index >>> 20) | 0))), 1));
      $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get((31 & ((index >>> 15) | 0))), 1));
      $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((index >>> 10) | 0))), 1));
      $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get((31 & ((index >>> 5) | 0))), 1))
    } else if ((xor < 1073741824)) {
      $thiz.display4$und$eq__AO__V($asArrayOf_O($thiz.display5__AO().get((31 & ((index >>> 25) | 0))), 1));
      $thiz.display3$und$eq__AO__V($asArrayOf_O($thiz.display4__AO().get((31 & ((index >>> 20) | 0))), 1));
      $thiz.display2$und$eq__AO__V($asArrayOf_O($thiz.display3__AO().get((31 & ((index >>> 15) | 0))), 1));
      $thiz.display1$und$eq__AO__V($asArrayOf_O($thiz.display2__AO().get((31 & ((index >>> 10) | 0))), 1));
      $thiz.display0$und$eq__AO__V($asArrayOf_O($thiz.display1__AO().get((31 & ((index >>> 5) | 0))), 1))
    } else {
      throw new $c_jl_IllegalArgumentException().init___()
    }
  }
}
function $f_sci_VectorPointer__gotoPosWritable0__I__I__V($thiz, newIndex, xor) {
  var x1 = (((-1) + $thiz.depth__I()) | 0);
  switch (x1) {
    case 5: {
      var a = $thiz.display5__AO();
      $thiz.display5$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a));
      var array = $thiz.display5__AO();
      var index = (31 & ((newIndex >>> 25) | 0));
      $thiz.display4$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array, index));
      var array$1 = $thiz.display4__AO();
      var index$1 = (31 & ((newIndex >>> 20) | 0));
      $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$1, index$1));
      var array$2 = $thiz.display3__AO();
      var index$2 = (31 & ((newIndex >>> 15) | 0));
      $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$2, index$2));
      var array$3 = $thiz.display2__AO();
      var index$3 = (31 & ((newIndex >>> 10) | 0));
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$3, index$3));
      var array$4 = $thiz.display1__AO();
      var index$4 = (31 & ((newIndex >>> 5) | 0));
      $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$4, index$4));
      break
    }
    case 4: {
      var a$1 = $thiz.display4__AO();
      $thiz.display4$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$1));
      var array$5 = $thiz.display4__AO();
      var index$5 = (31 & ((newIndex >>> 20) | 0));
      $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$5, index$5));
      var array$6 = $thiz.display3__AO();
      var index$6 = (31 & ((newIndex >>> 15) | 0));
      $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$6, index$6));
      var array$7 = $thiz.display2__AO();
      var index$7 = (31 & ((newIndex >>> 10) | 0));
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$7, index$7));
      var array$8 = $thiz.display1__AO();
      var index$8 = (31 & ((newIndex >>> 5) | 0));
      $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$8, index$8));
      break
    }
    case 3: {
      var a$2 = $thiz.display3__AO();
      $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$2));
      var array$9 = $thiz.display3__AO();
      var index$9 = (31 & ((newIndex >>> 15) | 0));
      $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$9, index$9));
      var array$10 = $thiz.display2__AO();
      var index$10 = (31 & ((newIndex >>> 10) | 0));
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$10, index$10));
      var array$11 = $thiz.display1__AO();
      var index$11 = (31 & ((newIndex >>> 5) | 0));
      $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$11, index$11));
      break
    }
    case 2: {
      var a$3 = $thiz.display2__AO();
      $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$3));
      var array$12 = $thiz.display2__AO();
      var index$12 = (31 & ((newIndex >>> 10) | 0));
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$12, index$12));
      var array$13 = $thiz.display1__AO();
      var index$13 = (31 & ((newIndex >>> 5) | 0));
      $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$13, index$13));
      break
    }
    case 1: {
      var a$4 = $thiz.display1__AO();
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$4));
      var array$14 = $thiz.display1__AO();
      var index$14 = (31 & ((newIndex >>> 5) | 0));
      $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array$14, index$14));
      break
    }
    case 0: {
      var a$5 = $thiz.display0__AO();
      $thiz.display0$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$5));
      break
    }
    default: {
      throw new $c_s_MatchError(x1)
    }
  }
}
function $f_sci_VectorPointer__stabilize__I__V($thiz, index) {
  var x1 = (((-1) + $thiz.depth__I()) | 0);
  switch (x1) {
    case 5: {
      var a = $thiz.display5__AO();
      $thiz.display5$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a));
      var a$1 = $thiz.display4__AO();
      $thiz.display4$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$1));
      var a$2 = $thiz.display3__AO();
      $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$2));
      var a$3 = $thiz.display2__AO();
      $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$3));
      var a$4 = $thiz.display1__AO();
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$4));
      $thiz.display5__AO().set((31 & ((index >>> 25) | 0)), $thiz.display4__AO());
      $thiz.display4__AO().set((31 & ((index >>> 20) | 0)), $thiz.display3__AO());
      $thiz.display3__AO().set((31 & ((index >>> 15) | 0)), $thiz.display2__AO());
      $thiz.display2__AO().set((31 & ((index >>> 10) | 0)), $thiz.display1__AO());
      $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
      break
    }
    case 4: {
      var a$5 = $thiz.display4__AO();
      $thiz.display4$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$5));
      var a$6 = $thiz.display3__AO();
      $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$6));
      var a$7 = $thiz.display2__AO();
      $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$7));
      var a$8 = $thiz.display1__AO();
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$8));
      $thiz.display4__AO().set((31 & ((index >>> 20) | 0)), $thiz.display3__AO());
      $thiz.display3__AO().set((31 & ((index >>> 15) | 0)), $thiz.display2__AO());
      $thiz.display2__AO().set((31 & ((index >>> 10) | 0)), $thiz.display1__AO());
      $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
      break
    }
    case 3: {
      var a$9 = $thiz.display3__AO();
      $thiz.display3$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$9));
      var a$10 = $thiz.display2__AO();
      $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$10));
      var a$11 = $thiz.display1__AO();
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$11));
      $thiz.display3__AO().set((31 & ((index >>> 15) | 0)), $thiz.display2__AO());
      $thiz.display2__AO().set((31 & ((index >>> 10) | 0)), $thiz.display1__AO());
      $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
      break
    }
    case 2: {
      var a$12 = $thiz.display2__AO();
      $thiz.display2$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$12));
      var a$13 = $thiz.display1__AO();
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$13));
      $thiz.display2__AO().set((31 & ((index >>> 10) | 0)), $thiz.display1__AO());
      $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
      break
    }
    case 1: {
      var a$14 = $thiz.display1__AO();
      $thiz.display1$und$eq__AO__V($f_sci_VectorPointer__copyOf__AO__AO($thiz, a$14));
      $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
      break
    }
    case 0: {
      break
    }
    default: {
      throw new $c_s_MatchError(x1)
    }
  }
}
function $f_sci_VectorPointer__nullSlotAndCopy__AO__I__AO($thiz, array, index) {
  var x = array.get(index);
  array.set(index, null);
  var a = $asArrayOf_O(x, 1);
  return $f_sci_VectorPointer__copyOf__AO__AO($thiz, a)
}
function $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V($thiz, that, depth) {
  $thiz.depth$und$eq__I__V(depth);
  var x1 = (((-1) + depth) | 0);
  switch (x1) {
    case (-1): {
      break
    }
    case 0: {
      $thiz.display0$und$eq__AO__V(that.display0__AO());
      break
    }
    case 1: {
      $thiz.display1$und$eq__AO__V(that.display1__AO());
      $thiz.display0$und$eq__AO__V(that.display0__AO());
      break
    }
    case 2: {
      $thiz.display2$und$eq__AO__V(that.display2__AO());
      $thiz.display1$und$eq__AO__V(that.display1__AO());
      $thiz.display0$und$eq__AO__V(that.display0__AO());
      break
    }
    case 3: {
      $thiz.display3$und$eq__AO__V(that.display3__AO());
      $thiz.display2$und$eq__AO__V(that.display2__AO());
      $thiz.display1$und$eq__AO__V(that.display1__AO());
      $thiz.display0$und$eq__AO__V(that.display0__AO());
      break
    }
    case 4: {
      $thiz.display4$und$eq__AO__V(that.display4__AO());
      $thiz.display3$und$eq__AO__V(that.display3__AO());
      $thiz.display2$und$eq__AO__V(that.display2__AO());
      $thiz.display1$und$eq__AO__V(that.display1__AO());
      $thiz.display0$und$eq__AO__V(that.display0__AO());
      break
    }
    case 5: {
      $thiz.display5$und$eq__AO__V(that.display5__AO());
      $thiz.display4$und$eq__AO__V(that.display4__AO());
      $thiz.display3$und$eq__AO__V(that.display3__AO());
      $thiz.display2$und$eq__AO__V(that.display2__AO());
      $thiz.display1$und$eq__AO__V(that.display1__AO());
      $thiz.display0$und$eq__AO__V(that.display0__AO());
      break
    }
    default: {
      throw new $c_s_MatchError(x1)
    }
  }
}
function $f_sci_VectorPointer__gotoNextBlockStartWritable__I__I__V($thiz, index, xor) {
  if ((xor < 1024)) {
    if (($thiz.depth__I() === 1)) {
      $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
      $thiz.display1__AO().set(0, $thiz.display0__AO());
      $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
    };
    $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO())
  } else if ((xor < 32768)) {
    if (($thiz.depth__I() === 2)) {
      $thiz.display2$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
      $thiz.display2__AO().set(0, $thiz.display1__AO());
      $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
    };
    $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
    $thiz.display2__AO().set((31 & ((index >>> 10) | 0)), $thiz.display1__AO())
  } else if ((xor < 1048576)) {
    if (($thiz.depth__I() === 3)) {
      $thiz.display3$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
      $thiz.display3__AO().set(0, $thiz.display2__AO());
      $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
    };
    $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display2$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
    $thiz.display2__AO().set((31 & ((index >>> 10) | 0)), $thiz.display1__AO());
    $thiz.display3__AO().set((31 & ((index >>> 15) | 0)), $thiz.display2__AO())
  } else if ((xor < 33554432)) {
    if (($thiz.depth__I() === 4)) {
      $thiz.display4$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
      $thiz.display4__AO().set(0, $thiz.display3__AO());
      $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
    };
    $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display2$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display3$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
    $thiz.display2__AO().set((31 & ((index >>> 10) | 0)), $thiz.display1__AO());
    $thiz.display3__AO().set((31 & ((index >>> 15) | 0)), $thiz.display2__AO());
    $thiz.display4__AO().set((31 & ((index >>> 20) | 0)), $thiz.display3__AO())
  } else if ((xor < 1073741824)) {
    if (($thiz.depth__I() === 5)) {
      $thiz.display5$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
      $thiz.display5__AO().set(0, $thiz.display4__AO());
      $thiz.depth$und$eq__I__V(((1 + $thiz.depth__I()) | 0))
    };
    $thiz.display0$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display2$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display3$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display4$und$eq__AO__V($newArrayObject($d_O.getArrayOf(), [32]));
    $thiz.display1__AO().set((31 & ((index >>> 5) | 0)), $thiz.display0__AO());
    $thiz.display2__AO().set((31 & ((index >>> 10) | 0)), $thiz.display1__AO());
    $thiz.display3__AO().set((31 & ((index >>> 15) | 0)), $thiz.display2__AO());
    $thiz.display4__AO().set((31 & ((index >>> 20) | 0)), $thiz.display3__AO());
    $thiz.display5__AO().set((31 & ((index >>> 25) | 0)), $thiz.display4__AO())
  } else {
    throw new $c_jl_IllegalArgumentException().init___()
  }
}
function $f_scm_FlatHashTable$HashUtils__elemToEntry__O__O($thiz, elem) {
  return ((elem === null) ? $m_scm_FlatHashTable$NullSentinel$() : elem)
}
function $f_scm_FlatHashTable$HashUtils__entryToElem__O__O($thiz, entry) {
  return (($m_scm_FlatHashTable$NullSentinel$() === entry) ? null : entry)
}
function $f_scm_FlatHashTable$HashUtils__improve__I__I__I($thiz, hcode, seed) {
  var i = $m_s_util_hashing_package$().byteswap32__I__I(hcode);
  return (((i >>> seed) | 0) | (i << ((-seed) | 0)))
}
/** @constructor */
function $c_Lcom_kos_wormpad_dpad_DPad(centerX, centerY, radius, acceleration) {
  this.centerX$1 = 0.0;
  this.centerY$1 = 0.0;
  this.radius$1 = 0.0;
  this.acceleration$1 = 0.0;
  this.x$und$1 = 0.0;
  this.y$und$1 = 0.0;
  this.pressed$1 = false;
  this.centerX$1 = centerX;
  this.centerY$1 = centerY;
  this.radius$1 = radius;
  this.acceleration$1 = acceleration;
  this.x$und$1 = 0.0;
  this.y$und$1 = 0.0;
  this.pressed$1 = false
}
$c_Lcom_kos_wormpad_dpad_DPad.prototype = new $h_O();
$c_Lcom_kos_wormpad_dpad_DPad.prototype.constructor = $c_Lcom_kos_wormpad_dpad_DPad;
/** @constructor */
function $h_Lcom_kos_wormpad_dpad_DPad() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_dpad_DPad.prototype = $c_Lcom_kos_wormpad_dpad_DPad.prototype;
$c_Lcom_kos_wormpad_dpad_DPad.prototype.bounds__D__D = (function(v) {
  return ((v > 1.0) ? 1.0 : ((v < (-1.0)) ? (-1.0) : v))
});
$c_Lcom_kos_wormpad_dpad_DPad.prototype.x__D = (function() {
  return (this.x$und$1 * this.acceleration$1)
});
$c_Lcom_kos_wormpad_dpad_DPad.prototype.touchUp__V = (function() {
  this.pressed$1 = false;
  this.x$und$1 = 0.0;
  this.y$und$1 = 0.0
});
$c_Lcom_kos_wormpad_dpad_DPad.prototype.y__D = (function() {
  return (this.y$und$1 * this.acceleration$1)
});
$c_Lcom_kos_wormpad_dpad_DPad.prototype.touchDown__D__D__V = (function(x, y) {
  this.x$und$1 = this.bounds__D__D(((x - this.centerX$1) / this.radius$1));
  this.y$und$1 = this.bounds__D__D(((-(y - this.centerY$1)) / this.radius$1));
  this.pressed$1 = true
});
$c_Lcom_kos_wormpad_dpad_DPad.prototype.touchMove__D__D__V = (function(x, y) {
  if (this.pressed$1) {
    this.x$und$1 = this.bounds__D__D(((x - this.centerX$1) / this.radius$1));
    this.y$und$1 = this.bounds__D__D(((-(y - this.centerY$1)) / this.radius$1))
  }
});
var $d_Lcom_kos_wormpad_dpad_DPad = new $TypeData().initClass({
  Lcom_kos_wormpad_dpad_DPad: 0
}, false, "com.kos.wormpad.dpad.DPad", {
  Lcom_kos_wormpad_dpad_DPad: 1,
  O: 1
});
$c_Lcom_kos_wormpad_dpad_DPad.prototype.$classData = $d_Lcom_kos_wormpad_dpad_DPad;
function $f_Lcom_kos_wormpad_game_AudioState__$$init$__V($thiz) {
  $thiz.soundPlay$und$1 = true;
  $thiz.musicPlay$und$1 = true;
  $thiz.com$kos$wormpad$game$AudioState$$soundPath$1 = "audio/sound/";
  $thiz.com$kos$wormpad$game$AudioState$$musicPath$1 = "audio/music/";
  var this$1 = $m_sci_Seq$();
  var elems = $m_sci_Nil$();
  $thiz.soundBank$1 = $as_sci_Seq(this$1.from__sc_IterableOnce__sc_SeqOps(elems))
}
/** @constructor */
function $c_Lcom_kos_wormpad_game_BackgroundLayer(srcPath, width, height, x, y, paradoxX, paradoxY) {
  this.width$1 = 0.0;
  this.height$1 = 0.0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.paradoxX$1 = 0.0;
  this.paradoxY$1 = 0.0;
  this.img$1 = null;
  this.width$1 = width;
  this.height$1 = height;
  this.x$1 = x;
  this.y$1 = y;
  this.paradoxX$1 = paradoxX;
  this.paradoxY$1 = paradoxY;
  this.img$1 = $m_Lcom_kos_wormpad_game_helpers_JSHelper$().loadImage__T__Lorg_scalajs_dom_raw_HTMLImageElement(srcPath)
}
$c_Lcom_kos_wormpad_game_BackgroundLayer.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_BackgroundLayer.prototype.constructor = $c_Lcom_kos_wormpad_game_BackgroundLayer;
/** @constructor */
function $h_Lcom_kos_wormpad_game_BackgroundLayer() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_BackgroundLayer.prototype = $c_Lcom_kos_wormpad_game_BackgroundLayer.prototype;
function $is_Lcom_kos_wormpad_game_BackgroundLayer(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_game_BackgroundLayer)))
}
function $as_Lcom_kos_wormpad_game_BackgroundLayer(obj) {
  return (($is_Lcom_kos_wormpad_game_BackgroundLayer(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.game.BackgroundLayer"))
}
function $isArrayOf_Lcom_kos_wormpad_game_BackgroundLayer(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_game_BackgroundLayer)))
}
function $asArrayOf_Lcom_kos_wormpad_game_BackgroundLayer(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_game_BackgroundLayer(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.game.BackgroundLayer;", depth))
}
var $d_Lcom_kos_wormpad_game_BackgroundLayer = new $TypeData().initClass({
  Lcom_kos_wormpad_game_BackgroundLayer: 0
}, false, "com.kos.wormpad.game.BackgroundLayer", {
  Lcom_kos_wormpad_game_BackgroundLayer: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_BackgroundLayer.prototype.$classData = $d_Lcom_kos_wormpad_game_BackgroundLayer;
/** @constructor */
function $c_Lcom_kos_wormpad_game_EnemyCreator(lastCreateTime, expression) {
  this.lastCreateTime$1 = 0.0;
  this.expression$1 = null;
  this.nextCreateTime$1 = 0.0;
  this.lastCreateTime$1 = lastCreateTime;
  this.expression$1 = expression;
  this.nextCreateTime$1 = (this.lastCreateTime$1 + expression.deltaTime$1)
}
$c_Lcom_kos_wormpad_game_EnemyCreator.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_EnemyCreator.prototype.constructor = $c_Lcom_kos_wormpad_game_EnemyCreator;
/** @constructor */
function $h_Lcom_kos_wormpad_game_EnemyCreator() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_EnemyCreator.prototype = $c_Lcom_kos_wormpad_game_EnemyCreator.prototype;
$c_Lcom_kos_wormpad_game_EnemyCreator.prototype.create__D__Lcom_kos_wormpad_heroes_Hero = (function(gameTime) {
  var hero = $as_Lcom_kos_wormpad_heroes_Hero(this.expression$1.creator$1.apply__O());
  this.nextCreateTime$1 = (this.expression$1.deltaTime$1 + this.nextCreateTime$1);
  this.lastCreateTime$1 = gameTime;
  return hero
});
$c_Lcom_kos_wormpad_game_EnemyCreator.prototype.createIfNeed__D__s_util_Random__Lcom_kos_wormpad_heroes_Hero = (function(gameTime, random) {
  if ((gameTime >= this.nextCreateTime$1)) {
    var hero = this.create__D__Lcom_kos_wormpad_heroes_Hero(gameTime);
    hero.x$1 = $m_Lcom_kos_wormpad_geometry_Geometry$().randomX__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D(random, this.expression$1.area$1);
    hero.y$1 = $m_Lcom_kos_wormpad_geometry_Geometry$().randomY__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D(random, this.expression$1.area$1);
    return hero
  } else {
    return $m_Lcom_kos_wormpad_heroes_Hero$().NONE$undHERO$1
  }
});
function $is_Lcom_kos_wormpad_game_EnemyCreator(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_game_EnemyCreator)))
}
function $as_Lcom_kos_wormpad_game_EnemyCreator(obj) {
  return (($is_Lcom_kos_wormpad_game_EnemyCreator(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.game.EnemyCreator"))
}
function $isArrayOf_Lcom_kos_wormpad_game_EnemyCreator(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_game_EnemyCreator)))
}
function $asArrayOf_Lcom_kos_wormpad_game_EnemyCreator(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_game_EnemyCreator(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.game.EnemyCreator;", depth))
}
var $d_Lcom_kos_wormpad_game_EnemyCreator = new $TypeData().initClass({
  Lcom_kos_wormpad_game_EnemyCreator: 0
}, false, "com.kos.wormpad.game.EnemyCreator", {
  Lcom_kos_wormpad_game_EnemyCreator: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_EnemyCreator.prototype.$classData = $d_Lcom_kos_wormpad_game_EnemyCreator;
/** @constructor */
function $c_Lcom_kos_wormpad_game_GameListener() {
  this.onChangeSoundState$1 = null;
  this.onGameOver$1 = null;
  this.onNewGame$1 = null;
  this.onPause$1 = null;
  this.onChangeScore$1 = null;
  this.onChangeSoundState$1 = (function(arg$outer) {
    return (function(arg1$2, arg2$2) {
      $uZ(arg1$2);
      $uZ(arg2$2)
    })
  })(this);
  this.onGameOver$1 = (function(arg$outer$1) {
    return (function() {
      return (void 0)
    })
  })(this);
  this.onNewGame$1 = (function(arg$outer$2) {
    return (function() {
      return (void 0)
    })
  })(this);
  this.onPause$1 = (function(arg$outer$3) {
    return (function(arg1$2$1) {
      $uZ(arg1$2$1)
    })
  })(this);
  this.onChangeScore$1 = (function(arg$outer$4) {
    return (function(arg1$2$2) {
      $uI(arg1$2$2)
    })
  })(this)
}
$c_Lcom_kos_wormpad_game_GameListener.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_GameListener.prototype.constructor = $c_Lcom_kos_wormpad_game_GameListener;
/** @constructor */
function $h_Lcom_kos_wormpad_game_GameListener() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_GameListener.prototype = $c_Lcom_kos_wormpad_game_GameListener.prototype;
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onChangeScore__sjs_js_Function1__O = (function(x$1) {
  this.onChangeScore$1 = x$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onPause__O = (function() {
  return this.onPause$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onGameOver__O = (function() {
  return this.onGameOver$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onChangeScore__O = (function() {
  return this.onChangeScore$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onChangeSoundState__O = (function() {
  return this.onChangeSoundState$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onNewGame__O = (function() {
  return this.onNewGame$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onChangeSoundState__sjs_js_Function2__O = (function(x$1) {
  this.onChangeSoundState$1 = x$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onNewGame__sjs_js_Function0__O = (function(x$1) {
  this.onNewGame$1 = x$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onPause__sjs_js_Function1__O = (function(x$1) {
  this.onPause$1 = x$1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$$js$exported$prop$onGameOver__sjs_js_Function0__O = (function(x$1) {
  this.onGameOver$1 = x$1
});
Object.defineProperty($c_Lcom_kos_wormpad_game_GameListener.prototype, "onChangeScore", {
  "get": (function() {
    return this.$$js$exported$prop$onChangeScore__O()
  }),
  "set": (function(arg$1) {
    var prep0 = arg$1;
    this.$$js$exported$prop$onChangeScore__sjs_js_Function1__O(prep0)
  }),
  "configurable": true
});
Object.defineProperty($c_Lcom_kos_wormpad_game_GameListener.prototype, "onPause", {
  "get": (function() {
    return this.$$js$exported$prop$onPause__O()
  }),
  "set": (function(arg$1) {
    var prep0 = arg$1;
    this.$$js$exported$prop$onPause__sjs_js_Function1__O(prep0)
  }),
  "configurable": true
});
Object.defineProperty($c_Lcom_kos_wormpad_game_GameListener.prototype, "onNewGame", {
  "get": (function() {
    return this.$$js$exported$prop$onNewGame__O()
  }),
  "set": (function(arg$1) {
    var prep0 = arg$1;
    this.$$js$exported$prop$onNewGame__sjs_js_Function0__O(prep0)
  }),
  "configurable": true
});
Object.defineProperty($c_Lcom_kos_wormpad_game_GameListener.prototype, "onGameOver", {
  "get": (function() {
    return this.$$js$exported$prop$onGameOver__O()
  }),
  "set": (function(arg$1) {
    var prep0 = arg$1;
    this.$$js$exported$prop$onGameOver__sjs_js_Function0__O(prep0)
  }),
  "configurable": true
});
Object.defineProperty($c_Lcom_kos_wormpad_game_GameListener.prototype, "onChangeSoundState", {
  "get": (function() {
    return this.$$js$exported$prop$onChangeSoundState__O()
  }),
  "set": (function(arg$1) {
    var prep0 = arg$1;
    this.$$js$exported$prop$onChangeSoundState__sjs_js_Function2__O(prep0)
  }),
  "configurable": true
});
function $is_Lcom_kos_wormpad_game_GameListener(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_game_GameListener)))
}
function $as_Lcom_kos_wormpad_game_GameListener(obj) {
  return (($is_Lcom_kos_wormpad_game_GameListener(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.game.GameListener"))
}
function $isArrayOf_Lcom_kos_wormpad_game_GameListener(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_game_GameListener)))
}
function $asArrayOf_Lcom_kos_wormpad_game_GameListener(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_game_GameListener(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.game.GameListener;", depth))
}
var $d_Lcom_kos_wormpad_game_GameListener = new $TypeData().initClass({
  Lcom_kos_wormpad_game_GameListener: 0
}, false, "com.kos.wormpad.game.GameListener", {
  Lcom_kos_wormpad_game_GameListener: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_GameListener.prototype.$classData = $d_Lcom_kos_wormpad_game_GameListener;
/** @constructor */
function $c_Lcom_kos_wormpad_game_GameListenerDelegate() {
  /*<skip>*/
}
$c_Lcom_kos_wormpad_game_GameListenerDelegate.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_GameListenerDelegate.prototype.constructor = $c_Lcom_kos_wormpad_game_GameListenerDelegate;
/** @constructor */
function $h_Lcom_kos_wormpad_game_GameListenerDelegate() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_GameListenerDelegate.prototype = $c_Lcom_kos_wormpad_game_GameListenerDelegate.prototype;
function $is_Lcom_kos_wormpad_game_GameListenerDelegate(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_game_GameListenerDelegate)))
}
function $as_Lcom_kos_wormpad_game_GameListenerDelegate(obj) {
  return (($is_Lcom_kos_wormpad_game_GameListenerDelegate(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.game.GameListenerDelegate"))
}
function $isArrayOf_Lcom_kos_wormpad_game_GameListenerDelegate(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_game_GameListenerDelegate)))
}
function $asArrayOf_Lcom_kos_wormpad_game_GameListenerDelegate(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_game_GameListenerDelegate(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.game.GameListenerDelegate;", depth))
}
/** @constructor */
function $c_Lcom_kos_wormpad_game_GameLoop() {
  this.thenTime$1 = $L0;
  this.thenTime$1 = $m_Lcom_kos_wormpad_game_helpers_SystemMethod$().time__J()
}
$c_Lcom_kos_wormpad_game_GameLoop.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_GameLoop.prototype.constructor = $c_Lcom_kos_wormpad_game_GameLoop;
/** @constructor */
function $h_Lcom_kos_wormpad_game_GameLoop() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_GameLoop.prototype = $c_Lcom_kos_wormpad_game_GameLoop.prototype;
$c_Lcom_kos_wormpad_game_GameLoop.prototype.start__F1__F0__V = (function(update, render) {
  var this$1 = this.loop__F1__F0__F0(update, render);
  this$1.apply__O()
});
$c_Lcom_kos_wormpad_game_GameLoop.prototype.loop__F1__F0__F0 = (function(update, render) {
  return new $c_sjsr_AnonFunction0((function($this, update$1, render$1) {
    return (function() {
      window.requestAnimationFrame($m_sjs_js_Any$().fromFunction0__F0__sjs_js_Function0($this.loop__F1__F0__F0(update$1, render$1)));
      var t = $m_Lcom_kos_wormpad_game_helpers_SystemMethod$().time__J();
      var lo = t.lo$2;
      var hi = t.hi$2;
      var b = $this.thenTime$1;
      var bhi = b.hi$2;
      var lo$1 = ((lo - b.lo$2) | 0);
      var hi$1 = ((((-2147483648) ^ lo$1) > ((-2147483648) ^ lo)) ? (((-1) + ((hi - bhi) | 0)) | 0) : ((hi - bhi) | 0));
      update$1.apply__O__O(new $c_sjsr_RuntimeLong(lo$1, hi$1));
      render$1.apply__O();
      $this.thenTime$1 = new $c_sjsr_RuntimeLong(lo, hi)
    })
  })(this, update, render))
});
var $d_Lcom_kos_wormpad_game_GameLoop = new $TypeData().initClass({
  Lcom_kos_wormpad_game_GameLoop: 0
}, false, "com.kos.wormpad.game.GameLoop", {
  Lcom_kos_wormpad_game_GameLoop: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_GameLoop.prototype.$classData = $d_Lcom_kos_wormpad_game_GameLoop;
/** @constructor */
function $c_Lcom_kos_wormpad_game_HeroTexture(srcPath) {
  this.srcPath$1 = null;
  this.img$1 = null;
  this.width$1 = 0;
  this.height$1 = 0;
  this.srcPath$1 = srcPath;
  this.img$1 = $m_Lcom_kos_wormpad_game_helpers_JSHelper$().loadImage__T__Lorg_scalajs_dom_raw_HTMLImageElement(srcPath);
  this.width$1 = 256;
  this.height$1 = 256
}
$c_Lcom_kos_wormpad_game_HeroTexture.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_HeroTexture.prototype.constructor = $c_Lcom_kos_wormpad_game_HeroTexture;
/** @constructor */
function $h_Lcom_kos_wormpad_game_HeroTexture() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_HeroTexture.prototype = $c_Lcom_kos_wormpad_game_HeroTexture.prototype;
$c_Lcom_kos_wormpad_game_HeroTexture.prototype.complete__Z = (function() {
  return $uZ(this.img$1.complete)
});
function $is_Lcom_kos_wormpad_game_HeroTexture(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_game_HeroTexture)))
}
function $as_Lcom_kos_wormpad_game_HeroTexture(obj) {
  return (($is_Lcom_kos_wormpad_game_HeroTexture(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.game.HeroTexture"))
}
function $isArrayOf_Lcom_kos_wormpad_game_HeroTexture(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_game_HeroTexture)))
}
function $asArrayOf_Lcom_kos_wormpad_game_HeroTexture(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_game_HeroTexture(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.game.HeroTexture;", depth))
}
var $d_Lcom_kos_wormpad_game_HeroTexture = new $TypeData().initClass({
  Lcom_kos_wormpad_game_HeroTexture: 0
}, false, "com.kos.wormpad.game.HeroTexture", {
  Lcom_kos_wormpad_game_HeroTexture: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_HeroTexture.prototype.$classData = $d_Lcom_kos_wormpad_game_HeroTexture;
function $f_Lcom_kos_wormpad_game_WormScore__score$und$eq__I__V($thiz, value) {
  $thiz.com$kos$wormpad$game$WormScore$$score$und$1 = value;
  $thiz.listener$und$1.onChangeScore__I__V($thiz.com$kos$wormpad$game$WormScore$$score$und$1)
}
/** @constructor */
function $c_Lcom_kos_wormpad_game_helpers_JSHelper$() {
  /*<skip>*/
}
$c_Lcom_kos_wormpad_game_helpers_JSHelper$.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_helpers_JSHelper$.prototype.constructor = $c_Lcom_kos_wormpad_game_helpers_JSHelper$;
/** @constructor */
function $h_Lcom_kos_wormpad_game_helpers_JSHelper$() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_helpers_JSHelper$.prototype = $c_Lcom_kos_wormpad_game_helpers_JSHelper$.prototype;
$c_Lcom_kos_wormpad_game_helpers_JSHelper$.prototype.addClass__Lorg_scalajs_dom_raw_HTMLElement__T__V = (function(element, cls) {
  element.classList.add(cls)
});
$c_Lcom_kos_wormpad_game_helpers_JSHelper$.prototype.removeClass__Lorg_scalajs_dom_raw_HTMLElement__T__V = (function(element, cls) {
  element.classList.remove(cls)
});
$c_Lcom_kos_wormpad_game_helpers_JSHelper$.prototype.loadImage__T__Lorg_scalajs_dom_raw_HTMLImageElement = (function(fileName) {
  var img = $m_Lorg_scalajs_dom_package$().document__Lorg_scalajs_dom_raw_HTMLDocument().createElement("img");
  img.src = fileName;
  return img
});
var $d_Lcom_kos_wormpad_game_helpers_JSHelper$ = new $TypeData().initClass({
  Lcom_kos_wormpad_game_helpers_JSHelper$: 0
}, false, "com.kos.wormpad.game.helpers.JSHelper$", {
  Lcom_kos_wormpad_game_helpers_JSHelper$: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_helpers_JSHelper$.prototype.$classData = $d_Lcom_kos_wormpad_game_helpers_JSHelper$;
var $n_Lcom_kos_wormpad_game_helpers_JSHelper$ = (void 0);
function $m_Lcom_kos_wormpad_game_helpers_JSHelper$() {
  if ((!$n_Lcom_kos_wormpad_game_helpers_JSHelper$)) {
    $n_Lcom_kos_wormpad_game_helpers_JSHelper$ = new $c_Lcom_kos_wormpad_game_helpers_JSHelper$()
  };
  return $n_Lcom_kos_wormpad_game_helpers_JSHelper$
}
/** @constructor */
function $c_Lcom_kos_wormpad_game_helpers_SystemMethod$() {
  /*<skip>*/
}
$c_Lcom_kos_wormpad_game_helpers_SystemMethod$.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_helpers_SystemMethod$.prototype.constructor = $c_Lcom_kos_wormpad_game_helpers_SystemMethod$;
/** @constructor */
function $h_Lcom_kos_wormpad_game_helpers_SystemMethod$() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_helpers_SystemMethod$.prototype = $c_Lcom_kos_wormpad_game_helpers_SystemMethod$.prototype;
$c_Lcom_kos_wormpad_game_helpers_SystemMethod$.prototype.time__J = (function() {
  var this$1 = $m_sjsr_RuntimeLong$();
  var value = $uD(Date.now());
  var lo = this$1.scala$scalajs$runtime$RuntimeLong$$fromDoubleImpl__D__I(value);
  var hi = this$1.scala$scalajs$runtime$RuntimeLong$$hiReturn$f;
  return new $c_sjsr_RuntimeLong(lo, hi)
});
var $d_Lcom_kos_wormpad_game_helpers_SystemMethod$ = new $TypeData().initClass({
  Lcom_kos_wormpad_game_helpers_SystemMethod$: 0
}, false, "com.kos.wormpad.game.helpers.SystemMethod$", {
  Lcom_kos_wormpad_game_helpers_SystemMethod$: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_helpers_SystemMethod$.prototype.$classData = $d_Lcom_kos_wormpad_game_helpers_SystemMethod$;
var $n_Lcom_kos_wormpad_game_helpers_SystemMethod$ = (void 0);
function $m_Lcom_kos_wormpad_game_helpers_SystemMethod$() {
  if ((!$n_Lcom_kos_wormpad_game_helpers_SystemMethod$)) {
    $n_Lcom_kos_wormpad_game_helpers_SystemMethod$ = new $c_Lcom_kos_wormpad_game_helpers_SystemMethod$()
  };
  return $n_Lcom_kos_wormpad_game_helpers_SystemMethod$
}
/** @constructor */
function $c_Lcom_kos_wormpad_game_infrastructure_Keyboard$() {
  this.keysDown$1 = null;
  $n_Lcom_kos_wormpad_game_infrastructure_Keyboard$ = this;
  var this$1 = $m_scm_Set$();
  var elems = $m_sci_Nil$();
  this.keysDown$1 = $as_scm_Set(this$1.from__sc_IterableOnce__O(elems))
}
$c_Lcom_kos_wormpad_game_infrastructure_Keyboard$.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_infrastructure_Keyboard$.prototype.constructor = $c_Lcom_kos_wormpad_game_infrastructure_Keyboard$;
/** @constructor */
function $h_Lcom_kos_wormpad_game_infrastructure_Keyboard$() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_infrastructure_Keyboard$.prototype = $c_Lcom_kos_wormpad_game_infrastructure_Keyboard$.prototype;
$c_Lcom_kos_wormpad_game_infrastructure_Keyboard$.prototype.init__sjs_js_Dynamic = (function() {
  addEventListener("keydown", $m_sjs_js_Any$().fromFunction1__F1__sjs_js_Function1(new $c_sjsr_AnonFunction1((function($this) {
    return (function(e$2) {
      var this$2 = $m_Lcom_kos_wormpad_game_infrastructure_Keyboard$();
      var key = $uI(e$2.keyCode);
      var this$3 = this$2.keysDown$1;
      this$3.addOne__O__scm_HashSet(key)
    })
  })(this))), false);
  return addEventListener("keyup", $m_sjs_js_Any$().fromFunction1__F1__sjs_js_Function1(new $c_sjsr_AnonFunction1((function(this$2$1) {
    return (function(e$3$2) {
      var this$6 = $m_Lcom_kos_wormpad_game_infrastructure_Keyboard$();
      var key$1 = $uI(e$3$2.keyCode);
      var this$7 = this$6.keysDown$1;
      this$7.subtractOne__O__scm_HashSet(key$1)
    })
  })(this))), false)
});
var $d_Lcom_kos_wormpad_game_infrastructure_Keyboard$ = new $TypeData().initClass({
  Lcom_kos_wormpad_game_infrastructure_Keyboard$: 0
}, false, "com.kos.wormpad.game.infrastructure.Keyboard$", {
  Lcom_kos_wormpad_game_infrastructure_Keyboard$: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_infrastructure_Keyboard$.prototype.$classData = $d_Lcom_kos_wormpad_game_infrastructure_Keyboard$;
var $n_Lcom_kos_wormpad_game_infrastructure_Keyboard$ = (void 0);
function $m_Lcom_kos_wormpad_game_infrastructure_Keyboard$() {
  if ((!$n_Lcom_kos_wormpad_game_infrastructure_Keyboard$)) {
    $n_Lcom_kos_wormpad_game_infrastructure_Keyboard$ = new $c_Lcom_kos_wormpad_game_infrastructure_Keyboard$()
  };
  return $n_Lcom_kos_wormpad_game_infrastructure_Keyboard$
}
/** @constructor */
function $c_Lcom_kos_wormpad_geometry_Geometry$() {
  /*<skip>*/
}
$c_Lcom_kos_wormpad_geometry_Geometry$.prototype = new $h_O();
$c_Lcom_kos_wormpad_geometry_Geometry$.prototype.constructor = $c_Lcom_kos_wormpad_geometry_Geometry$;
/** @constructor */
function $h_Lcom_kos_wormpad_geometry_Geometry$() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_geometry_Geometry$.prototype = $c_Lcom_kos_wormpad_geometry_Geometry$.prototype;
$c_Lcom_kos_wormpad_geometry_Geometry$.prototype.randomX__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D = (function(r, rect) {
  var n = $doubleToInt(rect.width__F());
  return $fround(($fround(r.self$1.nextInt__I__I(n)) + rect.left$1))
});
$c_Lcom_kos_wormpad_geometry_Geometry$.prototype.randomY__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D = (function(r, rect) {
  var n = $doubleToInt(rect.height__F());
  return $fround(($fround(r.self$1.nextInt__I__I(n)) + rect.bottom$1))
});
var $d_Lcom_kos_wormpad_geometry_Geometry$ = new $TypeData().initClass({
  Lcom_kos_wormpad_geometry_Geometry$: 0
}, false, "com.kos.wormpad.geometry.Geometry$", {
  Lcom_kos_wormpad_geometry_Geometry$: 1,
  O: 1
});
$c_Lcom_kos_wormpad_geometry_Geometry$.prototype.$classData = $d_Lcom_kos_wormpad_geometry_Geometry$;
var $n_Lcom_kos_wormpad_geometry_Geometry$ = (void 0);
function $m_Lcom_kos_wormpad_geometry_Geometry$() {
  if ((!$n_Lcom_kos_wormpad_geometry_Geometry$)) {
    $n_Lcom_kos_wormpad_geometry_Geometry$ = new $c_Lcom_kos_wormpad_geometry_Geometry$()
  };
  return $n_Lcom_kos_wormpad_geometry_Geometry$
}
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_Hero() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null
}
$c_Lcom_kos_wormpad_heroes_Hero.prototype = new $h_O();
$c_Lcom_kos_wormpad_heroes_Hero.prototype.constructor = $c_Lcom_kos_wormpad_heroes_Hero;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_Hero() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_Hero.prototype = $c_Lcom_kos_wormpad_heroes_Hero.prototype;
$c_Lcom_kos_wormpad_heroes_Hero.prototype.init___ = (function() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 1;
  this.energy$1 = 10;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 100.0;
  this.radius$1 = 10.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = new $c_sjsr_AnonFunction2((function($this) {
    return (function(x$1$2, x$2$2) {
      $as_Lcom_kos_wormpad_heroes_Hero(x$1$2);
      $uD(x$2$2)
    })
  })(this));
  return this
});
$c_Lcom_kos_wormpad_heroes_Hero.prototype.kind__I = (function() {
  return this.kind$1
});
$c_Lcom_kos_wormpad_heroes_Hero.prototype.move__D__V = (function(timeDelta) {
  /*<skip>*/
});
$c_Lcom_kos_wormpad_heroes_Hero.prototype.ediible__Z = (function() {
  return this.ediible$1
});
$c_Lcom_kos_wormpad_heroes_Hero.prototype.inArea__Lcom_kos_wormpad_geometry_RectF__Z = (function(area) {
  return (((((this.x$1 - this.radius$1) >= area.left$1) && ((this.x$1 + this.radius$1) <= area.right$1)) && ((this.y$1 - this.radius$1) >= area.bottom$1)) && ((this.y$1 + this.radius$1) <= area.top$1))
});
function $is_Lcom_kos_wormpad_heroes_Hero(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_heroes_Hero)))
}
function $as_Lcom_kos_wormpad_heroes_Hero(obj) {
  return (($is_Lcom_kos_wormpad_heroes_Hero(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.heroes.Hero"))
}
function $isArrayOf_Lcom_kos_wormpad_heroes_Hero(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_heroes_Hero)))
}
function $asArrayOf_Lcom_kos_wormpad_heroes_Hero(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_heroes_Hero(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.heroes.Hero;", depth))
}
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_Hero$() {
  this.NONE$undHERO$1 = null;
  $n_Lcom_kos_wormpad_heroes_Hero$ = this;
  this.NONE$undHERO$1 = new $c_Lcom_kos_wormpad_heroes_Hero$$anon$1()
}
$c_Lcom_kos_wormpad_heroes_Hero$.prototype = new $h_O();
$c_Lcom_kos_wormpad_heroes_Hero$.prototype.constructor = $c_Lcom_kos_wormpad_heroes_Hero$;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_Hero$() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_Hero$.prototype = $c_Lcom_kos_wormpad_heroes_Hero$.prototype;
var $d_Lcom_kos_wormpad_heroes_Hero$ = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_Hero$: 0
}, false, "com.kos.wormpad.heroes.Hero$", {
  Lcom_kos_wormpad_heroes_Hero$: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_Hero$.prototype.$classData = $d_Lcom_kos_wormpad_heroes_Hero$;
var $n_Lcom_kos_wormpad_heroes_Hero$ = (void 0);
function $m_Lcom_kos_wormpad_heroes_Hero$() {
  if ((!$n_Lcom_kos_wormpad_heroes_Hero$)) {
    $n_Lcom_kos_wormpad_heroes_Hero$ = new $c_Lcom_kos_wormpad_heroes_Hero$()
  };
  return $n_Lcom_kos_wormpad_heroes_Hero$
}
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_ShipWithBurgers$() {
  /*<skip>*/
}
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers$.prototype = new $h_O();
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers$.prototype.constructor = $c_Lcom_kos_wormpad_heroes_ShipWithBurgers$;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_ShipWithBurgers$() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_ShipWithBurgers$.prototype = $c_Lcom_kos_wormpad_heroes_ShipWithBurgers$.prototype;
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers$.prototype.burgerFail__Lcom_kos_wormpad_heroes_Hero__D__V = (function(hero, deltaTime) {
  hero.ax$1 = (hero.ax$1 - ((hero.ax$1 * deltaTime) / 2.0));
  hero.ay$1 = (-100.0);
  hero.vx$1 = (hero.vx$1 + (hero.ax$1 * deltaTime));
  hero.vy$1 = (hero.vy$1 + (hero.ay$1 * deltaTime));
  var a = hero.vy$1;
  hero.vy$1 = $uD(Math.max(a, (-100.0)))
});
var $d_Lcom_kos_wormpad_heroes_ShipWithBurgers$ = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_ShipWithBurgers$: 0
}, false, "com.kos.wormpad.heroes.ShipWithBurgers$", {
  Lcom_kos_wormpad_heroes_ShipWithBurgers$: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers$.prototype.$classData = $d_Lcom_kos_wormpad_heroes_ShipWithBurgers$;
var $n_Lcom_kos_wormpad_heroes_ShipWithBurgers$ = (void 0);
function $m_Lcom_kos_wormpad_heroes_ShipWithBurgers$() {
  if ((!$n_Lcom_kos_wormpad_heroes_ShipWithBurgers$)) {
    $n_Lcom_kos_wormpad_heroes_ShipWithBurgers$ = new $c_Lcom_kos_wormpad_heroes_ShipWithBurgers$()
  };
  return $n_Lcom_kos_wormpad_heroes_ShipWithBurgers$
}
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_Worm$() {
  this.MAX$undHEALTH$1 = 0.0;
  this.MAX$undSPEED$1 = 0.0;
  this.WORM$undACCELERATION$1 = 0.0;
  this.SCALE$undSPEED$1 = 0.0;
  this.MAX$undHEALTH$1 = 100.0;
  this.MAX$undSPEED$1 = 1200.0;
  this.WORM$undACCELERATION$1 = 1500.0;
  this.SCALE$undSPEED$1 = 1200.0
}
$c_Lcom_kos_wormpad_heroes_Worm$.prototype = new $h_O();
$c_Lcom_kos_wormpad_heroes_Worm$.prototype.constructor = $c_Lcom_kos_wormpad_heroes_Worm$;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_Worm$() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_Worm$.prototype = $c_Lcom_kos_wormpad_heroes_Worm$.prototype;
var $d_Lcom_kos_wormpad_heroes_Worm$ = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_Worm$: 0
}, false, "com.kos.wormpad.heroes.Worm$", {
  Lcom_kos_wormpad_heroes_Worm$: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_Worm$.prototype.$classData = $d_Lcom_kos_wormpad_heroes_Worm$;
var $n_Lcom_kos_wormpad_heroes_Worm$ = (void 0);
function $m_Lcom_kos_wormpad_heroes_Worm$() {
  if ((!$n_Lcom_kos_wormpad_heroes_Worm$)) {
    $n_Lcom_kos_wormpad_heroes_Worm$ = new $c_Lcom_kos_wormpad_heroes_Worm$()
  };
  return $n_Lcom_kos_wormpad_heroes_Worm$
}
/** @constructor */
function $c_Lorg_scalajs_dom_package$() {
  this.ApplicationCache$1 = null;
  this.Blob$1 = null;
  this.BlobPropertyBag$1 = null;
  this.ClipboardEventInit$1 = null;
  this.DOMException$1 = null;
  this.Event$1 = null;
  this.EventException$1 = null;
  this.EventSource$1 = null;
  this.FileReader$1 = null;
  this.FormData$1 = null;
  this.KeyboardEvent$1 = null;
  this.MediaError$1 = null;
  this.MutationEvent$1 = null;
  this.MutationObserverInit$1 = null;
  this.Node$1 = null;
  this.NodeFilter$1 = null;
  this.PerformanceNavigation$1 = null;
  this.PositionError$1 = null;
  this.Range$1 = null;
  this.TextEvent$1 = null;
  this.TextTrack$1 = null;
  this.URL$1 = null;
  this.VisibilityState$1 = null;
  this.WebSocket$1 = null;
  this.WheelEvent$1 = null;
  this.XMLHttpRequest$1 = null;
  this.XPathResult$1 = null;
  this.window$1 = null;
  this.document$1 = null;
  this.console$1 = null;
  this.bitmap$0$1 = 0
}
$c_Lorg_scalajs_dom_package$.prototype = new $h_O();
$c_Lorg_scalajs_dom_package$.prototype.constructor = $c_Lorg_scalajs_dom_package$;
/** @constructor */
function $h_Lorg_scalajs_dom_package$() {
  /*<skip>*/
}
$h_Lorg_scalajs_dom_package$.prototype = $c_Lorg_scalajs_dom_package$.prototype;
$c_Lorg_scalajs_dom_package$.prototype.document__Lorg_scalajs_dom_raw_HTMLDocument = (function() {
  return (((268435456 & this.bitmap$0$1) === 0) ? this.document$lzycompute__p1__Lorg_scalajs_dom_raw_HTMLDocument() : this.document$1)
});
$c_Lorg_scalajs_dom_package$.prototype.window__Lorg_scalajs_dom_raw_Window = (function() {
  return (((134217728 & this.bitmap$0$1) === 0) ? this.window$lzycompute__p1__Lorg_scalajs_dom_raw_Window() : this.window$1)
});
$c_Lorg_scalajs_dom_package$.prototype.window$lzycompute__p1__Lorg_scalajs_dom_raw_Window = (function() {
  if (((134217728 & this.bitmap$0$1) === 0)) {
    this.window$1 = window;
    this.bitmap$0$1 = (134217728 | this.bitmap$0$1)
  };
  return this.window$1
});
$c_Lorg_scalajs_dom_package$.prototype.document$lzycompute__p1__Lorg_scalajs_dom_raw_HTMLDocument = (function() {
  if (((268435456 & this.bitmap$0$1) === 0)) {
    this.document$1 = this.window__Lorg_scalajs_dom_raw_Window().document;
    this.bitmap$0$1 = (268435456 | this.bitmap$0$1)
  };
  return this.document$1
});
var $d_Lorg_scalajs_dom_package$ = new $TypeData().initClass({
  Lorg_scalajs_dom_package$: 0
}, false, "org.scalajs.dom.package$", {
  Lorg_scalajs_dom_package$: 1,
  O: 1
});
$c_Lorg_scalajs_dom_package$.prototype.$classData = $d_Lorg_scalajs_dom_package$;
var $n_Lorg_scalajs_dom_package$ = (void 0);
function $m_Lorg_scalajs_dom_package$() {
  if ((!$n_Lorg_scalajs_dom_package$)) {
    $n_Lorg_scalajs_dom_package$ = new $c_Lorg_scalajs_dom_package$()
  };
  return $n_Lorg_scalajs_dom_package$
}
/** @constructor */
function $c_jl_Class(data0) {
  this.data$1 = null;
  this.data$1 = data0
}
$c_jl_Class.prototype = new $h_O();
$c_jl_Class.prototype.constructor = $c_jl_Class;
/** @constructor */
function $h_jl_Class() {
  /*<skip>*/
}
$h_jl_Class.prototype = $c_jl_Class.prototype;
$c_jl_Class.prototype.getName__T = (function() {
  return $as_T(this.data$1.name)
});
$c_jl_Class.prototype.getComponentType__jl_Class = (function() {
  return $as_jl_Class(this.data$1.getComponentType())
});
$c_jl_Class.prototype.isPrimitive__Z = (function() {
  return $uZ(this.data$1.isPrimitive)
});
$c_jl_Class.prototype.toString__T = (function() {
  return ((this.isInterface__Z() ? "interface " : (this.isPrimitive__Z() ? "" : "class ")) + this.getName__T())
});
$c_jl_Class.prototype.isAssignableFrom__jl_Class__Z = (function(that) {
  return $uZ(this.data$1.isAssignableFrom(that.data$1))
});
$c_jl_Class.prototype.newArrayOfThisClass__sjs_js_Array__O = (function(dimensions) {
  return this.data$1.newArrayOfThisClass(dimensions)
});
$c_jl_Class.prototype.isArray__Z = (function() {
  return $uZ(this.data$1.isArrayClass)
});
$c_jl_Class.prototype.isInterface__Z = (function() {
  return $uZ(this.data$1.isInterface)
});
function $is_jl_Class(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.jl_Class)))
}
function $as_jl_Class(obj) {
  return (($is_jl_Class(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "java.lang.Class"))
}
function $isArrayOf_jl_Class(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.jl_Class)))
}
function $asArrayOf_jl_Class(obj, depth) {
  return (($isArrayOf_jl_Class(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.Class;", depth))
}
var $d_jl_Class = new $TypeData().initClass({
  jl_Class: 0
}, false, "java.lang.Class", {
  jl_Class: 1,
  O: 1
});
$c_jl_Class.prototype.$classData = $d_jl_Class;
/** @constructor */
function $c_jl_FloatingPointBits$() {
  this.java$lang$FloatingPointBits$$$undareTypedArraysSupported$f = false;
  this.arrayBuffer$1 = null;
  this.int32Array$1 = null;
  this.float32Array$1 = null;
  this.float64Array$1 = null;
  this.areTypedArraysBigEndian$1 = false;
  this.highOffset$1 = 0;
  this.lowOffset$1 = 0;
  $n_jl_FloatingPointBits$ = this;
  this.java$lang$FloatingPointBits$$$undareTypedArraysSupported$f = (((($as_T((typeof ArrayBuffer)) !== "undefined") && ($as_T((typeof Int32Array)) !== "undefined")) && ($as_T((typeof Float32Array)) !== "undefined")) && ($as_T((typeof Float64Array)) !== "undefined"));
  this.arrayBuffer$1 = (this.java$lang$FloatingPointBits$$$undareTypedArraysSupported$f ? new ArrayBuffer(8) : null);
  this.int32Array$1 = (this.java$lang$FloatingPointBits$$$undareTypedArraysSupported$f ? new Int32Array(this.arrayBuffer$1, 0, 2) : null);
  this.float32Array$1 = (this.java$lang$FloatingPointBits$$$undareTypedArraysSupported$f ? new Float32Array(this.arrayBuffer$1, 0, 2) : null);
  this.float64Array$1 = (this.java$lang$FloatingPointBits$$$undareTypedArraysSupported$f ? new Float64Array(this.arrayBuffer$1, 0, 1) : null);
  if ((!this.java$lang$FloatingPointBits$$$undareTypedArraysSupported$f)) {
    var jsx$1 = true
  } else {
    this.int32Array$1[0] = 16909060;
    var jsx$1 = ($uB(new Int8Array(this.arrayBuffer$1, 0, 8)[0]) === 1)
  };
  this.areTypedArraysBigEndian$1 = jsx$1;
  this.highOffset$1 = (this.areTypedArraysBigEndian$1 ? 0 : 1);
  this.lowOffset$1 = (this.areTypedArraysBigEndian$1 ? 1 : 0)
}
$c_jl_FloatingPointBits$.prototype = new $h_O();
$c_jl_FloatingPointBits$.prototype.constructor = $c_jl_FloatingPointBits$;
/** @constructor */
function $h_jl_FloatingPointBits$() {
  /*<skip>*/
}
$h_jl_FloatingPointBits$.prototype = $c_jl_FloatingPointBits$.prototype;
$c_jl_FloatingPointBits$.prototype.numberHashCode__D__I = (function(value) {
  var iv = $uI((value | 0));
  if (((iv === value) && ((1.0 / value) !== (-Infinity)))) {
    return iv
  } else {
    var t = this.doubleToLongBits__D__J(value);
    var lo = t.lo$2;
    var hi = t.hi$2;
    return (lo ^ hi)
  }
});
$c_jl_FloatingPointBits$.prototype.doubleToLongBitsPolyfill__p1__D__J = (function(value) {
  if ((value !== value)) {
    var _3 = $uD(Math.pow(2.0, 51.0));
    var x1_$_$$und1$1 = false;
    var x1_$_$$und2$1 = 2047;
    var x1_$_$$und3$1 = _3
  } else if (((value === Infinity) || (value === (-Infinity)))) {
    var _1 = (value < 0.0);
    var x1_$_$$und1$1 = _1;
    var x1_$_$$und2$1 = 2047;
    var x1_$_$$und3$1 = 0.0
  } else if ((value === 0.0)) {
    var _1$1 = ((1.0 / value) === (-Infinity));
    var x1_$_$$und1$1 = _1$1;
    var x1_$_$$und2$1 = 0;
    var x1_$_$$und3$1 = 0.0
  } else {
    var s = (value < 0.0);
    var av = (s ? (-value) : value);
    if ((av >= $uD(Math.pow(2.0, (-1022.0))))) {
      var twoPowFbits = $uD(Math.pow(2.0, 52.0));
      var a = ($uD(Math.log(av)) / 0.6931471805599453);
      var x = $uD(Math.floor(a));
      var a$1 = $uI((x | 0));
      var e = ((a$1 < 1023) ? a$1 : 1023);
      var b = e;
      var twoPowE = $uD(Math.pow(2.0, b));
      if ((twoPowE > av)) {
        e = (((-1) + e) | 0);
        twoPowE = (twoPowE / 2.0)
      };
      var n = ((av / twoPowE) * twoPowFbits);
      var w = $uD(Math.floor(n));
      var f = (n - w);
      var f$1 = ((f < 0.5) ? w : ((f > 0.5) ? (1.0 + w) : (((w % 2.0) !== 0.0) ? (1.0 + w) : w)));
      if (((f$1 / twoPowFbits) >= 2.0)) {
        e = ((1 + e) | 0);
        f$1 = 1.0
      };
      if ((e > 1023)) {
        e = 2047;
        f$1 = 0.0
      } else {
        e = ((1023 + e) | 0);
        f$1 = (f$1 - twoPowFbits)
      };
      var _2 = e;
      var _3$1 = f$1;
      var x1_$_$$und1$1 = s;
      var x1_$_$$und2$1 = _2;
      var x1_$_$$und3$1 = _3$1
    } else {
      var n$1 = (av / $uD(Math.pow(2.0, (-1074.0))));
      var w$1 = $uD(Math.floor(n$1));
      var f$2 = (n$1 - w$1);
      var _3$2 = ((f$2 < 0.5) ? w$1 : ((f$2 > 0.5) ? (1.0 + w$1) : (((w$1 % 2.0) !== 0.0) ? (1.0 + w$1) : w$1)));
      var x1_$_$$und1$1 = s;
      var x1_$_$$und2$1 = 0;
      var x1_$_$$und3$1 = _3$2
    }
  };
  var s$1 = $uZ(x1_$_$$und1$1);
  var e$1 = $uI(x1_$_$$und2$1);
  var f$3 = $uD(x1_$_$$und3$1);
  var x$1 = (f$3 / 4.294967296E9);
  var hif = $uI((x$1 | 0));
  var hi = (((s$1 ? (-2147483648) : 0) | (e$1 << 20)) | hif);
  var lo = $uI((f$3 | 0));
  return new $c_sjsr_RuntimeLong(lo, hi)
});
$c_jl_FloatingPointBits$.prototype.doubleToLongBits__D__J = (function(value) {
  if (this.java$lang$FloatingPointBits$$$undareTypedArraysSupported$f) {
    this.float64Array$1[0] = value;
    var value$1 = $uI(this.int32Array$1[this.highOffset$1]);
    var value$2 = $uI(this.int32Array$1[this.lowOffset$1]);
    return new $c_sjsr_RuntimeLong(value$2, value$1)
  } else {
    return this.doubleToLongBitsPolyfill__p1__D__J(value)
  }
});
var $d_jl_FloatingPointBits$ = new $TypeData().initClass({
  jl_FloatingPointBits$: 0
}, false, "java.lang.FloatingPointBits$", {
  jl_FloatingPointBits$: 1,
  O: 1
});
$c_jl_FloatingPointBits$.prototype.$classData = $d_jl_FloatingPointBits$;
var $n_jl_FloatingPointBits$ = (void 0);
function $m_jl_FloatingPointBits$() {
  if ((!$n_jl_FloatingPointBits$)) {
    $n_jl_FloatingPointBits$ = new $c_jl_FloatingPointBits$()
  };
  return $n_jl_FloatingPointBits$
}
/** @constructor */
function $c_jl_Math$() {
  /*<skip>*/
}
$c_jl_Math$.prototype = new $h_O();
$c_jl_Math$.prototype.constructor = $c_jl_Math$;
/** @constructor */
function $h_jl_Math$() {
  /*<skip>*/
}
$h_jl_Math$.prototype = $c_jl_Math$.prototype;
$c_jl_Math$.prototype.hypot__D__D__D = (function(a, b) {
  var v = Math.hypot;
  if ((!(v === (void 0)))) {
    return $uD(Math.hypot(a, b))
  } else if ((($uD(Math.abs(a)) === Infinity) || ($uD(Math.abs(b)) === Infinity))) {
    return Infinity
  } else if (((a !== a) || (b !== b))) {
    return (NaN)
  } else if (((a === 0.0) && (b === 0.0))) {
    return 0.0
  } else {
    var x = $uD(Math.abs(a));
    var y = $uD(Math.abs(b));
    var m = $uD(Math.max(x, y));
    var t = ($uD(Math.min(x, y)) / m);
    var a$1 = (1.0 + (t * t));
    return (m * $uD(Math.sqrt(a$1)))
  }
});
var $d_jl_Math$ = new $TypeData().initClass({
  jl_Math$: 0
}, false, "java.lang.Math$", {
  jl_Math$: 1,
  O: 1
});
$c_jl_Math$.prototype.$classData = $d_jl_Math$;
var $n_jl_Math$ = (void 0);
function $m_jl_Math$() {
  if ((!$n_jl_Math$)) {
    $n_jl_Math$ = new $c_jl_Math$()
  };
  return $n_jl_Math$
}
/** @constructor */
function $c_jl_System$() {
  this.out$1 = null;
  this.err$1 = null;
  this.in$1 = null;
  this.getHighPrecisionTime$1 = null;
  $n_jl_System$ = this;
  this.out$1 = new $c_jl_JSConsoleBasedPrintStream(false);
  this.err$1 = new $c_jl_JSConsoleBasedPrintStream(true);
  this.in$1 = null;
  if (($as_T((typeof performance)) !== "undefined")) {
    var x = performance.now;
    if ($uZ((!(!x)))) {
      var jsx$1 = (function() {
        return $m_jl_System$().java$lang$System$$$anonfun$getHighPrecisionTime$1__D()
      })
    } else {
      var x$1 = performance.webkitNow;
      if ($uZ((!(!x$1)))) {
        var jsx$1 = (function() {
          return $m_jl_System$().java$lang$System$$$anonfun$getHighPrecisionTime$2__D()
        })
      } else {
        var jsx$1 = (function() {
          return $m_jl_System$().java$lang$System$$$anonfun$getHighPrecisionTime$3__D()
        })
      }
    }
  } else {
    var jsx$1 = (function() {
      return $m_jl_System$().java$lang$System$$$anonfun$getHighPrecisionTime$4__D()
    })
  };
  this.getHighPrecisionTime$1 = jsx$1
}
$c_jl_System$.prototype = new $h_O();
$c_jl_System$.prototype.constructor = $c_jl_System$;
/** @constructor */
function $h_jl_System$() {
  /*<skip>*/
}
$h_jl_System$.prototype = $c_jl_System$.prototype;
$c_jl_System$.prototype.getenv__T__T = (function(name) {
  if ((name === null)) {
    throw new $c_jl_NullPointerException()
  };
  return null
});
$c_jl_System$.prototype.java$lang$System$$$anonfun$getHighPrecisionTime$3__D = (function() {
  return $uD(new Date().getTime())
});
$c_jl_System$.prototype.java$lang$System$$$anonfun$getHighPrecisionTime$1__D = (function() {
  return $uD(performance.now())
});
$c_jl_System$.prototype.java$lang$System$$$anonfun$getHighPrecisionTime$4__D = (function() {
  return $uD(new Date().getTime())
});
$c_jl_System$.prototype.java$lang$System$$$anonfun$getHighPrecisionTime$2__D = (function() {
  return $uD(performance.webkitNow())
});
var $d_jl_System$ = new $TypeData().initClass({
  jl_System$: 0
}, false, "java.lang.System$", {
  jl_System$: 1,
  O: 1
});
$c_jl_System$.prototype.$classData = $d_jl_System$;
var $n_jl_System$ = (void 0);
function $m_jl_System$() {
  if ((!$n_jl_System$)) {
    $n_jl_System$ = new $c_jl_System$()
  };
  return $n_jl_System$
}
/** @constructor */
function $c_jl_reflect_Array$() {
  /*<skip>*/
}
$c_jl_reflect_Array$.prototype = new $h_O();
$c_jl_reflect_Array$.prototype.constructor = $c_jl_reflect_Array$;
/** @constructor */
function $h_jl_reflect_Array$() {
  /*<skip>*/
}
$h_jl_reflect_Array$.prototype = $c_jl_reflect_Array$.prototype;
$c_jl_reflect_Array$.prototype.getLength__O__I = (function(array) {
  if ($isArrayOf_O(array, 1)) {
    var x2 = $asArrayOf_O(array, 1);
    return x2.u.length
  } else if ($isArrayOf_Z(array, 1)) {
    var x3 = $asArrayOf_Z(array, 1);
    return x3.u.length
  } else if ($isArrayOf_C(array, 1)) {
    var x4 = $asArrayOf_C(array, 1);
    return x4.u.length
  } else if ($isArrayOf_B(array, 1)) {
    var x5 = $asArrayOf_B(array, 1);
    return x5.u.length
  } else if ($isArrayOf_S(array, 1)) {
    var x6 = $asArrayOf_S(array, 1);
    return x6.u.length
  } else if ($isArrayOf_I(array, 1)) {
    var x7 = $asArrayOf_I(array, 1);
    return x7.u.length
  } else if ($isArrayOf_J(array, 1)) {
    var x8 = $asArrayOf_J(array, 1);
    return x8.u.length
  } else if ($isArrayOf_F(array, 1)) {
    var x9 = $asArrayOf_F(array, 1);
    return x9.u.length
  } else if ($isArrayOf_D(array, 1)) {
    var x10 = $asArrayOf_D(array, 1);
    return x10.u.length
  } else {
    throw new $c_jl_IllegalArgumentException().init___T("argument type mismatch")
  }
});
$c_jl_reflect_Array$.prototype.newInstance__jl_Class__I__O = (function(componentType, length) {
  return componentType.newArrayOfThisClass__sjs_js_Array__O([length])
});
var $d_jl_reflect_Array$ = new $TypeData().initClass({
  jl_reflect_Array$: 0
}, false, "java.lang.reflect.Array$", {
  jl_reflect_Array$: 1,
  O: 1
});
$c_jl_reflect_Array$.prototype.$classData = $d_jl_reflect_Array$;
var $n_jl_reflect_Array$ = (void 0);
function $m_jl_reflect_Array$() {
  if ((!$n_jl_reflect_Array$)) {
    $n_jl_reflect_Array$ = new $c_jl_reflect_Array$()
  };
  return $n_jl_reflect_Array$
}
/** @constructor */
function $c_ju_Arrays$() {
  /*<skip>*/
}
$c_ju_Arrays$.prototype = new $h_O();
$c_ju_Arrays$.prototype.constructor = $c_ju_Arrays$;
/** @constructor */
function $h_ju_Arrays$() {
  /*<skip>*/
}
$h_ju_Arrays$.prototype = $c_ju_Arrays$.prototype;
$c_ju_Arrays$.prototype.equals__AI__AI__Z = (function(a, b) {
  if ((a === b)) {
    return true
  } else if ((((a !== null) && (b !== null)) && (a.u.length === b.u.length))) {
    var this$2 = $m_sc_ArrayOps$().indices$extension__O__sci_Range(a);
    var res = true;
    var it = this$2.iterator__sc_Iterator();
    while ((res && it.hasNext__Z())) {
      var arg1 = it.next__O();
      var i = $uI(arg1);
      res = $m_sr_BoxesRunTime$().equals__O__O__Z(a.get(i), b.get(i))
    };
    return res
  } else {
    return false
  }
});
$c_ju_Arrays$.prototype.java$util$Arrays$$insertionSortAnyRef__AO__I__I__s_math_Ordering__V = (function(a, start, end, ord) {
  var n = ((end - start) | 0);
  if ((n >= 2)) {
    if ((ord.compare__O__O__I(a.get(start), a.get(((1 + start) | 0))) > 0)) {
      var temp = a.get(start);
      a.set(start, a.get(((1 + start) | 0)));
      a.set(((1 + start) | 0), temp)
    };
    var m = 2;
    while ((m < n)) {
      var next = a.get(((start + m) | 0));
      if ((ord.compare__O__O__I(next, a.get((((-1) + ((start + m) | 0)) | 0))) < 0)) {
        var iA = start;
        var iB = (((-1) + ((start + m) | 0)) | 0);
        while ((((iB - iA) | 0) > 1)) {
          var ix = ((((iA + iB) | 0) >>> 1) | 0);
          if ((ord.compare__O__O__I(next, a.get(ix)) < 0)) {
            iB = ix
          } else {
            iA = ix
          }
        };
        var ix$2 = ((iA + ((ord.compare__O__O__I(next, a.get(iA)) < 0) ? 0 : 1)) | 0);
        var i = ((start + m) | 0);
        while ((i > ix$2)) {
          a.set(i, a.get((((-1) + i) | 0)));
          i = (((-1) + i) | 0)
        };
        a.set(ix$2, next)
      };
      m = ((1 + m) | 0)
    }
  }
});
$c_ju_Arrays$.prototype.fill__AI__I__V = (function(a, value) {
  var toIndex = a.u.length;
  var i = 0;
  while ((i !== toIndex)) {
    a.set(i, value);
    i = ((1 + i) | 0)
  }
});
$c_ju_Arrays$.prototype.sort__AO__ju_Comparator__V = (function(array, comparator) {
  var ord = new $c_ju_Arrays$$anon$3(comparator);
  var end = array.u.length;
  if ((end > 16)) {
    this.java$util$Arrays$$stableSplitMergeAnyRef__AO__AO__I__I__s_math_Ordering__V(array, $newArrayObject($d_O.getArrayOf(), [array.u.length]), 0, end, ord)
  } else {
    this.java$util$Arrays$$insertionSortAnyRef__AO__I__I__s_math_Ordering__V(array, 0, end, ord)
  }
});
$c_ju_Arrays$.prototype.copyOf__AO__I__AO = (function(original, newLength) {
  var tagT = $m_s_reflect_ClassTag$().apply__jl_Class__s_reflect_ClassTag($objectGetClass(original).getComponentType__jl_Class());
  if ((newLength < 0)) {
    throw new $c_jl_NegativeArraySizeException()
  };
  var b = original.u.length;
  var copyLength = ((newLength < b) ? newLength : b);
  var ret = tagT.newArray__I__O(newLength);
  $systemArraycopy(original, 0, ret, 0, copyLength);
  return $asArrayOf_O(ret, 1)
});
$c_ju_Arrays$.prototype.java$util$Arrays$$stableSplitMergeAnyRef__AO__AO__I__I__s_math_Ordering__V = (function(a, temp, start, end, ord) {
  var length = ((end - start) | 0);
  if ((length > 16)) {
    var middle = ((start + ((length / 2) | 0)) | 0);
    this.java$util$Arrays$$stableSplitMergeAnyRef__AO__AO__I__I__s_math_Ordering__V(a, temp, start, middle, ord);
    this.java$util$Arrays$$stableSplitMergeAnyRef__AO__AO__I__I__s_math_Ordering__V(a, temp, middle, end, ord);
    var outIndex = start;
    var leftInIndex = start;
    var rightInIndex = middle;
    while ((outIndex < end)) {
      if ((leftInIndex < middle)) {
        if ((rightInIndex >= end)) {
          var jsx$1 = true
        } else {
          var x = a.get(leftInIndex);
          var y = a.get(rightInIndex);
          var jsx$1 = $f_s_math_Ordering__lteq__O__O__Z(ord, x, y)
        }
      } else {
        var jsx$1 = false
      };
      if (jsx$1) {
        temp.set(outIndex, a.get(leftInIndex));
        leftInIndex = ((1 + leftInIndex) | 0)
      } else {
        temp.set(outIndex, a.get(rightInIndex));
        rightInIndex = ((1 + rightInIndex) | 0)
      };
      outIndex = ((1 + outIndex) | 0)
    };
    $systemArraycopy(temp, start, a, start, length)
  } else {
    this.java$util$Arrays$$insertionSortAnyRef__AO__I__I__s_math_Ordering__V(a, start, end, ord)
  }
});
var $d_ju_Arrays$ = new $TypeData().initClass({
  ju_Arrays$: 0
}, false, "java.util.Arrays$", {
  ju_Arrays$: 1,
  O: 1
});
$c_ju_Arrays$.prototype.$classData = $d_ju_Arrays$;
var $n_ju_Arrays$ = (void 0);
function $m_ju_Arrays$() {
  if ((!$n_ju_Arrays$)) {
    $n_ju_Arrays$ = new $c_ju_Arrays$()
  };
  return $n_ju_Arrays$
}
/** @constructor */
function $c_s_LowPriorityImplicits2() {
  /*<skip>*/
}
$c_s_LowPriorityImplicits2.prototype = new $h_O();
$c_s_LowPriorityImplicits2.prototype.constructor = $c_s_LowPriorityImplicits2;
/** @constructor */
function $h_s_LowPriorityImplicits2() {
  /*<skip>*/
}
$h_s_LowPriorityImplicits2.prototype = $c_s_LowPriorityImplicits2.prototype;
/** @constructor */
function $c_s_math_Ordered$() {
  /*<skip>*/
}
$c_s_math_Ordered$.prototype = new $h_O();
$c_s_math_Ordered$.prototype.constructor = $c_s_math_Ordered$;
/** @constructor */
function $h_s_math_Ordered$() {
  /*<skip>*/
}
$h_s_math_Ordered$.prototype = $c_s_math_Ordered$.prototype;
var $d_s_math_Ordered$ = new $TypeData().initClass({
  s_math_Ordered$: 0
}, false, "scala.math.Ordered$", {
  s_math_Ordered$: 1,
  O: 1
});
$c_s_math_Ordered$.prototype.$classData = $d_s_math_Ordered$;
var $n_s_math_Ordered$ = (void 0);
function $m_s_math_Ordered$() {
  if ((!$n_s_math_Ordered$)) {
    $n_s_math_Ordered$ = new $c_s_math_Ordered$()
  };
  return $n_s_math_Ordered$
}
/** @constructor */
function $c_s_package$() {
  this.BigDecimal$1 = null;
  this.BigInt$1 = null;
  this.AnyRef$1 = null;
  this.Traversable$1 = null;
  this.Iterable$1 = null;
  this.Seq$1 = null;
  this.IndexedSeq$1 = null;
  this.Iterator$1 = null;
  this.List$1 = null;
  this.Nil$1 = null;
  this.$$colon$colon$1 = null;
  this.$$plus$colon$1 = null;
  this.$$colon$plus$1 = null;
  this.Stream$1 = null;
  this.LazyList$1 = null;
  this.Vector$1 = null;
  this.StringBuilder$1 = null;
  this.Range$1 = null;
  this.Equiv$1 = null;
  this.Fractional$1 = null;
  this.Integral$1 = null;
  this.Numeric$1 = null;
  this.Ordered$1 = null;
  this.Ordering$1 = null;
  this.Either$1 = null;
  this.Left$1 = null;
  this.Right$1 = null;
  this.bitmap$0$1 = 0;
  $n_s_package$ = this;
  this.AnyRef$1 = new $c_s_package$$anon$1();
  this.Traversable$1 = $m_sc_Iterable$();
  this.Iterable$1 = $m_sc_Iterable$();
  this.Seq$1 = $m_sci_Seq$();
  this.IndexedSeq$1 = $m_sci_IndexedSeq$();
  this.Iterator$1 = $m_sc_Iterator$();
  this.List$1 = $m_sci_List$();
  this.Nil$1 = $m_sci_Nil$();
  this.$$colon$colon$1 = $m_sci_$colon$colon$();
  this.$$plus$colon$1 = $m_sc_package$$plus$colon$();
  this.$$colon$plus$1 = $m_sc_package$$colon$plus$();
  this.Stream$1 = $m_sci_Stream$();
  this.LazyList$1 = $m_sci_LazyList$();
  this.Vector$1 = $m_sci_Vector$();
  this.StringBuilder$1 = $m_scm_StringBuilder$();
  this.Range$1 = $m_sci_Range$();
  this.Equiv$1 = $m_s_math_Equiv$();
  this.Fractional$1 = $m_s_math_Fractional$();
  this.Integral$1 = $m_s_math_Integral$();
  this.Numeric$1 = $m_s_math_Numeric$();
  this.Ordered$1 = $m_s_math_Ordered$();
  this.Ordering$1 = $m_s_math_Ordering$();
  this.Either$1 = $m_s_util_Either$();
  this.Left$1 = $m_s_util_Left$();
  this.Right$1 = $m_s_util_Right$()
}
$c_s_package$.prototype = new $h_O();
$c_s_package$.prototype.constructor = $c_s_package$;
/** @constructor */
function $h_s_package$() {
  /*<skip>*/
}
$h_s_package$.prototype = $c_s_package$.prototype;
var $d_s_package$ = new $TypeData().initClass({
  s_package$: 0
}, false, "scala.package$", {
  s_package$: 1,
  O: 1
});
$c_s_package$.prototype.$classData = $d_s_package$;
var $n_s_package$ = (void 0);
function $m_s_package$() {
  if ((!$n_s_package$)) {
    $n_s_package$ = new $c_s_package$()
  };
  return $n_s_package$
}
/** @constructor */
function $c_s_reflect_ClassManifestFactory$() {
  this.Byte$1 = null;
  this.Short$1 = null;
  this.Char$1 = null;
  this.Int$1 = null;
  this.Long$1 = null;
  this.Float$1 = null;
  this.Double$1 = null;
  this.Boolean$1 = null;
  this.Unit$1 = null;
  this.Any$1 = null;
  this.Object$1 = null;
  this.AnyVal$1 = null;
  this.Nothing$1 = null;
  this.Null$1 = null;
  $n_s_reflect_ClassManifestFactory$ = this;
  this.Byte$1 = $m_s_reflect_ManifestFactory$ByteManifest$();
  this.Short$1 = $m_s_reflect_ManifestFactory$ShortManifest$();
  this.Char$1 = $m_s_reflect_ManifestFactory$CharManifest$();
  this.Int$1 = $m_s_reflect_ManifestFactory$IntManifest$();
  this.Long$1 = $m_s_reflect_ManifestFactory$LongManifest$();
  this.Float$1 = $m_s_reflect_ManifestFactory$FloatManifest$();
  this.Double$1 = $m_s_reflect_ManifestFactory$DoubleManifest$();
  this.Boolean$1 = $m_s_reflect_ManifestFactory$BooleanManifest$();
  this.Unit$1 = $m_s_reflect_ManifestFactory$UnitManifest$();
  this.Any$1 = $m_s_reflect_ManifestFactory$AnyManifest$();
  this.Object$1 = $m_s_reflect_ManifestFactory$ObjectManifest$();
  this.AnyVal$1 = $m_s_reflect_ManifestFactory$AnyValManifest$();
  this.Nothing$1 = $m_s_reflect_ManifestFactory$NothingManifest$();
  this.Null$1 = $m_s_reflect_ManifestFactory$NullManifest$()
}
$c_s_reflect_ClassManifestFactory$.prototype = new $h_O();
$c_s_reflect_ClassManifestFactory$.prototype.constructor = $c_s_reflect_ClassManifestFactory$;
/** @constructor */
function $h_s_reflect_ClassManifestFactory$() {
  /*<skip>*/
}
$h_s_reflect_ClassManifestFactory$.prototype = $c_s_reflect_ClassManifestFactory$.prototype;
var $d_s_reflect_ClassManifestFactory$ = new $TypeData().initClass({
  s_reflect_ClassManifestFactory$: 0
}, false, "scala.reflect.ClassManifestFactory$", {
  s_reflect_ClassManifestFactory$: 1,
  O: 1
});
$c_s_reflect_ClassManifestFactory$.prototype.$classData = $d_s_reflect_ClassManifestFactory$;
var $n_s_reflect_ClassManifestFactory$ = (void 0);
function $m_s_reflect_ClassManifestFactory$() {
  if ((!$n_s_reflect_ClassManifestFactory$)) {
    $n_s_reflect_ClassManifestFactory$ = new $c_s_reflect_ClassManifestFactory$()
  };
  return $n_s_reflect_ClassManifestFactory$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$() {
  /*<skip>*/
}
$c_s_reflect_ManifestFactory$.prototype = new $h_O();
$c_s_reflect_ManifestFactory$.prototype.constructor = $c_s_reflect_ManifestFactory$;
/** @constructor */
function $h_s_reflect_ManifestFactory$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$.prototype = $c_s_reflect_ManifestFactory$.prototype;
var $d_s_reflect_ManifestFactory$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$: 0
}, false, "scala.reflect.ManifestFactory$", {
  s_reflect_ManifestFactory$: 1,
  O: 1
});
$c_s_reflect_ManifestFactory$.prototype.$classData = $d_s_reflect_ManifestFactory$;
var $n_s_reflect_ManifestFactory$ = (void 0);
function $m_s_reflect_ManifestFactory$() {
  if ((!$n_s_reflect_ManifestFactory$)) {
    $n_s_reflect_ManifestFactory$ = new $c_s_reflect_ManifestFactory$()
  };
  return $n_s_reflect_ManifestFactory$
}
/** @constructor */
function $c_s_reflect_package$() {
  this.ClassManifest$1 = null;
  this.Manifest$1 = null;
  $n_s_reflect_package$ = this;
  this.ClassManifest$1 = $m_s_reflect_ClassManifestFactory$();
  this.Manifest$1 = $m_s_reflect_ManifestFactory$()
}
$c_s_reflect_package$.prototype = new $h_O();
$c_s_reflect_package$.prototype.constructor = $c_s_reflect_package$;
/** @constructor */
function $h_s_reflect_package$() {
  /*<skip>*/
}
$h_s_reflect_package$.prototype = $c_s_reflect_package$.prototype;
var $d_s_reflect_package$ = new $TypeData().initClass({
  s_reflect_package$: 0
}, false, "scala.reflect.package$", {
  s_reflect_package$: 1,
  O: 1
});
$c_s_reflect_package$.prototype.$classData = $d_s_reflect_package$;
var $n_s_reflect_package$ = (void 0);
function $m_s_reflect_package$() {
  if ((!$n_s_reflect_package$)) {
    $n_s_reflect_package$ = new $c_s_reflect_package$()
  };
  return $n_s_reflect_package$
}
/** @constructor */
function $c_s_util_hashing_MurmurHash3() {
  /*<skip>*/
}
$c_s_util_hashing_MurmurHash3.prototype = new $h_O();
$c_s_util_hashing_MurmurHash3.prototype.constructor = $c_s_util_hashing_MurmurHash3;
/** @constructor */
function $h_s_util_hashing_MurmurHash3() {
  /*<skip>*/
}
$h_s_util_hashing_MurmurHash3.prototype = $c_s_util_hashing_MurmurHash3.prototype;
$c_s_util_hashing_MurmurHash3.prototype.mixLast__I__I__I = (function(hash, data) {
  var k = data;
  k = $imul((-862048943), k);
  var i = k;
  k = ((i << 15) | ((i >>> 17) | 0));
  k = $imul(461845907, k);
  return (hash ^ k)
});
$c_s_util_hashing_MurmurHash3.prototype.unorderedHash__sc_IterableOnce__I__I = (function(xs, seed) {
  var elem$1 = 0;
  elem$1 = 0;
  var elem$1$1 = 0;
  elem$1$1 = 0;
  var elem$1$2 = 0;
  elem$1$2 = 0;
  var elem$1$3 = 0;
  elem$1$3 = 1;
  var this$5 = xs.iterator__sc_Iterator();
  while (this$5.hasNext__Z()) {
    var arg1 = this$5.next__O();
    var h = $m_sr_Statics$().anyHash__O__I(arg1);
    elem$1 = ((elem$1 + h) | 0);
    elem$1$1 = (elem$1$1 ^ h);
    if ((h !== 0)) {
      elem$1$3 = $imul(elem$1$3, h)
    };
    elem$1$2 = ((1 + elem$1$2) | 0)
  };
  var h$1 = seed;
  h$1 = this.mix__I__I__I(h$1, elem$1);
  h$1 = this.mix__I__I__I(h$1, elem$1$1);
  h$1 = this.mixLast__I__I__I(h$1, elem$1$3);
  return this.finalizeHash__I__I__I(h$1, elem$1$2)
});
$c_s_util_hashing_MurmurHash3.prototype.mix__I__I__I = (function(hash, data) {
  var h = this.mixLast__I__I__I(hash, data);
  var i = h;
  h = ((i << 13) | ((i >>> 19) | 0));
  return (((-430675100) + $imul(5, h)) | 0)
});
$c_s_util_hashing_MurmurHash3.prototype.avalanche__p1__I__I = (function(hash) {
  var h = hash;
  h = (h ^ ((h >>> 16) | 0));
  h = $imul((-2048144789), h);
  h = (h ^ ((h >>> 13) | 0));
  h = $imul((-1028477387), h);
  h = (h ^ ((h >>> 16) | 0));
  return h
});
$c_s_util_hashing_MurmurHash3.prototype.orderedHash__sc_IterableOnce__I__I = (function(xs, seed) {
  var elem$1 = 0;
  elem$1 = 0;
  var elem$1$1 = 0;
  elem$1$1 = seed;
  var this$3 = xs.iterator__sc_Iterator();
  while (this$3.hasNext__Z()) {
    var arg1 = this$3.next__O();
    elem$1$1 = this.mix__I__I__I(elem$1$1, $m_sr_Statics$().anyHash__O__I(arg1));
    elem$1 = ((1 + elem$1) | 0)
  };
  return this.finalizeHash__I__I__I(elem$1$1, elem$1)
});
$c_s_util_hashing_MurmurHash3.prototype.productHash__s_Product__I__I = (function(x, seed) {
  var arr = x.productArity__I();
  if ((arr === 0)) {
    return $f_T__hashCode__I(x.productPrefix__T())
  } else {
    var h = seed;
    var i = 0;
    while ((i < arr)) {
      h = this.mix__I__I__I(h, $m_sr_Statics$().anyHash__O__I(x.productElement__I__O(i)));
      i = ((1 + i) | 0)
    };
    return this.finalizeHash__I__I__I(h, arr)
  }
});
$c_s_util_hashing_MurmurHash3.prototype.finalizeHash__I__I__I = (function(hash, length) {
  return this.avalanche__p1__I__I((hash ^ length))
});
$c_s_util_hashing_MurmurHash3.prototype.listHash__sci_List__I__I = (function(xs, seed) {
  var n = 0;
  var h = seed;
  var elems = xs;
  while ((!elems.isEmpty__Z())) {
    var head = elems.head__O();
    var tail = $as_sci_List(elems.tail__O());
    h = this.mix__I__I__I(h, $m_sr_Statics$().anyHash__O__I(head));
    n = ((1 + n) | 0);
    elems = tail
  };
  return this.finalizeHash__I__I__I(h, n)
});
/** @constructor */
function $c_s_util_hashing_package$() {
  /*<skip>*/
}
$c_s_util_hashing_package$.prototype = new $h_O();
$c_s_util_hashing_package$.prototype.constructor = $c_s_util_hashing_package$;
/** @constructor */
function $h_s_util_hashing_package$() {
  /*<skip>*/
}
$h_s_util_hashing_package$.prototype = $c_s_util_hashing_package$.prototype;
$c_s_util_hashing_package$.prototype.byteswap32__I__I = (function(v) {
  var hc = $imul((-1640532531), v);
  hc = $m_jl_Integer$().reverseBytes__I__I(hc);
  return $imul((-1640532531), hc)
});
var $d_s_util_hashing_package$ = new $TypeData().initClass({
  s_util_hashing_package$: 0
}, false, "scala.util.hashing.package$", {
  s_util_hashing_package$: 1,
  O: 1
});
$c_s_util_hashing_package$.prototype.$classData = $d_s_util_hashing_package$;
var $n_s_util_hashing_package$ = (void 0);
function $m_s_util_hashing_package$() {
  if ((!$n_s_util_hashing_package$)) {
    $n_s_util_hashing_package$ = new $c_s_util_hashing_package$()
  };
  return $n_s_util_hashing_package$
}
/** @constructor */
function $c_sc_ArrayOps$() {
  /*<skip>*/
}
$c_sc_ArrayOps$.prototype = new $h_O();
$c_sc_ArrayOps$.prototype.constructor = $c_sc_ArrayOps$;
/** @constructor */
function $h_sc_ArrayOps$() {
  /*<skip>*/
}
$h_sc_ArrayOps$.prototype = $c_sc_ArrayOps$.prototype;
$c_sc_ArrayOps$.prototype.indices$extension__O__sci_Range = (function($$this) {
  var end = $m_sr_ScalaRunTime$().array$undlength__O__I($$this);
  return new $c_sci_Range$Exclusive(0, end, 1)
});
var $d_sc_ArrayOps$ = new $TypeData().initClass({
  sc_ArrayOps$: 0
}, false, "scala.collection.ArrayOps$", {
  sc_ArrayOps$: 1,
  O: 1
});
$c_sc_ArrayOps$.prototype.$classData = $d_sc_ArrayOps$;
var $n_sc_ArrayOps$ = (void 0);
function $m_sc_ArrayOps$() {
  if ((!$n_sc_ArrayOps$)) {
    $n_sc_ArrayOps$ = new $c_sc_ArrayOps$()
  };
  return $n_sc_ArrayOps$
}
/** @constructor */
function $c_sc_Hashing$() {
  /*<skip>*/
}
$c_sc_Hashing$.prototype = new $h_O();
$c_sc_Hashing$.prototype.constructor = $c_sc_Hashing$;
/** @constructor */
function $h_sc_Hashing$() {
  /*<skip>*/
}
$h_sc_Hashing$.prototype = $c_sc_Hashing$.prototype;
$c_sc_Hashing$.prototype.computeHash__O__I = (function(key) {
  return this.improve__I__I($m_sr_Statics$().anyHash__O__I(key))
});
$c_sc_Hashing$.prototype.improve__I__I = (function(hcode) {
  var h = ((hcode + (~(hcode << 9))) | 0);
  h = (h ^ ((h >>> 14) | 0));
  h = ((h + (h << 4)) | 0);
  return (h ^ ((h >>> 10) | 0))
});
$c_sc_Hashing$.prototype.keepBits__I__I__I = (function(bitmap, keep) {
  var result = 0;
  var current = bitmap;
  var kept = keep;
  while ((kept !== 0)) {
    var lsb = (current ^ (current & (((-1) + current) | 0)));
    if (((1 & kept) !== 0)) {
      result = (result | lsb)
    };
    current = (current & (~lsb));
    kept = ((kept >>> 1) | 0)
  };
  return result
});
var $d_sc_Hashing$ = new $TypeData().initClass({
  sc_Hashing$: 0
}, false, "scala.collection.Hashing$", {
  sc_Hashing$: 1,
  O: 1
});
$c_sc_Hashing$.prototype.$classData = $d_sc_Hashing$;
var $n_sc_Hashing$ = (void 0);
function $m_sc_Hashing$() {
  if ((!$n_sc_Hashing$)) {
    $n_sc_Hashing$ = new $c_sc_Hashing$()
  };
  return $n_sc_Hashing$
}
/** @constructor */
function $c_sc_IterableOnceExtensionMethods$() {
  /*<skip>*/
}
$c_sc_IterableOnceExtensionMethods$.prototype = new $h_O();
$c_sc_IterableOnceExtensionMethods$.prototype.constructor = $c_sc_IterableOnceExtensionMethods$;
/** @constructor */
function $h_sc_IterableOnceExtensionMethods$() {
  /*<skip>*/
}
$h_sc_IterableOnceExtensionMethods$.prototype = $c_sc_IterableOnceExtensionMethods$.prototype;
$c_sc_IterableOnceExtensionMethods$.prototype.isEmpty$extension__sc_IterableOnce__Z = (function($$this) {
  if ($is_sc_Iterable($$this)) {
    var x2 = $as_sc_Iterable($$this);
    return x2.isEmpty__Z()
  } else {
    var this$1 = $$this.iterator__sc_Iterator();
    return (!this$1.hasNext__Z())
  }
});
var $d_sc_IterableOnceExtensionMethods$ = new $TypeData().initClass({
  sc_IterableOnceExtensionMethods$: 0
}, false, "scala.collection.IterableOnceExtensionMethods$", {
  sc_IterableOnceExtensionMethods$: 1,
  O: 1
});
$c_sc_IterableOnceExtensionMethods$.prototype.$classData = $d_sc_IterableOnceExtensionMethods$;
var $n_sc_IterableOnceExtensionMethods$ = (void 0);
function $m_sc_IterableOnceExtensionMethods$() {
  if ((!$n_sc_IterableOnceExtensionMethods$)) {
    $n_sc_IterableOnceExtensionMethods$ = new $c_sc_IterableOnceExtensionMethods$()
  };
  return $n_sc_IterableOnceExtensionMethods$
}
/** @constructor */
function $c_sc_Iterator$ConcatIteratorCell(head, tail) {
  this.head$1 = null;
  this.tail$1 = null;
  this.head$1 = head;
  this.tail$1 = tail
}
$c_sc_Iterator$ConcatIteratorCell.prototype = new $h_O();
$c_sc_Iterator$ConcatIteratorCell.prototype.constructor = $c_sc_Iterator$ConcatIteratorCell;
/** @constructor */
function $h_sc_Iterator$ConcatIteratorCell() {
  /*<skip>*/
}
$h_sc_Iterator$ConcatIteratorCell.prototype = $c_sc_Iterator$ConcatIteratorCell.prototype;
$c_sc_Iterator$ConcatIteratorCell.prototype.headIterator__sc_Iterator = (function() {
  return $as_sc_IterableOnce(this.head$1.apply__O()).iterator__sc_Iterator()
});
var $d_sc_Iterator$ConcatIteratorCell = new $TypeData().initClass({
  sc_Iterator$ConcatIteratorCell: 0
}, false, "scala.collection.Iterator$ConcatIteratorCell", {
  sc_Iterator$ConcatIteratorCell: 1,
  O: 1
});
$c_sc_Iterator$ConcatIteratorCell.prototype.$classData = $d_sc_Iterator$ConcatIteratorCell;
/** @constructor */
function $c_sc_LinearSeqIterator$LazyCell($$outer, st) {
  this.v$1 = null;
  this.st$1 = null;
  this.bitmap$0$1 = false;
  this.st$1 = st
}
$c_sc_LinearSeqIterator$LazyCell.prototype = new $h_O();
$c_sc_LinearSeqIterator$LazyCell.prototype.constructor = $c_sc_LinearSeqIterator$LazyCell;
/** @constructor */
function $h_sc_LinearSeqIterator$LazyCell() {
  /*<skip>*/
}
$h_sc_LinearSeqIterator$LazyCell.prototype = $c_sc_LinearSeqIterator$LazyCell.prototype;
$c_sc_LinearSeqIterator$LazyCell.prototype.v$lzycompute__p1__sc_Seq = (function() {
  if ((!this.bitmap$0$1)) {
    this.v$1 = $as_sc_Seq(this.st$1.apply__O());
    this.bitmap$0$1 = true
  };
  this.st$1 = null;
  return this.v$1
});
$c_sc_LinearSeqIterator$LazyCell.prototype.v__sc_Seq = (function() {
  return ((!this.bitmap$0$1) ? this.v$lzycompute__p1__sc_Seq() : this.v$1)
});
var $d_sc_LinearSeqIterator$LazyCell = new $TypeData().initClass({
  sc_LinearSeqIterator$LazyCell: 0
}, false, "scala.collection.LinearSeqIterator$LazyCell", {
  sc_LinearSeqIterator$LazyCell: 1,
  O: 1
});
$c_sc_LinearSeqIterator$LazyCell.prototype.$classData = $d_sc_LinearSeqIterator$LazyCell;
/** @constructor */
function $c_sc_WithFilter() {
  /*<skip>*/
}
$c_sc_WithFilter.prototype = new $h_O();
$c_sc_WithFilter.prototype.constructor = $c_sc_WithFilter;
/** @constructor */
function $h_sc_WithFilter() {
  /*<skip>*/
}
$h_sc_WithFilter.prototype = $c_sc_WithFilter.prototype;
/** @constructor */
function $c_sc_package$$colon$plus$() {
  /*<skip>*/
}
$c_sc_package$$colon$plus$.prototype = new $h_O();
$c_sc_package$$colon$plus$.prototype.constructor = $c_sc_package$$colon$plus$;
/** @constructor */
function $h_sc_package$$colon$plus$() {
  /*<skip>*/
}
$h_sc_package$$colon$plus$.prototype = $c_sc_package$$colon$plus$.prototype;
var $d_sc_package$$colon$plus$ = new $TypeData().initClass({
  sc_package$$colon$plus$: 0
}, false, "scala.collection.package$$colon$plus$", {
  sc_package$$colon$plus$: 1,
  O: 1
});
$c_sc_package$$colon$plus$.prototype.$classData = $d_sc_package$$colon$plus$;
var $n_sc_package$$colon$plus$ = (void 0);
function $m_sc_package$$colon$plus$() {
  if ((!$n_sc_package$$colon$plus$)) {
    $n_sc_package$$colon$plus$ = new $c_sc_package$$colon$plus$()
  };
  return $n_sc_package$$colon$plus$
}
/** @constructor */
function $c_sc_package$$plus$colon$() {
  /*<skip>*/
}
$c_sc_package$$plus$colon$.prototype = new $h_O();
$c_sc_package$$plus$colon$.prototype.constructor = $c_sc_package$$plus$colon$;
/** @constructor */
function $h_sc_package$$plus$colon$() {
  /*<skip>*/
}
$h_sc_package$$plus$colon$.prototype = $c_sc_package$$plus$colon$.prototype;
var $d_sc_package$$plus$colon$ = new $TypeData().initClass({
  sc_package$$plus$colon$: 0
}, false, "scala.collection.package$$plus$colon$", {
  sc_package$$plus$colon$: 1,
  O: 1
});
$c_sc_package$$plus$colon$.prototype.$classData = $d_sc_package$$plus$colon$;
var $n_sc_package$$plus$colon$ = (void 0);
function $m_sc_package$$plus$colon$() {
  if ((!$n_sc_package$$plus$colon$)) {
    $n_sc_package$$plus$colon$ = new $c_sc_package$$plus$colon$()
  };
  return $n_sc_package$$plus$colon$
}
/** @constructor */
function $c_sci_ChampBaseIterator() {
  this.currentValueCursor$1 = 0;
  this.currentValueLength$1 = 0;
  this.currentValueNode$1 = null;
  this.currentStackLevel$1 = 0;
  this.nodeCursorsAndLengths$1 = null;
  this.nodes$1 = null
}
$c_sci_ChampBaseIterator.prototype = new $h_O();
$c_sci_ChampBaseIterator.prototype.constructor = $c_sci_ChampBaseIterator;
/** @constructor */
function $h_sci_ChampBaseIterator() {
  /*<skip>*/
}
$h_sci_ChampBaseIterator.prototype = $c_sci_ChampBaseIterator.prototype;
$c_sci_ChampBaseIterator.prototype.init___ = (function() {
  this.currentValueCursor$1 = 0;
  this.currentValueLength$1 = 0;
  this.currentStackLevel$1 = (-1);
  this.nodeCursorsAndLengths$1 = $newArrayObject($d_I.getArrayOf(), [($m_sci_Node$().MaxDepth$1 << 1)]);
  this.nodes$1 = $newArrayObject($d_sci_Node.getArrayOf(), [$m_sci_Node$().MaxDepth$1]);
  return this
});
$c_sci_ChampBaseIterator.prototype.init___sci_Node = (function(rootNode) {
  $c_sci_ChampBaseIterator.prototype.init___.call(this);
  if (rootNode.hasNodes__Z()) {
    this.pushNode__p1__sci_Node__V(rootNode)
  };
  if (rootNode.hasPayload__Z()) {
    this.setupPayloadNode__p1__sci_Node__V(rootNode)
  };
  return this
});
$c_sci_ChampBaseIterator.prototype.popNode__p1__V = (function() {
  this.currentStackLevel$1 = (((-1) + this.currentStackLevel$1) | 0)
});
$c_sci_ChampBaseIterator.prototype.setupPayloadNode__p1__sci_Node__V = (function(node) {
  this.currentValueNode$1 = node;
  this.currentValueCursor$1 = 0;
  this.currentValueLength$1 = node.payloadArity__I()
});
$c_sci_ChampBaseIterator.prototype.hasNext__Z = (function() {
  return ((this.currentValueCursor$1 < this.currentValueLength$1) || this.searchNextValueNode__p1__Z())
});
$c_sci_ChampBaseIterator.prototype.searchNextValueNode__p1__Z = (function() {
  while ((this.currentStackLevel$1 >= 0)) {
    var cursorIndex = (this.currentStackLevel$1 << 1);
    var lengthIndex = ((1 + (this.currentStackLevel$1 << 1)) | 0);
    var nodeCursor = this.nodeCursorsAndLengths$1.get(cursorIndex);
    var nodeLength = this.nodeCursorsAndLengths$1.get(lengthIndex);
    if ((nodeCursor < nodeLength)) {
      this.nodeCursorsAndLengths$1.set(cursorIndex, ((1 + this.nodeCursorsAndLengths$1.get(cursorIndex)) | 0));
      var nextNode = this.nodes$1.get(this.currentStackLevel$1).getNode__I__sci_Node(nodeCursor);
      if (nextNode.hasNodes__Z()) {
        this.pushNode__p1__sci_Node__V(nextNode)
      };
      if (nextNode.hasPayload__Z()) {
        this.setupPayloadNode__p1__sci_Node__V(nextNode);
        return true
      }
    } else {
      this.popNode__p1__V()
    }
  };
  return false
});
$c_sci_ChampBaseIterator.prototype.pushNode__p1__sci_Node__V = (function(node) {
  this.currentStackLevel$1 = ((1 + this.currentStackLevel$1) | 0);
  var cursorIndex = (this.currentStackLevel$1 << 1);
  var lengthIndex = ((1 + (this.currentStackLevel$1 << 1)) | 0);
  this.nodes$1.set(this.currentStackLevel$1, node);
  this.nodeCursorsAndLengths$1.set(cursorIndex, 0);
  this.nodeCursorsAndLengths$1.set(lengthIndex, node.nodeArity__I())
});
/** @constructor */
function $c_sci_ChampBaseReverseIterator() {
  this.currentValueCursor$1 = 0;
  this.currentValueNode$1 = null;
  this.currentStackLevel$1 = 0;
  this.nodeIndex$1 = null;
  this.nodeStack$1 = null
}
$c_sci_ChampBaseReverseIterator.prototype = new $h_O();
$c_sci_ChampBaseReverseIterator.prototype.constructor = $c_sci_ChampBaseReverseIterator;
/** @constructor */
function $h_sci_ChampBaseReverseIterator() {
  /*<skip>*/
}
$h_sci_ChampBaseReverseIterator.prototype = $c_sci_ChampBaseReverseIterator.prototype;
$c_sci_ChampBaseReverseIterator.prototype.init___ = (function() {
  this.currentValueCursor$1 = (-1);
  this.currentStackLevel$1 = (-1);
  this.nodeIndex$1 = $newArrayObject($d_I.getArrayOf(), [((1 + $m_sci_Node$().MaxDepth$1) | 0)]);
  this.nodeStack$1 = $newArrayObject($d_sci_Node.getArrayOf(), [((1 + $m_sci_Node$().MaxDepth$1) | 0)]);
  return this
});
$c_sci_ChampBaseReverseIterator.prototype.init___sci_Node = (function(rootNode) {
  $c_sci_ChampBaseReverseIterator.prototype.init___.call(this);
  this.pushNode__p1__sci_Node__V(rootNode);
  this.searchNextValueNode__p1__Z();
  return this
});
$c_sci_ChampBaseReverseIterator.prototype.popNode__p1__V = (function() {
  this.currentStackLevel$1 = (((-1) + this.currentStackLevel$1) | 0)
});
$c_sci_ChampBaseReverseIterator.prototype.setupPayloadNode__p1__sci_Node__V = (function(node) {
  this.currentValueNode$1 = node;
  this.currentValueCursor$1 = (((-1) + node.payloadArity__I()) | 0)
});
$c_sci_ChampBaseReverseIterator.prototype.hasNext__Z = (function() {
  return ((this.currentValueCursor$1 >= 0) || this.searchNextValueNode__p1__Z())
});
$c_sci_ChampBaseReverseIterator.prototype.searchNextValueNode__p1__Z = (function() {
  while ((this.currentStackLevel$1 >= 0)) {
    var nodeCursor = this.nodeIndex$1.get(this.currentStackLevel$1);
    this.nodeIndex$1.set(this.currentStackLevel$1, (((-1) + nodeCursor) | 0));
    if ((nodeCursor >= 0)) {
      var nextNode = this.nodeStack$1.get(this.currentStackLevel$1).getNode__I__sci_Node(nodeCursor);
      this.pushNode__p1__sci_Node__V(nextNode)
    } else {
      var currNode = this.nodeStack$1.get(this.currentStackLevel$1);
      this.popNode__p1__V();
      if (currNode.hasPayload__Z()) {
        this.setupPayloadNode__p1__sci_Node__V(currNode);
        return true
      }
    }
  };
  return false
});
$c_sci_ChampBaseReverseIterator.prototype.pushNode__p1__sci_Node__V = (function(node) {
  this.currentStackLevel$1 = ((1 + this.currentStackLevel$1) | 0);
  this.nodeStack$1.set(this.currentStackLevel$1, node);
  this.nodeIndex$1.set(this.currentStackLevel$1, (((-1) + node.nodeArity__I()) | 0))
});
/** @constructor */
function $c_sci_MapKeyValueTupleHashIterator$$anon$1($$outer) {
  this.$$outer$1 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$1 = $$outer
  }
}
$c_sci_MapKeyValueTupleHashIterator$$anon$1.prototype = new $h_O();
$c_sci_MapKeyValueTupleHashIterator$$anon$1.prototype.constructor = $c_sci_MapKeyValueTupleHashIterator$$anon$1;
/** @constructor */
function $h_sci_MapKeyValueTupleHashIterator$$anon$1() {
  /*<skip>*/
}
$h_sci_MapKeyValueTupleHashIterator$$anon$1.prototype = $c_sci_MapKeyValueTupleHashIterator$$anon$1.prototype;
$c_sci_MapKeyValueTupleHashIterator$$anon$1.prototype.hashCode__I = (function() {
  return this.$$outer$1.scala$collection$immutable$MapKeyValueTupleHashIterator$$hash$f
});
var $d_sci_MapKeyValueTupleHashIterator$$anon$1 = new $TypeData().initClass({
  sci_MapKeyValueTupleHashIterator$$anon$1: 0
}, false, "scala.collection.immutable.MapKeyValueTupleHashIterator$$anon$1", {
  sci_MapKeyValueTupleHashIterator$$anon$1: 1,
  O: 1
});
$c_sci_MapKeyValueTupleHashIterator$$anon$1.prototype.$classData = $d_sci_MapKeyValueTupleHashIterator$$anon$1;
/** @constructor */
function $c_sci_MapNode$() {
  this.EmptyMapNode$1 = null;
  $n_sci_MapNode$ = this;
  this.EmptyMapNode$1 = new $c_sci_BitmapIndexedMapNode(0, 0, ($m_s_reflect_ManifestFactory$AnyManifest$(), $newArrayObject($d_O.getArrayOf(), [0])), ($m_s_reflect_ManifestFactory$IntManifest$(), $newArrayObject($d_I.getArrayOf(), [0])), 0)
}
$c_sci_MapNode$.prototype = new $h_O();
$c_sci_MapNode$.prototype.constructor = $c_sci_MapNode$;
/** @constructor */
function $h_sci_MapNode$() {
  /*<skip>*/
}
$h_sci_MapNode$.prototype = $c_sci_MapNode$.prototype;
var $d_sci_MapNode$ = new $TypeData().initClass({
  sci_MapNode$: 0
}, false, "scala.collection.immutable.MapNode$", {
  sci_MapNode$: 1,
  O: 1
});
$c_sci_MapNode$.prototype.$classData = $d_sci_MapNode$;
var $n_sci_MapNode$ = (void 0);
function $m_sci_MapNode$() {
  if ((!$n_sci_MapNode$)) {
    $n_sci_MapNode$ = new $c_sci_MapNode$()
  };
  return $n_sci_MapNode$
}
/** @constructor */
function $c_sci_Node() {
  /*<skip>*/
}
$c_sci_Node.prototype = new $h_O();
$c_sci_Node.prototype.constructor = $c_sci_Node;
/** @constructor */
function $h_sci_Node() {
  /*<skip>*/
}
$h_sci_Node.prototype = $c_sci_Node.prototype;
$c_sci_Node.prototype.insertElement__AI__I__I__AI = (function(as, ix, elem) {
  if ((ix < 0)) {
    throw new $c_jl_ArrayIndexOutOfBoundsException().init___()
  };
  if ((ix > as.u.length)) {
    throw new $c_jl_ArrayIndexOutOfBoundsException().init___()
  };
  var result = $newArrayObject($d_I.getArrayOf(), [((1 + as.u.length) | 0)]);
  $systemArraycopy(as, 0, result, 0, ix);
  result.set(ix, elem);
  $systemArraycopy(as, ix, result, ((1 + ix) | 0), ((as.u.length - ix) | 0));
  return result
});
$c_sci_Node.prototype.removeElement__AI__I__AI = (function(as, ix) {
  if ((ix < 0)) {
    throw new $c_jl_ArrayIndexOutOfBoundsException().init___()
  };
  if ((ix > (((-1) + as.u.length) | 0))) {
    throw new $c_jl_ArrayIndexOutOfBoundsException().init___()
  };
  var result = $newArrayObject($d_I.getArrayOf(), [(((-1) + as.u.length) | 0)]);
  $systemArraycopy(as, 0, result, 0, ix);
  $systemArraycopy(as, ((1 + ix) | 0), result, ix, (((-1) + ((as.u.length - ix) | 0)) | 0));
  return result
});
var $d_sci_Node = new $TypeData().initClass({
  sci_Node: 0
}, false, "scala.collection.immutable.Node", {
  sci_Node: 1,
  O: 1
});
$c_sci_Node.prototype.$classData = $d_sci_Node;
/** @constructor */
function $c_sci_Node$() {
  this.MaxDepth$1 = 0;
  $n_sci_Node$ = this;
  this.MaxDepth$1 = $doubleToInt($uD(Math.ceil(6.4)))
}
$c_sci_Node$.prototype = new $h_O();
$c_sci_Node$.prototype.constructor = $c_sci_Node$;
/** @constructor */
function $h_sci_Node$() {
  /*<skip>*/
}
$h_sci_Node$.prototype = $c_sci_Node$.prototype;
$c_sci_Node$.prototype.indexFrom__I__I__I = (function(bitmap, bitpos) {
  return $m_jl_Integer$().bitCount__I__I((bitmap & (((-1) + bitpos) | 0)))
});
$c_sci_Node$.prototype.maskFrom__I__I__I = (function(hash, shift) {
  return (31 & ((hash >>> shift) | 0))
});
$c_sci_Node$.prototype.indexFrom__I__I__I__I = (function(bitmap, mask, bitpos) {
  return ((bitmap === (-1)) ? mask : this.indexFrom__I__I__I(bitmap, bitpos))
});
$c_sci_Node$.prototype.bitposFrom__I__I = (function(mask) {
  return (1 << mask)
});
var $d_sci_Node$ = new $TypeData().initClass({
  sci_Node$: 0
}, false, "scala.collection.immutable.Node$", {
  sci_Node$: 1,
  O: 1
});
$c_sci_Node$.prototype.$classData = $d_sci_Node$;
var $n_sci_Node$ = (void 0);
function $m_sci_Node$() {
  if ((!$n_sci_Node$)) {
    $n_sci_Node$ = new $c_sci_Node$()
  };
  return $n_sci_Node$
}
/** @constructor */
function $c_sci_OldHashMap$Merger() {
  /*<skip>*/
}
$c_sci_OldHashMap$Merger.prototype = new $h_O();
$c_sci_OldHashMap$Merger.prototype.constructor = $c_sci_OldHashMap$Merger;
/** @constructor */
function $h_sci_OldHashMap$Merger() {
  /*<skip>*/
}
$h_sci_OldHashMap$Merger.prototype = $c_sci_OldHashMap$Merger.prototype;
/** @constructor */
function $c_sci_SetNode$() {
  this.EmptySetNode$1 = null;
  $n_sci_SetNode$ = this;
  this.EmptySetNode$1 = new $c_sci_BitmapIndexedSetNode(0, 0, ($m_s_reflect_ManifestFactory$AnyManifest$(), $newArrayObject($d_O.getArrayOf(), [0])), ($m_s_reflect_ManifestFactory$IntManifest$(), $newArrayObject($d_I.getArrayOf(), [0])), 0)
}
$c_sci_SetNode$.prototype = new $h_O();
$c_sci_SetNode$.prototype.constructor = $c_sci_SetNode$;
/** @constructor */
function $h_sci_SetNode$() {
  /*<skip>*/
}
$h_sci_SetNode$.prototype = $c_sci_SetNode$.prototype;
var $d_sci_SetNode$ = new $TypeData().initClass({
  sci_SetNode$: 0
}, false, "scala.collection.immutable.SetNode$", {
  sci_SetNode$: 1,
  O: 1
});
$c_sci_SetNode$.prototype.$classData = $d_sci_SetNode$;
var $n_sci_SetNode$ = (void 0);
function $m_sci_SetNode$() {
  if ((!$n_sci_SetNode$)) {
    $n_sci_SetNode$ = new $c_sci_SetNode$()
  };
  return $n_sci_SetNode$
}
/** @constructor */
function $c_scm_FlatHashTable$() {
  /*<skip>*/
}
$c_scm_FlatHashTable$.prototype = new $h_O();
$c_scm_FlatHashTable$.prototype.constructor = $c_scm_FlatHashTable$;
/** @constructor */
function $h_scm_FlatHashTable$() {
  /*<skip>*/
}
$h_scm_FlatHashTable$.prototype = $c_scm_FlatHashTable$.prototype;
$c_scm_FlatHashTable$.prototype.newThreshold__I__I__I = (function(_loadFactor, size) {
  var assertion = (_loadFactor < 500);
  if ((!assertion)) {
    throw new $c_jl_AssertionError("assertion failed: loadFactor too large; must be < 0.5")
  };
  var hi = (size >> 31);
  var hi$1 = (_loadFactor >> 31);
  var a0 = (65535 & size);
  var a1 = ((size >>> 16) | 0);
  var b0 = (65535 & _loadFactor);
  var b1 = ((_loadFactor >>> 16) | 0);
  var a0b0 = $imul(a0, b0);
  var a1b0 = $imul(a1, b0);
  var a0b1 = $imul(a0, b1);
  var lo = ((a0b0 + (((a1b0 + a0b1) | 0) << 16)) | 0);
  var c1part = ((((a0b0 >>> 16) | 0) + a0b1) | 0);
  var hi$2 = (((((((($imul(size, hi$1) + $imul(hi, _loadFactor)) | 0) + $imul(a1, b1)) | 0) + ((c1part >>> 16) | 0)) | 0) + (((((65535 & c1part) + a1b0) | 0) >>> 16) | 0)) | 0);
  var this$4 = $m_sjsr_RuntimeLong$();
  var lo$1 = this$4.divideImpl__I__I__I__I__I(lo, hi$2, 1000, 0);
  return lo$1
});
var $d_scm_FlatHashTable$ = new $TypeData().initClass({
  scm_FlatHashTable$: 0
}, false, "scala.collection.mutable.FlatHashTable$", {
  scm_FlatHashTable$: 1,
  O: 1
});
$c_scm_FlatHashTable$.prototype.$classData = $d_scm_FlatHashTable$;
var $n_scm_FlatHashTable$ = (void 0);
function $m_scm_FlatHashTable$() {
  if ((!$n_scm_FlatHashTable$)) {
    $n_scm_FlatHashTable$ = new $c_scm_FlatHashTable$()
  };
  return $n_scm_FlatHashTable$
}
/** @constructor */
function $c_scm_FlatHashTable$NullSentinel$() {
  /*<skip>*/
}
$c_scm_FlatHashTable$NullSentinel$.prototype = new $h_O();
$c_scm_FlatHashTable$NullSentinel$.prototype.constructor = $c_scm_FlatHashTable$NullSentinel$;
/** @constructor */
function $h_scm_FlatHashTable$NullSentinel$() {
  /*<skip>*/
}
$h_scm_FlatHashTable$NullSentinel$.prototype = $c_scm_FlatHashTable$NullSentinel$.prototype;
$c_scm_FlatHashTable$NullSentinel$.prototype.toString__T = (function() {
  return "NullSentinel"
});
$c_scm_FlatHashTable$NullSentinel$.prototype.hashCode__I = (function() {
  return 0
});
var $d_scm_FlatHashTable$NullSentinel$ = new $TypeData().initClass({
  scm_FlatHashTable$NullSentinel$: 0
}, false, "scala.collection.mutable.FlatHashTable$NullSentinel$", {
  scm_FlatHashTable$NullSentinel$: 1,
  O: 1
});
$c_scm_FlatHashTable$NullSentinel$.prototype.$classData = $d_scm_FlatHashTable$NullSentinel$;
var $n_scm_FlatHashTable$NullSentinel$ = (void 0);
function $m_scm_FlatHashTable$NullSentinel$() {
  if ((!$n_scm_FlatHashTable$NullSentinel$)) {
    $n_scm_FlatHashTable$NullSentinel$ = new $c_scm_FlatHashTable$NullSentinel$()
  };
  return $n_scm_FlatHashTable$NullSentinel$
}
function $f_scm_Growable__addAll__sc_IterableOnce__scm_Growable($thiz, xs) {
  var it = xs.iterator__sc_Iterator();
  while (it.hasNext__Z()) {
    $thiz.addOne__O__scm_Growable(it.next__O())
  };
  return $thiz
}
/** @constructor */
function $c_scm_HashTable$() {
  /*<skip>*/
}
$c_scm_HashTable$.prototype = new $h_O();
$c_scm_HashTable$.prototype.constructor = $c_scm_HashTable$;
/** @constructor */
function $h_scm_HashTable$() {
  /*<skip>*/
}
$h_scm_HashTable$.prototype = $c_scm_HashTable$.prototype;
$c_scm_HashTable$.prototype.nextPositivePowerOfTwo__I__I = (function(target) {
  return (1 << ((-$clz32((((-1) + target) | 0))) | 0))
});
var $d_scm_HashTable$ = new $TypeData().initClass({
  scm_HashTable$: 0
}, false, "scala.collection.mutable.HashTable$", {
  scm_HashTable$: 1,
  O: 1
});
$c_scm_HashTable$.prototype.$classData = $d_scm_HashTable$;
var $n_scm_HashTable$ = (void 0);
function $m_scm_HashTable$() {
  if ((!$n_scm_HashTable$)) {
    $n_scm_HashTable$ = new $c_scm_HashTable$()
  };
  return $n_scm_HashTable$
}
/** @constructor */
function $c_scm_RefArrayUtils$() {
  /*<skip>*/
}
$c_scm_RefArrayUtils$.prototype = new $h_O();
$c_scm_RefArrayUtils$.prototype.constructor = $c_scm_RefArrayUtils$;
/** @constructor */
function $h_scm_RefArrayUtils$() {
  /*<skip>*/
}
$h_scm_RefArrayUtils$.prototype = $c_scm_RefArrayUtils$.prototype;
$c_scm_RefArrayUtils$.prototype.growArray$1__p1__J__I__I__AO__AO = (function(arrayLength$1, n$1, end$1, array$2) {
  var lo = (arrayLength$1.lo$2 << 1);
  var hi = (((arrayLength$1.lo$2 >>> 31) | 0) | (arrayLength$1.hi$2 << 1));
  var t = (((hi === 0) ? (((-2147483648) ^ lo) > (-2147483640)) : (hi > 0)) ? new $c_sjsr_RuntimeLong(lo, hi) : new $c_sjsr_RuntimeLong(8, 0));
  var lo$1 = t.lo$2;
  var hi$1 = t.hi$2;
  var newSize_$_lo$2 = lo$1;
  var newSize_$_hi$2 = hi$1;
  while (true) {
    var hi$2 = (n$1 >> 31);
    var b_$_lo$2 = newSize_$_lo$2;
    var b_$_hi$2 = newSize_$_hi$2;
    var bhi = b_$_hi$2;
    if (((hi$2 === bhi) ? (((-2147483648) ^ n$1) > ((-2147483648) ^ b_$_lo$2)) : (hi$2 > bhi))) {
      var this$4_$_lo$2 = newSize_$_lo$2;
      var this$4_$_hi$2 = newSize_$_hi$2;
      var lo$2 = (this$4_$_lo$2 << 1);
      var hi$3 = (((this$4_$_lo$2 >>> 31) | 0) | (this$4_$_hi$2 << 1));
      var jsx$1_$_lo$2 = lo$2;
      var jsx$1_$_hi$2 = hi$3;
      newSize_$_lo$2 = jsx$1_$_lo$2;
      newSize_$_hi$2 = jsx$1_$_hi$2
    } else {
      break
    }
  };
  var this$5_$_lo$2 = newSize_$_lo$2;
  var this$5_$_hi$2 = newSize_$_hi$2;
  var ahi = this$5_$_hi$2;
  if (((ahi === 0) ? (((-2147483648) ^ this$5_$_lo$2) > (-1)) : (ahi > 0))) {
    if ((end$1 === 2147483647)) {
      throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(new $c_jl_Exception().init___T("Collections can not have more than 2147483647 elements"))
    };
    var jsx$2_$_lo$2 = 2147483647;
    var jsx$2_$_hi$2 = 0;
    newSize_$_lo$2 = jsx$2_$_lo$2;
    newSize_$_hi$2 = jsx$2_$_hi$2
  };
  var this$6_$_lo$2 = newSize_$_lo$2;
  var this$6_$_hi$2 = newSize_$_hi$2;
  var newArray = $newArrayObject($d_O.getArrayOf(), [this$6_$_lo$2]);
  $m_s_Array$().copy__O__I__O__I__I__V(array$2, 0, newArray, 0, end$1);
  return newArray
});
$c_scm_RefArrayUtils$.prototype.ensureSize__AO__I__I__AO = (function(array, end, n) {
  var value = array.u.length;
  var hi = (value >> 31);
  var hi$1 = (n >> 31);
  if (((hi$1 === hi) ? (((-2147483648) ^ n) <= ((-2147483648) ^ value)) : (hi$1 < hi))) {
    return array
  } else {
    return this.growArray$1__p1__J__I__I__AO__AO(new $c_sjsr_RuntimeLong(value, hi), n, end, array)
  }
});
var $d_scm_RefArrayUtils$ = new $TypeData().initClass({
  scm_RefArrayUtils$: 0
}, false, "scala.collection.mutable.RefArrayUtils$", {
  scm_RefArrayUtils$: 1,
  O: 1
});
$c_scm_RefArrayUtils$.prototype.$classData = $d_scm_RefArrayUtils$;
var $n_scm_RefArrayUtils$ = (void 0);
function $m_scm_RefArrayUtils$() {
  if ((!$n_scm_RefArrayUtils$)) {
    $n_scm_RefArrayUtils$ = new $c_scm_RefArrayUtils$()
  };
  return $n_scm_RefArrayUtils$
}
/** @constructor */
function $c_sjs_js_special_package$() {
  /*<skip>*/
}
$c_sjs_js_special_package$.prototype = new $h_O();
$c_sjs_js_special_package$.prototype.constructor = $c_sjs_js_special_package$;
/** @constructor */
function $h_sjs_js_special_package$() {
  /*<skip>*/
}
$h_sjs_js_special_package$.prototype = $c_sjs_js_special_package$.prototype;
$c_sjs_js_special_package$.prototype.objectLiteral__sci_Seq__sjs_js_Object = (function(properties) {
  var result = {};
  properties.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this, result$1) {
    return (function(pair$2) {
      var pair = $as_T2(pair$2);
      result$1[pair.$$und1$f] = pair.$$und2$f
    })
  })(this, result)));
  return result
});
var $d_sjs_js_special_package$ = new $TypeData().initClass({
  sjs_js_special_package$: 0
}, false, "scala.scalajs.js.special.package$", {
  sjs_js_special_package$: 1,
  O: 1
});
$c_sjs_js_special_package$.prototype.$classData = $d_sjs_js_special_package$;
var $n_sjs_js_special_package$ = (void 0);
function $m_sjs_js_special_package$() {
  if ((!$n_sjs_js_special_package$)) {
    $n_sjs_js_special_package$ = new $c_sjs_js_special_package$()
  };
  return $n_sjs_js_special_package$
}
/** @constructor */
function $c_sjsr_package$() {
  /*<skip>*/
}
$c_sjsr_package$.prototype = new $h_O();
$c_sjsr_package$.prototype.constructor = $c_sjsr_package$;
/** @constructor */
function $h_sjsr_package$() {
  /*<skip>*/
}
$h_sjsr_package$.prototype = $c_sjsr_package$.prototype;
$c_sjsr_package$.prototype.unwrapJavaScriptException__jl_Throwable__O = (function(th) {
  if ($is_sjs_js_JavaScriptException(th)) {
    var x2 = $as_sjs_js_JavaScriptException(th);
    var e = x2.exception$4;
    return e
  } else {
    return th
  }
});
$c_sjsr_package$.prototype.wrapJavaScriptException__O__jl_Throwable = (function(e) {
  if ($is_jl_Throwable(e)) {
    var x2 = $as_jl_Throwable(e);
    return x2
  } else {
    return new $c_sjs_js_JavaScriptException(e)
  }
});
var $d_sjsr_package$ = new $TypeData().initClass({
  sjsr_package$: 0
}, false, "scala.scalajs.runtime.package$", {
  sjsr_package$: 1,
  O: 1
});
$c_sjsr_package$.prototype.$classData = $d_sjsr_package$;
var $n_sjsr_package$ = (void 0);
function $m_sjsr_package$() {
  if ((!$n_sjsr_package$)) {
    $n_sjsr_package$ = new $c_sjsr_package$()
  };
  return $n_sjsr_package$
}
/** @constructor */
function $c_sr_BoxesRunTime$() {
  /*<skip>*/
}
$c_sr_BoxesRunTime$.prototype = new $h_O();
$c_sr_BoxesRunTime$.prototype.constructor = $c_sr_BoxesRunTime$;
/** @constructor */
function $h_sr_BoxesRunTime$() {
  /*<skip>*/
}
$h_sr_BoxesRunTime$.prototype = $c_sr_BoxesRunTime$.prototype;
$c_sr_BoxesRunTime$.prototype.equalsCharObject__jl_Character__O__Z = (function(xc, y) {
  if ($isChar(y)) {
    var x2 = $asChar(y);
    return ($uC(xc) === $uC(x2))
  } else if ($is_jl_Number(y)) {
    var x3 = $as_jl_Number(y);
    if (((typeof x3) === "number")) {
      var x2$1 = $uD(x3);
      return (x2$1 === $uC(xc))
    } else if ($is_sjsr_RuntimeLong(x3)) {
      var t = $uJ(x3);
      var lo = t.lo$2;
      var hi = t.hi$2;
      var value = $uC(xc);
      var hi$1 = (value >> 31);
      return ((lo === value) && (hi === hi$1))
    } else {
      return ((x3 === null) ? (xc === null) : $dp_equals__O__Z(x3, xc))
    }
  } else {
    return ((xc === null) && (y === null))
  }
});
$c_sr_BoxesRunTime$.prototype.equalsNumObject__jl_Number__O__Z = (function(xn, y) {
  if ($is_jl_Number(y)) {
    var x2 = $as_jl_Number(y);
    return this.equalsNumNum__jl_Number__jl_Number__Z(xn, x2)
  } else if ($isChar(y)) {
    var x3 = $asChar(y);
    if (((typeof xn) === "number")) {
      var x2$1 = $uD(xn);
      return (x2$1 === $uC(x3))
    } else if ($is_sjsr_RuntimeLong(xn)) {
      var t = $uJ(xn);
      var lo = t.lo$2;
      var hi = t.hi$2;
      var value = $uC(x3);
      var hi$1 = (value >> 31);
      return ((lo === value) && (hi === hi$1))
    } else {
      return ((xn === null) ? (x3 === null) : $dp_equals__O__Z(xn, x3))
    }
  } else {
    return ((xn === null) ? (y === null) : $dp_equals__O__Z(xn, y))
  }
});
$c_sr_BoxesRunTime$.prototype.equals__O__O__Z = (function(x, y) {
  if ((x === y)) {
    return true
  } else if ($is_jl_Number(x)) {
    var x2 = $as_jl_Number(x);
    return this.equalsNumObject__jl_Number__O__Z(x2, y)
  } else if ($isChar(x)) {
    var x3 = $asChar(x);
    return this.equalsCharObject__jl_Character__O__Z(x3, y)
  } else {
    return ((x === null) ? (y === null) : $dp_equals__O__Z(x, y))
  }
});
$c_sr_BoxesRunTime$.prototype.equalsNumNum__jl_Number__jl_Number__Z = (function(xn, yn) {
  if (((typeof xn) === "number")) {
    var x2 = $uD(xn);
    if (((typeof yn) === "number")) {
      var x2$2 = $uD(yn);
      return (x2 === x2$2)
    } else if ($is_sjsr_RuntimeLong(yn)) {
      var t = $uJ(yn);
      var lo = t.lo$2;
      var hi = t.hi$2;
      return (x2 === $m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toDouble__I__I__D(lo, hi))
    } else if ($is_s_math_ScalaNumber(yn)) {
      var x4 = $as_s_math_ScalaNumber(yn);
      return x4.equals__O__Z(x2)
    } else {
      return false
    }
  } else if ($is_sjsr_RuntimeLong(xn)) {
    var t$1 = $uJ(xn);
    var lo$1 = t$1.lo$2;
    var hi$1 = t$1.hi$2;
    if ($is_sjsr_RuntimeLong(yn)) {
      var t$2 = $uJ(yn);
      var lo$2 = t$2.lo$2;
      var hi$2 = t$2.hi$2;
      return ((lo$1 === lo$2) && (hi$1 === hi$2))
    } else if (((typeof yn) === "number")) {
      var x3$3 = $uD(yn);
      return ($m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toDouble__I__I__D(lo$1, hi$1) === x3$3)
    } else if ($is_s_math_ScalaNumber(yn)) {
      var x4$2 = $as_s_math_ScalaNumber(yn);
      return x4$2.equals__O__Z(new $c_sjsr_RuntimeLong(lo$1, hi$1))
    } else {
      return false
    }
  } else {
    return ((xn === null) ? (yn === null) : $dp_equals__O__Z(xn, yn))
  }
});
var $d_sr_BoxesRunTime$ = new $TypeData().initClass({
  sr_BoxesRunTime$: 0
}, false, "scala.runtime.BoxesRunTime$", {
  sr_BoxesRunTime$: 1,
  O: 1
});
$c_sr_BoxesRunTime$.prototype.$classData = $d_sr_BoxesRunTime$;
var $n_sr_BoxesRunTime$ = (void 0);
function $m_sr_BoxesRunTime$() {
  if ((!$n_sr_BoxesRunTime$)) {
    $n_sr_BoxesRunTime$ = new $c_sr_BoxesRunTime$()
  };
  return $n_sr_BoxesRunTime$
}
var $d_sr_Null$ = new $TypeData().initClass({
  sr_Null$: 0
}, false, "scala.runtime.Null$", {
  sr_Null$: 1,
  O: 1
});
/** @constructor */
function $c_sr_ScalaRunTime$() {
  /*<skip>*/
}
$c_sr_ScalaRunTime$.prototype = new $h_O();
$c_sr_ScalaRunTime$.prototype.constructor = $c_sr_ScalaRunTime$;
/** @constructor */
function $h_sr_ScalaRunTime$() {
  /*<skip>*/
}
$h_sr_ScalaRunTime$.prototype = $c_sr_ScalaRunTime$.prototype;
$c_sr_ScalaRunTime$.prototype.array$undlength__O__I = (function(xs) {
  return $m_jl_reflect_Array$().getLength__O__I(xs)
});
$c_sr_ScalaRunTime$.prototype.array$undupdate__O__I__O__V = (function(xs, idx, value) {
  if ($isArrayOf_O(xs, 1)) {
    var x2 = $asArrayOf_O(xs, 1);
    x2.set(idx, value)
  } else if ($isArrayOf_I(xs, 1)) {
    var x3 = $asArrayOf_I(xs, 1);
    x3.set(idx, $uI(value))
  } else if ($isArrayOf_D(xs, 1)) {
    var x4 = $asArrayOf_D(xs, 1);
    x4.set(idx, $uD(value))
  } else if ($isArrayOf_J(xs, 1)) {
    var x5 = $asArrayOf_J(xs, 1);
    x5.set(idx, $uJ(value))
  } else if ($isArrayOf_F(xs, 1)) {
    var x6 = $asArrayOf_F(xs, 1);
    x6.set(idx, $uF(value))
  } else if ($isArrayOf_C(xs, 1)) {
    var x7 = $asArrayOf_C(xs, 1);
    x7.set(idx, $uC(value))
  } else if ($isArrayOf_B(xs, 1)) {
    var x8 = $asArrayOf_B(xs, 1);
    x8.set(idx, $uB(value))
  } else if ($isArrayOf_S(xs, 1)) {
    var x9 = $asArrayOf_S(xs, 1);
    x9.set(idx, $uS(value))
  } else if ($isArrayOf_Z(xs, 1)) {
    var x10 = $asArrayOf_Z(xs, 1);
    x10.set(idx, $uZ(value))
  } else if ($isArrayOf_sr_BoxedUnit(xs, 1)) {
    var x11 = $asArrayOf_sr_BoxedUnit(xs, 1);
    x11.set(idx, (void 0))
  } else if ((xs === null)) {
    throw new $c_jl_NullPointerException()
  } else {
    throw new $c_s_MatchError(xs)
  }
});
$c_sr_ScalaRunTime$.prototype.$$undtoString__s_Product__T = (function(x) {
  var this$1 = x.productIterator__sc_Iterator();
  var start = (x.productPrefix__T() + "(");
  return $f_sc_IterableOnceOps__mkString__T__T__T__T(this$1, start, ",", ")")
});
$c_sr_ScalaRunTime$.prototype.array$undapply__O__I__O = (function(xs, idx) {
  if ($isArrayOf_O(xs, 1)) {
    var x2 = $asArrayOf_O(xs, 1);
    return x2.get(idx)
  } else if ($isArrayOf_I(xs, 1)) {
    var x3 = $asArrayOf_I(xs, 1);
    return x3.get(idx)
  } else if ($isArrayOf_D(xs, 1)) {
    var x4 = $asArrayOf_D(xs, 1);
    return x4.get(idx)
  } else if ($isArrayOf_J(xs, 1)) {
    var x5 = $asArrayOf_J(xs, 1);
    return x5.get(idx)
  } else if ($isArrayOf_F(xs, 1)) {
    var x6 = $asArrayOf_F(xs, 1);
    return x6.get(idx)
  } else if ($isArrayOf_C(xs, 1)) {
    var x7 = $asArrayOf_C(xs, 1);
    return $bC(x7.get(idx))
  } else if ($isArrayOf_B(xs, 1)) {
    var x8 = $asArrayOf_B(xs, 1);
    return x8.get(idx)
  } else if ($isArrayOf_S(xs, 1)) {
    var x9 = $asArrayOf_S(xs, 1);
    return x9.get(idx)
  } else if ($isArrayOf_Z(xs, 1)) {
    var x10 = $asArrayOf_Z(xs, 1);
    return x10.get(idx)
  } else if ($isArrayOf_sr_BoxedUnit(xs, 1)) {
    var x11 = $asArrayOf_sr_BoxedUnit(xs, 1);
    return x11.get(idx)
  } else if ((xs === null)) {
    throw new $c_jl_NullPointerException()
  } else {
    throw new $c_s_MatchError(xs)
  }
});
var $d_sr_ScalaRunTime$ = new $TypeData().initClass({
  sr_ScalaRunTime$: 0
}, false, "scala.runtime.ScalaRunTime$", {
  sr_ScalaRunTime$: 1,
  O: 1
});
$c_sr_ScalaRunTime$.prototype.$classData = $d_sr_ScalaRunTime$;
var $n_sr_ScalaRunTime$ = (void 0);
function $m_sr_ScalaRunTime$() {
  if ((!$n_sr_ScalaRunTime$)) {
    $n_sr_ScalaRunTime$ = new $c_sr_ScalaRunTime$()
  };
  return $n_sr_ScalaRunTime$
}
/** @constructor */
function $c_sr_Statics$() {
  /*<skip>*/
}
$c_sr_Statics$.prototype = new $h_O();
$c_sr_Statics$.prototype.constructor = $c_sr_Statics$;
/** @constructor */
function $h_sr_Statics$() {
  /*<skip>*/
}
$h_sr_Statics$.prototype = $c_sr_Statics$.prototype;
$c_sr_Statics$.prototype.mixLast__I__I__I = (function(hash, data) {
  var k = data;
  k = $imul((-862048943), k);
  var i = k;
  k = ((i << 15) | ((i >>> 17) | 0));
  k = $imul(461845907, k);
  return (hash ^ k)
});
$c_sr_Statics$.prototype.doubleHash__D__I = (function(dv) {
  var iv = $doubleToInt(dv);
  if ((iv === dv)) {
    return iv
  } else {
    var this$1 = $m_sjsr_RuntimeLong$();
    var lo = this$1.scala$scalajs$runtime$RuntimeLong$$fromDoubleImpl__D__I(dv);
    var hi = this$1.scala$scalajs$runtime$RuntimeLong$$hiReturn$f;
    return (($m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toDouble__I__I__D(lo, hi) === dv) ? (lo ^ hi) : $m_jl_FloatingPointBits$().numberHashCode__D__I(dv))
  }
});
$c_sr_Statics$.prototype.anyHash__O__I = (function(x) {
  if ((x === null)) {
    return 0
  } else if (((typeof x) === "number")) {
    var x3 = $uD(x);
    return this.doubleHash__D__I(x3)
  } else if ($is_sjsr_RuntimeLong(x)) {
    var t = $uJ(x);
    var lo = t.lo$2;
    var hi = t.hi$2;
    return this.longHash__J__I(new $c_sjsr_RuntimeLong(lo, hi))
  } else {
    return $dp_hashCode__I(x)
  }
});
$c_sr_Statics$.prototype.avalanche__I__I = (function(h0) {
  var h = h0;
  h = (h ^ ((h >>> 16) | 0));
  h = $imul((-2048144789), h);
  h = (h ^ ((h >>> 13) | 0));
  h = $imul((-1028477387), h);
  h = (h ^ ((h >>> 16) | 0));
  return h
});
$c_sr_Statics$.prototype.mix__I__I__I = (function(hash, data) {
  var h = this.mixLast__I__I__I(hash, data);
  var i = h;
  h = ((i << 13) | ((i >>> 19) | 0));
  return (((-430675100) + $imul(5, h)) | 0)
});
$c_sr_Statics$.prototype.longHash__J__I = (function(lv) {
  var lo = lv.lo$2;
  var lo$1 = lv.hi$2;
  return ((lo$1 === (lo >> 31)) ? lo : (lo ^ lo$1))
});
$c_sr_Statics$.prototype.finalizeHash__I__I__I = (function(hash, length) {
  return this.avalanche__I__I((hash ^ length))
});
var $d_sr_Statics$ = new $TypeData().initClass({
  sr_Statics$: 0
}, false, "scala.runtime.Statics$", {
  sr_Statics$: 1,
  O: 1
});
$c_sr_Statics$.prototype.$classData = $d_sr_Statics$;
var $n_sr_Statics$ = (void 0);
function $m_sr_Statics$() {
  if ((!$n_sr_Statics$)) {
    $n_sr_Statics$ = new $c_sr_Statics$()
  };
  return $n_sr_Statics$
}
/** @constructor */
function $c_Lcom_kos_wormpad_GameHeroes() {
  this.worm$1 = null;
  this.burgers$1 = null;
  this.enemies$1 = null;
  this.enemyCreatorList$1 = null;
  this.gameBorder$1 = null;
  this.wormBorder$1 = null;
  this.earthBorder$1 = null;
  this.burgersArea$1 = null;
  this.rainArea$1 = null;
  this.burgersObitanieArea$1 = null;
  this.heroObitanieArea$1 = null;
  this.topArea$1 = null;
  this.flyArea$1 = null;
  this.horizontArea$1 = null;
  this.cloudArea$1 = null;
  this.chastota$1 = null;
  this.LEVEL$undWORM$undHEALTH$undSPEED$undUPDATE$1 = 0.0;
  this.ENERGY$undBURGER$1 = 0;
  this.ENERGY$undBOMB$1 = 0;
  this.RANDOM$undBURGER$1 = 0;
  this.RANDOM$undBOMB$1 = 0;
  this.RANDOM$undHIDE$undEAT$1 = 0;
  this.GAME$undBOARD$1 = null;
  $f_Lcom_kos_wormpad_WormGameConst__$$init$__V(this);
  this.worm$1 = new $c_Lcom_kos_wormpad_heroes_Worm();
  this.burgers$1 = $m_sci_Set$EmptySet$();
  this.enemies$1 = $m_sci_Set$EmptySet$();
  var this$3 = $m_sci_Seq$();
  var elems = $m_sci_Nil$();
  this.enemyCreatorList$1 = $as_sci_Seq(this$3.from__sc_IterableOnce__sc_SeqOps(elems));
  this.gameBorder$1 = new $c_Lcom_kos_wormpad_geometry_RectF(this.GAME$undBOARD$1.left$1, this.GAME$undBOARD$1.bottom$1, this.GAME$undBOARD$1.right$1, this.GAME$undBOARD$1.top$1);
  this.wormBorder$1 = new $c_Lcom_kos_wormpad_geometry_RectF($fround((20.0 + this.GAME$undBOARD$1.left$1)), $fround((20.0 + this.GAME$undBOARD$1.bottom$1)), $fround(((-20.0) + this.GAME$undBOARD$1.right$1)), $fround(((-20.0) + this.GAME$undBOARD$1.top$1)));
  this.earthBorder$1 = new $c_Lcom_kos_wormpad_geometry_RectF(this.GAME$undBOARD$1.left$1, this.GAME$undBOARD$1.bottom$1, this.GAME$undBOARD$1.right$1, 0.0);
  this.burgersArea$1 = new $c_Lcom_kos_wormpad_geometry_RectF($fround((200.0 + this.GAME$undBOARD$1.left$1)), 10.0, $fround(((-200.0) + this.GAME$undBOARD$1.right$1)), 500.0);
  this.rainArea$1 = new $c_Lcom_kos_wormpad_geometry_RectF($fround((200.0 + this.GAME$undBOARD$1.left$1)), $fround(((-200.0) + this.GAME$undBOARD$1.top$1)), $fround(((-200.0) + this.GAME$undBOARD$1.right$1)), this.GAME$undBOARD$1.top$1);
  this.burgersObitanieArea$1 = new $c_Lcom_kos_wormpad_geometry_RectF($fround(((-200.0) + this.GAME$undBOARD$1.left$1)), (-10.0), $fround((200.0 + this.GAME$undBOARD$1.right$1)), $fround((200.0 + this.GAME$undBOARD$1.top$1)));
  this.heroObitanieArea$1 = new $c_Lcom_kos_wormpad_geometry_RectF($fround(((-400.0) + this.GAME$undBOARD$1.left$1)), $fround(((-400.0) + this.GAME$undBOARD$1.bottom$1)), $fround((400.0 + this.GAME$undBOARD$1.right$1)), $fround((2400.0 + this.GAME$undBOARD$1.top$1)));
  this.topArea$1 = new $c_Lcom_kos_wormpad_geometry_RectF(this.GAME$undBOARD$1.left$1, 1000.0, this.GAME$undBOARD$1.right$1, 1010.0);
  this.flyArea$1 = new $c_Lcom_kos_wormpad_geometry_RectF(this.GAME$undBOARD$1.left$1, 200.0, this.GAME$undBOARD$1.right$1, $fround(((-200.0) + this.GAME$undBOARD$1.top$1)));
  this.horizontArea$1 = new $c_Lcom_kos_wormpad_geometry_RectF(this.GAME$undBOARD$1.left$1, 0.0, this.GAME$undBOARD$1.right$1, 0.0);
  this.cloudArea$1 = new $c_Lcom_kos_wormpad_geometry_RectF(this.GAME$undBOARD$1.left$1, 100.0, this.GAME$undBOARD$1.right$1, this.GAME$undBOARD$1.top$1);
  var this$7 = $m_sci_Seq$();
  var array = [new $c_Lcom_kos_wormpad_game_EnemyCreatorExpression(10.0, new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      return new $c_Lcom_kos_wormpad_heroes_MeteorRain($this)
    })
  })(this)), this.rainArea$1), new $c_Lcom_kos_wormpad_game_EnemyCreatorExpression(5.0, new $c_sjsr_AnonFunction0((function(this$2$1) {
    return (function() {
      return new $c_Lcom_kos_wormpad_heroes_ShipWithBurgers(this$2$1)
    })
  })(this)), this.flyArea$1)];
  var elems$1 = new $c_sjsr_WrappedVarArgs(array);
  this.chastota$1 = $as_sci_Seq(this$7.from__sc_IterableOnce__sc_SeqOps(elems$1))
}
$c_Lcom_kos_wormpad_GameHeroes.prototype = new $h_O();
$c_Lcom_kos_wormpad_GameHeroes.prototype.constructor = $c_Lcom_kos_wormpad_GameHeroes;
/** @constructor */
function $h_Lcom_kos_wormpad_GameHeroes() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_GameHeroes.prototype = $c_Lcom_kos_wormpad_GameHeroes.prototype;
var $d_Lcom_kos_wormpad_GameHeroes = new $TypeData().initClass({
  Lcom_kos_wormpad_GameHeroes: 0
}, false, "com.kos.wormpad.GameHeroes", {
  Lcom_kos_wormpad_GameHeroes: 1,
  O: 1,
  Lcom_kos_wormpad_WormGameConst: 1
});
$c_Lcom_kos_wormpad_GameHeroes.prototype.$classData = $d_Lcom_kos_wormpad_GameHeroes;
/** @constructor */
function $c_Lcom_kos_wormpad_game_GameState$$anon$1($$outer) {
  this.$$outer$2 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  }
}
$c_Lcom_kos_wormpad_game_GameState$$anon$1.prototype = new $h_Lcom_kos_wormpad_game_GameListenerDelegate();
$c_Lcom_kos_wormpad_game_GameState$$anon$1.prototype.constructor = $c_Lcom_kos_wormpad_game_GameState$$anon$1;
/** @constructor */
function $h_Lcom_kos_wormpad_game_GameState$$anon$1() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_GameState$$anon$1.prototype = $c_Lcom_kos_wormpad_game_GameState$$anon$1.prototype;
$c_Lcom_kos_wormpad_game_GameState$$anon$1.prototype.onNewGame__V = (function() {
  (0, this.$$outer$2.jslistener$1.onNewGame$1)()
});
$c_Lcom_kos_wormpad_game_GameState$$anon$1.prototype.onGameOver__V = (function() {
  (0, this.$$outer$2.jslistener$1.onGameOver$1)()
});
$c_Lcom_kos_wormpad_game_GameState$$anon$1.prototype.onChangeScore__I__V = (function(score) {
  (0, this.$$outer$2.jslistener$1.onChangeScore$1)(score)
});
$c_Lcom_kos_wormpad_game_GameState$$anon$1.prototype.onPause__Z__V = (function(pause) {
  (0, this.$$outer$2.jslistener$1.onPause$1)(pause)
});
var $d_Lcom_kos_wormpad_game_GameState$$anon$1 = new $TypeData().initClass({
  Lcom_kos_wormpad_game_GameState$$anon$1: 0
}, false, "com.kos.wormpad.game.GameState$$anon$1", {
  Lcom_kos_wormpad_game_GameState$$anon$1: 1,
  Lcom_kos_wormpad_game_GameListenerDelegate: 1,
  O: 1
});
$c_Lcom_kos_wormpad_game_GameState$$anon$1.prototype.$classData = $d_Lcom_kos_wormpad_game_GameState$$anon$1;
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_Burger() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  this.ediible$2 = false;
  this.kind$2 = 0
}
$c_Lcom_kos_wormpad_heroes_Burger.prototype = new $h_Lcom_kos_wormpad_heroes_Hero();
$c_Lcom_kos_wormpad_heroes_Burger.prototype.constructor = $c_Lcom_kos_wormpad_heroes_Burger;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_Burger() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_Burger.prototype = $c_Lcom_kos_wormpad_heroes_Burger.prototype;
$c_Lcom_kos_wormpad_heroes_Burger.prototype.init___ = (function() {
  $c_Lcom_kos_wormpad_heroes_Hero.prototype.init___.call(this);
  this.radius$1 = 10.0;
  this.ediible$2 = true;
  this.kind$2 = 201;
  return this
});
$c_Lcom_kos_wormpad_heroes_Burger.prototype.move__D__V = (function(timeDelta) {
  this.accelerationFun$1.apply__O__O__O(this, timeDelta);
  this.x$1 = (this.x$1 + (this.vx$1 * timeDelta));
  this.y$1 = (this.y$1 + (this.vy$1 * timeDelta))
});
$c_Lcom_kos_wormpad_heroes_Burger.prototype.kind__I = (function() {
  return this.kind$2
});
$c_Lcom_kos_wormpad_heroes_Burger.prototype.ediible__Z = (function() {
  return this.ediible$2
});
function $is_Lcom_kos_wormpad_heroes_Burger(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_heroes_Burger)))
}
function $as_Lcom_kos_wormpad_heroes_Burger(obj) {
  return (($is_Lcom_kos_wormpad_heroes_Burger(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.heroes.Burger"))
}
function $isArrayOf_Lcom_kos_wormpad_heroes_Burger(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_heroes_Burger)))
}
function $asArrayOf_Lcom_kos_wormpad_heroes_Burger(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_heroes_Burger(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.heroes.Burger;", depth))
}
var $d_Lcom_kos_wormpad_heroes_Burger = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_Burger: 0
}, false, "com.kos.wormpad.heroes.Burger", {
  Lcom_kos_wormpad_heroes_Burger: 1,
  Lcom_kos_wormpad_heroes_Hero: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_Burger.prototype.$classData = $d_Lcom_kos_wormpad_heroes_Burger;
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_Cloud() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  this.width$2 = 0;
  this.height$2 = 0;
  this.velocityX$2 = 0.0;
  this.kind$2 = 0
}
$c_Lcom_kos_wormpad_heroes_Cloud.prototype = new $h_Lcom_kos_wormpad_heroes_Hero();
$c_Lcom_kos_wormpad_heroes_Cloud.prototype.constructor = $c_Lcom_kos_wormpad_heroes_Cloud;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_Cloud() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_Cloud.prototype = $c_Lcom_kos_wormpad_heroes_Cloud.prototype;
$c_Lcom_kos_wormpad_heroes_Cloud.prototype.init___ = (function() {
  $c_Lcom_kos_wormpad_heroes_Hero.prototype.init___.call(this);
  this.width$2 = 100;
  this.height$2 = 50;
  this.velocityX$2 = 1.0;
  this.kind$2 = 401;
  return this
});
$c_Lcom_kos_wormpad_heroes_Cloud.prototype.kind__I = (function() {
  return this.kind$2
});
function $is_Lcom_kos_wormpad_heroes_Cloud(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_heroes_Cloud)))
}
function $as_Lcom_kos_wormpad_heroes_Cloud(obj) {
  return (($is_Lcom_kos_wormpad_heroes_Cloud(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.heroes.Cloud"))
}
function $isArrayOf_Lcom_kos_wormpad_heroes_Cloud(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_heroes_Cloud)))
}
function $asArrayOf_Lcom_kos_wormpad_heroes_Cloud(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_heroes_Cloud(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.heroes.Cloud;", depth))
}
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_Hero$$anon$1() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  $c_Lcom_kos_wormpad_heroes_Hero.prototype.init___.call(this);
  this.massa$1 = 0.0;
  this.radius$1 = 0.0
}
$c_Lcom_kos_wormpad_heroes_Hero$$anon$1.prototype = new $h_Lcom_kos_wormpad_heroes_Hero();
$c_Lcom_kos_wormpad_heroes_Hero$$anon$1.prototype.constructor = $c_Lcom_kos_wormpad_heroes_Hero$$anon$1;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_Hero$$anon$1() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_Hero$$anon$1.prototype = $c_Lcom_kos_wormpad_heroes_Hero$$anon$1.prototype;
var $d_Lcom_kos_wormpad_heroes_Hero$$anon$1 = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_Hero$$anon$1: 0
}, false, "com.kos.wormpad.heroes.Hero$$anon$1", {
  Lcom_kos_wormpad_heroes_Hero$$anon$1: 1,
  Lcom_kos_wormpad_heroes_Hero: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_Hero$$anon$1.prototype.$classData = $d_Lcom_kos_wormpad_heroes_Hero$$anon$1;
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_MeteorRain(heroes) {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  this.heroes$2 = null;
  this.kind$2 = 0;
  this.meterPowers$2 = null;
  this.random$2 = null;
  this.speedx$2 = 0.0;
  this.meteors$2 = null;
  this.prevTime$2 = 0.0;
  this.heroes$2 = heroes;
  $c_Lcom_kos_wormpad_heroes_Hero.prototype.init___.call(this);
  this.kind$2 = 501;
  this.radius$1 = 128.0;
  var this$10 = $m_sci_Seq$();
  var y = new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      return new $c_Lcom_kos_wormpad_heroes_Burger().init___()
    })
  })(this));
  var jsx$1 = new $c_T2(15, y);
  var y$1 = new $c_sjsr_AnonFunction0((function(this$2$1) {
    return (function() {
      return new $c_Lcom_kos_wormpad_heroes_Bomb()
    })
  })(this));
  var array = [jsx$1, new $c_T2(5, y$1)];
  var elems = new $c_sjsr_WrappedVarArgs(array);
  this.meterPowers$2 = $as_sci_Seq(this$10.from__sc_IterableOnce__sc_SeqOps(elems));
  this.random$2 = new $c_s_util_Random().init___();
  var this$11 = this.random$2;
  this.speedx$2 = ((-120.0) + (2.0 * (120.0 * this$11.self$1.nextDouble__D())));
  var this$23 = $as_sc_SeqOps(this.meterPowers$2.flatMap__F1__O(new $c_sjsr_AnonFunction1((function(this$3$1) {
    return (function(f$2) {
      var f = $as_T2(f$2);
      var end = $uI(f.$$und1$f);
      var isEmpty$4 = (end <= 1);
      var scala$collection$immutable$Range$$lastElement$f = (((-1) + end) | 0);
      var b = $m_sci_IndexedSeq$().newBuilder__scm_Builder();
      var it = new $c_sci_RangeIterator(1, 1, scala$collection$immutable$Range$$lastElement$f, isEmpty$4);
      while (it.$$undhasNext$2) {
        var arg1 = it.next__I();
        var this$21 = this$3$1.random$2;
        var jsx$2 = this$21.self$1.nextDouble__D();
        var this$22 = this$3$1.random$2;
        var elem = new $c_T3(jsx$2, this$22.self$1.nextDouble__D(), new $c_sjsr_AnonFunction0((function($this$1, f$1) {
          return (function() {
            var b$1 = $as_Lcom_kos_wormpad_heroes_Hero($as_F0(f$1.$$und2$f).apply__O());
            b$1.vx$1 = $this$1.speedx$2;
            b$1.vy$1 = (-400.0);
            return b$1
          })
        })(this$3$1, f)));
        b.addOne__O__scm_Growable(elem)
      };
      return $as_sci_IndexedSeq(b.result__O())
    })
  })(this))));
  var f$3 = new $c_sjsr_AnonFunction1((function(this$4$1) {
    return (function(x$1$2) {
      var x$1 = $as_T3(x$1$2);
      return $uD(x$1.$$und1$1)
    })
  })(this));
  var ord = $m_s_math_Ordering$DeprecatedDoubleOrdering$();
  this.meteors$2 = $as_sci_Seq($f_sc_SeqOps__sortBy__F1__s_math_Ordering__O(this$23, f$3, ord));
  this.prevTime$2 = (-3.0)
}
$c_Lcom_kos_wormpad_heroes_MeteorRain.prototype = new $h_Lcom_kos_wormpad_heroes_Hero();
$c_Lcom_kos_wormpad_heroes_MeteorRain.prototype.constructor = $c_Lcom_kos_wormpad_heroes_MeteorRain;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_MeteorRain() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_MeteorRain.prototype = $c_Lcom_kos_wormpad_heroes_MeteorRain.prototype;
$c_Lcom_kos_wormpad_heroes_MeteorRain.prototype.kind__I = (function() {
  return this.kind$2
});
$c_Lcom_kos_wormpad_heroes_MeteorRain.prototype.move__D__V = (function(timeDelta) {
  this.prevTime$2 = (this.prevTime$2 + timeDelta);
  var this$1 = this.meteors$2;
  if ((!this$1.isEmpty__Z())) {
    var h = $as_T3(this.meteors$2.head__O());
    if ((this.prevTime$2 > $uD(h.$$und2$1))) {
      this.prevTime$2 = (this.prevTime$2 - $uD(h.$$und2$1));
      this.meteors$2 = $as_sci_Seq(this.meteors$2.tail__O());
      var b = $as_Lcom_kos_wormpad_heroes_Hero($as_F0(h.$$und3$1).apply__O());
      var jsx$2 = this.x$1;
      var jsx$1 = this.radius$1;
      var this$2 = this.random$2;
      b.x$1 = ((jsx$2 - jsx$1) + (2.0 * (this$2.self$1.nextDouble__D() * this.radius$1)));
      b.y$1 = (this.y$1 - this.radius$1);
      var jsx$3 = this.heroes$2;
      var this$3 = this.heroes$2.burgers$1;
      jsx$3.burgers$1 = $as_sci_Set(this$3.incl__O__sci_SetOps(b))
    }
  } else {
    this.destroy$und$1 = true
  }
});
var $d_Lcom_kos_wormpad_heroes_MeteorRain = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_MeteorRain: 0
}, false, "com.kos.wormpad.heroes.MeteorRain", {
  Lcom_kos_wormpad_heroes_MeteorRain: 1,
  Lcom_kos_wormpad_heroes_Hero: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_MeteorRain.prototype.$classData = $d_Lcom_kos_wormpad_heroes_MeteorRain;
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_ShipWithBurgers(heroes) {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  this.heroes$2 = null;
  this.kind$2 = 0;
  this.ediible$2 = false;
  this.meterPowers$2 = null;
  this.random$2 = null;
  this.speedx$2 = 0.0;
  this.startY$2 = 0.0;
  this.meteors$2 = null;
  this.prevTime$2 = 0.0;
  this.fullTime$2 = 0.0;
  this.first$2 = false;
  this.heroes$2 = heroes;
  $c_Lcom_kos_wormpad_heroes_Hero.prototype.init___.call(this);
  this.kind$2 = 701;
  this.ediible$2 = true;
  this.radius$1 = 50.0;
  this.score$1 = 50;
  var this$10 = $m_sci_Seq$();
  var y = new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      return new $c_Lcom_kos_wormpad_heroes_Burger().init___()
    })
  })(this));
  var jsx$1 = new $c_T2(10, y);
  var y$1 = new $c_sjsr_AnonFunction0((function(this$2$1) {
    return (function() {
      return new $c_Lcom_kos_wormpad_heroes_Bomb()
    })
  })(this));
  var array = [jsx$1, new $c_T2(1, y$1)];
  var elems = new $c_sjsr_WrappedVarArgs(array);
  this.meterPowers$2 = $as_sci_Seq(this$10.from__sc_IterableOnce__sc_SeqOps(elems));
  this.random$2 = new $c_s_util_Random().init___();
  var this$11 = this.random$2;
  this.speedx$2 = ((-100.0) + (2.0 * (100.0 * this$11.self$1.nextDouble__D())));
  this.startY$2 = this.y$1;
  var this$23 = $as_sc_SeqOps(this.meterPowers$2.flatMap__F1__O(new $c_sjsr_AnonFunction1((function(this$3$1) {
    return (function(f$2) {
      var f = $as_T2(f$2);
      var end = $uI(f.$$und1$f);
      var isEmpty$4 = (end <= 1);
      var scala$collection$immutable$Range$$lastElement$f = (((-1) + end) | 0);
      var b = $m_sci_IndexedSeq$().newBuilder__scm_Builder();
      var it = new $c_sci_RangeIterator(1, 1, scala$collection$immutable$Range$$lastElement$f, isEmpty$4);
      while (it.$$undhasNext$2) {
        var arg1 = it.next__I();
        var this$21 = this$3$1.random$2;
        var jsx$2 = this$21.self$1.nextDouble__D();
        var this$22 = this$3$1.random$2;
        var elem = new $c_T3(jsx$2, (1.0 + (2.0 * this$22.self$1.nextDouble__D())), new $c_sjsr_AnonFunction0((function($this$1, f$1) {
          return (function() {
            var b$1 = $as_Lcom_kos_wormpad_heroes_Hero($as_F0(f$1.$$und2$f).apply__O());
            b$1.vx$1 = $this$1.speedx$2;
            b$1.vy$1 = 0.0;
            b$1.accelerationFun$1 = new $c_sjsr_AnonFunction2((function($this$2) {
              return (function(hero$2, deltaTime$2) {
                var hero = $as_Lcom_kos_wormpad_heroes_Hero(hero$2);
                var deltaTime = $uD(deltaTime$2);
                $m_Lcom_kos_wormpad_heroes_ShipWithBurgers$().burgerFail__Lcom_kos_wormpad_heroes_Hero__D__V(hero, deltaTime)
              })
            })($this$1));
            return b$1
          })
        })(this$3$1, f)));
        b.addOne__O__scm_Growable(elem)
      };
      return $as_sci_IndexedSeq(b.result__O())
    })
  })(this))));
  var f$3 = new $c_sjsr_AnonFunction1((function(this$4$1) {
    return (function(x$1$2) {
      var x$1 = $as_T3(x$1$2);
      return $uD(x$1.$$und1$1)
    })
  })(this));
  var ord = $m_s_math_Ordering$DeprecatedDoubleOrdering$();
  this.meteors$2 = $as_sci_Seq($f_sc_SeqOps__sortBy__F1__s_math_Ordering__O(this$23, f$3, ord));
  this.prevTime$2 = (-1.0);
  var this$24 = this.random$2;
  this.vx$1 = (80.0 + (120.0 * this$24.self$1.nextDouble__D()));
  this.fullTime$2 = 0.0;
  this.first$2 = true
}
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers.prototype = new $h_Lcom_kos_wormpad_heroes_Hero();
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers.prototype.constructor = $c_Lcom_kos_wormpad_heroes_ShipWithBurgers;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_ShipWithBurgers() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_ShipWithBurgers.prototype = $c_Lcom_kos_wormpad_heroes_ShipWithBurgers.prototype;
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers.prototype.kind__I = (function() {
  return this.kind$2
});
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers.prototype.move__D__V = (function(timeDelta) {
  this.fullTime$2 = (this.fullTime$2 + timeDelta);
  if (this.first$2) {
    this.first$2 = false;
    this.startY$2 = this.y$1;
    if ((this.x$1 < 0.0)) {
      this.x$1 = (this.heroes$2.gameBorder$1.left$1 - this.radius$1)
    } else {
      this.x$1 = (this.heroes$2.gameBorder$1.right$1 + this.radius$1);
      this.vx$1 = (-this.vx$1)
    }
  };
  this.x$1 = (this.x$1 + (this.vx$1 * timeDelta));
  var jsx$1 = this.startY$2;
  var a = ((2.0 * (3.141592653589793 * this.fullTime$2)) / 5.0);
  this.y$1 = (jsx$1 + (50.0 * $uD(Math.sin(a))));
  this.prevTime$2 = (this.prevTime$2 + timeDelta);
  var this$2 = this.meteors$2;
  if ((!this$2.isEmpty__Z())) {
    var h = $as_T3(this.meteors$2.head__O());
    if ((this.prevTime$2 > $uD(h.$$und2$1))) {
      this.prevTime$2 = (this.prevTime$2 - $uD(h.$$und2$1));
      this.meteors$2 = $as_sci_Seq(this.meteors$2.tail__O());
      var b = $as_Lcom_kos_wormpad_heroes_Hero($as_F0(h.$$und3$1).apply__O());
      var jsx$3 = this.x$1;
      var jsx$2 = this.radius$1;
      var this$3 = this.random$2;
      b.x$1 = ((jsx$3 - jsx$2) + (2.0 * (this$3.self$1.nextDouble__D() * this.radius$1)));
      b.y$1 = (this.y$1 - this.radius$1);
      var jsx$4 = this.heroes$2;
      var this$4 = this.heroes$2.burgers$1;
      jsx$4.burgers$1 = $as_sci_Set(this$4.incl__O__sci_SetOps(b))
    }
  }
});
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers.prototype.ediible__Z = (function() {
  return this.ediible$2
});
var $d_Lcom_kos_wormpad_heroes_ShipWithBurgers = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_ShipWithBurgers: 0
}, false, "com.kos.wormpad.heroes.ShipWithBurgers", {
  Lcom_kos_wormpad_heroes_ShipWithBurgers: 1,
  Lcom_kos_wormpad_heroes_Hero: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_ShipWithBurgers.prototype.$classData = $d_Lcom_kos_wormpad_heroes_ShipWithBurgers;
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_Worm() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  this.kind$2 = 0;
  this.wormHeadRadius$2 = 0;
  this.health$2 = 0.0;
  this.tail$2 = null;
  this.wormMaxRadius$2 = 0;
  $c_Lcom_kos_wormpad_heroes_Hero.prototype.init___.call(this);
  this.kind$2 = 901;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.wormHeadRadius$2 = 20;
  this.health$2 = $m_Lcom_kos_wormpad_heroes_Worm$().MAX$undHEALTH$1;
  var this$1 = $m_sci_Seq$();
  var elem = new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      return new $c_Lcom_kos_wormpad_heroes_WormTail()
    })
  })(this));
  this.tail$2 = $as_sci_Seq($f_sc_IterableFactory__fill__I__F0__O(this$1, 5, elem));
  var this$2 = this.tail$2;
  var end = this$2.length__I();
  var isEmpty$4 = (end <= 0);
  var scala$collection$immutable$Range$$lastElement$f = (((-1) + end) | 0);
  if ((!isEmpty$4)) {
    var i = 0;
    while (true) {
      var v1 = i;
      $as_Lcom_kos_wormpad_heroes_Hero(this.tail$2.apply__I__O(v1)).radius$1 = ((5 + $imul(3, ((6 - v1) | 0))) | 0);
      if ((i === scala$collection$immutable$Range$$lastElement$f)) {
        break
      };
      i = ((1 + i) | 0)
    }
  };
  this.wormMaxRadius$2 = ((this.wormHeadRadius$2 + $uI($as_sc_IterableOnceOps(this.tail$2.map__F1__O(new $c_sjsr_AnonFunction1((function(this$3$1) {
    return (function(x$1$2) {
      var x$1 = $as_Lcom_kos_wormpad_heroes_WormTail(x$1$2);
      return x$1.tailDistance$2
    })
  })(this)))).sum__s_math_Numeric__O($m_s_math_Numeric$IntIsIntegral$()))) | 0)
}
$c_Lcom_kos_wormpad_heroes_Worm.prototype = new $h_Lcom_kos_wormpad_heroes_Hero();
$c_Lcom_kos_wormpad_heroes_Worm.prototype.constructor = $c_Lcom_kos_wormpad_heroes_Worm;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_Worm() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_Worm.prototype = $c_Lcom_kos_wormpad_heroes_Worm.prototype;
$c_Lcom_kos_wormpad_heroes_Worm.prototype.kind__I = (function() {
  return this.kind$2
});
$c_Lcom_kos_wormpad_heroes_Worm.prototype.move__D__V = (function(timeDelta) {
  this.x$1 = (this.x$1 + (this.vx$1 * timeDelta));
  this.y$1 = (this.y$1 + (this.vy$1 * timeDelta));
  this.moveTail$1__p2__D__D__sci_Seq__V(this.x$1, this.y$1, this.tail$2)
});
$c_Lcom_kos_wormpad_heroes_Worm.prototype.eat__Lcom_kos_wormpad_heroes_Hero__Z = (function(burger) {
  return ($m_jl_Math$().hypot__D__D__D((burger.x$1 - this.x$1), (burger.y$1 - this.y$1)) < (this.wormHeadRadius$2 + burger.radius$1))
});
$c_Lcom_kos_wormpad_heroes_Worm.prototype.moveTail$1__p2__D__D__sci_Seq__V = (function(predx, predy, tail) {
  while (true) {
    var this$1 = tail;
    if ((!this$1.isEmpty__Z())) {
      var wt = $as_Lcom_kos_wormpad_heroes_WormTail(tail.head__O());
      var distx = (predx - wt.x$1);
      var disty = (predy - wt.y$1);
      var h = $m_jl_Math$().hypot__D__D__D(distx, disty);
      if ((h > wt.tailDistance$2)) {
        var scale = (wt.tailDistance$2 / h);
        wt.x$1 = (predx - (distx * scale));
        wt.y$1 = (predy - (disty * scale))
      };
      var temp$predx = wt.x$1;
      var temp$predy = wt.y$1;
      var temp$tail = $as_sci_Seq(tail.tail__O());
      predx = temp$predx;
      predy = temp$predy;
      tail = temp$tail;
      continue
    };
    break
  }
});
$c_Lcom_kos_wormpad_heroes_Worm.prototype.inFreeZone__D__D__Z = (function(xp, yp) {
  return ($m_jl_Math$().hypot__D__D__D((xp - this.x$1), (yp - this.y$1)) < this.wormMaxRadius$2)
});
var $d_Lcom_kos_wormpad_heroes_Worm = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_Worm: 0
}, false, "com.kos.wormpad.heroes.Worm", {
  Lcom_kos_wormpad_heroes_Worm: 1,
  Lcom_kos_wormpad_heroes_Hero: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_Worm.prototype.$classData = $d_Lcom_kos_wormpad_heroes_Worm;
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_WormTail() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  this.tailDistance$2 = 0;
  this.kind$2 = 0;
  $c_Lcom_kos_wormpad_heroes_Hero.prototype.init___.call(this);
  this.radius$1 = 10.0;
  this.tailDistance$2 = 24;
  this.kind$2 = 902
}
$c_Lcom_kos_wormpad_heroes_WormTail.prototype = new $h_Lcom_kos_wormpad_heroes_Hero();
$c_Lcom_kos_wormpad_heroes_WormTail.prototype.constructor = $c_Lcom_kos_wormpad_heroes_WormTail;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_WormTail() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_WormTail.prototype = $c_Lcom_kos_wormpad_heroes_WormTail.prototype;
$c_Lcom_kos_wormpad_heroes_WormTail.prototype.kind__I = (function() {
  return this.kind$2
});
function $is_Lcom_kos_wormpad_heroes_WormTail(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_heroes_WormTail)))
}
function $as_Lcom_kos_wormpad_heroes_WormTail(obj) {
  return (($is_Lcom_kos_wormpad_heroes_WormTail(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.heroes.WormTail"))
}
function $isArrayOf_Lcom_kos_wormpad_heroes_WormTail(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_heroes_WormTail)))
}
function $asArrayOf_Lcom_kos_wormpad_heroes_WormTail(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_heroes_WormTail(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.heroes.WormTail;", depth))
}
var $d_Lcom_kos_wormpad_heroes_WormTail = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_WormTail: 0
}, false, "com.kos.wormpad.heroes.WormTail", {
  Lcom_kos_wormpad_heroes_WormTail: 1,
  Lcom_kos_wormpad_heroes_Hero: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_WormTail.prototype.$classData = $d_Lcom_kos_wormpad_heroes_WormTail;
/** @constructor */
function $c_jl_Number() {
  /*<skip>*/
}
$c_jl_Number.prototype = new $h_O();
$c_jl_Number.prototype.constructor = $c_jl_Number;
/** @constructor */
function $h_jl_Number() {
  /*<skip>*/
}
$h_jl_Number.prototype = $c_jl_Number.prototype;
function $is_jl_Number(obj) {
  return (!(!(((obj && obj.$classData) && obj.$classData.ancestors.jl_Number) || ((typeof obj) === "number"))))
}
function $as_jl_Number(obj) {
  return (($is_jl_Number(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "java.lang.Number"))
}
function $isArrayOf_jl_Number(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.jl_Number)))
}
function $asArrayOf_jl_Number(obj, depth) {
  return (($isArrayOf_jl_Number(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.Number;", depth))
}
/** @constructor */
function $c_jl_Throwable() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
/** @constructor */
function $hh_jl_Throwable() {
  /*<skip>*/
}
$hh_jl_Throwable.prototype = Error.prototype;
$c_jl_Throwable.prototype = new $hh_jl_Throwable();
$c_jl_Throwable.prototype.constructor = $c_jl_Throwable;
/** @constructor */
function $h_jl_Throwable() {
  /*<skip>*/
}
$h_jl_Throwable.prototype = $c_jl_Throwable.prototype;
$c_jl_Throwable.prototype.fillInStackTrace__jl_Throwable = (function() {
  var identifyingString = Object.prototype.toString.call(this);
  if ((identifyingString === "[object Error]")) {
    this.stackTraceStateInternal$1 = this
  } else {
    var v = Error.captureStackTrace;
    if ((v === (void 0))) {
      try {
        var e$1 = {}.undef()
      } catch (e) {
        var e$2 = $m_sjsr_package$().wrapJavaScriptException__O__jl_Throwable(e);
        if ((e$2 !== null)) {
          if ($is_sjs_js_JavaScriptException(e$2)) {
            var x5 = $as_sjs_js_JavaScriptException(e$2);
            var e$3 = x5.exception$4;
            var e$1 = e$3
          } else {
            var e$1;
            throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(e$2)
          }
        } else {
          var e$1;
          throw e
        }
      };
      this.stackTraceStateInternal$1 = e$1
    } else {
      Error.captureStackTrace(this);
      this.stackTraceStateInternal$1 = this
    }
  };
  return this
});
$c_jl_Throwable.prototype.$$js$exported$prop$name__O = (function() {
  return $objectGetClass(this).getName__T()
});
$c_jl_Throwable.prototype.getMessage__T = (function() {
  return this.s$1
});
$c_jl_Throwable.prototype.$$js$exported$meth$toString__O = (function() {
  return this.toString__T()
});
$c_jl_Throwable.prototype.toString__T = (function() {
  var className = $objectGetClass(this).getName__T();
  var message = this.getMessage__T();
  return ((message === null) ? className : ((className + ": ") + message))
});
$c_jl_Throwable.prototype.$$js$exported$prop$message__O = (function() {
  var m = this.getMessage__T();
  return ((m === null) ? "" : m)
});
$c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z = (function(s, e, enableSuppression, writableStackTrace) {
  this.s$1 = s;
  this.e$1 = e;
  this.enableSuppression$1 = enableSuppression;
  this.writableStackTrace$1 = writableStackTrace;
  if (writableStackTrace) {
    this.fillInStackTrace__jl_Throwable()
  };
  return this
});
$c_jl_Throwable.prototype.equals__O__Z = (function(that) {
  return $c_O.prototype.equals__O__Z.call(this, that)
});
$c_jl_Throwable.prototype.hashCode__I = (function() {
  return $c_O.prototype.hashCode__I.call(this)
});
Object.defineProperty($c_jl_Throwable.prototype, "message", {
  "get": (function() {
    return this.$$js$exported$prop$message__O()
  }),
  "configurable": true
});
Object.defineProperty($c_jl_Throwable.prototype, "name", {
  "get": (function() {
    return this.$$js$exported$prop$name__O()
  }),
  "configurable": true
});
$c_jl_Throwable.prototype.toString = (function() {
  return this.$$js$exported$meth$toString__O()
});
function $is_jl_Throwable(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.jl_Throwable)))
}
function $as_jl_Throwable(obj) {
  return (($is_jl_Throwable(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "java.lang.Throwable"))
}
function $isArrayOf_jl_Throwable(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.jl_Throwable)))
}
function $asArrayOf_jl_Throwable(obj, depth) {
  return (($isArrayOf_jl_Throwable(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.Throwable;", depth))
}
/** @constructor */
function $c_ju_Random() {
  this.seedHi$1 = 0;
  this.seedLo$1 = 0;
  this.nextNextGaussian$1 = 0.0;
  this.haveNextNextGaussian$1 = false
}
$c_ju_Random.prototype = new $h_O();
$c_ju_Random.prototype.constructor = $c_ju_Random;
/** @constructor */
function $h_ju_Random() {
  /*<skip>*/
}
$h_ju_Random.prototype = $c_ju_Random.prototype;
$c_ju_Random.prototype.init___ = (function() {
  $c_ju_Random.prototype.init___J.call(this, $m_ju_Random$().java$util$Random$$randomSeed__J());
  return this
});
$c_ju_Random.prototype.init___J = (function(seed_in) {
  this.haveNextNextGaussian$1 = false;
  this.setSeed__J__V(seed_in);
  return this
});
$c_ju_Random.prototype.nextInt__I__I = (function(n) {
  if ((n <= 0)) {
    throw new $c_jl_IllegalArgumentException().init___T("n must be positive")
  } else {
    return (((n & ((-n) | 0)) === n) ? (this.next__I__I(31) >> $clz32(n)) : this.loop$1__p1__I__I(n))
  }
});
$c_ju_Random.prototype.next__I__I = (function(bits) {
  var oldSeedHi = this.seedHi$1;
  var oldSeedLo = this.seedLo$1;
  var loProd = (11.0 + (1.5525485E7 * oldSeedLo));
  var hiProd = ((1502.0 * oldSeedLo) + (1.5525485E7 * oldSeedHi));
  var x = (loProd / 1.6777216E7);
  var newSeedHi = (16777215 & (($uI((x | 0)) + (16777215 & $uI((hiProd | 0)))) | 0));
  var newSeedLo = (16777215 & $uI((loProd | 0)));
  this.seedHi$1 = newSeedHi;
  this.seedLo$1 = newSeedLo;
  var result32 = ((newSeedHi << 8) | (newSeedLo >> 16));
  return ((result32 >>> ((32 - bits) | 0)) | 0)
});
$c_ju_Random.prototype.loop$1__p1__I__I = (function(n$1) {
  while (true) {
    var bits = this.next__I__I(31);
    var value = ((bits % n$1) | 0);
    if ((((((bits - value) | 0) + (((-1) + n$1) | 0)) | 0) < 0)) {
      /*<skip>*/
    } else {
      return value
    }
  }
});
$c_ju_Random.prototype.nextDouble__D = (function() {
  return (((1.34217728E8 * this.next__I__I(26)) + this.next__I__I(27)) / 9.007199254740992E15)
});
$c_ju_Random.prototype.setSeed__J__V = (function(seed_in) {
  var lo = ((-554899859) ^ seed_in.lo$2);
  var hi = (5 ^ seed_in.hi$2);
  var hi$1 = (65535 & hi);
  var lo$1 = (((lo >>> 24) | 0) | (hi$1 << 8));
  this.seedHi$1 = lo$1;
  this.seedLo$1 = (16777215 & lo);
  this.haveNextNextGaussian$1 = false
});
var $d_ju_Random = new $TypeData().initClass({
  ju_Random: 0
}, false, "java.util.Random", {
  ju_Random: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_ju_Random.prototype.$classData = $d_ju_Random;
/** @constructor */
function $c_s_LowPriorityImplicits() {
  /*<skip>*/
}
$c_s_LowPriorityImplicits.prototype = new $h_s_LowPriorityImplicits2();
$c_s_LowPriorityImplicits.prototype.constructor = $c_s_LowPriorityImplicits;
/** @constructor */
function $h_s_LowPriorityImplicits() {
  /*<skip>*/
}
$h_s_LowPriorityImplicits.prototype = $c_s_LowPriorityImplicits.prototype;
function $f_s_Product2__productElement__I__O($thiz, n) {
  switch (n) {
    case 0: {
      return $thiz.$$und1__O();
      break
    }
    case 1: {
      return $thiz.$$und2__O();
      break
    }
    default: {
      throw new $c_jl_IndexOutOfBoundsException().init___T(("" + n))
    }
  }
}
function $f_s_Product3__productElement__I__O($thiz, n) {
  switch (n) {
    case 0: {
      return $thiz.$$und1$1;
      break
    }
    case 1: {
      return $thiz.$$und2$1;
      break
    }
    case 2: {
      return $thiz.$$und3$1;
      break
    }
    default: {
      throw new $c_jl_IndexOutOfBoundsException().init___T(("" + n))
    }
  }
}
/** @constructor */
function $c_s_package$$anon$1() {
  /*<skip>*/
}
$c_s_package$$anon$1.prototype = new $h_O();
$c_s_package$$anon$1.prototype.constructor = $c_s_package$$anon$1;
/** @constructor */
function $h_s_package$$anon$1() {
  /*<skip>*/
}
$h_s_package$$anon$1.prototype = $c_s_package$$anon$1.prototype;
$c_s_package$$anon$1.prototype.toString__T = (function() {
  return "object AnyRef"
});
var $d_s_package$$anon$1 = new $TypeData().initClass({
  s_package$$anon$1: 0
}, false, "scala.package$$anon$1", {
  s_package$$anon$1: 1,
  O: 1,
  s_Specializable: 1
});
$c_s_package$$anon$1.prototype.$classData = $d_s_package$$anon$1;
/** @constructor */
function $c_s_util_hashing_MurmurHash3$() {
  this.seqSeed$2 = 0;
  this.mapSeed$2 = 0;
  this.setSeed$2 = 0;
  $n_s_util_hashing_MurmurHash3$ = this;
  this.seqSeed$2 = $f_T__hashCode__I("Seq");
  this.mapSeed$2 = $f_T__hashCode__I("Map");
  this.setSeed$2 = $f_T__hashCode__I("Set")
}
$c_s_util_hashing_MurmurHash3$.prototype = new $h_s_util_hashing_MurmurHash3();
$c_s_util_hashing_MurmurHash3$.prototype.constructor = $c_s_util_hashing_MurmurHash3$;
/** @constructor */
function $h_s_util_hashing_MurmurHash3$() {
  /*<skip>*/
}
$h_s_util_hashing_MurmurHash3$.prototype = $c_s_util_hashing_MurmurHash3$.prototype;
$c_s_util_hashing_MurmurHash3$.prototype.seqHash__sc_Seq__I = (function(xs) {
  if ($is_sci_List(xs)) {
    var x2 = $as_sci_List(xs);
    return this.listHash__sci_List__I__I(x2, this.seqSeed$2)
  } else {
    return this.orderedHash__sc_IterableOnce__I__I(xs, this.seqSeed$2)
  }
});
var $d_s_util_hashing_MurmurHash3$ = new $TypeData().initClass({
  s_util_hashing_MurmurHash3$: 0
}, false, "scala.util.hashing.MurmurHash3$", {
  s_util_hashing_MurmurHash3$: 1,
  s_util_hashing_MurmurHash3: 1,
  O: 1
});
$c_s_util_hashing_MurmurHash3$.prototype.$classData = $d_s_util_hashing_MurmurHash3$;
var $n_s_util_hashing_MurmurHash3$ = (void 0);
function $m_s_util_hashing_MurmurHash3$() {
  if ((!$n_s_util_hashing_MurmurHash3$)) {
    $n_s_util_hashing_MurmurHash3$ = new $c_s_util_hashing_MurmurHash3$()
  };
  return $n_s_util_hashing_MurmurHash3$
}
function $f_sc_IterableFactory__fill__I__F0__O($thiz, n, elem) {
  return $thiz.from__sc_IterableOnce__O(new $c_sc_View$Fill(n, elem))
}
function $f_sc_IterableOps__flatMap__F1__O($thiz, f) {
  return $thiz.iterableFactory__sc_IterableFactory().from__sc_IterableOnce__O(new $c_sc_View$FlatMap($thiz, f))
}
function $f_sc_IterableOps__filter__F1__O($thiz, pred) {
  return $thiz.fromSpecific__sc_IterableOnce__O(new $c_sc_View$Filter($thiz, pred, false))
}
function $f_sc_IterableOps__filterNot__F1__O($thiz, pred) {
  return $thiz.fromSpecific__sc_IterableOnce__O(new $c_sc_View$Filter($thiz, pred, true))
}
function $f_sc_IterableOps__splitAt__I__T2($thiz, n) {
  return new $c_T2($thiz.take__I__O(n), $thiz.drop__I__O(n))
}
function $f_sc_IterableOps__take__I__O($thiz, n) {
  return $thiz.fromSpecific__sc_IterableOnce__O(new $c_sc_View$Take().init___sc_IterableOps__I($thiz, n))
}
function $f_sc_IterableOps__last__O($thiz) {
  var it = $thiz.iterator__sc_Iterator();
  var lst = it.next__O();
  while (it.hasNext__Z()) {
    lst = it.next__O()
  };
  return lst
}
function $f_sc_IterableOps__drop__I__O($thiz, n) {
  return $thiz.fromSpecific__sc_IterableOnce__O(new $c_sc_View$Drop().init___sc_IterableOps__I($thiz, n))
}
function $f_sc_IterableOps__tail__O($thiz) {
  if ($thiz.isEmpty__Z()) {
    throw new $c_jl_UnsupportedOperationException().init___()
  };
  return $thiz.drop__I__O(1)
}
function $f_sc_IterableOps__map__F1__O($thiz, f) {
  return $thiz.iterableFactory__sc_IterableFactory().from__sc_IterableOnce__O(new $c_sc_View$Map().init___sc_IterableOps__F1($thiz, f))
}
function $f_sc_IterableOps__sizeCompare__I__I($thiz, otherSize) {
  if ((otherSize < 0)) {
    return 1
  } else {
    var known = $thiz.knownSize__I();
    if ((known >= 0)) {
      return ((known === otherSize) ? 0 : ((known < otherSize) ? (-1) : 1))
    } else {
      var i = 0;
      var it = $thiz.iterator__sc_Iterator();
      while (it.hasNext__Z()) {
        if ((i === otherSize)) {
          return (it.hasNext__Z() ? 1 : 0)
        };
        it.next__O();
        i = ((1 + i) | 0)
      };
      return ((i - otherSize) | 0)
    }
  }
}
function $is_sc_IterableOps(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_IterableOps)))
}
function $as_sc_IterableOps(obj) {
  return (($is_sc_IterableOps(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.IterableOps"))
}
function $isArrayOf_sc_IterableOps(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_IterableOps)))
}
function $asArrayOf_sc_IterableOps(obj, depth) {
  return (($isArrayOf_sc_IterableOps(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.IterableOps;", depth))
}
/** @constructor */
function $c_sc_IterableOps$WithFilter() {
  this.self$2 = null;
  this.p$2 = null
}
$c_sc_IterableOps$WithFilter.prototype = new $h_sc_WithFilter();
$c_sc_IterableOps$WithFilter.prototype.constructor = $c_sc_IterableOps$WithFilter;
/** @constructor */
function $h_sc_IterableOps$WithFilter() {
  /*<skip>*/
}
$h_sc_IterableOps$WithFilter.prototype = $c_sc_IterableOps$WithFilter.prototype;
$c_sc_IterableOps$WithFilter.prototype.init___sc_IterableOps__F1 = (function(self, p) {
  this.self$2 = self;
  this.p$2 = p;
  return this
});
$c_sc_IterableOps$WithFilter.prototype.foreach__F1__V = (function(f) {
  this.filtered__sc_Iterable().foreach__F1__V(f)
});
$c_sc_IterableOps$WithFilter.prototype.filtered__sc_Iterable = (function() {
  return new $c_sc_View$Filter(this.self$2, this.p$2, false)
});
var $d_sc_IterableOps$WithFilter = new $TypeData().initClass({
  sc_IterableOps$WithFilter: 0
}, false, "scala.collection.IterableOps$WithFilter", {
  sc_IterableOps$WithFilter: 1,
  sc_WithFilter: 1,
  O: 1
});
$c_sc_IterableOps$WithFilter.prototype.$classData = $d_sc_IterableOps$WithFilter;
function $f_sc_Iterator__concat__F0__sc_Iterator($thiz, xs) {
  return new $c_sc_Iterator$ConcatIterator($thiz).concat__F0__sc_Iterator(xs)
}
function $f_sc_Iterator__take__I__sc_Iterator($thiz, n) {
  return $thiz.sliceIterator__I__I__sc_Iterator(0, ((n > 0) ? n : 0))
}
function $f_sc_Iterator__sameElements__sc_IterableOnce__Z($thiz, that) {
  var those = that.iterator__sc_Iterator();
  while (($thiz.hasNext__Z() && those.hasNext__Z())) {
    if ((!$m_sr_BoxesRunTime$().equals__O__O__Z($thiz.next__O(), those.next__O()))) {
      return false
    }
  };
  return ($thiz.hasNext__Z() === those.hasNext__Z())
}
function $f_sc_Iterator__sliceIterator__I__I__sc_Iterator($thiz, from, until) {
  var lo = ((from > 0) ? from : 0);
  var rest = ((until < 0) ? (-1) : ((until <= lo) ? 0 : ((until - lo) | 0)));
  return ((rest === 0) ? $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f : new $c_sc_Iterator$SliceIterator($thiz, lo, rest))
}
function $f_sc_Iterator__drop__I__sc_Iterator($thiz, n) {
  var i = 0;
  while (((i < n) && $thiz.hasNext__Z())) {
    $thiz.next__O();
    i = ((1 + i) | 0)
  };
  return $thiz
}
function $is_sc_Iterator(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_Iterator)))
}
function $as_sc_Iterator(obj) {
  return (($is_sc_Iterator(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.Iterator"))
}
function $isArrayOf_sc_Iterator(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_Iterator)))
}
function $asArrayOf_sc_Iterator(obj, depth) {
  return (($isArrayOf_sc_Iterator(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.Iterator;", depth))
}
/** @constructor */
function $c_scg_BitOperations$Int$() {
  /*<skip>*/
}
$c_scg_BitOperations$Int$.prototype = new $h_O();
$c_scg_BitOperations$Int$.prototype.constructor = $c_scg_BitOperations$Int$;
/** @constructor */
function $h_scg_BitOperations$Int$() {
  /*<skip>*/
}
$h_scg_BitOperations$Int$.prototype = $c_scg_BitOperations$Int$.prototype;
var $d_scg_BitOperations$Int$ = new $TypeData().initClass({
  scg_BitOperations$Int$: 0
}, false, "scala.collection.generic.BitOperations$Int$", {
  scg_BitOperations$Int$: 1,
  O: 1,
  scg_BitOperations$Int: 1
});
$c_scg_BitOperations$Int$.prototype.$classData = $d_scg_BitOperations$Int$;
var $n_scg_BitOperations$Int$ = (void 0);
function $m_scg_BitOperations$Int$() {
  if ((!$n_scg_BitOperations$Int$)) {
    $n_scg_BitOperations$Int$ = new $c_scg_BitOperations$Int$()
  };
  return $n_scg_BitOperations$Int$
}
function $is_sci_LazyList$State(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_LazyList$State)))
}
function $as_sci_LazyList$State(obj) {
  return (($is_sci_LazyList$State(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.LazyList$State"))
}
function $isArrayOf_sci_LazyList$State(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_LazyList$State)))
}
function $asArrayOf_sci_LazyList$State(obj, depth) {
  return (($isArrayOf_sci_LazyList$State(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.LazyList$State;", depth))
}
/** @constructor */
function $c_sci_LazyList$WithFilter(lazyList, p) {
  this.filtered$2 = null;
  this.filtered$2 = lazyList.filter__F1__sci_LazyList(p)
}
$c_sci_LazyList$WithFilter.prototype = new $h_sc_WithFilter();
$c_sci_LazyList$WithFilter.prototype.constructor = $c_sci_LazyList$WithFilter;
/** @constructor */
function $h_sci_LazyList$WithFilter() {
  /*<skip>*/
}
$h_sci_LazyList$WithFilter.prototype = $c_sci_LazyList$WithFilter.prototype;
$c_sci_LazyList$WithFilter.prototype.foreach__F1__V = (function(f) {
  this.filtered$2.foreach__F1__V(f)
});
var $d_sci_LazyList$WithFilter = new $TypeData().initClass({
  sci_LazyList$WithFilter: 0
}, false, "scala.collection.immutable.LazyList$WithFilter", {
  sci_LazyList$WithFilter: 1,
  sc_WithFilter: 1,
  O: 1
});
$c_sci_LazyList$WithFilter.prototype.$classData = $d_sci_LazyList$WithFilter;
/** @constructor */
function $c_sci_List$$anon$1() {
  /*<skip>*/
}
$c_sci_List$$anon$1.prototype = new $h_O();
$c_sci_List$$anon$1.prototype.constructor = $c_sci_List$$anon$1;
/** @constructor */
function $h_sci_List$$anon$1() {
  /*<skip>*/
}
$h_sci_List$$anon$1.prototype = $c_sci_List$$anon$1.prototype;
$c_sci_List$$anon$1.prototype.apply__O__O = (function(x) {
  return this
});
$c_sci_List$$anon$1.prototype.toString__T = (function() {
  return "<function1>"
});
var $d_sci_List$$anon$1 = new $TypeData().initClass({
  sci_List$$anon$1: 0
}, false, "scala.collection.immutable.List$$anon$1", {
  sci_List$$anon$1: 1,
  O: 1,
  F1: 1
});
$c_sci_List$$anon$1.prototype.$classData = $d_sci_List$$anon$1;
/** @constructor */
function $c_sci_MapNode() {
  /*<skip>*/
}
$c_sci_MapNode.prototype = new $h_sci_Node();
$c_sci_MapNode.prototype.constructor = $c_sci_MapNode;
/** @constructor */
function $h_sci_MapNode() {
  /*<skip>*/
}
$h_sci_MapNode.prototype = $c_sci_MapNode.prototype;
function $is_sci_MapNode(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_MapNode)))
}
function $as_sci_MapNode(obj) {
  return (($is_sci_MapNode(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.MapNode"))
}
function $isArrayOf_sci_MapNode(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_MapNode)))
}
function $asArrayOf_sci_MapNode(obj, depth) {
  return (($isArrayOf_sci_MapNode(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.MapNode;", depth))
}
/** @constructor */
function $c_sci_OldHashMap$$anon$2(mergef$1) {
  this.invert$2 = null;
  this.mergef$1$f = null;
  this.mergef$1$f = mergef$1;
  this.invert$2 = new $c_sci_OldHashMap$$anon$2$$anon$3(this)
}
$c_sci_OldHashMap$$anon$2.prototype = new $h_sci_OldHashMap$Merger();
$c_sci_OldHashMap$$anon$2.prototype.constructor = $c_sci_OldHashMap$$anon$2;
/** @constructor */
function $h_sci_OldHashMap$$anon$2() {
  /*<skip>*/
}
$h_sci_OldHashMap$$anon$2.prototype = $c_sci_OldHashMap$$anon$2.prototype;
$c_sci_OldHashMap$$anon$2.prototype.apply__T2__T2__T2 = (function(kv1, kv2) {
  return $as_T2(this.mergef$1$f.apply__O__O__O(kv1, kv2))
});
var $d_sci_OldHashMap$$anon$2 = new $TypeData().initClass({
  sci_OldHashMap$$anon$2: 0
}, false, "scala.collection.immutable.OldHashMap$$anon$2", {
  sci_OldHashMap$$anon$2: 1,
  sci_OldHashMap$Merger: 1,
  O: 1
});
$c_sci_OldHashMap$$anon$2.prototype.$classData = $d_sci_OldHashMap$$anon$2;
/** @constructor */
function $c_sci_OldHashMap$$anon$2$$anon$3($$outer) {
  this.$$outer$2 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  }
}
$c_sci_OldHashMap$$anon$2$$anon$3.prototype = new $h_sci_OldHashMap$Merger();
$c_sci_OldHashMap$$anon$2$$anon$3.prototype.constructor = $c_sci_OldHashMap$$anon$2$$anon$3;
/** @constructor */
function $h_sci_OldHashMap$$anon$2$$anon$3() {
  /*<skip>*/
}
$h_sci_OldHashMap$$anon$2$$anon$3.prototype = $c_sci_OldHashMap$$anon$2$$anon$3.prototype;
$c_sci_OldHashMap$$anon$2$$anon$3.prototype.apply__T2__T2__T2 = (function(kv1, kv2) {
  return $as_T2(this.$$outer$2.mergef$1$f.apply__O__O__O(kv2, kv1))
});
var $d_sci_OldHashMap$$anon$2$$anon$3 = new $TypeData().initClass({
  sci_OldHashMap$$anon$2$$anon$3: 0
}, false, "scala.collection.immutable.OldHashMap$$anon$2$$anon$3", {
  sci_OldHashMap$$anon$2$$anon$3: 1,
  sci_OldHashMap$Merger: 1,
  O: 1
});
$c_sci_OldHashMap$$anon$2$$anon$3.prototype.$classData = $d_sci_OldHashMap$$anon$2$$anon$3;
/** @constructor */
function $c_sci_SetNode() {
  /*<skip>*/
}
$c_sci_SetNode.prototype = new $h_sci_Node();
$c_sci_SetNode.prototype.constructor = $c_sci_SetNode;
/** @constructor */
function $h_sci_SetNode() {
  /*<skip>*/
}
$h_sci_SetNode.prototype = $c_sci_SetNode.prototype;
function $is_sci_SetNode(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_SetNode)))
}
function $as_sci_SetNode(obj) {
  return (($is_sci_SetNode(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.SetNode"))
}
function $isArrayOf_sci_SetNode(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_SetNode)))
}
function $asArrayOf_sci_SetNode(obj, depth) {
  return (($isArrayOf_sci_SetNode(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.SetNode;", depth))
}
/** @constructor */
function $c_sci_Stream$WithFilter(l, p) {
  this.filtered$2 = null;
  this.p$2 = null;
  this.s$2 = null;
  this.bitmap$0$2 = false;
  this.p$2 = p;
  this.s$2 = l
}
$c_sci_Stream$WithFilter.prototype = new $h_sc_WithFilter();
$c_sci_Stream$WithFilter.prototype.constructor = $c_sci_Stream$WithFilter;
/** @constructor */
function $h_sci_Stream$WithFilter() {
  /*<skip>*/
}
$h_sci_Stream$WithFilter.prototype = $c_sci_Stream$WithFilter.prototype;
$c_sci_Stream$WithFilter.prototype.filtered__p2__sci_Stream = (function() {
  return ((!this.bitmap$0$2) ? this.filtered$lzycompute__p2__sci_Stream() : this.filtered$2)
});
$c_sci_Stream$WithFilter.prototype.foreach__F1__V = (function(f) {
  this.filtered__p2__sci_Stream().foreach__F1__V(f)
});
$c_sci_Stream$WithFilter.prototype.filtered$lzycompute__p2__sci_Stream = (function() {
  if ((!this.bitmap$0$2)) {
    var this$1 = this.s$2;
    var pred = this.p$2;
    var f = this$1.filterImpl__F1__Z__sci_Stream(pred, false);
    this.s$2 = null;
    this.filtered$2 = f;
    this.bitmap$0$2 = true
  };
  return this.filtered$2
});
var $d_sci_Stream$WithFilter = new $TypeData().initClass({
  sci_Stream$WithFilter: 0
}, false, "scala.collection.immutable.Stream$WithFilter", {
  sci_Stream$WithFilter: 1,
  sc_WithFilter: 1,
  O: 1
});
$c_sci_Stream$WithFilter.prototype.$classData = $d_sci_Stream$WithFilter;
function $is_scm_Builder(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.scm_Builder)))
}
function $as_scm_Builder(obj) {
  return (($is_scm_Builder(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.mutable.Builder"))
}
function $isArrayOf_scm_Builder(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.scm_Builder)))
}
function $asArrayOf_scm_Builder(obj, depth) {
  return (($isArrayOf_scm_Builder(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.mutable.Builder;", depth))
}
/** @constructor */
function $c_scm_FlatHashTable() {
  this.$$undloadFactor$1 = 0;
  this.table$1 = null;
  this.tableSize$1 = 0;
  this.threshold$1 = 0;
  this.sizemap$1 = null;
  this.seedvalue$1 = 0;
  this.$$undloadFactor$1 = 450;
  this.table$1 = $newArrayObject($d_O.getArrayOf(), [$m_scm_HashTable$().nextPositivePowerOfTwo__I__I(32)]);
  this.tableSize$1 = 0;
  this.threshold$1 = $m_scm_FlatHashTable$().newThreshold__I__I__I(this.$$undloadFactor$1, $m_scm_HashTable$().nextPositivePowerOfTwo__I__I(32));
  this.sizemap$1 = null;
  this.seedvalue$1 = this.tableSizeSeed__I()
}
$c_scm_FlatHashTable.prototype = new $h_O();
$c_scm_FlatHashTable.prototype.constructor = $c_scm_FlatHashTable;
/** @constructor */
function $h_scm_FlatHashTable() {
  /*<skip>*/
}
$h_scm_FlatHashTable.prototype = $c_scm_FlatHashTable.prototype;
$c_scm_FlatHashTable.prototype.calcSizeMapSize__I__I = (function(tableLength) {
  return ((1 + (tableLength >> 5)) | 0)
});
$c_scm_FlatHashTable.prototype.tableSizeSeed__I = (function() {
  return $m_jl_Integer$().bitCount__I__I((((-1) + this.table$1.u.length) | 0))
});
$c_scm_FlatHashTable.prototype.growTable__p1__V = (function() {
  var oldtable = this.table$1;
  this.table$1 = $newArrayObject($d_O.getArrayOf(), [(this.table$1.u.length << 1)]);
  this.tableSize$1 = 0;
  this.nnSizeMapReset__I__V(this.table$1.u.length);
  this.seedvalue$1 = this.tableSizeSeed__I();
  this.threshold$1 = $m_scm_FlatHashTable$().newThreshold__I__I__I(this.$$undloadFactor$1, this.table$1.u.length);
  var i = 0;
  while ((i < oldtable.u.length)) {
    var entry = oldtable.get(i);
    if ((entry !== null)) {
      this.addEntry__O__Z(entry)
    };
    i = ((1 + i) | 0)
  }
});
$c_scm_FlatHashTable.prototype.addElem__O__Z = (function(elem) {
  return this.addEntry__O__Z($f_scm_FlatHashTable$HashUtils__elemToEntry__O__O(this, elem))
});
$c_scm_FlatHashTable.prototype.addEntry__O__Z = (function(newEntry) {
  var h = this.index__I__I($dp_hashCode__I(newEntry));
  var curEntry = this.table$1.get(h);
  while ((curEntry !== null)) {
    if ($m_sr_BoxesRunTime$().equals__O__O__Z(curEntry, newEntry)) {
      return false
    };
    h = ((((1 + h) | 0) % this.table$1.u.length) | 0);
    curEntry = this.table$1.get(h)
  };
  this.table$1.set(h, newEntry);
  this.tableSize$1 = ((1 + this.tableSize$1) | 0);
  this.nnSizeMapAdd__I__V(h);
  if ((this.tableSize$1 >= this.threshold$1)) {
    this.growTable__p1__V()
  };
  return true
});
$c_scm_FlatHashTable.prototype.index__I__I = (function(hcode) {
  var seed = this.seedvalue$1;
  var improved = $f_scm_FlatHashTable$HashUtils__improve__I__I__I(this, hcode, seed);
  var ones = (((-1) + this.table$1.u.length) | 0);
  return (((improved >>> ((32 - $m_jl_Integer$().bitCount__I__I(ones)) | 0)) | 0) & ones)
});
$c_scm_FlatHashTable.prototype.removeElem__O__Z = (function(elem) {
  var removalEntry = $f_scm_FlatHashTable$HashUtils__elemToEntry__O__O(this, elem);
  var h = this.index__I__I($dp_hashCode__I(removalEntry));
  var curEntry = this.table$1.get(h);
  while ((curEntry !== null)) {
    if ($m_sr_BoxesRunTime$().equals__O__O__Z(curEntry, removalEntry)) {
      var h0 = h;
      var h1 = ((((1 + h0) | 0) % this.table$1.u.length) | 0);
      while ((this.table$1.get(h1) !== null)) {
        var h2 = this.index__I__I($dp_hashCode__I(this.table$1.get(h1)));
        if (((h2 !== h1) && this.precedes$1__p1__I__I__Z(h2, h0))) {
          this.table$1.set(h0, this.table$1.get(h1));
          h0 = h1
        };
        h1 = ((((1 + h1) | 0) % this.table$1.u.length) | 0)
      };
      this.table$1.set(h0, null);
      this.tableSize$1 = (((-1) + this.tableSize$1) | 0);
      this.nnSizeMapRemove__I__V(h0);
      return true
    };
    h = ((((1 + h) | 0) % this.table$1.u.length) | 0);
    curEntry = this.table$1.get(h)
  };
  return false
});
$c_scm_FlatHashTable.prototype.findElemImpl__p1__O__O = (function(elem) {
  var searchEntry = $f_scm_FlatHashTable$HashUtils__elemToEntry__O__O(this, elem);
  var h = this.index__I__I($dp_hashCode__I(searchEntry));
  var curEntry = this.table$1.get(h);
  while (((curEntry !== null) && (!$m_sr_BoxesRunTime$().equals__O__O__Z(curEntry, searchEntry)))) {
    h = ((((1 + h) | 0) % this.table$1.u.length) | 0);
    curEntry = this.table$1.get(h)
  };
  return curEntry
});
$c_scm_FlatHashTable.prototype.precedes$1__p1__I__I__Z = (function(i, j) {
  var d = (this.table$1.u.length >> 1);
  return ((i <= j) ? (((j - i) | 0) < d) : (((i - j) | 0) > d))
});
$c_scm_FlatHashTable.prototype.containsElem__O__Z = (function(elem) {
  return (this.findElemImpl__p1__O__O(elem) !== null)
});
$c_scm_FlatHashTable.prototype.nnSizeMapRemove__I__V = (function(h) {
  if ((this.sizemap$1 !== null)) {
    var ev$1 = this.sizemap$1;
    var ev$2 = (h >> 5);
    ev$1.set(ev$2, (((-1) + ev$1.get(ev$2)) | 0))
  }
});
$c_scm_FlatHashTable.prototype.nnSizeMapReset__I__V = (function(tableLength) {
  if ((this.sizemap$1 !== null)) {
    var nsize = this.calcSizeMapSize__I__I(tableLength);
    if ((this.sizemap$1.u.length !== nsize)) {
      this.sizemap$1 = $newArrayObject($d_I.getArrayOf(), [nsize])
    } else {
      $m_ju_Arrays$().fill__AI__I__V(this.sizemap$1, 0)
    }
  }
});
$c_scm_FlatHashTable.prototype.nnSizeMapAdd__I__V = (function(h) {
  if ((this.sizemap$1 !== null)) {
    var p = (h >> 5);
    var ev$1 = this.sizemap$1;
    ev$1.set(p, ((1 + ev$1.get(p)) | 0))
  }
});
var $d_scm_FlatHashTable = new $TypeData().initClass({
  scm_FlatHashTable: 0
}, false, "scala.collection.mutable.FlatHashTable", {
  scm_FlatHashTable: 1,
  O: 1,
  scm_FlatHashTable$HashUtils: 1
});
$c_scm_FlatHashTable.prototype.$classData = $d_scm_FlatHashTable;
/** @constructor */
function $c_sr_AbstractFunction0() {
  /*<skip>*/
}
$c_sr_AbstractFunction0.prototype = new $h_O();
$c_sr_AbstractFunction0.prototype.constructor = $c_sr_AbstractFunction0;
/** @constructor */
function $h_sr_AbstractFunction0() {
  /*<skip>*/
}
$h_sr_AbstractFunction0.prototype = $c_sr_AbstractFunction0.prototype;
$c_sr_AbstractFunction0.prototype.toString__T = (function() {
  return "<function0>"
});
/** @constructor */
function $c_sr_AbstractFunction1() {
  /*<skip>*/
}
$c_sr_AbstractFunction1.prototype = new $h_O();
$c_sr_AbstractFunction1.prototype.constructor = $c_sr_AbstractFunction1;
/** @constructor */
function $h_sr_AbstractFunction1() {
  /*<skip>*/
}
$h_sr_AbstractFunction1.prototype = $c_sr_AbstractFunction1.prototype;
$c_sr_AbstractFunction1.prototype.toString__T = (function() {
  return "<function1>"
});
/** @constructor */
function $c_sr_AbstractFunction2() {
  /*<skip>*/
}
$c_sr_AbstractFunction2.prototype = new $h_O();
$c_sr_AbstractFunction2.prototype.constructor = $c_sr_AbstractFunction2;
/** @constructor */
function $h_sr_AbstractFunction2() {
  /*<skip>*/
}
$h_sr_AbstractFunction2.prototype = $c_sr_AbstractFunction2.prototype;
$c_sr_AbstractFunction2.prototype.toString__T = (function() {
  return "<function2>"
});
function $f_sr_BoxedUnit__equals__O__Z($thiz, that) {
  return ($thiz === that)
}
function $f_sr_BoxedUnit__toString__T($thiz) {
  return "undefined"
}
function $f_sr_BoxedUnit__hashCode__I($thiz) {
  return 0
}
function $isArrayOf_sr_BoxedUnit(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sr_BoxedUnit)))
}
function $asArrayOf_sr_BoxedUnit(obj, depth) {
  return (($isArrayOf_sr_BoxedUnit(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.runtime.BoxedUnit;", depth))
}
var $d_sr_BoxedUnit = new $TypeData().initClass({
  sr_BoxedUnit: 0
}, false, "scala.runtime.BoxedUnit", {
  sr_BoxedUnit: 1,
  O: 1,
  Ljava_io_Serializable: 1
}, (void 0), (void 0), (function(x) {
  return (x === (void 0))
}));
/** @constructor */
function $c_sr_IntRef(elem) {
  this.elem$1 = 0;
  this.elem$1 = elem
}
$c_sr_IntRef.prototype = new $h_O();
$c_sr_IntRef.prototype.constructor = $c_sr_IntRef;
/** @constructor */
function $h_sr_IntRef() {
  /*<skip>*/
}
$h_sr_IntRef.prototype = $c_sr_IntRef.prototype;
$c_sr_IntRef.prototype.toString__T = (function() {
  var i = this.elem$1;
  return ("" + i)
});
var $d_sr_IntRef = new $TypeData().initClass({
  sr_IntRef: 0
}, false, "scala.runtime.IntRef", {
  sr_IntRef: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_sr_IntRef.prototype.$classData = $d_sr_IntRef;
/** @constructor */
function $c_sr_ObjectRef(elem) {
  this.elem$1 = null;
  this.elem$1 = elem
}
$c_sr_ObjectRef.prototype = new $h_O();
$c_sr_ObjectRef.prototype.constructor = $c_sr_ObjectRef;
/** @constructor */
function $h_sr_ObjectRef() {
  /*<skip>*/
}
$h_sr_ObjectRef.prototype = $c_sr_ObjectRef.prototype;
$c_sr_ObjectRef.prototype.toString__T = (function() {
  var obj = this.elem$1;
  return ("" + obj)
});
var $d_sr_ObjectRef = new $TypeData().initClass({
  sr_ObjectRef: 0
}, false, "scala.runtime.ObjectRef", {
  sr_ObjectRef: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_sr_ObjectRef.prototype.$classData = $d_sr_ObjectRef;
/** @constructor */
function $c_Lcom_kos_wormpad_WormApp$$anon$1() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  this.width$2 = 0;
  this.height$2 = 0;
  this.velocityX$2 = 0.0;
  this.kind$2 = 0;
  $c_Lcom_kos_wormpad_heroes_Cloud.prototype.init___.call(this);
  this.x$1 = $m_Lcom_kos_wormpad_geometry_Geometry$().randomX__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D($m_Lcom_kos_wormpad_WormApp$().random$1, $m_Lcom_kos_wormpad_WormApp$().heroes$1.cloudArea$1);
  this.y$1 = $m_Lcom_kos_wormpad_geometry_Geometry$().randomY__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D($m_Lcom_kos_wormpad_WormApp$().random$1, $m_Lcom_kos_wormpad_WormApp$().heroes$1.cloudArea$1);
  var this$1 = $m_Lcom_kos_wormpad_WormApp$().random$1;
  this.velocityX$2 = (1.0 + (10.0 * this$1.self$1.nextDouble__D()));
  this.width$2 = 180;
  this.height$2 = 90
}
$c_Lcom_kos_wormpad_WormApp$$anon$1.prototype = new $h_Lcom_kos_wormpad_heroes_Cloud();
$c_Lcom_kos_wormpad_WormApp$$anon$1.prototype.constructor = $c_Lcom_kos_wormpad_WormApp$$anon$1;
/** @constructor */
function $h_Lcom_kos_wormpad_WormApp$$anon$1() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_WormApp$$anon$1.prototype = $c_Lcom_kos_wormpad_WormApp$$anon$1.prototype;
var $d_Lcom_kos_wormpad_WormApp$$anon$1 = new $TypeData().initClass({
  Lcom_kos_wormpad_WormApp$$anon$1: 0
}, false, "com.kos.wormpad.WormApp$$anon$1", {
  Lcom_kos_wormpad_WormApp$$anon$1: 1,
  Lcom_kos_wormpad_heroes_Cloud: 1,
  Lcom_kos_wormpad_heroes_Hero: 1,
  O: 1
});
$c_Lcom_kos_wormpad_WormApp$$anon$1.prototype.$classData = $d_Lcom_kos_wormpad_WormApp$$anon$1;
function $f_Lcom_kos_wormpad_game_GameState__pause__V($thiz) {
  $thiz.pause$und$1 = true;
  $thiz.listener$und$1.onPause__Z__V($thiz.pause$und$1)
}
function $f_Lcom_kos_wormpad_game_GameState__togglePause__V($thiz) {
  $thiz.pause$und$1 = (!$thiz.pause$und$1);
  $thiz.listener$und$1.onPause__Z__V($thiz.pause$und$1)
}
function $f_Lcom_kos_wormpad_game_GameState__$$init$__V($thiz) {
  $thiz.pause$und$1 = false;
  $thiz.isGameOver$und$1 = false;
  $thiz.listener$und$1 = new $c_Lcom_kos_wormpad_game_GameState$$anon$1($thiz);
  $thiz.jslistener$1 = new $c_Lcom_kos_wormpad_game_GameListener()
}
function $f_Lcom_kos_wormpad_game_GameState__resume__V($thiz) {
  $thiz.pause$und$1 = false;
  $thiz.listener$und$1.onPause__Z__V($thiz.pause$und$1)
}
/** @constructor */
function $c_Lcom_kos_wormpad_game_WebWormGameDrawer(canvas) {
  this.canvas$1 = null;
  this.ctx$1 = null;
  this.canvasWidth$1 = 0;
  this.canvasHeight$1 = 0;
  this.displayWidth$1 = 0;
  this.displayHeight$1 = 0;
  this.backgroundPath$1 = null;
  this.heroesPath$1 = null;
  this.imgCloud$1 = null;
  this.imgLayers$1 = null;
  this.com$kos$wormpad$game$WormTextures$$texNames$1 = null;
  this.heroTextures$1 = null;
  this.cloudWidth$1 = 0;
  this.cloudHeight$1 = 0;
  this.canvas$1 = canvas;
  $f_Lcom_kos_wormpad_game_WormTextures__$$init$__V(this);
  var array = [new $c_T2("alpha", false)];
  var properties = new $c_sjsr_WrappedVarArgs(array);
  var jsx$1 = canvas.getContext("2d", $m_sjs_js_special_package$().objectLiteral__sci_Seq__sjs_js_Object(properties));
  this.ctx$1 = jsx$1;
  this.canvasWidth$1 = $uI(canvas.width);
  this.canvasHeight$1 = $uI(canvas.height);
  this.displayWidth$1 = 1280;
  this.displayHeight$1 = 960
}
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.constructor = $c_Lcom_kos_wormpad_game_WebWormGameDrawer;
/** @constructor */
function $h_Lcom_kos_wormpad_game_WebWormGameDrawer() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype = $c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype;
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawLayer$1__p1__Lcom_kos_wormpad_game_BackgroundLayer__Lcom_kos_wormpad_geometry_RectF__Lcom_kos_wormpad_heroes_Worm__V = (function(layer, area$1, worm$1) {
  var layer2paradox = ((area$1.left$1 + (worm$1.x$1 * layer.paradoxX$1)) - layer.width$1);
  while ((layer2paradox < area$1.right$1)) {
    this.ctx$1.drawImage(layer.img$1, 0.0, 0.0, layer.width$1, layer.height$1, layer2paradox, (-layer.y$1), layer.width$1, layer.height$1);
    layer2paradox = (layer2paradox + layer.width$1)
  }
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.setupCamera__Lcom_kos_wormpad_heroes_Worm__D__V = (function(worm, scale) {
  var cw = ((this.canvasWidth$1 / 2) | 0);
  var ch = ((this.canvasHeight$1 / 2) | 0);
  this.ctx$1.translate(cw, ch);
  var sc = (this.canvasWidth$1 / this.displayWidth$1);
  this.ctx$1.scale(sc, sc);
  this.ctx$1.scale(scale, scale);
  this.ctx$1.translate((-worm.x$1), worm.y$1)
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawClouds__sci_Seq__V = (function(clouds) {
  if ($uZ(this.imgCloud$1.complete)) {
    clouds.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this) {
      return (function(c$2) {
        var c = $as_Lcom_kos_wormpad_heroes_Cloud(c$2);
        $this.ctx$1.drawImage($this.imgCloud$1, 0.0, 0.0, $this.cloudWidth$1, $this.cloudHeight$1, c.x$1, (-c.y$1), c.width$2, c.height$2)
      })
    })(this)))
  }
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawWormHealth__Lcom_kos_wormpad_heroes_Worm__V = (function(worm) {
  var ch = ((this.canvasHeight$1 / 2) | 0);
  this.ctx$1.beginPath();
  this.ctx$1.fillStyle = "red";
  this.ctx$1.rect(0.0, 0.0, ((worm.health$2 * this.canvasWidth$1) / $m_Lcom_kos_wormpad_heroes_Worm$().MAX$undHEALTH$1), ((ch / 25) | 0));
  this.ctx$1.fill()
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawBackgroundLayers__Lcom_kos_wormpad_heroes_Worm__Lcom_kos_wormpad_geometry_RectF__V = (function(worm, area) {
  $as_sc_IterableOnceOps(this.imgLayers$1.filter__F1__O(new $c_sjsr_AnonFunction1((function($this) {
    return (function(x$1$2) {
      var x$1 = $as_Lcom_kos_wormpad_game_BackgroundLayer(x$1$2);
      return $uZ(x$1.img$1.complete)
    })
  })(this)))).foreach__F1__V(new $c_sjsr_AnonFunction1((function(this$2, area$1, worm$1) {
    return (function(layer$2) {
      var layer = $as_Lcom_kos_wormpad_game_BackgroundLayer(layer$2);
      this$2.drawLayer$1__p1__Lcom_kos_wormpad_game_BackgroundLayer__Lcom_kos_wormpad_geometry_RectF__Lcom_kos_wormpad_heroes_Worm__V(layer, area$1, worm$1)
    })
  })(this, area, worm)))
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawWorm__Lcom_kos_wormpad_heroes_Worm__V = (function(worm) {
  var wormx = worm.x$1;
  var wormy = worm.y$1;
  this.ctx$1.beginPath();
  this.ctx$1.fillStyle = "red";
  this.ctx$1.arc(wormx, (-wormy), worm.wormHeadRadius$2, 0.0, 6.283185307179586, true);
  this.ctx$1.fill();
  worm.tail$2.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this) {
    return (function(wt$2) {
      var wt = $as_Lcom_kos_wormpad_heroes_WormTail(wt$2);
      $this.ctx$1.beginPath();
      $this.ctx$1.fillStyle = "red";
      $this.ctx$1.arc(wt.x$1, (-wt.y$1), wt.radius$1, 0.0, 6.283185307179586, true);
      $this.ctx$1.fill()
    })
  })(this)))
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawBurgers__sci_Set__V = (function(burgers) {
  burgers.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this) {
    return (function(x0$1$2) {
      var x0$1 = $as_Lcom_kos_wormpad_heroes_Hero(x0$1$2);
      if ($is_Lcom_kos_wormpad_heroes_Bomb(x0$1)) {
        var x2 = $as_Lcom_kos_wormpad_heroes_Bomb(x0$1);
        $this.ctx$1.beginPath();
        $this.ctx$1.fillStyle = "darkred";
        $this.ctx$1.arc(x2.x$1, (-x2.y$1), x2.radius$1, 0.0, 6.283185307179586, true);
        $this.ctx$1.fill()
      } else if ($is_Lcom_kos_wormpad_heroes_Burger(x0$1)) {
        var x3 = $as_Lcom_kos_wormpad_heroes_Burger(x0$1);
        $this.ctx$1.beginPath();
        $this.ctx$1.fillStyle = "darkblue";
        $this.ctx$1.arc(x3.x$1, (-x3.y$1), x3.radius$1, 0.0, 6.283185307179586, true);
        $this.ctx$1.fill()
      }
    })
  })(this)))
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.clear__V = (function() {
  this.ctx$1.clearRect(0.0, 0.0, this.canvasWidth$1, this.canvasHeight$1)
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawFrameEdges__Lcom_kos_wormpad_geometry_RectF__D__V = (function(bounds, scale) {
  this.ctx$1.beginPath();
  this.ctx$1.fillStyle = "sandybrown";
  var sw = (2.0 + (this.displayWidth$1 / scale));
  var sh = (2.0 + (this.displayHeight$1 / scale));
  this.ctx$1.rect((bounds.left$1 - sw), $fround((0.0 - bounds.top$1)), (2.0 + sw), (bounds.height__F() + sh));
  this.ctx$1.rect($fround(((-2.0) + bounds.right$1)), $fround((0.0 - bounds.top$1)), sw, (bounds.height__F() + sh));
  this.ctx$1.rect((bounds.left$1 - sw), $fround(((-2.0) - bounds.bottom$1)), (bounds.width__F() + (2.0 * sw)), sh);
  this.ctx$1.fill();
  this.ctx$1.beginPath();
  this.ctx$1.fillStyle = "lightskyblue";
  this.ctx$1.rect((bounds.left$1 - sw), (2.0 + ($fround((0.0 - bounds.top$1)) - sh)), (bounds.width__F() + (2.0 * sw)), sh);
  this.ctx$1.fill()
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawSky__Lcom_kos_wormpad_geometry_RectF__V = (function(bounds) {
  this.ctx$1.beginPath();
  this.ctx$1.fillStyle = "lightskyblue";
  this.ctx$1.rect(bounds.left$1, $fround((0.0 - bounds.top$1)), bounds.width__F(), bounds.height__F());
  this.ctx$1.fill()
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawEnemies__sci_Set__V = (function(enemies) {
  enemies.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this) {
    return (function(e$2) {
      var e = $as_Lcom_kos_wormpad_heroes_Hero(e$2);
      var tex = $as_Lcom_kos_wormpad_game_HeroTexture($this.heroTextures$1.apply__O__O(e.kind__I()));
      if (tex.complete__Z()) {
        $this.ctx$1.drawImage(tex.img$1, 0.0, 0.0, tex.width$1, tex.height$1, (e.x$1 - e.radius$1), (-(e.y$1 + e.radius$1)), (2.0 * e.radius$1), (2.0 * e.radius$1))
      }
    })
  })(this)))
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.drawEarth__Lcom_kos_wormpad_geometry_RectF__V = (function(bounds) {
  this.ctx$1.beginPath();
  this.ctx$1.fillStyle = "sandybrown";
  this.ctx$1.rect(bounds.left$1, $fround((0.0 - bounds.top$1)), bounds.width__F(), bounds.height__F());
  this.ctx$1.fill()
});
var $d_Lcom_kos_wormpad_game_WebWormGameDrawer = new $TypeData().initClass({
  Lcom_kos_wormpad_game_WebWormGameDrawer: 0
}, false, "com.kos.wormpad.game.WebWormGameDrawer", {
  Lcom_kos_wormpad_game_WebWormGameDrawer: 1,
  O: 1,
  Lcom_kos_wormpad_game_WormGameDrawer: 1,
  Lcom_kos_wormpad_game_WormTextures: 1
});
$c_Lcom_kos_wormpad_game_WebWormGameDrawer.prototype.$classData = $d_Lcom_kos_wormpad_game_WebWormGameDrawer;
/** @constructor */
function $c_Lcom_kos_wormpad_heroes_Bomb() {
  this.kind$1 = 0;
  this.subKind$1 = 0;
  this.score$1 = 0;
  this.energy$1 = 0;
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.vx$1 = 0.0;
  this.vy$1 = 0.0;
  this.ax$1 = 0.0;
  this.ay$1 = 0.0;
  this.massa$1 = 0.0;
  this.radius$1 = 0.0;
  this.ediible$1 = false;
  this.destroy$und$1 = false;
  this.accelerationFun$1 = null;
  this.ediible$2 = false;
  this.kind$2 = 0;
  this.kind$3 = 0;
  $c_Lcom_kos_wormpad_heroes_Burger.prototype.init___.call(this);
  this.score$1 = 0;
  this.energy$1 = (-15);
  this.kind$3 = 101
}
$c_Lcom_kos_wormpad_heroes_Bomb.prototype = new $h_Lcom_kos_wormpad_heroes_Burger();
$c_Lcom_kos_wormpad_heroes_Bomb.prototype.constructor = $c_Lcom_kos_wormpad_heroes_Bomb;
/** @constructor */
function $h_Lcom_kos_wormpad_heroes_Bomb() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_heroes_Bomb.prototype = $c_Lcom_kos_wormpad_heroes_Bomb.prototype;
$c_Lcom_kos_wormpad_heroes_Bomb.prototype.kind__I = (function() {
  return this.kind$3
});
function $is_Lcom_kos_wormpad_heroes_Bomb(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_heroes_Bomb)))
}
function $as_Lcom_kos_wormpad_heroes_Bomb(obj) {
  return (($is_Lcom_kos_wormpad_heroes_Bomb(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.heroes.Bomb"))
}
function $isArrayOf_Lcom_kos_wormpad_heroes_Bomb(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_heroes_Bomb)))
}
function $asArrayOf_Lcom_kos_wormpad_heroes_Bomb(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_heroes_Bomb(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.heroes.Bomb;", depth))
}
var $d_Lcom_kos_wormpad_heroes_Bomb = new $TypeData().initClass({
  Lcom_kos_wormpad_heroes_Bomb: 0
}, false, "com.kos.wormpad.heroes.Bomb", {
  Lcom_kos_wormpad_heroes_Bomb: 1,
  Lcom_kos_wormpad_heroes_Burger: 1,
  Lcom_kos_wormpad_heroes_Hero: 1,
  O: 1
});
$c_Lcom_kos_wormpad_heroes_Bomb.prototype.$classData = $d_Lcom_kos_wormpad_heroes_Bomb;
function $f_jl_Boolean__equals__O__Z($thiz, that) {
  return ($thiz === that)
}
function $f_jl_Boolean__toString__T($thiz) {
  var b = $uZ($thiz);
  return ("" + b)
}
function $f_jl_Boolean__hashCode__I($thiz) {
  return ($uZ($thiz) ? 1231 : 1237)
}
var $d_jl_Boolean = new $TypeData().initClass({
  jl_Boolean: 0
}, false, "java.lang.Boolean", {
  jl_Boolean: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
}, (void 0), (void 0), (function(x) {
  return ((typeof x) === "boolean")
}));
function $f_jl_Character__equals__O__Z($thiz, that) {
  if ($isChar(that)) {
    var jsx$1 = $uC($thiz);
    var this$1 = $asChar(that);
    return (jsx$1 === $uC(this$1))
  } else {
    return false
  }
}
function $f_jl_Character__toString__T($thiz) {
  var c = $uC($thiz);
  return $as_T(String.fromCharCode(c))
}
function $f_jl_Character__hashCode__I($thiz) {
  return $uC($thiz)
}
function $isArrayOf_jl_Character(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.jl_Character)))
}
function $asArrayOf_jl_Character(obj, depth) {
  return (($isArrayOf_jl_Character(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.Character;", depth))
}
var $d_jl_Character = new $TypeData().initClass({
  jl_Character: 0
}, false, "java.lang.Character", {
  jl_Character: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
}, (void 0), (void 0), (function(x) {
  return $isChar(x)
}));
/** @constructor */
function $c_jl_Double$() {
  this.doubleStrPat$1 = null;
  this.doubleStrHexPat$1 = null;
  this.bitmap$0$1 = 0
}
$c_jl_Double$.prototype = new $h_O();
$c_jl_Double$.prototype.constructor = $c_jl_Double$;
/** @constructor */
function $h_jl_Double$() {
  /*<skip>*/
}
$h_jl_Double$.prototype = $c_jl_Double$.prototype;
$c_jl_Double$.prototype.compare__D__D__I = (function(a, b) {
  if ((a !== a)) {
    return ((b !== b) ? 0 : 1)
  } else if ((b !== b)) {
    return (-1)
  } else if ((a === b)) {
    if ((a === 0.0)) {
      var ainf = (1.0 / a);
      return ((ainf === (1.0 / b)) ? 0 : ((ainf < 0.0) ? (-1) : 1))
    } else {
      return 0
    }
  } else {
    return ((a < b) ? (-1) : 1)
  }
});
var $d_jl_Double$ = new $TypeData().initClass({
  jl_Double$: 0
}, false, "java.lang.Double$", {
  jl_Double$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_jl_Double$.prototype.$classData = $d_jl_Double$;
var $n_jl_Double$ = (void 0);
function $m_jl_Double$() {
  if ((!$n_jl_Double$)) {
    $n_jl_Double$ = new $c_jl_Double$()
  };
  return $n_jl_Double$
}
/** @constructor */
function $c_jl_Error() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_Error.prototype = new $h_jl_Throwable();
$c_jl_Error.prototype.constructor = $c_jl_Error;
/** @constructor */
function $h_jl_Error() {
  /*<skip>*/
}
$h_jl_Error.prototype = $c_jl_Error.prototype;
/** @constructor */
function $c_jl_Exception() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_Exception.prototype = new $h_jl_Throwable();
$c_jl_Exception.prototype.constructor = $c_jl_Exception;
/** @constructor */
function $h_jl_Exception() {
  /*<skip>*/
}
$h_jl_Exception.prototype = $c_jl_Exception.prototype;
$c_jl_Exception.prototype.init___T = (function(s) {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, s, null, true, true);
  return this
});
var $d_jl_Exception = new $TypeData().initClass({
  jl_Exception: 0
}, false, "java.lang.Exception", {
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_Exception.prototype.$classData = $d_jl_Exception;
/** @constructor */
function $c_jl_Integer$() {
  /*<skip>*/
}
$c_jl_Integer$.prototype = new $h_O();
$c_jl_Integer$.prototype.constructor = $c_jl_Integer$;
/** @constructor */
function $h_jl_Integer$() {
  /*<skip>*/
}
$h_jl_Integer$.prototype = $c_jl_Integer$.prototype;
$c_jl_Integer$.prototype.bitCount__I__I = (function(i) {
  var t1 = ((i - (1431655765 & (i >> 1))) | 0);
  var t2 = (((858993459 & t1) + (858993459 & (t1 >> 2))) | 0);
  return ($imul(16843009, (252645135 & ((t2 + (t2 >> 4)) | 0))) >> 24)
});
$c_jl_Integer$.prototype.reverseBytes__I__I = (function(i) {
  var byte3 = ((i >>> 24) | 0);
  var byte2 = (65280 & ((i >>> 8) | 0));
  var byte1 = (16711680 & (i << 8));
  var byte0 = (i << 24);
  return (((byte0 | byte1) | byte2) | byte3)
});
var $d_jl_Integer$ = new $TypeData().initClass({
  jl_Integer$: 0
}, false, "java.lang.Integer$", {
  jl_Integer$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_jl_Integer$.prototype.$classData = $d_jl_Integer$;
var $n_jl_Integer$ = (void 0);
function $m_jl_Integer$() {
  if ((!$n_jl_Integer$)) {
    $n_jl_Integer$ = new $c_jl_Integer$()
  };
  return $n_jl_Integer$
}
/** @constructor */
function $c_jl_String$() {
  this.CASE$undINSENSITIVE$undORDER$1 = null;
  this.bitmap$0$1 = false
}
$c_jl_String$.prototype = new $h_O();
$c_jl_String$.prototype.constructor = $c_jl_String$;
/** @constructor */
function $h_jl_String$() {
  /*<skip>*/
}
$h_jl_String$.prototype = $c_jl_String$.prototype;
$c_jl_String$.prototype.$new__AC__I__I__T = (function(value, offset, count) {
  var end = ((offset + count) | 0);
  if ((((offset < 0) || (end < offset)) || (end > value.u.length))) {
    throw new $c_jl_StringIndexOutOfBoundsException()
  };
  var result = "";
  var i = offset;
  while ((i !== end)) {
    var jsx$1 = result;
    var this$1 = value.get(i);
    result = (("" + jsx$1) + $as_T(String.fromCharCode(this$1)));
    i = ((1 + i) | 0)
  };
  return result
});
var $d_jl_String$ = new $TypeData().initClass({
  jl_String$: 0
}, false, "java.lang.String$", {
  jl_String$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_jl_String$.prototype.$classData = $d_jl_String$;
var $n_jl_String$ = (void 0);
function $m_jl_String$() {
  if ((!$n_jl_String$)) {
    $n_jl_String$ = new $c_jl_String$()
  };
  return $n_jl_String$
}
/** @constructor */
function $c_ju_Random$() {
  /*<skip>*/
}
$c_ju_Random$.prototype = new $h_O();
$c_ju_Random$.prototype.constructor = $c_ju_Random$;
/** @constructor */
function $h_ju_Random$() {
  /*<skip>*/
}
$h_ju_Random$.prototype = $c_ju_Random$.prototype;
$c_ju_Random$.prototype.java$util$Random$$randomSeed__J = (function() {
  var value = this.randomInt__p1__I();
  var value$1 = this.randomInt__p1__I();
  return new $c_sjsr_RuntimeLong(value$1, value)
});
$c_ju_Random$.prototype.randomInt__p1__I = (function() {
  var a = (4.294967296E9 * $uD(Math.random()));
  return $doubleToInt(((-2.147483648E9) + $uD(Math.floor(a))))
});
var $d_ju_Random$ = new $TypeData().initClass({
  ju_Random$: 0
}, false, "java.util.Random$", {
  ju_Random$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_ju_Random$.prototype.$classData = $d_ju_Random$;
var $n_ju_Random$ = (void 0);
function $m_ju_Random$() {
  if ((!$n_ju_Random$)) {
    $n_ju_Random$ = new $c_ju_Random$()
  };
  return $n_ju_Random$
}
/** @constructor */
function $c_s_Array$() {
  /*<skip>*/
}
$c_s_Array$.prototype = new $h_O();
$c_s_Array$.prototype.constructor = $c_s_Array$;
/** @constructor */
function $h_s_Array$() {
  /*<skip>*/
}
$h_s_Array$.prototype = $c_s_Array$.prototype;
$c_s_Array$.prototype.apply__I__sci_Seq__AI = (function(x, xs) {
  var array = $newArrayObject($d_I.getArrayOf(), [((1 + xs.length__I()) | 0)]);
  array.set(0, x);
  var elem$1 = 0;
  elem$1 = 1;
  var this$2 = xs.iterator__sc_Iterator();
  while (this$2.hasNext__Z()) {
    var arg1 = this$2.next__O();
    var x$2 = $uI(arg1);
    array.set(elem$1, x$2);
    elem$1 = ((1 + elem$1) | 0)
  };
  return array
});
$c_s_Array$.prototype.copy__O__I__O__I__I__V = (function(src, srcPos, dest, destPos, length) {
  var srcClass = $objectGetClass(src);
  if ((srcClass.isArray__Z() && $objectGetClass(dest).isAssignableFrom__jl_Class__Z(srcClass))) {
    $systemArraycopy(src, srcPos, dest, destPos, length)
  } else {
    this.slowcopy__p1__O__I__O__I__I__V(src, srcPos, dest, destPos, length)
  }
});
$c_s_Array$.prototype.slowcopy__p1__O__I__O__I__I__V = (function(src, srcPos, dest, destPos, length) {
  var i = srcPos;
  var j = destPos;
  var srcUntil = ((srcPos + length) | 0);
  while ((i < srcUntil)) {
    $m_sr_ScalaRunTime$().array$undupdate__O__I__O__V(dest, j, $m_sr_ScalaRunTime$().array$undapply__O__I__O(src, i));
    i = ((1 + i) | 0);
    j = ((1 + j) | 0)
  }
});
var $d_s_Array$ = new $TypeData().initClass({
  s_Array$: 0
}, false, "scala.Array$", {
  s_Array$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_Array$.prototype.$classData = $d_s_Array$;
var $n_s_Array$ = (void 0);
function $m_s_Array$() {
  if ((!$n_s_Array$)) {
    $n_s_Array$ = new $c_s_Array$()
  };
  return $n_s_Array$
}
/** @constructor */
function $c_s_Predef$() {
  this.Map$3 = null;
  this.Set$3 = null;
  this.$$minus$greater$3 = null;
  this.Manifest$3 = null;
  this.NoManifest$3 = null;
  $n_s_Predef$ = this;
  $m_s_package$();
  $m_sci_List$();
  this.Map$3 = $m_sci_Map$();
  this.Set$3 = $m_sci_Set$();
  this.$$minus$greater$3 = $m_s_Tuple2$();
  this.Manifest$3 = $m_s_reflect_package$().Manifest$1;
  this.NoManifest$3 = $m_s_reflect_NoManifest$()
}
$c_s_Predef$.prototype = new $h_s_LowPriorityImplicits();
$c_s_Predef$.prototype.constructor = $c_s_Predef$;
/** @constructor */
function $h_s_Predef$() {
  /*<skip>*/
}
$h_s_Predef$.prototype = $c_s_Predef$.prototype;
$c_s_Predef$.prototype.assert__Z__V = (function(assertion) {
  if ((!assertion)) {
    throw new $c_jl_AssertionError("assertion failed")
  }
});
$c_s_Predef$.prototype.require__Z__V = (function(requirement) {
  if ((!requirement)) {
    throw new $c_jl_IllegalArgumentException().init___T("requirement failed")
  }
});
var $d_s_Predef$ = new $TypeData().initClass({
  s_Predef$: 0
}, false, "scala.Predef$", {
  s_Predef$: 1,
  s_LowPriorityImplicits: 1,
  s_LowPriorityImplicits2: 1,
  O: 1
});
$c_s_Predef$.prototype.$classData = $d_s_Predef$;
var $n_s_Predef$ = (void 0);
function $m_s_Predef$() {
  if ((!$n_s_Predef$)) {
    $n_s_Predef$ = new $c_s_Predef$()
  };
  return $n_s_Predef$
}
/** @constructor */
function $c_s_Predef$$eq$colon$eq$() {
  this.singleton$1 = null;
  $n_s_Predef$$eq$colon$eq$ = this;
  this.singleton$1 = new $c_s_Predef$$eq$colon$eq$$anon$1()
}
$c_s_Predef$$eq$colon$eq$.prototype = new $h_O();
$c_s_Predef$$eq$colon$eq$.prototype.constructor = $c_s_Predef$$eq$colon$eq$;
/** @constructor */
function $h_s_Predef$$eq$colon$eq$() {
  /*<skip>*/
}
$h_s_Predef$$eq$colon$eq$.prototype = $c_s_Predef$$eq$colon$eq$.prototype;
var $d_s_Predef$$eq$colon$eq$ = new $TypeData().initClass({
  s_Predef$$eq$colon$eq$: 0
}, false, "scala.Predef$$eq$colon$eq$", {
  s_Predef$$eq$colon$eq$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_Predef$$eq$colon$eq$.prototype.$classData = $d_s_Predef$$eq$colon$eq$;
var $n_s_Predef$$eq$colon$eq$ = (void 0);
function $m_s_Predef$$eq$colon$eq$() {
  if ((!$n_s_Predef$$eq$colon$eq$)) {
    $n_s_Predef$$eq$colon$eq$ = new $c_s_Predef$$eq$colon$eq$()
  };
  return $n_s_Predef$$eq$colon$eq$
}
/** @constructor */
function $c_s_Tuple2$() {
  /*<skip>*/
}
$c_s_Tuple2$.prototype = new $h_O();
$c_s_Tuple2$.prototype.constructor = $c_s_Tuple2$;
/** @constructor */
function $h_s_Tuple2$() {
  /*<skip>*/
}
$h_s_Tuple2$.prototype = $c_s_Tuple2$.prototype;
$c_s_Tuple2$.prototype.toString__T = (function() {
  return "Tuple2"
});
var $d_s_Tuple2$ = new $TypeData().initClass({
  s_Tuple2$: 0
}, false, "scala.Tuple2$", {
  s_Tuple2$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_Tuple2$.prototype.$classData = $d_s_Tuple2$;
var $n_s_Tuple2$ = (void 0);
function $m_s_Tuple2$() {
  if ((!$n_s_Tuple2$)) {
    $n_s_Tuple2$ = new $c_s_Tuple2$()
  };
  return $n_s_Tuple2$
}
/** @constructor */
function $c_s_math_Fractional$() {
  /*<skip>*/
}
$c_s_math_Fractional$.prototype = new $h_O();
$c_s_math_Fractional$.prototype.constructor = $c_s_math_Fractional$;
/** @constructor */
function $h_s_math_Fractional$() {
  /*<skip>*/
}
$h_s_math_Fractional$.prototype = $c_s_math_Fractional$.prototype;
var $d_s_math_Fractional$ = new $TypeData().initClass({
  s_math_Fractional$: 0
}, false, "scala.math.Fractional$", {
  s_math_Fractional$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_math_Fractional$.prototype.$classData = $d_s_math_Fractional$;
var $n_s_math_Fractional$ = (void 0);
function $m_s_math_Fractional$() {
  if ((!$n_s_math_Fractional$)) {
    $n_s_math_Fractional$ = new $c_s_math_Fractional$()
  };
  return $n_s_math_Fractional$
}
/** @constructor */
function $c_s_math_Integral$() {
  /*<skip>*/
}
$c_s_math_Integral$.prototype = new $h_O();
$c_s_math_Integral$.prototype.constructor = $c_s_math_Integral$;
/** @constructor */
function $h_s_math_Integral$() {
  /*<skip>*/
}
$h_s_math_Integral$.prototype = $c_s_math_Integral$.prototype;
var $d_s_math_Integral$ = new $TypeData().initClass({
  s_math_Integral$: 0
}, false, "scala.math.Integral$", {
  s_math_Integral$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_math_Integral$.prototype.$classData = $d_s_math_Integral$;
var $n_s_math_Integral$ = (void 0);
function $m_s_math_Integral$() {
  if ((!$n_s_math_Integral$)) {
    $n_s_math_Integral$ = new $c_s_math_Integral$()
  };
  return $n_s_math_Integral$
}
/** @constructor */
function $c_s_math_Numeric$() {
  /*<skip>*/
}
$c_s_math_Numeric$.prototype = new $h_O();
$c_s_math_Numeric$.prototype.constructor = $c_s_math_Numeric$;
/** @constructor */
function $h_s_math_Numeric$() {
  /*<skip>*/
}
$h_s_math_Numeric$.prototype = $c_s_math_Numeric$.prototype;
var $d_s_math_Numeric$ = new $TypeData().initClass({
  s_math_Numeric$: 0
}, false, "scala.math.Numeric$", {
  s_math_Numeric$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_math_Numeric$.prototype.$classData = $d_s_math_Numeric$;
var $n_s_math_Numeric$ = (void 0);
function $m_s_math_Numeric$() {
  if ((!$n_s_math_Numeric$)) {
    $n_s_math_Numeric$ = new $c_s_math_Numeric$()
  };
  return $n_s_math_Numeric$
}
function $is_s_math_ScalaNumber(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.s_math_ScalaNumber)))
}
function $as_s_math_ScalaNumber(obj) {
  return (($is_s_math_ScalaNumber(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.math.ScalaNumber"))
}
function $isArrayOf_s_math_ScalaNumber(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.s_math_ScalaNumber)))
}
function $asArrayOf_s_math_ScalaNumber(obj, depth) {
  return (($isArrayOf_s_math_ScalaNumber(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.math.ScalaNumber;", depth))
}
/** @constructor */
function $c_s_reflect_ClassTag$() {
  /*<skip>*/
}
$c_s_reflect_ClassTag$.prototype = new $h_O();
$c_s_reflect_ClassTag$.prototype.constructor = $c_s_reflect_ClassTag$;
/** @constructor */
function $h_s_reflect_ClassTag$() {
  /*<skip>*/
}
$h_s_reflect_ClassTag$.prototype = $c_s_reflect_ClassTag$.prototype;
$c_s_reflect_ClassTag$.prototype.apply__jl_Class__s_reflect_ClassTag = (function(runtimeClass1) {
  return ((runtimeClass1 === $d_B.getClassOf()) ? $m_s_reflect_ManifestFactory$ByteManifest$() : ((runtimeClass1 === $d_S.getClassOf()) ? $m_s_reflect_ManifestFactory$ShortManifest$() : ((runtimeClass1 === $d_C.getClassOf()) ? $m_s_reflect_ManifestFactory$CharManifest$() : ((runtimeClass1 === $d_I.getClassOf()) ? $m_s_reflect_ManifestFactory$IntManifest$() : ((runtimeClass1 === $d_J.getClassOf()) ? $m_s_reflect_ManifestFactory$LongManifest$() : ((runtimeClass1 === $d_F.getClassOf()) ? $m_s_reflect_ManifestFactory$FloatManifest$() : ((runtimeClass1 === $d_D.getClassOf()) ? $m_s_reflect_ManifestFactory$DoubleManifest$() : ((runtimeClass1 === $d_Z.getClassOf()) ? $m_s_reflect_ManifestFactory$BooleanManifest$() : ((runtimeClass1 === $d_V.getClassOf()) ? $m_s_reflect_ManifestFactory$UnitManifest$() : ((runtimeClass1 === $d_O.getClassOf()) ? $m_s_reflect_ManifestFactory$ObjectManifest$() : ((runtimeClass1 === $d_sr_Nothing$.getClassOf()) ? $m_s_reflect_ManifestFactory$NothingManifest$() : ((runtimeClass1 === $d_sr_Null$.getClassOf()) ? $m_s_reflect_ManifestFactory$NullManifest$() : new $c_s_reflect_ClassTag$GenericClassTag(runtimeClass1)))))))))))))
});
var $d_s_reflect_ClassTag$ = new $TypeData().initClass({
  s_reflect_ClassTag$: 0
}, false, "scala.reflect.ClassTag$", {
  s_reflect_ClassTag$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_reflect_ClassTag$.prototype.$classData = $d_s_reflect_ClassTag$;
var $n_s_reflect_ClassTag$ = (void 0);
function $m_s_reflect_ClassTag$() {
  if ((!$n_s_reflect_ClassTag$)) {
    $n_s_reflect_ClassTag$ = new $c_s_reflect_ClassTag$()
  };
  return $n_s_reflect_ClassTag$
}
/** @constructor */
function $c_s_util_Either$() {
  /*<skip>*/
}
$c_s_util_Either$.prototype = new $h_O();
$c_s_util_Either$.prototype.constructor = $c_s_util_Either$;
/** @constructor */
function $h_s_util_Either$() {
  /*<skip>*/
}
$h_s_util_Either$.prototype = $c_s_util_Either$.prototype;
var $d_s_util_Either$ = new $TypeData().initClass({
  s_util_Either$: 0
}, false, "scala.util.Either$", {
  s_util_Either$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_util_Either$.prototype.$classData = $d_s_util_Either$;
var $n_s_util_Either$ = (void 0);
function $m_s_util_Either$() {
  if ((!$n_s_util_Either$)) {
    $n_s_util_Either$ = new $c_s_util_Either$()
  };
  return $n_s_util_Either$
}
/** @constructor */
function $c_s_util_Left$() {
  /*<skip>*/
}
$c_s_util_Left$.prototype = new $h_O();
$c_s_util_Left$.prototype.constructor = $c_s_util_Left$;
/** @constructor */
function $h_s_util_Left$() {
  /*<skip>*/
}
$h_s_util_Left$.prototype = $c_s_util_Left$.prototype;
$c_s_util_Left$.prototype.toString__T = (function() {
  return "Left"
});
var $d_s_util_Left$ = new $TypeData().initClass({
  s_util_Left$: 0
}, false, "scala.util.Left$", {
  s_util_Left$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_util_Left$.prototype.$classData = $d_s_util_Left$;
var $n_s_util_Left$ = (void 0);
function $m_s_util_Left$() {
  if ((!$n_s_util_Left$)) {
    $n_s_util_Left$ = new $c_s_util_Left$()
  };
  return $n_s_util_Left$
}
/** @constructor */
function $c_s_util_Random() {
  this.self$1 = null
}
$c_s_util_Random.prototype = new $h_O();
$c_s_util_Random.prototype.constructor = $c_s_util_Random;
/** @constructor */
function $h_s_util_Random() {
  /*<skip>*/
}
$h_s_util_Random.prototype = $c_s_util_Random.prototype;
$c_s_util_Random.prototype.init___ = (function() {
  $c_s_util_Random.prototype.init___ju_Random.call(this, new $c_ju_Random().init___());
  return this
});
$c_s_util_Random.prototype.init___ju_Random = (function(self) {
  this.self$1 = self;
  return this
});
var $d_s_util_Random = new $TypeData().initClass({
  s_util_Random: 0
}, false, "scala.util.Random", {
  s_util_Random: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_util_Random.prototype.$classData = $d_s_util_Random;
/** @constructor */
function $c_s_util_Right$() {
  /*<skip>*/
}
$c_s_util_Right$.prototype = new $h_O();
$c_s_util_Right$.prototype.constructor = $c_s_util_Right$;
/** @constructor */
function $h_s_util_Right$() {
  /*<skip>*/
}
$h_s_util_Right$.prototype = $c_s_util_Right$.prototype;
$c_s_util_Right$.prototype.toString__T = (function() {
  return "Right"
});
var $d_s_util_Right$ = new $TypeData().initClass({
  s_util_Right$: 0
}, false, "scala.util.Right$", {
  s_util_Right$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_util_Right$.prototype.$classData = $d_s_util_Right$;
var $n_s_util_Right$ = (void 0);
function $m_s_util_Right$() {
  if ((!$n_s_util_Right$)) {
    $n_s_util_Right$ = new $c_s_util_Right$()
  };
  return $n_s_util_Right$
}
/** @constructor */
function $c_sc_MapOps$WithFilter(self, p) {
  this.self$2 = null;
  this.p$2 = null;
  this.self$3 = null;
  this.p$3 = null;
  this.self$3 = self;
  this.p$3 = p;
  $c_sc_IterableOps$WithFilter.prototype.init___sc_IterableOps__F1.call(this, self, p)
}
$c_sc_MapOps$WithFilter.prototype = new $h_sc_IterableOps$WithFilter();
$c_sc_MapOps$WithFilter.prototype.constructor = $c_sc_MapOps$WithFilter;
/** @constructor */
function $h_sc_MapOps$WithFilter() {
  /*<skip>*/
}
$h_sc_MapOps$WithFilter.prototype = $c_sc_MapOps$WithFilter.prototype;
var $d_sc_MapOps$WithFilter = new $TypeData().initClass({
  sc_MapOps$WithFilter: 0
}, false, "scala.collection.MapOps$WithFilter", {
  sc_MapOps$WithFilter: 1,
  sc_IterableOps$WithFilter: 1,
  sc_WithFilter: 1,
  O: 1
});
$c_sc_MapOps$WithFilter.prototype.$classData = $d_sc_MapOps$WithFilter;
function $f_sc_SeqOps__isEmpty__Z($thiz) {
  return ($thiz.lengthCompare__I__I(0) === 0)
}
function $f_sc_SeqOps__sameElements__sc_IterableOnce__Z($thiz, that) {
  var thisKnownSize = $thiz.knownSize__I();
  if ((thisKnownSize !== (-1))) {
    var thatKnownSize = that.knownSize__I();
    var knownSizeDifference = ((thatKnownSize !== (-1)) && (thisKnownSize !== thatKnownSize))
  } else {
    var knownSizeDifference = false
  };
  if ((!knownSizeDifference)) {
    var this$1 = $thiz.iterator__sc_Iterator();
    return $f_sc_Iterator__sameElements__sc_IterableOnce__Z(this$1, that)
  } else {
    return false
  }
}
function $f_sc_SeqOps__sorted__s_math_Ordering__O($thiz, ord) {
  var len = $thiz.length__I();
  var b = $thiz.newSpecificBuilder__scm_Builder();
  if ((len === 1)) {
    b.addAll__sc_IterableOnce__scm_Growable($thiz)
  } else if ((len > 1)) {
    b.sizeHint__I__V(len);
    var arr = $newArrayObject($d_O.getArrayOf(), [len]);
    var i = new $c_sr_IntRef(0);
    $thiz.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this, arr$1, i$1) {
      return (function(x$2) {
        arr$1.set(i$1.elem$1, x$2);
        i$1.elem$1 = ((1 + i$1.elem$1) | 0)
      })
    })($thiz, arr, i)));
    $m_ju_Arrays$().sort__AO__ju_Comparator__V(arr, ord);
    i.elem$1 = 0;
    while ((i.elem$1 < arr.u.length)) {
      var elem = arr.get(i.elem$1);
      b.addOne__O__scm_Growable(elem);
      i.elem$1 = ((1 + i.elem$1) | 0)
    }
  };
  return b.result__O()
}
function $f_sc_SeqOps__contains__O__Z($thiz, elem) {
  return $thiz.exists__F1__Z(new $c_sjsr_AnonFunction1((function($this, elem$1) {
    return (function(x$3$2) {
      return $m_sr_BoxesRunTime$().equals__O__O__Z(x$3$2, elem$1)
    })
  })($thiz, elem)))
}
function $f_sc_SeqOps__sortBy__F1__s_math_Ordering__O($thiz, f, ord) {
  var ord$1 = new $c_s_math_Ordering$$anon$2(ord, f);
  return $f_sc_SeqOps__sorted__s_math_Ordering__O($thiz, ord$1)
}
function $is_sc_SeqOps(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_SeqOps)))
}
function $as_sc_SeqOps(obj) {
  return (($is_sc_SeqOps(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.SeqOps"))
}
function $isArrayOf_sc_SeqOps(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_SeqOps)))
}
function $asArrayOf_sc_SeqOps(obj, depth) {
  return (($isArrayOf_sc_SeqOps(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.SeqOps;", depth))
}
function $f_sc_StrictOptimizedIterableOps__flatMap__F1__O($thiz, f) {
  var b = $thiz.iterableFactory__sc_IterableFactory().newBuilder__scm_Builder();
  var it = $thiz.iterator__sc_Iterator();
  while (it.hasNext__Z()) {
    var xs = $as_sc_IterableOnce(f.apply__O__O(it.next__O()));
    b.addAll__sc_IterableOnce__scm_Growable(xs)
  };
  return b.result__O()
}
function $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O($thiz, pred, isFlipped) {
  var b = $thiz.newSpecificBuilder__scm_Builder();
  var it = $thiz.iterator__sc_Iterator();
  while (it.hasNext__Z()) {
    var elem = it.next__O();
    if (($uZ(pred.apply__O__O(elem)) !== isFlipped)) {
      b.addOne__O__scm_Growable(elem)
    }
  };
  return b.result__O()
}
function $f_sc_StrictOptimizedIterableOps__map__F1__O($thiz, f) {
  var b = $thiz.iterableFactory__sc_IterableFactory().newBuilder__scm_Builder();
  var it = $thiz.iterator__sc_Iterator();
  while (it.hasNext__Z()) {
    var elem = f.apply__O__O(it.next__O());
    b.addOne__O__scm_Growable(elem)
  };
  return b.result__O()
}
/** @constructor */
function $c_sci_$colon$colon$() {
  /*<skip>*/
}
$c_sci_$colon$colon$.prototype = new $h_O();
$c_sci_$colon$colon$.prototype.constructor = $c_sci_$colon$colon$;
/** @constructor */
function $h_sci_$colon$colon$() {
  /*<skip>*/
}
$h_sci_$colon$colon$.prototype = $c_sci_$colon$colon$.prototype;
$c_sci_$colon$colon$.prototype.toString__T = (function() {
  return "::"
});
var $d_sci_$colon$colon$ = new $TypeData().initClass({
  sci_$colon$colon$: 0
}, false, "scala.collection.immutable.$colon$colon$", {
  sci_$colon$colon$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_$colon$colon$.prototype.$classData = $d_sci_$colon$colon$;
var $n_sci_$colon$colon$ = (void 0);
function $m_sci_$colon$colon$() {
  if ((!$n_sci_$colon$colon$)) {
    $n_sci_$colon$colon$ = new $c_sci_$colon$colon$()
  };
  return $n_sci_$colon$colon$
}
/** @constructor */
function $c_sci_BitmapIndexedMapNode(dataMap, nodeMap, content, originalHashes, size) {
  this.dataMap$3 = 0;
  this.nodeMap$3 = 0;
  this.content$3 = null;
  this.originalHashes$3 = null;
  this.size$3 = 0;
  this.dataMap$3 = dataMap;
  this.nodeMap$3 = nodeMap;
  this.content$3 = content;
  this.originalHashes$3 = originalHashes;
  this.size$3 = size
}
$c_sci_BitmapIndexedMapNode.prototype = new $h_sci_MapNode();
$c_sci_BitmapIndexedMapNode.prototype.constructor = $c_sci_BitmapIndexedMapNode;
/** @constructor */
function $h_sci_BitmapIndexedMapNode() {
  /*<skip>*/
}
$h_sci_BitmapIndexedMapNode.prototype = $c_sci_BitmapIndexedMapNode.prototype;
$c_sci_BitmapIndexedMapNode.prototype.getHash__I__I = (function(index) {
  return this.originalHashes$3.get(index)
});
$c_sci_BitmapIndexedMapNode.prototype.getPayload__I__T2 = (function(index) {
  return new $c_T2(this.content$3.get((index << 1)), this.content$3.get(((1 + (index << 1)) | 0)))
});
$c_sci_BitmapIndexedMapNode.prototype.nodeIndex__I__I = (function(bitpos) {
  return $m_jl_Integer$().bitCount__I__I((this.nodeMap$3 & (((-1) + bitpos) | 0)))
});
$c_sci_BitmapIndexedMapNode.prototype.copyAndMigrateFromNodeToInline__I__I__I__sci_MapNode__sci_MapNode__sci_BitmapIndexedMapNode = (function(bitpos, originalHash, keyHash, oldNode, node) {
  var idxOld = (((((-1) + this.content$3.u.length) | 0) - this.nodeIndex__I__I(bitpos)) | 0);
  var dataIxNew = this.dataIndex__I__I(bitpos);
  var idxNew = (dataIxNew << 1);
  var key = node.getKey__I__O(0);
  var value = node.getValue__I__O(0);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [((1 + src.u.length) | 0)]);
  $systemArraycopy(src, 0, dst, 0, idxNew);
  dst.set(idxNew, key);
  dst.set(((1 + idxNew) | 0), value);
  $systemArraycopy(src, idxNew, dst, ((2 + idxNew) | 0), ((idxOld - idxNew) | 0));
  $systemArraycopy(src, ((1 + idxOld) | 0), dst, ((2 + idxOld) | 0), (((-1) + ((src.u.length - idxOld) | 0)) | 0));
  var hash = node.getHash__I__I(0);
  var dstHashes = this.insertElement__AI__I__I__AI(this.originalHashes$3, dataIxNew, hash);
  return new $c_sci_BitmapIndexedMapNode((this.dataMap$3 | bitpos), (this.nodeMap$3 ^ bitpos), dst, dstHashes, ((1 + ((this.size$3 - oldNode.size__I()) | 0)) | 0))
});
$c_sci_BitmapIndexedMapNode.prototype.get__O__I__I__I__s_Option = (function(key, originalHash, keyHash, shift) {
  var mask = $m_sci_Node$().maskFrom__I__I__I(keyHash, shift);
  var bitpos = $m_sci_Node$().bitposFrom__I__I(mask);
  if (((this.dataMap$3 & bitpos) !== 0)) {
    var index = $m_sci_Node$().indexFrom__I__I__I__I(this.dataMap$3, mask, bitpos);
    var key0 = this.getKey__I__O(index);
    return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, key0) ? new $c_s_Some(this.getValue__I__O(index)) : $m_s_None$())
  };
  if (((this.nodeMap$3 & bitpos) !== 0)) {
    var index$2 = $m_sci_Node$().indexFrom__I__I__I__I(this.nodeMap$3, mask, bitpos);
    return this.getNode__I__sci_MapNode(index$2).get__O__I__I__I__s_Option(key, originalHash, keyHash, ((5 + shift) | 0))
  };
  return $m_s_None$()
});
$c_sci_BitmapIndexedMapNode.prototype.equals__O__Z = (function(that) {
  if ($is_sci_BitmapIndexedMapNode(that)) {
    var x2 = $as_sci_BitmapIndexedMapNode(that);
    if ((this === x2)) {
      return true
    } else if ((((this.nodeMap$3 === x2.nodeMap$3) && (this.dataMap$3 === x2.dataMap$3)) && $m_ju_Arrays$().equals__AI__AI__Z(this.originalHashes$3, x2.originalHashes$3))) {
      var a1 = this.content$3;
      var a2 = x2.content$3;
      var length = this.content$3.u.length;
      if ((a1 === a2)) {
        return true
      } else {
        var isEqual = true;
        var i = 0;
        while ((isEqual && (i < length))) {
          isEqual = $m_sr_BoxesRunTime$().equals__O__O__Z(a1.get(i), a2.get(i));
          i = ((1 + i) | 0)
        };
        return isEqual
      }
    } else {
      return false
    }
  } else {
    return false
  }
});
$c_sci_BitmapIndexedMapNode.prototype.sizePredicate__I = (function() {
  if (($m_jl_Integer$().bitCount__I__I(this.nodeMap$3) === 0)) {
    var x1 = $m_jl_Integer$().bitCount__I__I(this.dataMap$3);
    switch (x1) {
      case 0: {
        return 0;
        break
      }
      case 1: {
        return 1;
        break
      }
      default: {
        return 2
      }
    }
  } else {
    return 2
  }
});
$c_sci_BitmapIndexedMapNode.prototype.copyAndRemoveValue__I__sci_BitmapIndexedMapNode = (function(bitpos) {
  var dataIx = this.dataIndex__I__I(bitpos);
  var idx = (dataIx << 1);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [(((-2) + src.u.length) | 0)]);
  $systemArraycopy(src, 0, dst, 0, idx);
  $systemArraycopy(src, ((2 + idx) | 0), dst, idx, (((-2) + ((src.u.length - idx) | 0)) | 0));
  var dstHashes = this.removeElement__AI__I__AI(this.originalHashes$3, dataIx);
  return new $c_sci_BitmapIndexedMapNode((this.dataMap$3 ^ bitpos), this.nodeMap$3, dst, dstHashes, (((-1) + this.size$3) | 0))
});
$c_sci_BitmapIndexedMapNode.prototype.copyAndMigrateFromInlineToNode__I__sci_MapNode__sci_BitmapIndexedMapNode = (function(bitpos, node) {
  var dataIx = this.dataIndex__I__I(bitpos);
  var idxOld = (dataIx << 1);
  var idxNew = (((((-2) + this.content$3.u.length) | 0) - this.nodeIndex__I__I(bitpos)) | 0);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [(((-1) + src.u.length) | 0)]);
  $systemArraycopy(src, 0, dst, 0, idxOld);
  $systemArraycopy(src, ((2 + idxOld) | 0), dst, idxOld, ((idxNew - idxOld) | 0));
  dst.set(idxNew, node);
  $systemArraycopy(src, ((2 + idxNew) | 0), dst, ((1 + idxNew) | 0), (((-2) + ((src.u.length - idxNew) | 0)) | 0));
  var dstHashes = this.removeElement__AI__I__AI(this.originalHashes$3, dataIx);
  return new $c_sci_BitmapIndexedMapNode((this.dataMap$3 ^ bitpos), (this.nodeMap$3 | bitpos), dst, dstHashes, (((((-1) + this.size$3) | 0) + node.size__I()) | 0))
});
$c_sci_BitmapIndexedMapNode.prototype.hasNodes__Z = (function() {
  return (this.nodeMap$3 !== 0)
});
$c_sci_BitmapIndexedMapNode.prototype.foreach__F1__V = (function(f) {
  var i = 0;
  while ((i < $m_jl_Integer$().bitCount__I__I(this.dataMap$3))) {
    f.apply__O__O(this.getPayload__I__T2(i));
    i = ((1 + i) | 0)
  };
  var j = 0;
  while ((j < $m_jl_Integer$().bitCount__I__I(this.nodeMap$3))) {
    this.getNode__I__sci_MapNode(j).foreach__F1__V(f);
    j = ((1 + j) | 0)
  }
});
$c_sci_BitmapIndexedMapNode.prototype.getOrElse__O__I__I__I__F0__O = (function(key, originalHash, keyHash, shift, f) {
  var mask = $m_sci_Node$().maskFrom__I__I__I(keyHash, shift);
  var bitpos = $m_sci_Node$().bitposFrom__I__I(mask);
  if (((this.dataMap$3 & bitpos) !== 0)) {
    var index = $m_sci_Node$().indexFrom__I__I__I__I(this.dataMap$3, mask, bitpos);
    var key0 = this.getKey__I__O(index);
    return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, key0) ? this.getValue__I__O(index) : f.apply__O())
  };
  if (((this.nodeMap$3 & bitpos) !== 0)) {
    var index$2 = $m_sci_Node$().indexFrom__I__I__I__I(this.nodeMap$3, mask, bitpos);
    return this.getNode__I__sci_MapNode(index$2).getOrElse__O__I__I__I__F0__O(key, originalHash, keyHash, ((5 + shift) | 0), f)
  };
  return f.apply__O()
});
$c_sci_BitmapIndexedMapNode.prototype.size__I = (function() {
  return this.size$3
});
$c_sci_BitmapIndexedMapNode.prototype.mergeTwoKeyValPairs__O__O__I__I__O__O__I__I__I__sci_MapNode = (function(key0, value0, originalHash0, keyHash0, key1, value1, originalHash1, keyHash1, shift) {
  if ((shift >= 32)) {
    var this$4 = $m_sci_Vector$();
    var array = [new $c_T2(key0, value0), new $c_T2(key1, value1)];
    var elems = new $c_sjsr_WrappedVarArgs(array);
    return new $c_sci_HashCollisionMapNode(originalHash0, keyHash0, this$4.from__sc_IterableOnce__sci_Vector(elems))
  } else {
    var mask0 = $m_sci_Node$().maskFrom__I__I__I(keyHash0, shift);
    var mask1 = $m_sci_Node$().maskFrom__I__I__I(keyHash1, shift);
    if ((mask0 !== mask1)) {
      var dataMap = ($m_sci_Node$().bitposFrom__I__I(mask0) | $m_sci_Node$().bitposFrom__I__I(mask1));
      if ((mask0 < mask1)) {
        var array$1 = [key0, value0, key1, value1];
        var xs = new $c_sjsr_WrappedVarArgs(array$1);
        $m_s_reflect_ManifestFactory$AnyManifest$();
        var len = xs.length__I();
        var array$2 = $newArrayObject($d_O.getArrayOf(), [len]);
        var elem$1 = 0;
        elem$1 = 0;
        var this$12 = new $c_sc_IndexedSeqView$Id(xs);
        var this$13 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$12);
        while (this$13.hasNext__Z()) {
          var arg1 = this$13.next__O();
          array$2.set(elem$1, arg1);
          elem$1 = ((1 + elem$1) | 0)
        };
        var jsx$1 = $m_s_Array$();
        var array$3 = [originalHash1];
        return new $c_sci_BitmapIndexedMapNode(dataMap, 0, array$2, jsx$1.apply__I__sci_Seq__AI(originalHash0, new $c_sjsr_WrappedVarArgs(array$3)), 2)
      } else {
        var array$4 = [key1, value1, key0, value0];
        var xs$1 = new $c_sjsr_WrappedVarArgs(array$4);
        $m_s_reflect_ManifestFactory$AnyManifest$();
        var len$1 = xs$1.length__I();
        var array$5 = $newArrayObject($d_O.getArrayOf(), [len$1]);
        var elem$1$1 = 0;
        elem$1$1 = 0;
        var this$24 = new $c_sc_IndexedSeqView$Id(xs$1);
        var this$25 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$24);
        while (this$25.hasNext__Z()) {
          var arg1$1 = this$25.next__O();
          array$5.set(elem$1$1, arg1$1);
          elem$1$1 = ((1 + elem$1$1) | 0)
        };
        var jsx$2 = $m_s_Array$();
        var array$6 = [originalHash0];
        return new $c_sci_BitmapIndexedMapNode(dataMap, 0, array$5, jsx$2.apply__I__sci_Seq__AI(originalHash1, new $c_sjsr_WrappedVarArgs(array$6)), 2)
      }
    } else {
      var nodeMap = $m_sci_Node$().bitposFrom__I__I(mask0);
      var node = this.mergeTwoKeyValPairs__O__O__I__I__O__O__I__I__I__sci_MapNode(key0, value0, originalHash0, keyHash0, key1, value1, originalHash1, keyHash1, ((5 + shift) | 0));
      var array$7 = [node];
      var xs$2 = new $c_sjsr_WrappedVarArgs(array$7);
      $m_s_reflect_ManifestFactory$AnyManifest$();
      var len$2 = xs$2.length__I();
      var array$8 = $newArrayObject($d_O.getArrayOf(), [len$2]);
      var elem$1$2 = 0;
      elem$1$2 = 0;
      var this$36 = new $c_sc_IndexedSeqView$Id(xs$2);
      var this$37 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$36);
      while (this$37.hasNext__Z()) {
        var arg1$2 = this$37.next__O();
        array$8.set(elem$1$2, arg1$2);
        elem$1$2 = ((1 + elem$1$2) | 0)
      };
      var xs$3 = $m_sci_Nil$();
      $m_s_reflect_ManifestFactory$IntManifest$();
      var len$3 = xs$3.length__I();
      var array$9 = $newArrayObject($d_I.getArrayOf(), [len$3]);
      var elem$1$3 = 0;
      elem$1$3 = 0;
      var this$42 = $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f;
      while (this$42.hasNext__Z()) {
        var arg1$3 = this$42.next__O();
        array$9.set(elem$1$3, $uI(arg1$3));
        elem$1$3 = ((1 + elem$1$3) | 0)
      };
      return new $c_sci_BitmapIndexedMapNode(0, nodeMap, array$8, array$9, node.size__I())
    }
  }
});
$c_sci_BitmapIndexedMapNode.prototype.copyAndSetNode__I__sci_MapNode__sci_MapNode__sci_MapNode = (function(bitpos, oldNode, newNode) {
  var idx = (((((-1) + this.content$3.u.length) | 0) - this.nodeIndex__I__I(bitpos)) | 0);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [src.u.length]);
  $systemArraycopy(src, 0, dst, 0, src.u.length);
  dst.set(idx, newNode);
  return new $c_sci_BitmapIndexedMapNode(this.dataMap$3, this.nodeMap$3, dst, this.originalHashes$3, ((((this.size$3 - oldNode.size__I()) | 0) + newNode.size__I()) | 0))
});
$c_sci_BitmapIndexedMapNode.prototype.copyAndSetValue__I__O__O__sci_MapNode = (function(bitpos, newKey, newValue) {
  var dataIx = this.dataIndex__I__I(bitpos);
  var idx = (dataIx << 1);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [src.u.length]);
  $systemArraycopy(src, 0, dst, 0, src.u.length);
  dst.set(idx, newKey);
  dst.set(((1 + idx) | 0), newValue);
  return new $c_sci_BitmapIndexedMapNode(this.dataMap$3, this.nodeMap$3, dst, this.originalHashes$3, this.size$3)
});
$c_sci_BitmapIndexedMapNode.prototype.hasPayload__Z = (function() {
  return (this.dataMap$3 !== 0)
});
$c_sci_BitmapIndexedMapNode.prototype.copyAndInsertValue__I__O__I__I__O__sci_BitmapIndexedMapNode = (function(bitpos, key, originalHash, keyHash, value) {
  var dataIx = this.dataIndex__I__I(bitpos);
  var idx = (dataIx << 1);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [((2 + src.u.length) | 0)]);
  $systemArraycopy(src, 0, dst, 0, idx);
  dst.set(idx, key);
  dst.set(((1 + idx) | 0), value);
  $systemArraycopy(src, idx, dst, ((2 + idx) | 0), ((src.u.length - idx) | 0));
  var dstHashes = this.insertElement__AI__I__I__AI(this.originalHashes$3, dataIx, originalHash);
  return new $c_sci_BitmapIndexedMapNode((this.dataMap$3 | bitpos), this.nodeMap$3, dst, dstHashes, ((1 + this.size$3) | 0))
});
$c_sci_BitmapIndexedMapNode.prototype.getValue__I__O = (function(index) {
  return this.content$3.get(((1 + (index << 1)) | 0))
});
$c_sci_BitmapIndexedMapNode.prototype.getNode__I__sci_Node = (function(index) {
  return this.getNode__I__sci_MapNode(index)
});
$c_sci_BitmapIndexedMapNode.prototype.removed__O__I__I__I__sci_MapNode = (function(key, originalHash, keyHash, shift) {
  var mask = $m_sci_Node$().maskFrom__I__I__I(keyHash, shift);
  var bitpos = $m_sci_Node$().bitposFrom__I__I(mask);
  if (((this.dataMap$3 & bitpos) !== 0)) {
    var index = $m_sci_Node$().indexFrom__I__I__I__I(this.dataMap$3, mask, bitpos);
    var key0 = this.getKey__I__O(index);
    if ($m_sr_BoxesRunTime$().equals__O__O__Z(key0, key)) {
      if ((($m_jl_Integer$().bitCount__I__I(this.dataMap$3) === 2) && ($m_jl_Integer$().bitCount__I__I(this.nodeMap$3) === 0))) {
        var newDataMap = ((shift === 0) ? (this.dataMap$3 ^ bitpos) : $m_sci_Node$().bitposFrom__I__I($m_sci_Node$().maskFrom__I__I__I(keyHash, 0)));
        if ((index === 0)) {
          var array = [this.getKey__I__O(1), this.getValue__I__O(1)];
          var xs = new $c_sjsr_WrappedVarArgs(array);
          $m_s_reflect_ManifestFactory$AnyManifest$();
          var len = xs.length__I();
          var array$1 = $newArrayObject($d_O.getArrayOf(), [len]);
          var elem$1 = 0;
          elem$1 = 0;
          var this$8 = new $c_sc_IndexedSeqView$Id(xs);
          var this$9 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$8);
          while (this$9.hasNext__Z()) {
            var arg1 = this$9.next__O();
            array$1.set(elem$1, arg1);
            elem$1 = ((1 + elem$1) | 0)
          };
          var jsx$2 = $m_s_Array$();
          var jsx$1 = this.originalHashes$3.get(1);
          var array$2 = [];
          return new $c_sci_BitmapIndexedMapNode(newDataMap, 0, array$1, jsx$2.apply__I__sci_Seq__AI(jsx$1, new $c_sjsr_WrappedVarArgs(array$2)), 1)
        } else {
          var array$3 = [this.getKey__I__O(0), this.getValue__I__O(0)];
          var xs$1 = new $c_sjsr_WrappedVarArgs(array$3);
          $m_s_reflect_ManifestFactory$AnyManifest$();
          var len$1 = xs$1.length__I();
          var array$4 = $newArrayObject($d_O.getArrayOf(), [len$1]);
          var elem$1$1 = 0;
          elem$1$1 = 0;
          var this$20 = new $c_sc_IndexedSeqView$Id(xs$1);
          var this$21 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$20);
          while (this$21.hasNext__Z()) {
            var arg1$1 = this$21.next__O();
            array$4.set(elem$1$1, arg1$1);
            elem$1$1 = ((1 + elem$1$1) | 0)
          };
          var jsx$4 = $m_s_Array$();
          var jsx$3 = this.originalHashes$3.get(0);
          var array$5 = [];
          return new $c_sci_BitmapIndexedMapNode(newDataMap, 0, array$4, jsx$4.apply__I__sci_Seq__AI(jsx$3, new $c_sjsr_WrappedVarArgs(array$5)), 1)
        }
      } else {
        return this.copyAndRemoveValue__I__sci_BitmapIndexedMapNode(bitpos)
      }
    } else {
      return this
    }
  };
  if (((this.nodeMap$3 & bitpos) !== 0)) {
    var index$2 = $m_sci_Node$().indexFrom__I__I__I__I(this.nodeMap$3, mask, bitpos);
    var subNode = this.getNode__I__sci_MapNode(index$2);
    var subNodeNew = subNode.removed__O__I__I__I__sci_MapNode(key, originalHash, keyHash, ((5 + shift) | 0));
    if ((subNodeNew === subNode)) {
      return this
    };
    var x1 = subNodeNew.sizePredicate__I();
    switch (x1) {
      case 1: {
        if ((($m_jl_Integer$().bitCount__I__I(this.dataMap$3) === 0) && ($m_jl_Integer$().bitCount__I__I(this.nodeMap$3) === 1))) {
          return subNodeNew
        } else {
          return this.copyAndMigrateFromNodeToInline__I__I__I__sci_MapNode__sci_MapNode__sci_BitmapIndexedMapNode(bitpos, originalHash, keyHash, subNode, subNodeNew)
        };
        break
      }
      case 2: {
        return this.copyAndSetNode__I__sci_MapNode__sci_MapNode__sci_MapNode(bitpos, subNode, subNodeNew);
        break
      }
      default: {
        throw new $c_s_MatchError(x1)
      }
    }
  };
  return this
});
$c_sci_BitmapIndexedMapNode.prototype.dataIndex__I__I = (function(bitpos) {
  return $m_jl_Integer$().bitCount__I__I((this.dataMap$3 & (((-1) + bitpos) | 0)))
});
$c_sci_BitmapIndexedMapNode.prototype.getNode__I__sci_MapNode = (function(index) {
  return $as_sci_MapNode(this.content$3.get((((((-1) + this.content$3.u.length) | 0) - index) | 0)))
});
$c_sci_BitmapIndexedMapNode.prototype.hashCode__I = (function() {
  throw new $c_jl_UnsupportedOperationException().init___T("Trie nodes do not support hashing.")
});
$c_sci_BitmapIndexedMapNode.prototype.nodeArity__I = (function() {
  return $m_jl_Integer$().bitCount__I__I(this.nodeMap$3)
});
$c_sci_BitmapIndexedMapNode.prototype.updated__O__O__I__I__I__sci_MapNode = (function(key, value, originalHash, keyHash, shift) {
  var mask = $m_sci_Node$().maskFrom__I__I__I(keyHash, shift);
  var bitpos = $m_sci_Node$().bitposFrom__I__I(mask);
  if (((this.dataMap$3 & bitpos) !== 0)) {
    var index = $m_sci_Node$().indexFrom__I__I__I__I(this.dataMap$3, mask, bitpos);
    var key0 = this.getKey__I__O(index);
    if ($m_sr_BoxesRunTime$().equals__O__O__Z(key0, key)) {
      var value0 = this.getValue__I__O(index);
      return (((key0 === key) && (value0 === value)) ? this : this.copyAndSetValue__I__O__O__sci_MapNode(bitpos, key, value))
    } else {
      var value0$2 = this.getValue__I__O(index);
      var key0UnimprovedHash = $m_sr_Statics$().anyHash__O__I(key0);
      var key0Hash = $m_sc_Hashing$().improve__I__I(key0UnimprovedHash);
      var subNodeNew = this.mergeTwoKeyValPairs__O__O__I__I__O__O__I__I__I__sci_MapNode(key0, value0$2, key0UnimprovedHash, key0Hash, key, value, originalHash, keyHash, ((5 + shift) | 0));
      return this.copyAndMigrateFromInlineToNode__I__sci_MapNode__sci_BitmapIndexedMapNode(bitpos, subNodeNew)
    }
  };
  if (((this.nodeMap$3 & bitpos) !== 0)) {
    var index$2 = $m_sci_Node$().indexFrom__I__I__I__I(this.nodeMap$3, mask, bitpos);
    var subNode = this.getNode__I__sci_MapNode(index$2);
    var subNodeNew$2 = subNode.updated__O__O__I__I__I__sci_MapNode(key, value, originalHash, keyHash, ((5 + shift) | 0));
    if ((subNodeNew$2 === subNode)) {
      return this
    } else {
      return this.copyAndSetNode__I__sci_MapNode__sci_MapNode__sci_MapNode(bitpos, subNode, subNodeNew$2)
    }
  };
  return this.copyAndInsertValue__I__O__I__I__O__sci_BitmapIndexedMapNode(bitpos, key, originalHash, keyHash, value)
});
$c_sci_BitmapIndexedMapNode.prototype.getKey__I__O = (function(index) {
  return this.content$3.get((index << 1))
});
$c_sci_BitmapIndexedMapNode.prototype.payloadArity__I = (function() {
  return $m_jl_Integer$().bitCount__I__I(this.dataMap$3)
});
function $is_sci_BitmapIndexedMapNode(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_BitmapIndexedMapNode)))
}
function $as_sci_BitmapIndexedMapNode(obj) {
  return (($is_sci_BitmapIndexedMapNode(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.BitmapIndexedMapNode"))
}
function $isArrayOf_sci_BitmapIndexedMapNode(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_BitmapIndexedMapNode)))
}
function $asArrayOf_sci_BitmapIndexedMapNode(obj, depth) {
  return (($isArrayOf_sci_BitmapIndexedMapNode(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.BitmapIndexedMapNode;", depth))
}
var $d_sci_BitmapIndexedMapNode = new $TypeData().initClass({
  sci_BitmapIndexedMapNode: 0
}, false, "scala.collection.immutable.BitmapIndexedMapNode", {
  sci_BitmapIndexedMapNode: 1,
  sci_MapNode: 1,
  sci_Node: 1,
  O: 1
});
$c_sci_BitmapIndexedMapNode.prototype.$classData = $d_sci_BitmapIndexedMapNode;
/** @constructor */
function $c_sci_BitmapIndexedSetNode(dataMap, nodeMap, content, originalHashes, size) {
  this.dataMap$3 = 0;
  this.nodeMap$3 = 0;
  this.content$3 = null;
  this.originalHashes$3 = null;
  this.size$3 = 0;
  this.dataMap$3 = dataMap;
  this.nodeMap$3 = nodeMap;
  this.content$3 = content;
  this.originalHashes$3 = originalHashes;
  this.size$3 = size
}
$c_sci_BitmapIndexedSetNode.prototype = new $h_sci_SetNode();
$c_sci_BitmapIndexedSetNode.prototype.constructor = $c_sci_BitmapIndexedSetNode;
/** @constructor */
function $h_sci_BitmapIndexedSetNode() {
  /*<skip>*/
}
$h_sci_BitmapIndexedSetNode.prototype = $c_sci_BitmapIndexedSetNode.prototype;
$c_sci_BitmapIndexedSetNode.prototype.getHash__I__I = (function(index) {
  return this.originalHashes$3.get(index)
});
$c_sci_BitmapIndexedSetNode.prototype.nodeIndex__I__I = (function(bitpos) {
  return $m_jl_Integer$().bitCount__I__I((this.nodeMap$3 & (((-1) + bitpos) | 0)))
});
$c_sci_BitmapIndexedSetNode.prototype.updated__O__I__I__I__sci_SetNode = (function(element, originalHash, elementHash, shift) {
  var mask = $m_sci_Node$().maskFrom__I__I__I(elementHash, shift);
  var bitpos = $m_sci_Node$().bitposFrom__I__I(mask);
  if (((this.dataMap$3 & bitpos) !== 0)) {
    var index = $m_sci_Node$().indexFrom__I__I__I__I(this.dataMap$3, mask, bitpos);
    var element0 = this.getPayload__I__O(index);
    if ((element0 === element)) {
      return this
    } else if ($dp_equals__O__Z(element0, element)) {
      var element0UnimprovedHash = $m_sr_Statics$().anyHash__O__I(element0);
      $m_sc_Hashing$().improve__I__I(element0UnimprovedHash);
      return this.copyAndSetValue__I__O__I__I__sci_BitmapIndexedSetNode(bitpos, element, originalHash, elementHash)
    } else {
      var element0UnimprovedHash$2 = $m_sr_Statics$().anyHash__O__I(element0);
      var element0Hash$2 = $m_sc_Hashing$().improve__I__I(element0UnimprovedHash$2);
      var subNodeNew = this.mergeTwoKeyValPairs__O__I__I__O__I__I__I__sci_SetNode(element0, element0UnimprovedHash$2, element0Hash$2, element, originalHash, elementHash, ((5 + shift) | 0));
      return this.copyAndMigrateFromInlineToNode__I__sci_SetNode__sci_BitmapIndexedSetNode(bitpos, subNodeNew)
    }
  };
  if (((this.nodeMap$3 & bitpos) !== 0)) {
    var index$2 = $m_sci_Node$().indexFrom__I__I__I__I(this.nodeMap$3, mask, bitpos);
    var subNode = this.getNode__I__sci_SetNode(index$2);
    var subNodeNew$2 = subNode.updated__O__I__I__I__sci_SetNode(element, originalHash, elementHash, ((5 + shift) | 0));
    if ((subNode === subNodeNew$2)) {
      return this
    } else {
      return this.copyAndSetNode__I__sci_SetNode__sci_SetNode__sci_BitmapIndexedSetNode(bitpos, subNode, subNodeNew$2)
    }
  };
  return this.copyAndInsertValue__I__O__I__I__sci_BitmapIndexedSetNode(bitpos, element, originalHash, elementHash)
});
$c_sci_BitmapIndexedSetNode.prototype.copyAndRemoveValue__I__sci_BitmapIndexedSetNode = (function(bitpos) {
  var dataIx = this.dataIndex__I__I(bitpos);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [(((-1) + src.u.length) | 0)]);
  $systemArraycopy(src, 0, dst, 0, dataIx);
  $systemArraycopy(src, ((1 + dataIx) | 0), dst, dataIx, (((-1) + ((src.u.length - dataIx) | 0)) | 0));
  var dstHashes = this.removeElement__AI__I__AI(this.originalHashes$3, dataIx);
  return new $c_sci_BitmapIndexedSetNode((this.dataMap$3 ^ bitpos), this.nodeMap$3, dst, dstHashes, (((-1) + this.size$3) | 0))
});
$c_sci_BitmapIndexedSetNode.prototype.equals__O__Z = (function(that) {
  if ($is_sci_BitmapIndexedSetNode(that)) {
    var x2 = $as_sci_BitmapIndexedSetNode(that);
    if ((this === x2)) {
      return true
    } else if ((((this.nodeMap$3 === x2.nodeMap$3) && (this.dataMap$3 === x2.dataMap$3)) && $m_ju_Arrays$().equals__AI__AI__Z(this.originalHashes$3, x2.originalHashes$3))) {
      var a1 = this.content$3;
      var a2 = x2.content$3;
      var length = this.content$3.u.length;
      if ((a1 === a2)) {
        return true
      } else {
        var isEqual = true;
        var i = 0;
        while ((isEqual && (i < length))) {
          isEqual = $m_sr_BoxesRunTime$().equals__O__O__Z(a1.get(i), a2.get(i));
          i = ((1 + i) | 0)
        };
        return isEqual
      }
    } else {
      return false
    }
  } else {
    return false
  }
});
$c_sci_BitmapIndexedSetNode.prototype.sizePredicate__I = (function() {
  if (($m_jl_Integer$().bitCount__I__I(this.nodeMap$3) === 0)) {
    var x1 = $m_jl_Integer$().bitCount__I__I(this.dataMap$3);
    switch (x1) {
      case 0: {
        return 0;
        break
      }
      case 1: {
        return 1;
        break
      }
      default: {
        return 2
      }
    }
  } else {
    return 2
  }
});
$c_sci_BitmapIndexedSetNode.prototype.copyAndMigrateFromNodeToInline__I__I__sci_SetNode__sci_SetNode__sci_BitmapIndexedSetNode = (function(bitpos, elementHash, oldNode, node) {
  var idxOld = (((((-1) + this.content$3.u.length) | 0) - this.nodeIndex__I__I(bitpos)) | 0);
  var dataIxNew = this.dataIndex__I__I(bitpos);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [src.u.length]);
  $systemArraycopy(src, 0, dst, 0, dataIxNew);
  dst.set(dataIxNew, node.getPayload__I__O(0));
  $systemArraycopy(src, dataIxNew, dst, ((1 + dataIxNew) | 0), ((idxOld - dataIxNew) | 0));
  $systemArraycopy(src, ((1 + idxOld) | 0), dst, ((1 + idxOld) | 0), (((-1) + ((src.u.length - idxOld) | 0)) | 0));
  var hash = node.getHash__I__I(0);
  var dstHashes = this.insertElement__AI__I__I__AI(this.originalHashes$3, dataIxNew, hash);
  return new $c_sci_BitmapIndexedSetNode((this.dataMap$3 | bitpos), (this.nodeMap$3 ^ bitpos), dst, dstHashes, ((1 + ((this.size$3 - oldNode.size__I()) | 0)) | 0))
});
$c_sci_BitmapIndexedSetNode.prototype.hasNodes__Z = (function() {
  return (this.nodeMap$3 !== 0)
});
$c_sci_BitmapIndexedSetNode.prototype.foreach__F1__V = (function(f) {
  var i = 0;
  while ((i < $m_jl_Integer$().bitCount__I__I(this.dataMap$3))) {
    f.apply__O__O(this.getPayload__I__O(i));
    i = ((1 + i) | 0)
  };
  var j = 0;
  while ((j < $m_jl_Integer$().bitCount__I__I(this.nodeMap$3))) {
    this.getNode__I__sci_SetNode(j).foreach__F1__V(f);
    j = ((1 + j) | 0)
  }
});
$c_sci_BitmapIndexedSetNode.prototype.getPayload__I__O = (function(index) {
  return this.content$3.get(index)
});
$c_sci_BitmapIndexedSetNode.prototype.size__I = (function() {
  return this.size$3
});
$c_sci_BitmapIndexedSetNode.prototype.copyAndSetNode__I__sci_SetNode__sci_SetNode__sci_BitmapIndexedSetNode = (function(bitpos, oldNode, newNode) {
  var idx = (((((-1) + this.content$3.u.length) | 0) - this.nodeIndex__I__I(bitpos)) | 0);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [src.u.length]);
  $systemArraycopy(src, 0, dst, 0, src.u.length);
  dst.set(idx, newNode);
  return new $c_sci_BitmapIndexedSetNode(this.dataMap$3, this.nodeMap$3, dst, this.originalHashes$3, ((((this.size$3 - oldNode.size__I()) | 0) + newNode.size__I()) | 0))
});
$c_sci_BitmapIndexedSetNode.prototype.hasPayload__Z = (function() {
  return (this.dataMap$3 !== 0)
});
$c_sci_BitmapIndexedSetNode.prototype.copyAndInsertValue__I__O__I__I__sci_BitmapIndexedSetNode = (function(bitpos, key, originalHash, elementHash) {
  var dataIx = this.dataIndex__I__I(bitpos);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [((1 + src.u.length) | 0)]);
  $systemArraycopy(src, 0, dst, 0, dataIx);
  dst.set(dataIx, key);
  $systemArraycopy(src, dataIx, dst, ((1 + dataIx) | 0), ((src.u.length - dataIx) | 0));
  var dstHashes = this.insertElement__AI__I__I__AI(this.originalHashes$3, dataIx, originalHash);
  return new $c_sci_BitmapIndexedSetNode((this.dataMap$3 | bitpos), this.nodeMap$3, dst, dstHashes, ((1 + this.size$3) | 0))
});
$c_sci_BitmapIndexedSetNode.prototype.copyAndMigrateFromInlineToNode__I__sci_SetNode__sci_BitmapIndexedSetNode = (function(bitpos, node) {
  var dataIx = this.dataIndex__I__I(bitpos);
  var idxNew = (((((-1) + this.content$3.u.length) | 0) - this.nodeIndex__I__I(bitpos)) | 0);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [src.u.length]);
  $systemArraycopy(src, 0, dst, 0, dataIx);
  $systemArraycopy(src, ((1 + dataIx) | 0), dst, dataIx, ((idxNew - dataIx) | 0));
  dst.set(idxNew, node);
  $systemArraycopy(src, ((1 + idxNew) | 0), dst, ((1 + idxNew) | 0), (((-1) + ((src.u.length - idxNew) | 0)) | 0));
  var dstHashes = this.removeElement__AI__I__AI(this.originalHashes$3, dataIx);
  return new $c_sci_BitmapIndexedSetNode((this.dataMap$3 ^ bitpos), (this.nodeMap$3 | bitpos), dst, dstHashes, (((((-1) + this.size$3) | 0) + node.size__I()) | 0))
});
$c_sci_BitmapIndexedSetNode.prototype.getNode__I__sci_SetNode = (function(index) {
  return $as_sci_SetNode(this.content$3.get((((((-1) + this.content$3.u.length) | 0) - index) | 0)))
});
$c_sci_BitmapIndexedSetNode.prototype.getNode__I__sci_Node = (function(index) {
  return this.getNode__I__sci_SetNode(index)
});
$c_sci_BitmapIndexedSetNode.prototype.dataIndex__I__I = (function(bitpos) {
  return $m_jl_Integer$().bitCount__I__I((this.dataMap$3 & (((-1) + bitpos) | 0)))
});
$c_sci_BitmapIndexedSetNode.prototype.hashCode__I = (function() {
  throw new $c_jl_UnsupportedOperationException().init___T("Trie nodes do not support hashing.")
});
$c_sci_BitmapIndexedSetNode.prototype.nodeArity__I = (function() {
  return $m_jl_Integer$().bitCount__I__I(this.nodeMap$3)
});
$c_sci_BitmapIndexedSetNode.prototype.removed__O__I__I__I__sci_SetNode = (function(element, originalHash, elementHash, shift) {
  var mask = $m_sci_Node$().maskFrom__I__I__I(elementHash, shift);
  var bitpos = $m_sci_Node$().bitposFrom__I__I(mask);
  if (((this.dataMap$3 & bitpos) !== 0)) {
    var index = $m_sci_Node$().indexFrom__I__I__I__I(this.dataMap$3, mask, bitpos);
    var element0 = this.getPayload__I__O(index);
    if ($m_sr_BoxesRunTime$().equals__O__O__Z(element0, element)) {
      if ((($m_jl_Integer$().bitCount__I__I(this.dataMap$3) === 2) && ($m_jl_Integer$().bitCount__I__I(this.nodeMap$3) === 0))) {
        var newDataMap = ((shift === 0) ? (this.dataMap$3 ^ bitpos) : $m_sci_Node$().bitposFrom__I__I($m_sci_Node$().maskFrom__I__I__I(elementHash, 0)));
        if ((index === 0)) {
          var array = [this.getPayload__I__O(1)];
          var xs = new $c_sjsr_WrappedVarArgs(array);
          $m_s_reflect_ManifestFactory$AnyManifest$();
          var len = xs.length__I();
          var array$1 = $newArrayObject($d_O.getArrayOf(), [len]);
          var elem$1 = 0;
          elem$1 = 0;
          var this$8 = new $c_sc_IndexedSeqView$Id(xs);
          var this$9 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$8);
          while (this$9.hasNext__Z()) {
            var arg1 = this$9.next__O();
            array$1.set(elem$1, arg1);
            elem$1 = ((1 + elem$1) | 0)
          };
          var jsx$2 = $m_s_Array$();
          var jsx$1 = this.originalHashes$3.get(1);
          var array$2 = [];
          return new $c_sci_BitmapIndexedSetNode(newDataMap, 0, array$1, jsx$2.apply__I__sci_Seq__AI(jsx$1, new $c_sjsr_WrappedVarArgs(array$2)), (((-1) + this.size$3) | 0))
        } else {
          var array$3 = [this.getPayload__I__O(0)];
          var xs$1 = new $c_sjsr_WrappedVarArgs(array$3);
          $m_s_reflect_ManifestFactory$AnyManifest$();
          var len$1 = xs$1.length__I();
          var array$4 = $newArrayObject($d_O.getArrayOf(), [len$1]);
          var elem$1$1 = 0;
          elem$1$1 = 0;
          var this$20 = new $c_sc_IndexedSeqView$Id(xs$1);
          var this$21 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$20);
          while (this$21.hasNext__Z()) {
            var arg1$1 = this$21.next__O();
            array$4.set(elem$1$1, arg1$1);
            elem$1$1 = ((1 + elem$1$1) | 0)
          };
          var jsx$4 = $m_s_Array$();
          var jsx$3 = this.originalHashes$3.get(0);
          var array$5 = [];
          return new $c_sci_BitmapIndexedSetNode(newDataMap, 0, array$4, jsx$4.apply__I__sci_Seq__AI(jsx$3, new $c_sjsr_WrappedVarArgs(array$5)), (((-1) + this.size$3) | 0))
        }
      } else {
        return this.copyAndRemoveValue__I__sci_BitmapIndexedSetNode(bitpos)
      }
    } else {
      return this
    }
  };
  if (((this.nodeMap$3 & bitpos) !== 0)) {
    var index$2 = $m_sci_Node$().indexFrom__I__I__I__I(this.nodeMap$3, mask, bitpos);
    var subNode = this.getNode__I__sci_SetNode(index$2);
    var subNodeNew = subNode.removed__O__I__I__I__sci_SetNode(element, originalHash, elementHash, ((5 + shift) | 0));
    if ((subNodeNew === subNode)) {
      return this
    };
    var x1 = subNodeNew.sizePredicate__I();
    switch (x1) {
      case 1: {
        if ((($m_jl_Integer$().bitCount__I__I(this.dataMap$3) === 0) && ($m_jl_Integer$().bitCount__I__I(this.nodeMap$3) === 1))) {
          return subNodeNew
        } else {
          return this.copyAndMigrateFromNodeToInline__I__I__sci_SetNode__sci_SetNode__sci_BitmapIndexedSetNode(bitpos, elementHash, subNode, subNodeNew)
        };
        break
      }
      case 2: {
        return this.copyAndSetNode__I__sci_SetNode__sci_SetNode__sci_BitmapIndexedSetNode(bitpos, subNode, subNodeNew);
        break
      }
      default: {
        throw new $c_s_MatchError(x1)
      }
    }
  };
  return this
});
$c_sci_BitmapIndexedSetNode.prototype.contains__O__I__I__I__Z = (function(element, originalHash, elementHash, shift) {
  var mask = $m_sci_Node$().maskFrom__I__I__I(elementHash, shift);
  var bitpos = $m_sci_Node$().bitposFrom__I__I(mask);
  if (((this.dataMap$3 & bitpos) !== 0)) {
    var index = $m_sci_Node$().indexFrom__I__I__I__I(this.dataMap$3, mask, bitpos);
    return ((this.originalHashes$3.get(index) === originalHash) && $m_sr_BoxesRunTime$().equals__O__O__Z(element, this.getPayload__I__O(index)))
  };
  if (((this.nodeMap$3 & bitpos) !== 0)) {
    var index$2 = $m_sci_Node$().indexFrom__I__I__I__I(this.nodeMap$3, mask, bitpos);
    return this.getNode__I__sci_SetNode(index$2).contains__O__I__I__I__Z(element, originalHash, elementHash, ((5 + shift) | 0))
  };
  return false
});
$c_sci_BitmapIndexedSetNode.prototype.copyAndSetValue__I__O__I__I__sci_BitmapIndexedSetNode = (function(bitpos, key, originalHash, elementHash) {
  var dataIx = this.dataIndex__I__I(bitpos);
  var src = this.content$3;
  var dst = $newArrayObject($d_O.getArrayOf(), [src.u.length]);
  $systemArraycopy(src, 0, dst, 0, src.u.length);
  dst.set(dataIx, key);
  return new $c_sci_BitmapIndexedSetNode((this.dataMap$3 | bitpos), this.nodeMap$3, dst, this.originalHashes$3, this.size$3)
});
$c_sci_BitmapIndexedSetNode.prototype.mergeTwoKeyValPairs__O__I__I__O__I__I__I__sci_SetNode = (function(key0, originalKeyHash0, keyHash0, key1, originalKeyHash1, keyHash1, shift) {
  if ((shift >= 32)) {
    var this$4 = $m_sci_Vector$();
    var array = [key0, key1];
    var elems = new $c_sjsr_WrappedVarArgs(array);
    return new $c_sci_HashCollisionSetNode(originalKeyHash0, keyHash0, this$4.from__sc_IterableOnce__sci_Vector(elems))
  } else {
    var mask0 = $m_sci_Node$().maskFrom__I__I__I(keyHash0, shift);
    var mask1 = $m_sci_Node$().maskFrom__I__I__I(keyHash1, shift);
    if ((mask0 !== mask1)) {
      var dataMap = ($m_sci_Node$().bitposFrom__I__I(mask0) | $m_sci_Node$().bitposFrom__I__I(mask1));
      if ((mask0 < mask1)) {
        var array$1 = [key0, key1];
        var xs = new $c_sjsr_WrappedVarArgs(array$1);
        $m_s_reflect_ManifestFactory$AnyManifest$();
        var len = xs.length__I();
        var array$2 = $newArrayObject($d_O.getArrayOf(), [len]);
        var elem$1 = 0;
        elem$1 = 0;
        var this$12 = new $c_sc_IndexedSeqView$Id(xs);
        var this$13 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$12);
        while (this$13.hasNext__Z()) {
          var arg1 = this$13.next__O();
          array$2.set(elem$1, arg1);
          elem$1 = ((1 + elem$1) | 0)
        };
        var jsx$1 = $m_s_Array$();
        var array$3 = [originalKeyHash1];
        return new $c_sci_BitmapIndexedSetNode(dataMap, 0, array$2, jsx$1.apply__I__sci_Seq__AI(originalKeyHash0, new $c_sjsr_WrappedVarArgs(array$3)), 2)
      } else {
        var array$4 = [key1, key0];
        var xs$1 = new $c_sjsr_WrappedVarArgs(array$4);
        $m_s_reflect_ManifestFactory$AnyManifest$();
        var len$1 = xs$1.length__I();
        var array$5 = $newArrayObject($d_O.getArrayOf(), [len$1]);
        var elem$1$1 = 0;
        elem$1$1 = 0;
        var this$24 = new $c_sc_IndexedSeqView$Id(xs$1);
        var this$25 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$24);
        while (this$25.hasNext__Z()) {
          var arg1$1 = this$25.next__O();
          array$5.set(elem$1$1, arg1$1);
          elem$1$1 = ((1 + elem$1$1) | 0)
        };
        var jsx$2 = $m_s_Array$();
        var array$6 = [originalKeyHash0];
        return new $c_sci_BitmapIndexedSetNode(dataMap, 0, array$5, jsx$2.apply__I__sci_Seq__AI(originalKeyHash1, new $c_sjsr_WrappedVarArgs(array$6)), 2)
      }
    } else {
      var nodeMap = $m_sci_Node$().bitposFrom__I__I(mask0);
      var node = this.mergeTwoKeyValPairs__O__I__I__O__I__I__I__sci_SetNode(key0, originalKeyHash0, keyHash0, key1, originalKeyHash1, keyHash1, ((5 + shift) | 0));
      var array$7 = [node];
      var xs$2 = new $c_sjsr_WrappedVarArgs(array$7);
      $m_s_reflect_ManifestFactory$AnyManifest$();
      var len$2 = xs$2.length__I();
      var array$8 = $newArrayObject($d_O.getArrayOf(), [len$2]);
      var elem$1$2 = 0;
      elem$1$2 = 0;
      var this$36 = new $c_sc_IndexedSeqView$Id(xs$2);
      var this$37 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$36);
      while (this$37.hasNext__Z()) {
        var arg1$2 = this$37.next__O();
        array$8.set(elem$1$2, arg1$2);
        elem$1$2 = ((1 + elem$1$2) | 0)
      };
      var xs$3 = $m_sci_Nil$();
      $m_s_reflect_ManifestFactory$IntManifest$();
      var len$3 = xs$3.length__I();
      var array$9 = $newArrayObject($d_I.getArrayOf(), [len$3]);
      var elem$1$3 = 0;
      elem$1$3 = 0;
      var this$42 = $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f;
      while (this$42.hasNext__Z()) {
        var arg1$3 = this$42.next__O();
        array$9.set(elem$1$3, $uI(arg1$3));
        elem$1$3 = ((1 + elem$1$3) | 0)
      };
      return new $c_sci_BitmapIndexedSetNode(0, nodeMap, array$8, array$9, node.size__I())
    }
  }
});
$c_sci_BitmapIndexedSetNode.prototype.payloadArity__I = (function() {
  return $m_jl_Integer$().bitCount__I__I(this.dataMap$3)
});
function $is_sci_BitmapIndexedSetNode(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_BitmapIndexedSetNode)))
}
function $as_sci_BitmapIndexedSetNode(obj) {
  return (($is_sci_BitmapIndexedSetNode(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.BitmapIndexedSetNode"))
}
function $isArrayOf_sci_BitmapIndexedSetNode(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_BitmapIndexedSetNode)))
}
function $asArrayOf_sci_BitmapIndexedSetNode(obj, depth) {
  return (($isArrayOf_sci_BitmapIndexedSetNode(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.BitmapIndexedSetNode;", depth))
}
var $d_sci_BitmapIndexedSetNode = new $TypeData().initClass({
  sci_BitmapIndexedSetNode: 0
}, false, "scala.collection.immutable.BitmapIndexedSetNode", {
  sci_BitmapIndexedSetNode: 1,
  sci_SetNode: 1,
  sci_Node: 1,
  O: 1
});
$c_sci_BitmapIndexedSetNode.prototype.$classData = $d_sci_BitmapIndexedSetNode;
/** @constructor */
function $c_sci_HashCollisionMapNode(originalHash, hash, content) {
  this.originalHash$3 = 0;
  this.hash$3 = 0;
  this.content$3 = null;
  this.originalHash$3 = originalHash;
  this.hash$3 = hash;
  this.content$3 = content;
  $m_s_Predef$().require__Z__V((content.length__I() >= 2))
}
$c_sci_HashCollisionMapNode.prototype = new $h_sci_MapNode();
$c_sci_HashCollisionMapNode.prototype.constructor = $c_sci_HashCollisionMapNode;
/** @constructor */
function $h_sci_HashCollisionMapNode() {
  /*<skip>*/
}
$h_sci_HashCollisionMapNode.prototype = $c_sci_HashCollisionMapNode.prototype;
$c_sci_HashCollisionMapNode.prototype.getHash__I__I = (function(index) {
  return this.originalHash$3
});
$c_sci_HashCollisionMapNode.prototype.getPayload__I__T2 = (function(index) {
  return $as_T2(this.content$3.apply__I__O(index))
});
$c_sci_HashCollisionMapNode.prototype.get__O__I__I__I__s_Option = (function(key, originalHash, hash, shift) {
  if ((this.hash$3 === hash)) {
    var this$1 = this.content$3;
    _return: {
      var it = this$1.iterator__sc_Iterator();
      while (it.hasNext__Z()) {
        var a = it.next__O();
        var x$1 = $as_T2(a);
        if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, x$1.$$und1$f)) {
          var this$2 = new $c_s_Some(a);
          break _return
        }
      };
      var this$2 = $m_s_None$()
    };
    if (this$2.isEmpty__Z()) {
      return $m_s_None$()
    } else {
      var arg1 = this$2.get__O();
      var x$2 = $as_T2(arg1);
      return new $c_s_Some(x$2.$$und2$f)
    }
  } else {
    return $m_s_None$()
  }
});
$c_sci_HashCollisionMapNode.prototype.sizePredicate__I = (function() {
  return 2
});
$c_sci_HashCollisionMapNode.prototype.equals__O__Z = (function(that) {
  if ($is_sci_HashCollisionMapNode(that)) {
    var x2 = $as_sci_HashCollisionMapNode(that);
    if ((this === x2)) {
      return true
    } else {
      if ((this.hash$3 === x2.hash$3)) {
        var this$1 = this.content$3;
        var jsx$2 = this$1.length__I();
        var this$2 = x2.content$3;
        var jsx$1 = (jsx$2 === this$2.length__I())
      } else {
        var jsx$1 = false
      };
      if (jsx$1) {
        var this$3 = this.content$3;
        var res = true;
        var it = this$3.iterator__sc_Iterator();
        while ((res && it.hasNext__Z())) {
          var arg1 = it.next__O();
          var this$4 = x2.content$3;
          res = $f_sc_SeqOps__contains__O__Z(this$4, arg1)
        };
        return res
      } else {
        return false
      }
    }
  } else {
    return false
  }
});
$c_sci_HashCollisionMapNode.prototype.hasNodes__Z = (function() {
  return false
});
$c_sci_HashCollisionMapNode.prototype.foreach__F1__V = (function(f) {
  var this$1 = this.content$3;
  $f_sc_IterableOnceOps__foreach__F1__V(this$1, f)
});
$c_sci_HashCollisionMapNode.prototype.getOrElse__O__I__I__I__F0__O = (function(key, originalHash, hash, shift, f) {
  if ((this.hash$3 === hash)) {
    var this$1 = this.content$3;
    _return: {
      var it = this$1.iterator__sc_Iterator();
      while (it.hasNext__Z()) {
        var a = it.next__O();
        var x$3 = $as_T2(a);
        if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, x$3.$$und1$f)) {
          var x1 = new $c_s_Some(a);
          break _return
        }
      };
      var x1 = $m_s_None$()
    };
    if ($is_s_Some(x1)) {
      var x2 = $as_s_Some(x1);
      var pair = $as_T2(x2.value$2);
      return pair.$$und2$f
    } else {
      var x = $m_s_None$();
      if ((x === x1)) {
        return f.apply__O()
      } else {
        throw new $c_s_MatchError(x1)
      }
    }
  } else {
    return f.apply__O()
  }
});
$c_sci_HashCollisionMapNode.prototype.size__I = (function() {
  var this$1 = this.content$3;
  return this$1.length__I()
});
$c_sci_HashCollisionMapNode.prototype.hasPayload__Z = (function() {
  return true
});
$c_sci_HashCollisionMapNode.prototype.getValue__I__O = (function(index) {
  return $as_T2(this.content$3.apply__I__O(index)).$$und2$f
});
$c_sci_HashCollisionMapNode.prototype.removed__O__I__I__I__sci_MapNode = (function(key, originalHash, hash, shift) {
  if ((!this.containsKey__O__I__I__I__Z(key, originalHash, hash, shift))) {
    return this
  } else {
    var this$1 = this.content$3;
    $m_sci_Vector$();
    var b = new $c_sci_VectorBuilder();
    var it = this$1.iterator__sc_Iterator();
    while (it.hasNext__Z()) {
      var elem = it.next__O();
      var keyValuePair = $as_T2(elem);
      if (($m_sr_BoxesRunTime$().equals__O__O__Z(keyValuePair.$$und1$f, key) !== true)) {
        b.addOne__O__sci_VectorBuilder(elem)
      }
    };
    var updatedContent = b.result__sci_Vector();
    var x1 = updatedContent.length__I();
    if ((x1 === 1)) {
      var x1$2 = $as_T2(updatedContent.apply__I__O(0));
      if ((x1$2 === null)) {
        throw new $c_s_MatchError(x1$2)
      };
      var k = x1$2.$$und1$f;
      var v = x1$2.$$und2$f;
      var jsx$2 = $m_sci_Node$().bitposFrom__I__I($m_sci_Node$().maskFrom__I__I__I(hash, 0));
      var array = [k, v];
      var xs = new $c_sjsr_WrappedVarArgs(array);
      $m_s_reflect_ManifestFactory$AnyManifest$();
      var len = xs.length__I();
      var array$1 = $newArrayObject($d_O.getArrayOf(), [len]);
      var elem$1 = 0;
      elem$1 = 0;
      var this$10 = new $c_sc_IndexedSeqView$Id(xs);
      var this$11 = new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$10);
      while (this$11.hasNext__Z()) {
        var arg1 = this$11.next__O();
        array$1.set(elem$1, arg1);
        elem$1 = ((1 + elem$1) | 0)
      };
      var jsx$1 = $m_s_Array$();
      var array$2 = [];
      return new $c_sci_BitmapIndexedMapNode(jsx$2, 0, array$1, jsx$1.apply__I__sci_Seq__AI(originalHash, new $c_sjsr_WrappedVarArgs(array$2)), 1)
    } else {
      return new $c_sci_HashCollisionMapNode(originalHash, hash, updatedContent)
    }
  }
});
$c_sci_HashCollisionMapNode.prototype.getNode__I__sci_Node = (function(index) {
  return this.getNode__I__sci_MapNode(index)
});
$c_sci_HashCollisionMapNode.prototype.getNode__I__sci_MapNode = (function(index) {
  throw new $c_jl_IndexOutOfBoundsException().init___T("No sub-nodes present in hash-collision leaf node.")
});
$c_sci_HashCollisionMapNode.prototype.containsKey__O__I__I__I__Z = (function(key, originalHash, hash, shift) {
  if ((this.hash$3 === hash)) {
    var this$1 = this.content$3;
    var res = false;
    var it = this$1.iterator__sc_Iterator();
    while (((!res) && it.hasNext__Z())) {
      var arg1 = it.next__O();
      var x$4 = $as_T2(arg1);
      res = $m_sr_BoxesRunTime$().equals__O__O__Z(key, x$4.$$und1$f)
    };
    return res
  } else {
    return false
  }
});
$c_sci_HashCollisionMapNode.prototype.nodeArity__I = (function() {
  return 0
});
$c_sci_HashCollisionMapNode.prototype.hashCode__I = (function() {
  throw new $c_jl_UnsupportedOperationException().init___T("Trie nodes do not support hashing.")
});
$c_sci_HashCollisionMapNode.prototype.updated__O__O__I__I__I__sci_MapNode = (function(key, value, originalHash, hash, shift) {
  if (this.contains__O__O__I__I__Z(key, value, hash, shift)) {
    return this
  } else if (this.containsKey__O__I__I__I__Z(key, originalHash, hash, shift)) {
    var this$1 = this.content$3;
    var this$2 = this$1.iterator__sc_Iterator();
    _return: {
      var i = 0;
      $f_sc_Iterator__drop__I__sc_Iterator(this$2, 0);
      while (this$2.hasNext__Z()) {
        var arg1 = this$2.next__O();
        var x$5 = $as_T2(arg1);
        if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, x$5.$$und1$f)) {
          var index = i;
          break _return
        };
        i = ((1 + i) | 0)
      };
      var index = (-1)
    };
    var this$5 = this.content$3;
    var x1 = $f_sc_IterableOps__splitAt__I__T2(this$5, index);
    if ((x1 === null)) {
      throw new $c_s_MatchError(x1)
    };
    var beforeTuple = $as_sci_Vector(x1.$$und1$f);
    var fromTuple = $as_sci_Vector(x1.$$und2$f);
    var updatedContent = beforeTuple.appended__O__sci_Vector(new $c_T2(key, value)).appendedAll__sc_IterableOnce__sci_Vector(fromTuple.drop__I__sci_Vector(1));
    return new $c_sci_HashCollisionMapNode(originalHash, hash, updatedContent)
  } else {
    return new $c_sci_HashCollisionMapNode(originalHash, hash, this.content$3.appended__O__sci_Vector(new $c_T2(key, value)))
  }
});
$c_sci_HashCollisionMapNode.prototype.getKey__I__O = (function(index) {
  return $as_T2(this.content$3.apply__I__O(index)).$$und1$f
});
$c_sci_HashCollisionMapNode.prototype.contains__O__O__I__I__Z = (function(key, value, hash, shift) {
  if ((this.hash$3 === hash)) {
    var this$1 = this.content$3;
    var res = false;
    var it = this$1.iterator__sc_Iterator();
    while (((!res) && it.hasNext__Z())) {
      var arg1 = it.next__O();
      var payload = $as_T2(arg1);
      res = ($m_sr_BoxesRunTime$().equals__O__O__Z(key, payload.$$und1$f) && (value === payload.$$und2$f))
    };
    return res
  } else {
    return false
  }
});
$c_sci_HashCollisionMapNode.prototype.payloadArity__I = (function() {
  var this$1 = this.content$3;
  return this$1.length__I()
});
function $is_sci_HashCollisionMapNode(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_HashCollisionMapNode)))
}
function $as_sci_HashCollisionMapNode(obj) {
  return (($is_sci_HashCollisionMapNode(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.HashCollisionMapNode"))
}
function $isArrayOf_sci_HashCollisionMapNode(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_HashCollisionMapNode)))
}
function $asArrayOf_sci_HashCollisionMapNode(obj, depth) {
  return (($isArrayOf_sci_HashCollisionMapNode(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.HashCollisionMapNode;", depth))
}
var $d_sci_HashCollisionMapNode = new $TypeData().initClass({
  sci_HashCollisionMapNode: 0
}, false, "scala.collection.immutable.HashCollisionMapNode", {
  sci_HashCollisionMapNode: 1,
  sci_MapNode: 1,
  sci_Node: 1,
  O: 1
});
$c_sci_HashCollisionMapNode.prototype.$classData = $d_sci_HashCollisionMapNode;
/** @constructor */
function $c_sci_HashCollisionSetNode(originalHash, hash, content) {
  this.originalHash$3 = 0;
  this.hash$3 = 0;
  this.content$3 = null;
  this.originalHash$3 = originalHash;
  this.hash$3 = hash;
  this.content$3 = content;
  $m_s_Predef$().require__Z__V((content.length__I() >= 2))
}
$c_sci_HashCollisionSetNode.prototype = new $h_sci_SetNode();
$c_sci_HashCollisionSetNode.prototype.constructor = $c_sci_HashCollisionSetNode;
/** @constructor */
function $h_sci_HashCollisionSetNode() {
  /*<skip>*/
}
$h_sci_HashCollisionSetNode.prototype = $c_sci_HashCollisionSetNode.prototype;
$c_sci_HashCollisionSetNode.prototype.getHash__I__I = (function(index) {
  return this.originalHash$3
});
$c_sci_HashCollisionSetNode.prototype.updated__O__I__I__I__sci_SetNode = (function(element, originalHash, hash, shift) {
  return (this.contains__O__I__I__I__Z(element, originalHash, hash, shift) ? this : new $c_sci_HashCollisionSetNode(originalHash, hash, this.content$3.appended__O__sci_Vector(element)))
});
$c_sci_HashCollisionSetNode.prototype.equals__O__Z = (function(that) {
  if ($is_sci_HashCollisionSetNode(that)) {
    var x2 = $as_sci_HashCollisionSetNode(that);
    if ((this === x2)) {
      return true
    } else {
      if ((this.hash$3 === x2.hash$3)) {
        var this$1 = this.content$3;
        var jsx$2 = this$1.length__I();
        var this$2 = x2.content$3;
        var jsx$1 = (jsx$2 === this$2.length__I())
      } else {
        var jsx$1 = false
      };
      if (jsx$1) {
        var this$3 = this.content$3;
        var res = true;
        var it = this$3.iterator__sc_Iterator();
        while ((res && it.hasNext__Z())) {
          var arg1 = it.next__O();
          var this$4 = x2.content$3;
          res = $f_sc_SeqOps__contains__O__Z(this$4, arg1)
        };
        return res
      } else {
        return false
      }
    }
  } else {
    return false
  }
});
$c_sci_HashCollisionSetNode.prototype.sizePredicate__I = (function() {
  return 2
});
$c_sci_HashCollisionSetNode.prototype.hasNodes__Z = (function() {
  return false
});
$c_sci_HashCollisionSetNode.prototype.foreach__F1__V = (function(f) {
  var this$1 = this.content$3;
  $f_sc_IterableOnceOps__foreach__F1__V(this$1, f)
});
$c_sci_HashCollisionSetNode.prototype.getPayload__I__O = (function(index) {
  return this.content$3.apply__I__O(index)
});
$c_sci_HashCollisionSetNode.prototype.size__I = (function() {
  var this$1 = this.content$3;
  return this$1.length__I()
});
$c_sci_HashCollisionSetNode.prototype.hasPayload__Z = (function() {
  return true
});
$c_sci_HashCollisionSetNode.prototype.getNode__I__sci_Node = (function(index) {
  return this.getNode__I__sci_SetNode(index)
});
$c_sci_HashCollisionSetNode.prototype.getNode__I__sci_SetNode = (function(index) {
  throw new $c_jl_IndexOutOfBoundsException().init___T("No sub-nodes present in hash-collision leaf node.")
});
$c_sci_HashCollisionSetNode.prototype.hashCode__I = (function() {
  throw new $c_jl_UnsupportedOperationException().init___T("Trie nodes do not support hashing.")
});
$c_sci_HashCollisionSetNode.prototype.nodeArity__I = (function() {
  return 0
});
$c_sci_HashCollisionSetNode.prototype.removed__O__I__I__I__sci_SetNode = (function(element, originalHash, hash, shift) {
  if ((!this.contains__O__I__I__I__Z(element, originalHash, hash, shift))) {
    return this
  } else {
    var this$1 = this.content$3;
    $m_sci_Vector$();
    var b = new $c_sci_VectorBuilder();
    var it = this$1.iterator__sc_Iterator();
    while (it.hasNext__Z()) {
      var elem = it.next__O();
      if (($m_sr_BoxesRunTime$().equals__O__O__Z(elem, element) !== true)) {
        b.addOne__O__sci_VectorBuilder(elem)
      }
    };
    var updatedContent = b.result__sci_Vector();
    var x1 = updatedContent.length__I();
    if ((x1 === 1)) {
      var jsx$4 = $m_sci_Node$().bitposFrom__I__I($m_sci_Node$().maskFrom__I__I__I(hash, 0));
      var evidence$2 = $m_s_reflect_ManifestFactory$AnyManifest$();
      if ((updatedContent.length__I() >= 0)) {
        var len = updatedContent.length__I();
        var destination = $newArrayObject($d_O.getArrayOf(), [len]);
        $f_sc_IterableOnceOps__copyToArray__O__I__I(updatedContent, destination, 0);
        var jsx$3 = destination
      } else {
        var jsx$3 = $m_scm_ArrayBuffer$().from__sc_IterableOnce__scm_ArrayBuffer(updatedContent).toArray__s_reflect_ClassTag__O(evidence$2)
      };
      var jsx$2 = $asArrayOf_O(jsx$3, 1);
      var jsx$1 = $m_s_Array$();
      var array = [];
      return new $c_sci_BitmapIndexedSetNode(jsx$4, 0, jsx$2, jsx$1.apply__I__sci_Seq__AI(originalHash, new $c_sjsr_WrappedVarArgs(array)), 1)
    } else {
      return new $c_sci_HashCollisionSetNode(originalHash, hash, updatedContent)
    }
  }
});
$c_sci_HashCollisionSetNode.prototype.contains__O__I__I__I__Z = (function(element, originalHash, hash, shift) {
  if ((this.hash$3 === hash)) {
    var this$1 = this.content$3;
    return $f_sc_SeqOps__contains__O__Z(this$1, element)
  } else {
    return false
  }
});
$c_sci_HashCollisionSetNode.prototype.payloadArity__I = (function() {
  var this$1 = this.content$3;
  return this$1.length__I()
});
function $is_sci_HashCollisionSetNode(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_HashCollisionSetNode)))
}
function $as_sci_HashCollisionSetNode(obj) {
  return (($is_sci_HashCollisionSetNode(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.HashCollisionSetNode"))
}
function $isArrayOf_sci_HashCollisionSetNode(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_HashCollisionSetNode)))
}
function $asArrayOf_sci_HashCollisionSetNode(obj, depth) {
  return (($isArrayOf_sci_HashCollisionSetNode(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.HashCollisionSetNode;", depth))
}
var $d_sci_HashCollisionSetNode = new $TypeData().initClass({
  sci_HashCollisionSetNode: 0
}, false, "scala.collection.immutable.HashCollisionSetNode", {
  sci_HashCollisionSetNode: 1,
  sci_SetNode: 1,
  sci_Node: 1,
  O: 1
});
$c_sci_HashCollisionSetNode.prototype.$classData = $d_sci_HashCollisionSetNode;
/** @constructor */
function $c_sci_Range$() {
  /*<skip>*/
}
$c_sci_Range$.prototype = new $h_O();
$c_sci_Range$.prototype.constructor = $c_sci_Range$;
/** @constructor */
function $h_sci_Range$() {
  /*<skip>*/
}
$h_sci_Range$.prototype = $c_sci_Range$.prototype;
$c_sci_Range$.prototype.scala$collection$immutable$Range$$fail__I__I__I__Z__E = (function(start, end, step, isInclusive) {
  throw new $c_jl_IllegalArgumentException().init___T((this.description__p1__I__I__I__Z__T(start, end, step, isInclusive) + ": seqs cannot contain more than Int.MaxValue elements."))
});
$c_sci_Range$.prototype.description__p1__I__I__I__Z__T = (function(start, end, step, isInclusive) {
  return ((((start + (isInclusive ? " to " : " until ")) + end) + " by ") + step)
});
var $d_sci_Range$ = new $TypeData().initClass({
  sci_Range$: 0
}, false, "scala.collection.immutable.Range$", {
  sci_Range$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_Range$.prototype.$classData = $d_sci_Range$;
var $n_sci_Range$ = (void 0);
function $m_sci_Range$() {
  if ((!$n_sci_Range$)) {
    $n_sci_Range$ = new $c_sci_Range$()
  };
  return $n_sci_Range$
}
/** @constructor */
function $c_scm_StringBuilder$() {
  /*<skip>*/
}
$c_scm_StringBuilder$.prototype = new $h_O();
$c_scm_StringBuilder$.prototype.constructor = $c_scm_StringBuilder$;
/** @constructor */
function $h_scm_StringBuilder$() {
  /*<skip>*/
}
$h_scm_StringBuilder$.prototype = $c_scm_StringBuilder$.prototype;
var $d_scm_StringBuilder$ = new $TypeData().initClass({
  scm_StringBuilder$: 0
}, false, "scala.collection.mutable.StringBuilder$", {
  scm_StringBuilder$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_scm_StringBuilder$.prototype.$classData = $d_scm_StringBuilder$;
var $n_scm_StringBuilder$ = (void 0);
function $m_scm_StringBuilder$() {
  if ((!$n_scm_StringBuilder$)) {
    $n_scm_StringBuilder$ = new $c_scm_StringBuilder$()
  };
  return $n_scm_StringBuilder$
}
/** @constructor */
function $c_sjs_js_Any$() {
  /*<skip>*/
}
$c_sjs_js_Any$.prototype = new $h_O();
$c_sjs_js_Any$.prototype.constructor = $c_sjs_js_Any$;
/** @constructor */
function $h_sjs_js_Any$() {
  /*<skip>*/
}
$h_sjs_js_Any$.prototype = $c_sjs_js_Any$.prototype;
$c_sjs_js_Any$.prototype.fromFunction0__F0__sjs_js_Function0 = (function(f) {
  return (function(f$1) {
    return (function() {
      return f$1.apply__O()
    })
  })(f)
});
$c_sjs_js_Any$.prototype.fromFunction1__F1__sjs_js_Function1 = (function(f) {
  return (function(f$2) {
    return (function(arg1$2) {
      return f$2.apply__O__O(arg1$2)
    })
  })(f)
});
var $d_sjs_js_Any$ = new $TypeData().initClass({
  sjs_js_Any$: 0
}, false, "scala.scalajs.js.Any$", {
  sjs_js_Any$: 1,
  O: 1,
  sjs_js_LowPrioAnyImplicits: 1,
  sjs_js_LowestPrioAnyImplicits: 1
});
$c_sjs_js_Any$.prototype.$classData = $d_sjs_js_Any$;
var $n_sjs_js_Any$ = (void 0);
function $m_sjs_js_Any$() {
  if ((!$n_sjs_js_Any$)) {
    $n_sjs_js_Any$ = new $c_sjs_js_Any$()
  };
  return $n_sjs_js_Any$
}
/** @constructor */
function $c_sjsr_AnonFunction0(f) {
  this.f$2 = null;
  this.f$2 = f
}
$c_sjsr_AnonFunction0.prototype = new $h_sr_AbstractFunction0();
$c_sjsr_AnonFunction0.prototype.constructor = $c_sjsr_AnonFunction0;
/** @constructor */
function $h_sjsr_AnonFunction0() {
  /*<skip>*/
}
$h_sjsr_AnonFunction0.prototype = $c_sjsr_AnonFunction0.prototype;
$c_sjsr_AnonFunction0.prototype.apply__O = (function() {
  return (0, this.f$2)()
});
var $d_sjsr_AnonFunction0 = new $TypeData().initClass({
  sjsr_AnonFunction0: 0
}, false, "scala.scalajs.runtime.AnonFunction0", {
  sjsr_AnonFunction0: 1,
  sr_AbstractFunction0: 1,
  O: 1,
  F0: 1
});
$c_sjsr_AnonFunction0.prototype.$classData = $d_sjsr_AnonFunction0;
/** @constructor */
function $c_sjsr_AnonFunction1(f) {
  this.f$2 = null;
  this.f$2 = f
}
$c_sjsr_AnonFunction1.prototype = new $h_sr_AbstractFunction1();
$c_sjsr_AnonFunction1.prototype.constructor = $c_sjsr_AnonFunction1;
/** @constructor */
function $h_sjsr_AnonFunction1() {
  /*<skip>*/
}
$h_sjsr_AnonFunction1.prototype = $c_sjsr_AnonFunction1.prototype;
$c_sjsr_AnonFunction1.prototype.apply__O__O = (function(arg1) {
  return (0, this.f$2)(arg1)
});
var $d_sjsr_AnonFunction1 = new $TypeData().initClass({
  sjsr_AnonFunction1: 0
}, false, "scala.scalajs.runtime.AnonFunction1", {
  sjsr_AnonFunction1: 1,
  sr_AbstractFunction1: 1,
  O: 1,
  F1: 1
});
$c_sjsr_AnonFunction1.prototype.$classData = $d_sjsr_AnonFunction1;
/** @constructor */
function $c_sjsr_AnonFunction2(f) {
  this.f$2 = null;
  this.f$2 = f
}
$c_sjsr_AnonFunction2.prototype = new $h_sr_AbstractFunction2();
$c_sjsr_AnonFunction2.prototype.constructor = $c_sjsr_AnonFunction2;
/** @constructor */
function $h_sjsr_AnonFunction2() {
  /*<skip>*/
}
$h_sjsr_AnonFunction2.prototype = $c_sjsr_AnonFunction2.prototype;
$c_sjsr_AnonFunction2.prototype.apply__O__O__O = (function(arg1, arg2) {
  return (0, this.f$2)(arg1, arg2)
});
var $d_sjsr_AnonFunction2 = new $TypeData().initClass({
  sjsr_AnonFunction2: 0
}, false, "scala.scalajs.runtime.AnonFunction2", {
  sjsr_AnonFunction2: 1,
  sr_AbstractFunction2: 1,
  O: 1,
  F2: 1
});
$c_sjsr_AnonFunction2.prototype.$classData = $d_sjsr_AnonFunction2;
/** @constructor */
function $c_sjsr_RuntimeLong$() {
  this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 0
}
$c_sjsr_RuntimeLong$.prototype = new $h_O();
$c_sjsr_RuntimeLong$.prototype.constructor = $c_sjsr_RuntimeLong$;
/** @constructor */
function $h_sjsr_RuntimeLong$() {
  /*<skip>*/
}
$h_sjsr_RuntimeLong$.prototype = $c_sjsr_RuntimeLong$.prototype;
$c_sjsr_RuntimeLong$.prototype.toUnsignedString__p1__I__I__T = (function(lo, hi) {
  if ((((-2097152) & hi) === 0)) {
    var this$3 = ((4.294967296E9 * hi) + $uD((lo >>> 0)));
    return ("" + this$3)
  } else {
    return $as_T(this.unsignedDivModHelper__p1__I__I__I__I__I__O(lo, hi, 1000000000, 0, 2))
  }
});
$c_sjsr_RuntimeLong$.prototype.divideImpl__I__I__I__I__I = (function(alo, ahi, blo, bhi) {
  if (((blo | bhi) === 0)) {
    throw new $c_jl_ArithmeticException("/ by zero")
  };
  if ((ahi === (alo >> 31))) {
    if ((bhi === (blo >> 31))) {
      if (((alo === (-2147483648)) && (blo === (-1)))) {
        this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 0;
        return (-2147483648)
      } else {
        var lo = ((alo / blo) | 0);
        this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = (lo >> 31);
        return lo
      }
    } else if (((alo === (-2147483648)) && ((blo === (-2147483648)) && (bhi === 0)))) {
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = (-1);
      return (-1)
    } else {
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 0;
      return 0
    }
  } else {
    if ((ahi < 0)) {
      var lo$1 = ((-alo) | 0);
      var hi = ((alo !== 0) ? (~ahi) : ((-ahi) | 0));
      var aAbs_$_lo$2 = lo$1;
      var aAbs_$_hi$2 = hi
    } else {
      var aAbs_$_lo$2 = alo;
      var aAbs_$_hi$2 = ahi
    };
    if ((bhi < 0)) {
      var lo$2 = ((-blo) | 0);
      var hi$1 = ((blo !== 0) ? (~bhi) : ((-bhi) | 0));
      var bAbs_$_lo$2 = lo$2;
      var bAbs_$_hi$2 = hi$1
    } else {
      var bAbs_$_lo$2 = blo;
      var bAbs_$_hi$2 = bhi
    };
    var absRLo = this.unsigned$und$div__p1__I__I__I__I__I(aAbs_$_lo$2, aAbs_$_hi$2, bAbs_$_lo$2, bAbs_$_hi$2);
    if (((ahi ^ bhi) >= 0)) {
      return absRLo
    } else {
      var hi$2 = this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f;
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = ((absRLo !== 0) ? (~hi$2) : ((-hi$2) | 0));
      return ((-absRLo) | 0)
    }
  }
});
$c_sjsr_RuntimeLong$.prototype.scala$scalajs$runtime$RuntimeLong$$toDouble__I__I__D = (function(lo, hi) {
  if ((hi < 0)) {
    var x = ((lo !== 0) ? (~hi) : ((-hi) | 0));
    var jsx$1 = $uD((x >>> 0));
    var x$1 = ((-lo) | 0);
    return (-((4.294967296E9 * jsx$1) + $uD((x$1 >>> 0))))
  } else {
    return ((4.294967296E9 * hi) + $uD((lo >>> 0)))
  }
});
$c_sjsr_RuntimeLong$.prototype.fromDouble__D__sjsr_RuntimeLong = (function(value) {
  var lo = this.scala$scalajs$runtime$RuntimeLong$$fromDoubleImpl__D__I(value);
  return new $c_sjsr_RuntimeLong(lo, this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f)
});
$c_sjsr_RuntimeLong$.prototype.scala$scalajs$runtime$RuntimeLong$$fromDoubleImpl__D__I = (function(value) {
  if ((value < (-9.223372036854776E18))) {
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = (-2147483648);
    return 0
  } else if ((value >= 9.223372036854776E18)) {
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 2147483647;
    return (-1)
  } else {
    var rawLo = $uI((value | 0));
    var x = (value / 4.294967296E9);
    var rawHi = $uI((x | 0));
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = (((value < 0.0) && (rawLo !== 0)) ? (((-1) + rawHi) | 0) : rawHi);
    return rawLo
  }
});
$c_sjsr_RuntimeLong$.prototype.unsigned$und$div__p1__I__I__I__I__I = (function(alo, ahi, blo, bhi) {
  if ((((-2097152) & ahi) === 0)) {
    if ((((-2097152) & bhi) === 0)) {
      var aDouble = ((4.294967296E9 * ahi) + $uD((alo >>> 0)));
      var bDouble = ((4.294967296E9 * bhi) + $uD((blo >>> 0)));
      var rDouble = (aDouble / bDouble);
      var x = (rDouble / 4.294967296E9);
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = $uI((x | 0));
      return $uI((rDouble | 0))
    } else {
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 0;
      return 0
    }
  } else if (((bhi === 0) && ((blo & (((-1) + blo) | 0)) === 0))) {
    var pow = ((31 - $clz32(blo)) | 0);
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = ((ahi >>> pow) | 0);
    return (((alo >>> pow) | 0) | ((ahi << 1) << ((31 - pow) | 0)))
  } else if (((blo === 0) && ((bhi & (((-1) + bhi) | 0)) === 0))) {
    var pow$2 = ((31 - $clz32(bhi)) | 0);
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 0;
    return ((ahi >>> pow$2) | 0)
  } else {
    return $uI(this.unsignedDivModHelper__p1__I__I__I__I__I__O(alo, ahi, blo, bhi, 0))
  }
});
$c_sjsr_RuntimeLong$.prototype.scala$scalajs$runtime$RuntimeLong$$toString__I__I__T = (function(lo, hi) {
  return ((hi === (lo >> 31)) ? ("" + lo) : ((hi < 0) ? ("-" + this.toUnsignedString__p1__I__I__T(((-lo) | 0), ((lo !== 0) ? (~hi) : ((-hi) | 0)))) : this.toUnsignedString__p1__I__I__T(lo, hi)))
});
$c_sjsr_RuntimeLong$.prototype.fromInt__I__sjsr_RuntimeLong = (function(value) {
  return new $c_sjsr_RuntimeLong(value, (value >> 31))
});
$c_sjsr_RuntimeLong$.prototype.scala$scalajs$runtime$RuntimeLong$$compare__I__I__I__I__I = (function(alo, ahi, blo, bhi) {
  return ((ahi === bhi) ? ((alo === blo) ? 0 : ((((-2147483648) ^ alo) < ((-2147483648) ^ blo)) ? (-1) : 1)) : ((ahi < bhi) ? (-1) : 1))
});
$c_sjsr_RuntimeLong$.prototype.unsignedDivModHelper__p1__I__I__I__I__I__O = (function(alo, ahi, blo, bhi, ask) {
  var shift = ((((bhi !== 0) ? $clz32(bhi) : ((32 + $clz32(blo)) | 0)) - ((ahi !== 0) ? $clz32(ahi) : ((32 + $clz32(alo)) | 0))) | 0);
  var n = shift;
  var lo = (((32 & n) === 0) ? (blo << n) : 0);
  var hi = (((32 & n) === 0) ? (((((blo >>> 1) | 0) >>> ((31 - n) | 0)) | 0) | (bhi << n)) : (blo << n));
  var bShiftLo = lo;
  var bShiftHi = hi;
  var remLo = alo;
  var remHi = ahi;
  var quotLo = 0;
  var quotHi = 0;
  while (((shift >= 0) && (((-2097152) & remHi) !== 0))) {
    var alo$1 = remLo;
    var ahi$1 = remHi;
    var blo$1 = bShiftLo;
    var bhi$1 = bShiftHi;
    if (((ahi$1 === bhi$1) ? (((-2147483648) ^ alo$1) >= ((-2147483648) ^ blo$1)) : (((-2147483648) ^ ahi$1) >= ((-2147483648) ^ bhi$1)))) {
      var lo$1 = remLo;
      var hi$1 = remHi;
      var lo$2 = bShiftLo;
      var hi$2 = bShiftHi;
      var lo$3 = ((lo$1 - lo$2) | 0);
      var hi$3 = ((((-2147483648) ^ lo$3) > ((-2147483648) ^ lo$1)) ? (((-1) + ((hi$1 - hi$2) | 0)) | 0) : ((hi$1 - hi$2) | 0));
      remLo = lo$3;
      remHi = hi$3;
      if ((shift < 32)) {
        quotLo = (quotLo | (1 << shift))
      } else {
        quotHi = (quotHi | (1 << shift))
      }
    };
    shift = (((-1) + shift) | 0);
    var lo$4 = bShiftLo;
    var hi$4 = bShiftHi;
    var lo$5 = (((lo$4 >>> 1) | 0) | (hi$4 << 31));
    var hi$5 = ((hi$4 >>> 1) | 0);
    bShiftLo = lo$5;
    bShiftHi = hi$5
  };
  var alo$2 = remLo;
  var ahi$2 = remHi;
  if (((ahi$2 === bhi) ? (((-2147483648) ^ alo$2) >= ((-2147483648) ^ blo)) : (((-2147483648) ^ ahi$2) >= ((-2147483648) ^ bhi)))) {
    var lo$6 = remLo;
    var hi$6 = remHi;
    var remDouble = ((4.294967296E9 * hi$6) + $uD((lo$6 >>> 0)));
    var bDouble = ((4.294967296E9 * bhi) + $uD((blo >>> 0)));
    if ((ask !== 1)) {
      var x = (remDouble / bDouble);
      var lo$7 = $uI((x | 0));
      var x$1 = (x / 4.294967296E9);
      var hi$7 = $uI((x$1 | 0));
      var lo$8 = quotLo;
      var hi$8 = quotHi;
      var lo$9 = ((lo$8 + lo$7) | 0);
      var hi$9 = ((((-2147483648) ^ lo$9) < ((-2147483648) ^ lo$8)) ? ((1 + ((hi$8 + hi$7) | 0)) | 0) : ((hi$8 + hi$7) | 0));
      quotLo = lo$9;
      quotHi = hi$9
    };
    if ((ask !== 0)) {
      var rem_mod_bDouble = (remDouble % bDouble);
      remLo = $uI((rem_mod_bDouble | 0));
      var x$2 = (rem_mod_bDouble / 4.294967296E9);
      remHi = $uI((x$2 | 0))
    }
  };
  if ((ask === 0)) {
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = quotHi;
    return quotLo
  } else if ((ask === 1)) {
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = remHi;
    return remLo
  } else {
    var lo$10 = quotLo;
    var hi$10 = quotHi;
    var quot = ((4.294967296E9 * hi$10) + $uD((lo$10 >>> 0)));
    var this$13 = remLo;
    var remStr = ("" + this$13);
    var start = $uI(remStr.length);
    return ((("" + quot) + $as_T("000000000".substring(start))) + remStr)
  }
});
$c_sjsr_RuntimeLong$.prototype.remainderImpl__I__I__I__I__I = (function(alo, ahi, blo, bhi) {
  if (((blo | bhi) === 0)) {
    throw new $c_jl_ArithmeticException("/ by zero")
  };
  if ((ahi === (alo >> 31))) {
    if ((bhi === (blo >> 31))) {
      if ((blo !== (-1))) {
        var lo = ((alo % blo) | 0);
        this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = (lo >> 31);
        return lo
      } else {
        this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 0;
        return 0
      }
    } else if (((alo === (-2147483648)) && ((blo === (-2147483648)) && (bhi === 0)))) {
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 0;
      return 0
    } else {
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = ahi;
      return alo
    }
  } else {
    if ((ahi < 0)) {
      var lo$1 = ((-alo) | 0);
      var hi = ((alo !== 0) ? (~ahi) : ((-ahi) | 0));
      var aAbs_$_lo$2 = lo$1;
      var aAbs_$_hi$2 = hi
    } else {
      var aAbs_$_lo$2 = alo;
      var aAbs_$_hi$2 = ahi
    };
    if ((bhi < 0)) {
      var lo$2 = ((-blo) | 0);
      var hi$1 = ((blo !== 0) ? (~bhi) : ((-bhi) | 0));
      var bAbs_$_lo$2 = lo$2;
      var bAbs_$_hi$2 = hi$1
    } else {
      var bAbs_$_lo$2 = blo;
      var bAbs_$_hi$2 = bhi
    };
    var absRLo = this.unsigned$und$percent__p1__I__I__I__I__I(aAbs_$_lo$2, aAbs_$_hi$2, bAbs_$_lo$2, bAbs_$_hi$2);
    if ((ahi < 0)) {
      var hi$2 = this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f;
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = ((absRLo !== 0) ? (~hi$2) : ((-hi$2) | 0));
      return ((-absRLo) | 0)
    } else {
      return absRLo
    }
  }
});
$c_sjsr_RuntimeLong$.prototype.unsigned$und$percent__p1__I__I__I__I__I = (function(alo, ahi, blo, bhi) {
  if ((((-2097152) & ahi) === 0)) {
    if ((((-2097152) & bhi) === 0)) {
      var aDouble = ((4.294967296E9 * ahi) + $uD((alo >>> 0)));
      var bDouble = ((4.294967296E9 * bhi) + $uD((blo >>> 0)));
      var rDouble = (aDouble % bDouble);
      var x = (rDouble / 4.294967296E9);
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = $uI((x | 0));
      return $uI((rDouble | 0))
    } else {
      this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = ahi;
      return alo
    }
  } else if (((bhi === 0) && ((blo & (((-1) + blo) | 0)) === 0))) {
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = 0;
    return (alo & (((-1) + blo) | 0))
  } else if (((blo === 0) && ((bhi & (((-1) + bhi) | 0)) === 0))) {
    this.scala$scalajs$runtime$RuntimeLong$$hiReturn$f = (ahi & (((-1) + bhi) | 0));
    return alo
  } else {
    return $uI(this.unsignedDivModHelper__p1__I__I__I__I__I__O(alo, ahi, blo, bhi, 1))
  }
});
var $d_sjsr_RuntimeLong$ = new $TypeData().initClass({
  sjsr_RuntimeLong$: 0
}, false, "scala.scalajs.runtime.RuntimeLong$", {
  sjsr_RuntimeLong$: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sjsr_RuntimeLong$.prototype.$classData = $d_sjsr_RuntimeLong$;
var $n_sjsr_RuntimeLong$ = (void 0);
function $m_sjsr_RuntimeLong$() {
  if ((!$n_sjsr_RuntimeLong$)) {
    $n_sjsr_RuntimeLong$ = new $c_sjsr_RuntimeLong$()
  };
  return $n_sjsr_RuntimeLong$
}
/** @constructor */
function $c_sr_LazyRef() {
  this.$$undinitialized$1 = false;
  this.$$undvalue$1 = null
}
$c_sr_LazyRef.prototype = new $h_O();
$c_sr_LazyRef.prototype.constructor = $c_sr_LazyRef;
/** @constructor */
function $h_sr_LazyRef() {
  /*<skip>*/
}
$h_sr_LazyRef.prototype = $c_sr_LazyRef.prototype;
$c_sr_LazyRef.prototype.toString__T = (function() {
  return ("LazyRef " + (this.$$undinitialized$1 ? ("of: " + this.$$undvalue$1) : "thunk"))
});
$c_sr_LazyRef.prototype.initialize__O__O = (function(value) {
  this.$$undvalue$1 = value;
  this.$$undinitialized$1 = true;
  return value
});
var $d_sr_LazyRef = new $TypeData().initClass({
  sr_LazyRef: 0
}, false, "scala.runtime.LazyRef", {
  sr_LazyRef: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sr_LazyRef.prototype.$classData = $d_sr_LazyRef;
var $d_sr_Nothing$ = new $TypeData().initClass({
  sr_Nothing$: 0
}, false, "scala.runtime.Nothing$", {
  sr_Nothing$: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
/** @constructor */
function $c_Ljava_io_OutputStream() {
  /*<skip>*/
}
$c_Ljava_io_OutputStream.prototype = new $h_O();
$c_Ljava_io_OutputStream.prototype.constructor = $c_Ljava_io_OutputStream;
/** @constructor */
function $h_Ljava_io_OutputStream() {
  /*<skip>*/
}
$h_Ljava_io_OutputStream.prototype = $c_Ljava_io_OutputStream.prototype;
function $f_T__equals__O__Z($thiz, that) {
  return ($thiz === that)
}
function $f_T__toString__T($thiz) {
  return $thiz
}
function $f_T__hashCode__I($thiz) {
  var res = 0;
  var mul = 1;
  var i = (((-1) + $uI($thiz.length)) | 0);
  while ((i >= 0)) {
    var jsx$1 = res;
    var index = i;
    res = ((jsx$1 + $imul((65535 & $uI($thiz.charCodeAt(index))), mul)) | 0);
    mul = $imul(31, mul);
    i = (((-1) + i) | 0)
  };
  return res
}
function $is_T(obj) {
  return ((typeof obj) === "string")
}
function $as_T(obj) {
  return (($is_T(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "java.lang.String"))
}
function $isArrayOf_T(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.T)))
}
function $asArrayOf_T(obj, depth) {
  return (($isArrayOf_T(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.String;", depth))
}
var $d_T = new $TypeData().initClass({
  T: 0
}, false, "java.lang.String", {
  T: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1,
  jl_CharSequence: 1
}, (void 0), (void 0), $is_T);
/** @constructor */
function $c_jl_AssertionError(detailMessage) {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null;
  var message = ("" + detailMessage);
  if ($is_jl_Throwable(detailMessage)) {
    var x2 = $as_jl_Throwable(detailMessage);
    var cause = x2
  } else {
    var cause = null
  };
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, message, cause, true, true)
}
$c_jl_AssertionError.prototype = new $h_jl_Error();
$c_jl_AssertionError.prototype.constructor = $c_jl_AssertionError;
/** @constructor */
function $h_jl_AssertionError() {
  /*<skip>*/
}
$h_jl_AssertionError.prototype = $c_jl_AssertionError.prototype;
var $d_jl_AssertionError = new $TypeData().initClass({
  jl_AssertionError: 0
}, false, "java.lang.AssertionError", {
  jl_AssertionError: 1,
  jl_Error: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_AssertionError.prototype.$classData = $d_jl_AssertionError;
function $f_jl_Byte__equals__O__Z($thiz, that) {
  return ($thiz === that)
}
function $f_jl_Byte__toString__T($thiz) {
  var b = $uB($thiz);
  return ("" + b)
}
function $f_jl_Byte__hashCode__I($thiz) {
  return $uB($thiz)
}
var $d_jl_Byte = new $TypeData().initClass({
  jl_Byte: 0
}, false, "java.lang.Byte", {
  jl_Byte: 1,
  jl_Number: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
}, (void 0), (void 0), (function(x) {
  return $isByte(x)
}));
/** @constructor */
function $c_jl_CloneNotSupportedException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null;
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true)
}
$c_jl_CloneNotSupportedException.prototype = new $h_jl_Exception();
$c_jl_CloneNotSupportedException.prototype.constructor = $c_jl_CloneNotSupportedException;
/** @constructor */
function $h_jl_CloneNotSupportedException() {
  /*<skip>*/
}
$h_jl_CloneNotSupportedException.prototype = $c_jl_CloneNotSupportedException.prototype;
var $d_jl_CloneNotSupportedException = new $TypeData().initClass({
  jl_CloneNotSupportedException: 0
}, false, "java.lang.CloneNotSupportedException", {
  jl_CloneNotSupportedException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_CloneNotSupportedException.prototype.$classData = $d_jl_CloneNotSupportedException;
function $f_jl_Double__equals__O__Z($thiz, that) {
  return (($thiz === that) ? (($uD($thiz) !== 0.0) || ((1.0 / $uD($thiz)) === (1.0 / $uD(that)))) : (($thiz !== $thiz) && (that !== that)))
}
function $f_jl_Double__toString__T($thiz) {
  var d = $uD($thiz);
  return ("" + d)
}
function $f_jl_Double__hashCode__I($thiz) {
  var value = $uD($thiz);
  return $m_jl_FloatingPointBits$().numberHashCode__D__I(value)
}
function $isArrayOf_jl_Double(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.jl_Double)))
}
function $asArrayOf_jl_Double(obj, depth) {
  return (($isArrayOf_jl_Double(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.Double;", depth))
}
var $d_jl_Double = new $TypeData().initClass({
  jl_Double: 0
}, false, "java.lang.Double", {
  jl_Double: 1,
  jl_Number: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
}, (void 0), (void 0), (function(x) {
  return ((typeof x) === "number")
}));
function $f_jl_Float__equals__O__Z($thiz, that) {
  return $f_jl_Double__equals__O__Z($uF($thiz), that)
}
function $f_jl_Float__toString__T($thiz) {
  var f = $uF($thiz);
  return ("" + f)
}
function $f_jl_Float__hashCode__I($thiz) {
  var value = $uF($thiz);
  return $m_jl_FloatingPointBits$().numberHashCode__D__I(value)
}
var $d_jl_Float = new $TypeData().initClass({
  jl_Float: 0
}, false, "java.lang.Float", {
  jl_Float: 1,
  jl_Number: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
}, (void 0), (void 0), (function(x) {
  return $isFloat(x)
}));
function $f_jl_Integer__equals__O__Z($thiz, that) {
  return ($thiz === that)
}
function $f_jl_Integer__toString__T($thiz) {
  var i = $uI($thiz);
  return ("" + i)
}
function $f_jl_Integer__hashCode__I($thiz) {
  return $uI($thiz)
}
var $d_jl_Integer = new $TypeData().initClass({
  jl_Integer: 0
}, false, "java.lang.Integer", {
  jl_Integer: 1,
  jl_Number: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
}, (void 0), (void 0), (function(x) {
  return $isInt(x)
}));
function $f_jl_Long__equals__O__Z($thiz, that) {
  if ($is_sjsr_RuntimeLong(that)) {
    var x2 = $as_sjsr_RuntimeLong(that);
    var t = $uJ($thiz);
    var lo = t.lo$2;
    var hi = t.hi$2;
    var b = $uJ(x2);
    return ((lo === b.lo$2) && (hi === b.hi$2))
  } else {
    return false
  }
}
function $f_jl_Long__toString__T($thiz) {
  var t = $uJ($thiz);
  var lo = t.lo$2;
  var hi = t.hi$2;
  return $m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toString__I__I__T(lo, hi)
}
function $f_jl_Long__hashCode__I($thiz) {
  var t = $uJ($thiz);
  var lo = t.lo$2;
  var hi = t.hi$2;
  return (lo ^ hi)
}
function $isArrayOf_jl_Long(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.jl_Long)))
}
function $asArrayOf_jl_Long(obj, depth) {
  return (($isArrayOf_jl_Long(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.Long;", depth))
}
var $d_jl_Long = new $TypeData().initClass({
  jl_Long: 0
}, false, "java.lang.Long", {
  jl_Long: 1,
  jl_Number: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
}, (void 0), (void 0), (function(x) {
  return $is_sjsr_RuntimeLong(x)
}));
/** @constructor */
function $c_jl_RuntimeException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_RuntimeException.prototype = new $h_jl_Exception();
$c_jl_RuntimeException.prototype.constructor = $c_jl_RuntimeException;
/** @constructor */
function $h_jl_RuntimeException() {
  /*<skip>*/
}
$h_jl_RuntimeException.prototype = $c_jl_RuntimeException.prototype;
function $f_jl_Short__equals__O__Z($thiz, that) {
  return ($thiz === that)
}
function $f_jl_Short__toString__T($thiz) {
  var s = $uS($thiz);
  return ("" + s)
}
function $f_jl_Short__hashCode__I($thiz) {
  return $uS($thiz)
}
var $d_jl_Short = new $TypeData().initClass({
  jl_Short: 0
}, false, "java.lang.Short", {
  jl_Short: 1,
  jl_Number: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
}, (void 0), (void 0), (function(x) {
  return $isShort(x)
}));
/** @constructor */
function $c_jl_StringBuilder() {
  this.java$lang$StringBuilder$$content$f = null
}
$c_jl_StringBuilder.prototype = new $h_O();
$c_jl_StringBuilder.prototype.constructor = $c_jl_StringBuilder;
/** @constructor */
function $h_jl_StringBuilder() {
  /*<skip>*/
}
$h_jl_StringBuilder.prototype = $c_jl_StringBuilder.prototype;
$c_jl_StringBuilder.prototype.init___ = (function() {
  this.java$lang$StringBuilder$$content$f = "";
  return this
});
$c_jl_StringBuilder.prototype.toString__T = (function() {
  return this.java$lang$StringBuilder$$content$f
});
$c_jl_StringBuilder.prototype.length__I = (function() {
  var this$1 = this.java$lang$StringBuilder$$content$f;
  return $uI(this$1.length)
});
$c_jl_StringBuilder.prototype.init___T = (function(str) {
  $c_jl_StringBuilder.prototype.init___.call(this);
  if ((str === null)) {
    throw new $c_jl_NullPointerException()
  };
  this.java$lang$StringBuilder$$content$f = str;
  return this
});
$c_jl_StringBuilder.prototype.charAt__I__C = (function(index) {
  var this$1 = this.java$lang$StringBuilder$$content$f;
  return (65535 & $uI(this$1.charCodeAt(index)))
});
$c_jl_StringBuilder.prototype.append__AC__jl_StringBuilder = (function(str) {
  var this$1 = $m_jl_String$();
  var count = str.u.length;
  var str$1 = this$1.$new__AC__I__I__T(str, 0, count);
  this.java$lang$StringBuilder$$content$f = (("" + this.java$lang$StringBuilder$$content$f) + str$1);
  return this
});
var $d_jl_StringBuilder = new $TypeData().initClass({
  jl_StringBuilder: 0
}, false, "java.lang.StringBuilder", {
  jl_StringBuilder: 1,
  O: 1,
  jl_CharSequence: 1,
  jl_Appendable: 1,
  Ljava_io_Serializable: 1
});
$c_jl_StringBuilder.prototype.$classData = $d_jl_StringBuilder;
/** @constructor */
function $c_jl_VirtualMachineError() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_VirtualMachineError.prototype = new $h_jl_Error();
$c_jl_VirtualMachineError.prototype.constructor = $c_jl_VirtualMachineError;
/** @constructor */
function $h_jl_VirtualMachineError() {
  /*<skip>*/
}
$h_jl_VirtualMachineError.prototype = $c_jl_VirtualMachineError.prototype;
/** @constructor */
function $c_s_Predef$$less$colon$less() {
  /*<skip>*/
}
$c_s_Predef$$less$colon$less.prototype = new $h_O();
$c_s_Predef$$less$colon$less.prototype.constructor = $c_s_Predef$$less$colon$less;
/** @constructor */
function $h_s_Predef$$less$colon$less() {
  /*<skip>*/
}
$h_s_Predef$$less$colon$less.prototype = $c_s_Predef$$less$colon$less.prototype;
/** @constructor */
function $c_s_math_Equiv$() {
  /*<skip>*/
}
$c_s_math_Equiv$.prototype = new $h_O();
$c_s_math_Equiv$.prototype.constructor = $c_s_math_Equiv$;
/** @constructor */
function $h_s_math_Equiv$() {
  /*<skip>*/
}
$h_s_math_Equiv$.prototype = $c_s_math_Equiv$.prototype;
var $d_s_math_Equiv$ = new $TypeData().initClass({
  s_math_Equiv$: 0
}, false, "scala.math.Equiv$", {
  s_math_Equiv$: 1,
  O: 1,
  s_math_LowPriorityEquiv: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_math_Equiv$.prototype.$classData = $d_s_math_Equiv$;
var $n_s_math_Equiv$ = (void 0);
function $m_s_math_Equiv$() {
  if ((!$n_s_math_Equiv$)) {
    $n_s_math_Equiv$ = new $c_s_math_Equiv$()
  };
  return $n_s_math_Equiv$
}
/** @constructor */
function $c_s_math_Ordering$() {
  /*<skip>*/
}
$c_s_math_Ordering$.prototype = new $h_O();
$c_s_math_Ordering$.prototype.constructor = $c_s_math_Ordering$;
/** @constructor */
function $h_s_math_Ordering$() {
  /*<skip>*/
}
$h_s_math_Ordering$.prototype = $c_s_math_Ordering$.prototype;
var $d_s_math_Ordering$ = new $TypeData().initClass({
  s_math_Ordering$: 0
}, false, "scala.math.Ordering$", {
  s_math_Ordering$: 1,
  O: 1,
  s_math_LowPriorityOrderingImplicits: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_math_Ordering$.prototype.$classData = $d_s_math_Ordering$;
var $n_s_math_Ordering$ = (void 0);
function $m_s_math_Ordering$() {
  if ((!$n_s_math_Ordering$)) {
    $n_s_math_Ordering$ = new $c_s_math_Ordering$()
  };
  return $n_s_math_Ordering$
}
/** @constructor */
function $c_s_reflect_NoManifest$() {
  /*<skip>*/
}
$c_s_reflect_NoManifest$.prototype = new $h_O();
$c_s_reflect_NoManifest$.prototype.constructor = $c_s_reflect_NoManifest$;
/** @constructor */
function $h_s_reflect_NoManifest$() {
  /*<skip>*/
}
$h_s_reflect_NoManifest$.prototype = $c_s_reflect_NoManifest$.prototype;
$c_s_reflect_NoManifest$.prototype.toString__T = (function() {
  return "<?>"
});
var $d_s_reflect_NoManifest$ = new $TypeData().initClass({
  s_reflect_NoManifest$: 0
}, false, "scala.reflect.NoManifest$", {
  s_reflect_NoManifest$: 1,
  O: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_reflect_NoManifest$.prototype.$classData = $d_s_reflect_NoManifest$;
var $n_s_reflect_NoManifest$ = (void 0);
function $m_s_reflect_NoManifest$() {
  if ((!$n_s_reflect_NoManifest$)) {
    $n_s_reflect_NoManifest$ = new $c_s_reflect_NoManifest$()
  };
  return $n_s_reflect_NoManifest$
}
/** @constructor */
function $c_s_util_Random$() {
  this.self$1 = null;
  $c_s_util_Random.prototype.init___ju_Random.call(this, new $c_ju_Random().init___())
}
$c_s_util_Random$.prototype = new $h_s_util_Random();
$c_s_util_Random$.prototype.constructor = $c_s_util_Random$;
/** @constructor */
function $h_s_util_Random$() {
  /*<skip>*/
}
$h_s_util_Random$.prototype = $c_s_util_Random$.prototype;
var $d_s_util_Random$ = new $TypeData().initClass({
  s_util_Random$: 0
}, false, "scala.util.Random$", {
  s_util_Random$: 1,
  s_util_Random: 1,
  O: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_util_Random$.prototype.$classData = $d_s_util_Random$;
var $n_s_util_Random$ = (void 0);
function $m_s_util_Random$() {
  if ((!$n_s_util_Random$)) {
    $n_s_util_Random$ = new $c_s_util_Random$()
  };
  return $n_s_util_Random$
}
/** @constructor */
function $c_sc_AbstractIterator() {
  /*<skip>*/
}
$c_sc_AbstractIterator.prototype = new $h_O();
$c_sc_AbstractIterator.prototype.constructor = $c_sc_AbstractIterator;
/** @constructor */
function $h_sc_AbstractIterator() {
  /*<skip>*/
}
$h_sc_AbstractIterator.prototype = $c_sc_AbstractIterator.prototype;
$c_sc_AbstractIterator.prototype.concat__F0__sc_Iterator = (function(xs) {
  return $f_sc_Iterator__concat__F0__sc_Iterator(this, xs)
});
$c_sc_AbstractIterator.prototype.isEmpty__Z = (function() {
  return (!this.hasNext__Z())
});
$c_sc_AbstractIterator.prototype.toString__T = (function() {
  return "<iterator>"
});
$c_sc_AbstractIterator.prototype.foreach__F1__V = (function(f) {
  $f_sc_IterableOnceOps__foreach__F1__V(this, f)
});
$c_sc_AbstractIterator.prototype.sliceIterator__I__I__sc_Iterator = (function(from, until) {
  return $f_sc_Iterator__sliceIterator__I__I__sc_Iterator(this, from, until)
});
$c_sc_AbstractIterator.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_IterableOnceOps__foldLeft__O__F2__O(this, z, op)
});
$c_sc_AbstractIterator.prototype.copyToArray__O__I__I = (function(xs, start) {
  return $f_sc_IterableOnceOps__copyToArray__O__I__I(this, xs, start)
});
$c_sc_AbstractIterator.prototype.iterator__sc_Iterator = (function() {
  return this
});
$c_sc_AbstractIterator.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(b, start, sep, end) {
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, b, start, sep, end)
});
$c_sc_AbstractIterator.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return $m_sci_Map$().from__sc_IterableOnce__sci_Map(this)
});
$c_sc_AbstractIterator.prototype.sum__s_math_Numeric__O = (function(num) {
  return $f_sc_IterableOnceOps__sum__s_math_Numeric__O(this, num)
});
$c_sc_AbstractIterator.prototype.knownSize__I = (function() {
  return (-1)
});
function $f_sc_IndexedSeqOps__take__I__O($thiz, n) {
  return $thiz.fromSpecific__sc_IterableOnce__O(new $c_sc_IndexedSeqView$Take($thiz, n))
}
function $f_sc_IndexedSeqOps__drop__I__O($thiz, n) {
  return $thiz.fromSpecific__sc_IterableOnce__O(new $c_sc_IndexedSeqView$Drop($thiz, n))
}
function $f_sc_IndexedSeqOps__map__F1__O($thiz, f) {
  return $thiz.iterableFactory__sc_IterableFactory().from__sc_IterableOnce__O(new $c_sc_IndexedSeqView$Map($thiz, f))
}
/** @constructor */
function $c_sc_IterableFactory$Delegate() {
  this.delegate$1 = null
}
$c_sc_IterableFactory$Delegate.prototype = new $h_O();
$c_sc_IterableFactory$Delegate.prototype.constructor = $c_sc_IterableFactory$Delegate;
/** @constructor */
function $h_sc_IterableFactory$Delegate() {
  /*<skip>*/
}
$h_sc_IterableFactory$Delegate.prototype = $c_sc_IterableFactory$Delegate.prototype;
$c_sc_IterableFactory$Delegate.prototype.init___sc_IterableFactory = (function(delegate) {
  this.delegate$1 = delegate;
  return this
});
$c_sc_IterableFactory$Delegate.prototype.from__sc_IterableOnce__O = (function(it) {
  return this.delegate$1.from__sc_IterableOnce__O(it)
});
$c_sc_IterableFactory$Delegate.prototype.newBuilder__scm_Builder = (function() {
  return this.delegate$1.newBuilder__scm_Builder()
});
/** @constructor */
function $c_sc_Iterator$() {
  this.scala$collection$Iterator$$$undempty$f = null;
  $n_sc_Iterator$ = this;
  this.scala$collection$Iterator$$$undempty$f = new $c_sc_Iterator$$anon$18()
}
$c_sc_Iterator$.prototype = new $h_O();
$c_sc_Iterator$.prototype.constructor = $c_sc_Iterator$;
/** @constructor */
function $h_sc_Iterator$() {
  /*<skip>*/
}
$h_sc_Iterator$.prototype = $c_sc_Iterator$.prototype;
$c_sc_Iterator$.prototype.from__sc_IterableOnce__O = (function(source) {
  return source.iterator__sc_Iterator()
});
$c_sc_Iterator$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sc_Iterator$$anon$20()
});
var $d_sc_Iterator$ = new $TypeData().initClass({
  sc_Iterator$: 0
}, false, "scala.collection.Iterator$", {
  sc_Iterator$: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sc_Iterator$.prototype.$classData = $d_sc_Iterator$;
var $n_sc_Iterator$ = (void 0);
function $m_sc_Iterator$() {
  if ((!$n_sc_Iterator$)) {
    $n_sc_Iterator$ = new $c_sc_Iterator$()
  };
  return $n_sc_Iterator$
}
function $f_sc_LinearSeqOps__linearSeqEq$1__psc_LinearSeqOps__sc_LinearSeq__sc_LinearSeq__Z($thiz, a, b) {
  while (true) {
    if ((a === b)) {
      return true
    } else {
      var this$1 = a;
      if ((!this$1.isEmpty__Z())) {
        var this$2 = b;
        var jsx$1 = (!this$2.isEmpty__Z())
      } else {
        var jsx$1 = false
      };
      if ((jsx$1 && $m_sr_BoxesRunTime$().equals__O__O__Z(a.head__O(), b.head__O()))) {
        var temp$a = $as_sc_LinearSeq(a.tail__O());
        var temp$b = $as_sc_LinearSeq(b.tail__O());
        a = temp$a;
        b = temp$b
      } else {
        return (a.isEmpty__Z() && b.isEmpty__Z())
      }
    }
  }
}
function $f_sc_LinearSeqOps__exists__F1__Z($thiz, p) {
  var these = $as_sc_LinearSeq($thiz);
  while ((!these.isEmpty__Z())) {
    if ($uZ(p.apply__O__O(these.head__O()))) {
      return true
    };
    these = $as_sc_LinearSeq(these.tail__O())
  };
  return false
}
function $f_sc_LinearSeqOps__apply__I__O($thiz, n) {
  if ((n < 0)) {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + n))
  };
  var skipped = $as_sc_LinearSeq($thiz.drop__I__O(n));
  if (skipped.isEmpty__Z()) {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + n))
  };
  return skipped.head__O()
}
function $f_sc_LinearSeqOps__lengthCompare__I__I($thiz, len) {
  if ((len < 0)) {
    return 1
  } else {
    var i = 0;
    var xs = $as_sc_LinearSeq($thiz);
    return $f_sc_LinearSeqOps__loop$1__psc_LinearSeqOps__I__sc_LinearSeq__I__I($thiz, i, xs, len)
  }
}
function $f_sc_LinearSeqOps__sameElements__sc_IterableOnce__Z($thiz, that) {
  if ($is_sc_LinearSeq(that)) {
    var x2 = $as_sc_LinearSeq(that);
    var a = $as_sc_LinearSeq($thiz);
    var b = x2;
    return $f_sc_LinearSeqOps__linearSeqEq$1__psc_LinearSeqOps__sc_LinearSeq__sc_LinearSeq__Z($thiz, a, b)
  } else {
    return $f_sc_SeqOps__sameElements__sc_IterableOnce__Z($thiz, that)
  }
}
function $f_sc_LinearSeqOps__loop$1__psc_LinearSeqOps__I__sc_LinearSeq__I__I($thiz, i, xs, len$1) {
  while (true) {
    if ((i === len$1)) {
      return (xs.isEmpty__Z() ? 0 : 1)
    } else if (xs.isEmpty__Z()) {
      return (-1)
    } else {
      var temp$i = ((1 + i) | 0);
      var temp$xs = $as_sc_LinearSeq(xs.tail__O());
      i = temp$i;
      xs = temp$xs
    }
  }
}
function $f_sc_LinearSeqOps__foldLeft__O__F2__O($thiz, z, op) {
  var acc = z;
  var these = $as_sc_LinearSeq($thiz);
  while ((!these.isEmpty__Z())) {
    acc = op.apply__O__O__O(acc, these.head__O());
    these = $as_sc_LinearSeq(these.tail__O())
  };
  return acc
}
function $f_sc_LinearSeqOps__length__I($thiz) {
  var these = $thiz;
  var len = 0;
  while ((!these.isEmpty__Z())) {
    len = ((1 + len) | 0);
    these = $as_sc_Iterable(these.tail__O())
  };
  return len
}
/** @constructor */
function $c_sc_MapFactory$Delegate() {
  this.delegate$1 = null
}
$c_sc_MapFactory$Delegate.prototype = new $h_O();
$c_sc_MapFactory$Delegate.prototype.constructor = $c_sc_MapFactory$Delegate;
/** @constructor */
function $h_sc_MapFactory$Delegate() {
  /*<skip>*/
}
$h_sc_MapFactory$Delegate.prototype = $c_sc_MapFactory$Delegate.prototype;
$c_sc_MapFactory$Delegate.prototype.from__sc_IterableOnce__O = (function(it) {
  return this.delegate$1.from__sc_IterableOnce__O(it)
});
$c_sc_MapFactory$Delegate.prototype.init___sc_MapFactory = (function(delegate) {
  this.delegate$1 = delegate;
  return this
});
$c_sc_MapFactory$Delegate.prototype.newBuilder__scm_Builder = (function() {
  return this.delegate$1.newBuilder__scm_Builder()
});
/** @constructor */
function $c_sc_View$() {
  /*<skip>*/
}
$c_sc_View$.prototype = new $h_O();
$c_sc_View$.prototype.constructor = $c_sc_View$;
/** @constructor */
function $h_sc_View$() {
  /*<skip>*/
}
$h_sc_View$.prototype = $c_sc_View$.prototype;
$c_sc_View$.prototype.from__sc_IterableOnce__sc_View = (function(it) {
  if ($is_sc_View(it)) {
    var x2 = $as_sc_View(it);
    return x2
  } else if ($is_sc_Iterable(it)) {
    var x3 = $as_sc_Iterable(it);
    var it$1 = new $c_sjsr_AnonFunction0((function($this, x3$1) {
      return (function() {
        return x3$1.iterator__sc_Iterator()
      })
    })(this, x3));
    return new $c_sc_View$$anon$1(it$1)
  } else {
    var this$2 = $m_sci_LazyList$().from__sc_IterableOnce__sci_LazyList(it);
    return new $c_sc_SeqView$Id().init___sc_SeqOps(this$2)
  }
});
$c_sc_View$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sc_View(source)
});
$c_sc_View$.prototype.newBuilder__scm_Builder = (function() {
  var this$2 = new $c_scm_ArrayBuffer$$anon$1();
  var f = new $c_sjsr_AnonFunction1((function($this) {
    return (function(it$2) {
      var it = $as_sc_IterableOnce(it$2);
      return $m_sc_View$().from__sc_IterableOnce__sc_View(it)
    })
  })(this));
  return new $c_scm_Builder$$anon$1(this$2, f)
});
var $d_sc_View$ = new $TypeData().initClass({
  sc_View$: 0
}, false, "scala.collection.View$", {
  sc_View$: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sc_View$.prototype.$classData = $d_sc_View$;
var $n_sc_View$ = (void 0);
function $m_sc_View$() {
  if ((!$n_sc_View$)) {
    $n_sc_View$ = new $c_sc_View$()
  };
  return $n_sc_View$
}
/** @constructor */
function $c_sci_HashMap$() {
  this.EmptyMap$1 = null;
  $n_sci_HashMap$ = this;
  var this$1 = $m_sci_MapNode$();
  this.EmptyMap$1 = new $c_sci_HashMap(this$1.EmptyMapNode$1, 0)
}
$c_sci_HashMap$.prototype = new $h_O();
$c_sci_HashMap$.prototype.constructor = $c_sci_HashMap$;
/** @constructor */
function $h_sci_HashMap$() {
  /*<skip>*/
}
$h_sci_HashMap$.prototype = $c_sci_HashMap$.prototype;
$c_sci_HashMap$.prototype.from__sc_IterableOnce__sci_HashMap = (function(source) {
  if ($is_sci_HashMap(source)) {
    var x2 = $as_sci_HashMap(source);
    return x2
  } else {
    var this$1 = new $c_sci_HashMap$$anon$2();
    return $as_sci_HashMap($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, source)).result__O())
  }
});
$c_sci_HashMap$.prototype.from__sc_IterableOnce__O = (function(it) {
  return this.from__sc_IterableOnce__sci_HashMap(it)
});
$c_sci_HashMap$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_HashMap$$anon$2()
});
var $d_sci_HashMap$ = new $TypeData().initClass({
  sci_HashMap$: 0
}, false, "scala.collection.immutable.HashMap$", {
  sci_HashMap$: 1,
  O: 1,
  sc_MapFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_HashMap$.prototype.$classData = $d_sci_HashMap$;
var $n_sci_HashMap$ = (void 0);
function $m_sci_HashMap$() {
  if ((!$n_sci_HashMap$)) {
    $n_sci_HashMap$ = new $c_sci_HashMap$()
  };
  return $n_sci_HashMap$
}
/** @constructor */
function $c_sci_HashSet$() {
  this.EmptySet$1 = null;
  $n_sci_HashSet$ = this;
  var this$1 = $m_sci_SetNode$();
  this.EmptySet$1 = new $c_sci_HashSet(this$1.EmptySetNode$1, 0)
}
$c_sci_HashSet$.prototype = new $h_O();
$c_sci_HashSet$.prototype.constructor = $c_sci_HashSet$;
/** @constructor */
function $h_sci_HashSet$() {
  /*<skip>*/
}
$h_sci_HashSet$.prototype = $c_sci_HashSet$.prototype;
$c_sci_HashSet$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sci_HashSet(source)
});
$c_sci_HashSet$.prototype.from__sc_IterableOnce__sci_HashSet = (function(source) {
  if ($is_sci_HashSet(source)) {
    var x2 = $as_sci_HashSet(source);
    return x2
  } else if ((source.knownSize__I() === 0)) {
    return this.EmptySet$1
  } else {
    var this$1 = new $c_sci_HashSet$$anon$1();
    return $as_sci_HashSet($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, source)).result__O())
  }
});
$c_sci_HashSet$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_HashSet$$anon$1()
});
var $d_sci_HashSet$ = new $TypeData().initClass({
  sci_HashSet$: 0
}, false, "scala.collection.immutable.HashSet$", {
  sci_HashSet$: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_HashSet$.prototype.$classData = $d_sci_HashSet$;
var $n_sci_HashSet$ = (void 0);
function $m_sci_HashSet$() {
  if ((!$n_sci_HashSet$)) {
    $n_sci_HashSet$ = new $c_sci_HashSet$()
  };
  return $n_sci_HashSet$
}
/** @constructor */
function $c_sci_LazyList$State$Cons(hd, tail) {
  this.head$1 = null;
  this.hd$1 = null;
  this.tail$1 = null;
  this.hdEvaluated$1 = false;
  this.bitmap$0$1 = false;
  this.hd$1 = hd;
  this.tail$1 = tail;
  this.hdEvaluated$1 = false
}
$c_sci_LazyList$State$Cons.prototype = new $h_O();
$c_sci_LazyList$State$Cons.prototype.constructor = $c_sci_LazyList$State$Cons;
/** @constructor */
function $h_sci_LazyList$State$Cons() {
  /*<skip>*/
}
$h_sci_LazyList$State$Cons.prototype = $c_sci_LazyList$State$Cons.prototype;
$c_sci_LazyList$State$Cons.prototype.head__O = (function() {
  return ((!this.bitmap$0$1) ? this.head$lzycompute__p1__O() : this.head$1)
});
$c_sci_LazyList$State$Cons.prototype.tail__sci_LazyList = (function() {
  return this.tail$1
});
$c_sci_LazyList$State$Cons.prototype.head$lzycompute__p1__O = (function() {
  if ((!this.bitmap$0$1)) {
    this.hdEvaluated$1 = true;
    var res = this.hd$1.apply__O();
    this.hd$1 = null;
    this.head$1 = res;
    this.bitmap$0$1 = true
  };
  return this.head$1
});
$c_sci_LazyList$State$Cons.prototype.headDefined__Z = (function() {
  return this.hdEvaluated$1
});
var $d_sci_LazyList$State$Cons = new $TypeData().initClass({
  sci_LazyList$State$Cons: 0
}, false, "scala.collection.immutable.LazyList$State$Cons", {
  sci_LazyList$State$Cons: 1,
  O: 1,
  sci_LazyList$State: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_LazyList$State$Cons.prototype.$classData = $d_sci_LazyList$State$Cons;
/** @constructor */
function $c_sci_LazyList$State$Empty$() {
  /*<skip>*/
}
$c_sci_LazyList$State$Empty$.prototype = new $h_O();
$c_sci_LazyList$State$Empty$.prototype.constructor = $c_sci_LazyList$State$Empty$;
/** @constructor */
function $h_sci_LazyList$State$Empty$() {
  /*<skip>*/
}
$h_sci_LazyList$State$Empty$.prototype = $c_sci_LazyList$State$Empty$.prototype;
$c_sci_LazyList$State$Empty$.prototype.head__O = (function() {
  this.head__E()
});
$c_sci_LazyList$State$Empty$.prototype.tail__sci_LazyList = (function() {
  throw new $c_jl_UnsupportedOperationException().init___T("tail of empty lazy list")
});
$c_sci_LazyList$State$Empty$.prototype.head__E = (function() {
  throw new $c_ju_NoSuchElementException().init___T("head of empty lazy list")
});
$c_sci_LazyList$State$Empty$.prototype.headDefined__Z = (function() {
  return false
});
var $d_sci_LazyList$State$Empty$ = new $TypeData().initClass({
  sci_LazyList$State$Empty$: 0
}, false, "scala.collection.immutable.LazyList$State$Empty$", {
  sci_LazyList$State$Empty$: 1,
  O: 1,
  sci_LazyList$State: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_LazyList$State$Empty$.prototype.$classData = $d_sci_LazyList$State$Empty$;
var $n_sci_LazyList$State$Empty$ = (void 0);
function $m_sci_LazyList$State$Empty$() {
  if ((!$n_sci_LazyList$State$Empty$)) {
    $n_sci_LazyList$State$Empty$ = new $c_sci_LazyList$State$Empty$()
  };
  return $n_sci_LazyList$State$Empty$
}
/** @constructor */
function $c_sci_ListMap$() {
  /*<skip>*/
}
$c_sci_ListMap$.prototype = new $h_O();
$c_sci_ListMap$.prototype.constructor = $c_sci_ListMap$;
/** @constructor */
function $h_sci_ListMap$() {
  /*<skip>*/
}
$h_sci_ListMap$.prototype = $c_sci_ListMap$.prototype;
$c_sci_ListMap$.prototype.from__sc_IterableOnce__O = (function(it) {
  return this.from__sc_IterableOnce__sci_ListMap(it)
});
$c_sci_ListMap$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_ListMap$$anon$1()
});
$c_sci_ListMap$.prototype.from__sc_IterableOnce__sci_ListMap = (function(it) {
  if ($is_sci_ListMap(it)) {
    var x2 = $as_sci_ListMap(it);
    return x2
  } else {
    var this$1 = new $c_sci_ListMap$$anon$1();
    return $as_sci_ListMap($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, it)).result__O())
  }
});
var $d_sci_ListMap$ = new $TypeData().initClass({
  sci_ListMap$: 0
}, false, "scala.collection.immutable.ListMap$", {
  sci_ListMap$: 1,
  O: 1,
  sc_MapFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_ListMap$.prototype.$classData = $d_sci_ListMap$;
var $n_sci_ListMap$ = (void 0);
function $m_sci_ListMap$() {
  if ((!$n_sci_ListMap$)) {
    $n_sci_ListMap$ = new $c_sci_ListMap$()
  };
  return $n_sci_ListMap$
}
/** @constructor */
function $c_sci_ListSet$() {
  /*<skip>*/
}
$c_sci_ListSet$.prototype = new $h_O();
$c_sci_ListSet$.prototype.constructor = $c_sci_ListSet$;
/** @constructor */
function $h_sci_ListSet$() {
  /*<skip>*/
}
$h_sci_ListSet$.prototype = $c_sci_ListSet$.prototype;
$c_sci_ListSet$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sci_ListSet(source)
});
$c_sci_ListSet$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_ListSet$$anon$1()
});
$c_sci_ListSet$.prototype.from__sc_IterableOnce__sci_ListSet = (function(it) {
  if ($is_sci_ListSet(it)) {
    var x2 = $as_sci_ListSet(it);
    return x2
  } else if ((it.knownSize__I() === 0)) {
    return $m_sci_ListSet$EmptyListSet$()
  } else {
    var this$1 = new $c_sci_ListSet$$anon$1();
    return $as_sci_ListSet($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, it)).result__O())
  }
});
var $d_sci_ListSet$ = new $TypeData().initClass({
  sci_ListSet$: 0
}, false, "scala.collection.immutable.ListSet$", {
  sci_ListSet$: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_ListSet$.prototype.$classData = $d_sci_ListSet$;
var $n_sci_ListSet$ = (void 0);
function $m_sci_ListSet$() {
  if ((!$n_sci_ListSet$)) {
    $n_sci_ListSet$ = new $c_sci_ListSet$()
  };
  return $n_sci_ListSet$
}
/** @constructor */
function $c_sci_Map$() {
  this.scala$collection$immutable$Map$$useBaseline$1 = false;
  $n_sci_Map$ = this;
  this.scala$collection$immutable$Map$$useBaseline$1 = ($m_jl_System$().getenv__T__T("SCALA_COLLECTION_IMMUTABLE_USE_BASELINE") === "true")
}
$c_sci_Map$.prototype = new $h_O();
$c_sci_Map$.prototype.constructor = $c_sci_Map$;
/** @constructor */
function $h_sci_Map$() {
  /*<skip>*/
}
$h_sci_Map$.prototype = $c_sci_Map$.prototype;
$c_sci_Map$.prototype.from__sc_IterableOnce__sci_Map = (function(it) {
  if ($is_sci_Iterable(it)) {
    var x2 = $as_sci_Iterable(it);
    if (x2.isEmpty__Z()) {
      return $m_sci_Map$EmptyMap$()
    }
  };
  if ($is_sci_Map(it)) {
    var x3 = $as_sci_Map(it);
    return x3
  };
  var this$1 = new $c_sci_Map$$anon$1();
  return $as_sci_Map($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, it)).result__O())
});
$c_sci_Map$.prototype.from__sc_IterableOnce__O = (function(it) {
  return this.from__sc_IterableOnce__sci_Map(it)
});
$c_sci_Map$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_Map$$anon$1()
});
var $d_sci_Map$ = new $TypeData().initClass({
  sci_Map$: 0
}, false, "scala.collection.immutable.Map$", {
  sci_Map$: 1,
  O: 1,
  sc_MapFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_Map$.prototype.$classData = $d_sci_Map$;
var $n_sci_Map$ = (void 0);
function $m_sci_Map$() {
  if ((!$n_sci_Map$)) {
    $n_sci_Map$ = new $c_sci_Map$()
  };
  return $n_sci_Map$
}
/** @constructor */
function $c_sci_OldHashMap$() {
  this.defaultMerger$1 = null;
  $n_sci_OldHashMap$ = this;
  var mergef = new $c_sjsr_AnonFunction2((function($this) {
    return (function(a$2, b$2) {
      var a = $as_T2(a$2);
      $as_T2(b$2);
      return a
    })
  })(this));
  this.defaultMerger$1 = new $c_sci_OldHashMap$$anon$2(mergef)
}
$c_sci_OldHashMap$.prototype = new $h_O();
$c_sci_OldHashMap$.prototype.constructor = $c_sci_OldHashMap$;
/** @constructor */
function $h_sci_OldHashMap$() {
  /*<skip>*/
}
$h_sci_OldHashMap$.prototype = $c_sci_OldHashMap$.prototype;
$c_sci_OldHashMap$.prototype.scala$collection$immutable$OldHashMap$$makeHashTrieMap__I__sci_OldHashMap__I__sci_OldHashMap__I__I__sci_OldHashMap$HashTrieMap = (function(hash0, elem0, hash1, elem1, level, size) {
  var index0 = (31 & ((hash0 >>> level) | 0));
  var index1 = (31 & ((hash1 >>> level) | 0));
  if ((index0 !== index1)) {
    var bitmap = ((1 << index0) | (1 << index1));
    var elems = $newArrayObject($d_sci_OldHashMap.getArrayOf(), [2]);
    if ((index0 < index1)) {
      elems.set(0, elem0);
      elems.set(1, elem1)
    } else {
      elems.set(0, elem1);
      elems.set(1, elem0)
    };
    return new $c_sci_OldHashMap$HashTrieMap(bitmap, elems, size)
  } else {
    var elems$2 = $newArrayObject($d_sci_OldHashMap.getArrayOf(), [1]);
    var bitmap$2 = (1 << index0);
    elems$2.set(0, this.scala$collection$immutable$OldHashMap$$makeHashTrieMap__I__sci_OldHashMap__I__sci_OldHashMap__I__I__sci_OldHashMap$HashTrieMap(hash0, elem0, hash1, elem1, ((5 + level) | 0), size));
    return new $c_sci_OldHashMap$HashTrieMap(bitmap$2, elems$2, size)
  }
});
$c_sci_OldHashMap$.prototype.from__sc_IterableOnce__O = (function(it) {
  return this.from__sc_IterableOnce__sci_OldHashMap(it)
});
$c_sci_OldHashMap$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_OldHashMap$$anon$1()
});
$c_sci_OldHashMap$.prototype.from__sc_IterableOnce__sci_OldHashMap = (function(it) {
  if ($is_sci_OldHashMap(it)) {
    var x2 = $as_sci_OldHashMap(it);
    return x2
  } else {
    var this$1 = new $c_sci_OldHashMap$$anon$1();
    return $as_sci_OldHashMap($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, it)).result__O())
  }
});
var $d_sci_OldHashMap$ = new $TypeData().initClass({
  sci_OldHashMap$: 0
}, false, "scala.collection.immutable.OldHashMap$", {
  sci_OldHashMap$: 1,
  O: 1,
  sc_MapFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_OldHashMap$.prototype.$classData = $d_sci_OldHashMap$;
var $n_sci_OldHashMap$ = (void 0);
function $m_sci_OldHashMap$() {
  if ((!$n_sci_OldHashMap$)) {
    $n_sci_OldHashMap$ = new $c_sci_OldHashMap$()
  };
  return $n_sci_OldHashMap$
}
/** @constructor */
function $c_sci_OldHashSet$() {
  /*<skip>*/
}
$c_sci_OldHashSet$.prototype = new $h_O();
$c_sci_OldHashSet$.prototype.constructor = $c_sci_OldHashSet$;
/** @constructor */
function $h_sci_OldHashSet$() {
  /*<skip>*/
}
$h_sci_OldHashSet$.prototype = $c_sci_OldHashSet$.prototype;
$c_sci_OldHashSet$.prototype.scala$collection$immutable$OldHashSet$$makeHashTrieSet__I__sci_OldHashSet__I__sci_OldHashSet__I__sci_OldHashSet$HashTrieSet = (function(hash0, elem0, hash1, elem1, level) {
  var index0 = (31 & ((hash0 >>> level) | 0));
  var index1 = (31 & ((hash1 >>> level) | 0));
  if ((index0 !== index1)) {
    var bitmap = ((1 << index0) | (1 << index1));
    var elems = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [2]);
    if ((index0 < index1)) {
      elems.set(0, elem0);
      elems.set(1, elem1)
    } else {
      elems.set(0, elem1);
      elems.set(1, elem0)
    };
    return new $c_sci_OldHashSet$HashTrieSet(bitmap, elems, ((elem0.size__I() + elem1.size__I()) | 0))
  } else {
    var elems$2 = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [1]);
    var bitmap$2 = (1 << index0);
    var child = this.scala$collection$immutable$OldHashSet$$makeHashTrieSet__I__sci_OldHashSet__I__sci_OldHashSet__I__sci_OldHashSet$HashTrieSet(hash0, elem0, hash1, elem1, ((5 + level) | 0));
    elems$2.set(0, child);
    return new $c_sci_OldHashSet$HashTrieSet(bitmap$2, elems$2, child.size0$5)
  }
});
$c_sci_OldHashSet$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sci_OldHashSet(source)
});
$c_sci_OldHashSet$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_OldHashSet$$anon$1()
});
$c_sci_OldHashSet$.prototype.from__sc_IterableOnce__sci_OldHashSet = (function(it) {
  if ($is_sci_OldHashSet(it)) {
    var x2 = $as_sci_OldHashSet(it);
    return x2
  } else {
    var this$1 = new $c_sci_OldHashSet$$anon$1();
    return $as_sci_OldHashSet($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, it)).result__O())
  }
});
var $d_sci_OldHashSet$ = new $TypeData().initClass({
  sci_OldHashSet$: 0
}, false, "scala.collection.immutable.OldHashSet$", {
  sci_OldHashSet$: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_OldHashSet$.prototype.$classData = $d_sci_OldHashSet$;
var $n_sci_OldHashSet$ = (void 0);
function $m_sci_OldHashSet$() {
  if ((!$n_sci_OldHashSet$)) {
    $n_sci_OldHashSet$ = new $c_sci_OldHashSet$()
  };
  return $n_sci_OldHashSet$
}
/** @constructor */
function $c_sci_Set$() {
  this.scala$collection$immutable$Set$$useBaseline$1 = false;
  $n_sci_Set$ = this;
  this.scala$collection$immutable$Set$$useBaseline$1 = ($m_jl_System$().getenv__T__T("SCALA_COLLECTION_IMMUTABLE_USE_BASELINE") === "true")
}
$c_sci_Set$.prototype = new $h_O();
$c_sci_Set$.prototype.constructor = $c_sci_Set$;
/** @constructor */
function $h_sci_Set$() {
  /*<skip>*/
}
$h_sci_Set$.prototype = $c_sci_Set$.prototype;
$c_sci_Set$.prototype.from__sc_IterableOnce__sci_Set = (function(it) {
  if ($is_sci_SortedSet(it)) {
    var this$1 = new $c_sci_Set$$anon$1();
    return $as_sci_Set($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, it)).result__O())
  } else if ((it.knownSize__I() === 0)) {
    return $m_sci_Set$EmptySet$()
  } else if ($is_sci_Set(it)) {
    var x3 = $as_sci_Set(it);
    return x3
  } else {
    var this$2 = new $c_sci_Set$$anon$1();
    return $as_sci_Set($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$2, it)).result__O())
  }
});
$c_sci_Set$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sci_Set(source)
});
$c_sci_Set$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_Set$$anon$1()
});
var $d_sci_Set$ = new $TypeData().initClass({
  sci_Set$: 0
}, false, "scala.collection.immutable.Set$", {
  sci_Set$: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_Set$.prototype.$classData = $d_sci_Set$;
var $n_sci_Set$ = (void 0);
function $m_sci_Set$() {
  if ((!$n_sci_Set$)) {
    $n_sci_Set$ = new $c_sci_Set$()
  };
  return $n_sci_Set$
}
/** @constructor */
function $c_sci_TrieIterator() {
  this.elems$1 = null;
  this.scala$collection$immutable$TrieIterator$$depth$f = 0;
  this.scala$collection$immutable$TrieIterator$$arrayStack$f = null;
  this.scala$collection$immutable$TrieIterator$$posStack$f = null;
  this.scala$collection$immutable$TrieIterator$$arrayD$f = null;
  this.scala$collection$immutable$TrieIterator$$posD$f = 0;
  this.scala$collection$immutable$TrieIterator$$subIter$f = null
}
$c_sci_TrieIterator.prototype = new $h_O();
$c_sci_TrieIterator.prototype.constructor = $c_sci_TrieIterator;
/** @constructor */
function $h_sci_TrieIterator() {
  /*<skip>*/
}
$h_sci_TrieIterator.prototype = $c_sci_TrieIterator.prototype;
$c_sci_TrieIterator.prototype.next__O = (function() {
  if ((this.scala$collection$immutable$TrieIterator$$subIter$f !== null)) {
    var el = this.scala$collection$immutable$TrieIterator$$subIter$f.next__O();
    if ((!this.scala$collection$immutable$TrieIterator$$subIter$f.hasNext__Z())) {
      this.scala$collection$immutable$TrieIterator$$subIter$f = null
    };
    return el
  } else {
    return this.next0__p1__Asci_Iterable__I__O(this.scala$collection$immutable$TrieIterator$$arrayD$f, this.scala$collection$immutable$TrieIterator$$posD$f)
  }
});
$c_sci_TrieIterator.prototype.isTrie__p1__O__Z = (function(x) {
  return ($is_sci_OldHashMap$HashTrieMap(x) || $is_sci_OldHashSet$HashTrieSet(x))
});
$c_sci_TrieIterator.prototype.concat__F0__sc_Iterator = (function(xs) {
  return $f_sc_Iterator__concat__F0__sc_Iterator(this, xs)
});
$c_sci_TrieIterator.prototype.initPosStack__AI = (function() {
  return $newArrayObject($d_I.getArrayOf(), [6])
});
$c_sci_TrieIterator.prototype.isEmpty__Z = (function() {
  return (!this.hasNext__Z())
});
$c_sci_TrieIterator.prototype.toString__T = (function() {
  return "<iterator>"
});
$c_sci_TrieIterator.prototype.next0__p1__Asci_Iterable__I__O = (function(elems, i) {
  while (true) {
    if ((i === (((-1) + elems.u.length) | 0))) {
      this.scala$collection$immutable$TrieIterator$$depth$f = (((-1) + this.scala$collection$immutable$TrieIterator$$depth$f) | 0);
      if ((this.scala$collection$immutable$TrieIterator$$depth$f >= 0)) {
        this.scala$collection$immutable$TrieIterator$$arrayD$f = this.scala$collection$immutable$TrieIterator$$arrayStack$f.get(this.scala$collection$immutable$TrieIterator$$depth$f);
        this.scala$collection$immutable$TrieIterator$$posD$f = this.scala$collection$immutable$TrieIterator$$posStack$f.get(this.scala$collection$immutable$TrieIterator$$depth$f);
        this.scala$collection$immutable$TrieIterator$$arrayStack$f.set(this.scala$collection$immutable$TrieIterator$$depth$f, null)
      } else {
        this.scala$collection$immutable$TrieIterator$$arrayD$f = null;
        this.scala$collection$immutable$TrieIterator$$posD$f = 0
      }
    } else {
      this.scala$collection$immutable$TrieIterator$$posD$f = ((1 + this.scala$collection$immutable$TrieIterator$$posD$f) | 0)
    };
    var m = elems.get(i);
    if (this.isContainer__p1__O__Z(m)) {
      return this.getElem__O__O(m)
    } else if (this.isTrie__p1__O__Z(m)) {
      if ((this.scala$collection$immutable$TrieIterator$$depth$f >= 0)) {
        this.scala$collection$immutable$TrieIterator$$arrayStack$f.set(this.scala$collection$immutable$TrieIterator$$depth$f, this.scala$collection$immutable$TrieIterator$$arrayD$f);
        this.scala$collection$immutable$TrieIterator$$posStack$f.set(this.scala$collection$immutable$TrieIterator$$depth$f, this.scala$collection$immutable$TrieIterator$$posD$f)
      };
      this.scala$collection$immutable$TrieIterator$$depth$f = ((1 + this.scala$collection$immutable$TrieIterator$$depth$f) | 0);
      this.scala$collection$immutable$TrieIterator$$arrayD$f = this.getElems__p1__sci_Iterable__Asci_Iterable(m);
      this.scala$collection$immutable$TrieIterator$$posD$f = 0;
      var temp$elems = this.getElems__p1__sci_Iterable__Asci_Iterable(m);
      elems = temp$elems;
      i = 0
    } else {
      this.scala$collection$immutable$TrieIterator$$subIter$f = m.iterator__sc_Iterator();
      return this.next__O()
    }
  }
});
$c_sci_TrieIterator.prototype.sliceIterator__I__I__sc_Iterator = (function(from, until) {
  return $f_sc_Iterator__sliceIterator__I__I__sc_Iterator(this, from, until)
});
$c_sci_TrieIterator.prototype.foreach__F1__V = (function(f) {
  $f_sc_IterableOnceOps__foreach__F1__V(this, f)
});
$c_sci_TrieIterator.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_IterableOnceOps__foldLeft__O__F2__O(this, z, op)
});
$c_sci_TrieIterator.prototype.copyToArray__O__I__I = (function(xs, start) {
  return $f_sc_IterableOnceOps__copyToArray__O__I__I(this, xs, start)
});
$c_sci_TrieIterator.prototype.isContainer__p1__O__Z = (function(x) {
  return ($is_sci_OldHashMap$OldHashMap1(x) || $is_sci_OldHashSet$OldHashSet1(x))
});
$c_sci_TrieIterator.prototype.iterator__sc_Iterator = (function() {
  return this
});
$c_sci_TrieIterator.prototype.hasNext__Z = (function() {
  return ((this.scala$collection$immutable$TrieIterator$$subIter$f !== null) || (this.scala$collection$immutable$TrieIterator$$depth$f >= 0))
});
$c_sci_TrieIterator.prototype.getElems__p1__sci_Iterable__Asci_Iterable = (function(x) {
  if ($is_sci_OldHashMap$HashTrieMap(x)) {
    var x2 = $as_sci_OldHashMap$HashTrieMap(x);
    var jsx$1 = x2.elems$5
  } else {
    if ((!$is_sci_OldHashSet$HashTrieSet(x))) {
      throw new $c_s_MatchError(x)
    };
    var x3 = $as_sci_OldHashSet$HashTrieSet(x);
    var jsx$1 = x3.elems$5
  };
  return $asArrayOf_sci_Iterable(jsx$1, 1)
});
$c_sci_TrieIterator.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(b, start, sep, end) {
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, b, start, sep, end)
});
$c_sci_TrieIterator.prototype.init___Asci_Iterable = (function(elems) {
  this.elems$1 = elems;
  this.scala$collection$immutable$TrieIterator$$depth$f = 0;
  this.scala$collection$immutable$TrieIterator$$arrayStack$f = this.initArrayStack__AAsci_Iterable();
  this.scala$collection$immutable$TrieIterator$$posStack$f = this.initPosStack__AI();
  this.scala$collection$immutable$TrieIterator$$arrayD$f = this.elems$1;
  this.scala$collection$immutable$TrieIterator$$posD$f = 0;
  this.scala$collection$immutable$TrieIterator$$subIter$f = null;
  return this
});
$c_sci_TrieIterator.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return $m_sci_Map$().from__sc_IterableOnce__sci_Map(this)
});
$c_sci_TrieIterator.prototype.sum__s_math_Numeric__O = (function(num) {
  return $f_sc_IterableOnceOps__sum__s_math_Numeric__O(this, num)
});
$c_sci_TrieIterator.prototype.knownSize__I = (function() {
  return (-1)
});
$c_sci_TrieIterator.prototype.initArrayStack__AAsci_Iterable = (function() {
  return $newArrayObject($d_sci_Iterable.getArrayOf().getArrayOf(), [6])
});
/** @constructor */
function $c_scm_Builder$$anon$1($$outer, f$1) {
  this.$$outer$1 = null;
  this.f$1$1 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$1 = $$outer
  };
  this.f$1$1 = f$1
}
$c_scm_Builder$$anon$1.prototype = new $h_O();
$c_scm_Builder$$anon$1.prototype.constructor = $c_scm_Builder$$anon$1;
/** @constructor */
function $h_scm_Builder$$anon$1() {
  /*<skip>*/
}
$h_scm_Builder$$anon$1.prototype = $c_scm_Builder$$anon$1.prototype;
$c_scm_Builder$$anon$1.prototype.result__O = (function() {
  return this.f$1$1.apply__O__O(this.$$outer$1.result__O())
});
$c_scm_Builder$$anon$1.prototype.addAll__sc_IterableOnce__scm_Growable = (function(xs) {
  return this.addAll__sc_IterableOnce__scm_Builder$$anon$1(xs)
});
$c_scm_Builder$$anon$1.prototype.addAll__sc_IterableOnce__scm_Builder$$anon$1 = (function(xs) {
  var this$1 = this.$$outer$1;
  this$1.addAll__sc_IterableOnce__scm_Growable(xs);
  return this
});
$c_scm_Builder$$anon$1.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__scm_Builder$$anon$1(elem)
});
$c_scm_Builder$$anon$1.prototype.sizeHint__I__V = (function(size) {
  this.$$outer$1.sizeHint__I__V(size)
});
$c_scm_Builder$$anon$1.prototype.addOne__O__scm_Builder$$anon$1 = (function(x) {
  var this$1 = this.$$outer$1;
  this$1.addOne__O__scm_Growable(x);
  return this
});
var $d_scm_Builder$$anon$1 = new $TypeData().initClass({
  scm_Builder$$anon$1: 0
}, false, "scala.collection.mutable.Builder$$anon$1", {
  scm_Builder$$anon$1: 1,
  O: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_scm_Builder$$anon$1.prototype.$classData = $d_scm_Builder$$anon$1;
/** @constructor */
function $c_scm_GrowableBuilder() {
  this.elems$1 = null
}
$c_scm_GrowableBuilder.prototype = new $h_O();
$c_scm_GrowableBuilder.prototype.constructor = $c_scm_GrowableBuilder;
/** @constructor */
function $h_scm_GrowableBuilder() {
  /*<skip>*/
}
$h_scm_GrowableBuilder.prototype = $c_scm_GrowableBuilder.prototype;
$c_scm_GrowableBuilder.prototype.init___scm_Growable = (function(elems) {
  this.elems$1 = elems;
  return this
});
$c_scm_GrowableBuilder.prototype.addOne__O__scm_GrowableBuilder = (function(elem) {
  var this$1 = this.elems$1;
  this$1.addOne__O__scm_Growable(elem);
  return this
});
$c_scm_GrowableBuilder.prototype.result__O = (function() {
  return this.elems$1
});
$c_scm_GrowableBuilder.prototype.addAll__sc_IterableOnce__scm_Growable = (function(xs) {
  return $f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this, xs)
});
$c_scm_GrowableBuilder.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__scm_GrowableBuilder(elem)
});
$c_scm_GrowableBuilder.prototype.sizeHint__I__V = (function(size) {
  /*<skip>*/
});
var $d_scm_GrowableBuilder = new $TypeData().initClass({
  scm_GrowableBuilder: 0
}, false, "scala.collection.mutable.GrowableBuilder", {
  scm_GrowableBuilder: 1,
  O: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_scm_GrowableBuilder.prototype.$classData = $d_scm_GrowableBuilder;
/** @constructor */
function $c_scm_HashSet$() {
  /*<skip>*/
}
$c_scm_HashSet$.prototype = new $h_O();
$c_scm_HashSet$.prototype.constructor = $c_scm_HashSet$;
/** @constructor */
function $h_scm_HashSet$() {
  /*<skip>*/
}
$h_scm_HashSet$.prototype = $c_scm_HashSet$.prototype;
$c_scm_HashSet$.prototype.from__sc_IterableOnce__O = (function(source) {
  var empty = new $c_scm_HashSet();
  return $as_scm_HashSet($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(empty, source))
});
$c_scm_HashSet$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_scm_GrowableBuilder().init___scm_Growable(new $c_scm_HashSet())
});
var $d_scm_HashSet$ = new $TypeData().initClass({
  scm_HashSet$: 0
}, false, "scala.collection.mutable.HashSet$", {
  scm_HashSet$: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_scm_HashSet$.prototype.$classData = $d_scm_HashSet$;
var $n_scm_HashSet$ = (void 0);
function $m_scm_HashSet$() {
  if ((!$n_scm_HashSet$)) {
    $n_scm_HashSet$ = new $c_scm_HashSet$()
  };
  return $n_scm_HashSet$
}
/** @constructor */
function $c_sjsr_RuntimeLong(lo, hi) {
  this.lo$2 = 0;
  this.hi$2 = 0;
  this.lo$2 = lo;
  this.hi$2 = hi
}
$c_sjsr_RuntimeLong.prototype = new $h_jl_Number();
$c_sjsr_RuntimeLong.prototype.constructor = $c_sjsr_RuntimeLong;
/** @constructor */
function $h_sjsr_RuntimeLong() {
  /*<skip>*/
}
$h_sjsr_RuntimeLong.prototype = $c_sjsr_RuntimeLong.prototype;
$c_sjsr_RuntimeLong.prototype.longValue__J = (function() {
  return $uJ(this)
});
$c_sjsr_RuntimeLong.prototype.$$bar__sjsr_RuntimeLong__sjsr_RuntimeLong = (function(b) {
  return new $c_sjsr_RuntimeLong((this.lo$2 | b.lo$2), (this.hi$2 | b.hi$2))
});
$c_sjsr_RuntimeLong.prototype.$$greater$eq__sjsr_RuntimeLong__Z = (function(b) {
  var ahi = this.hi$2;
  var bhi = b.hi$2;
  return ((ahi === bhi) ? (((-2147483648) ^ this.lo$2) >= ((-2147483648) ^ b.lo$2)) : (ahi > bhi))
});
$c_sjsr_RuntimeLong.prototype.byteValue__B = (function() {
  return ((this.lo$2 << 24) >> 24)
});
$c_sjsr_RuntimeLong.prototype.equals__O__Z = (function(that) {
  if ($is_sjsr_RuntimeLong(that)) {
    var x2 = $as_sjsr_RuntimeLong(that);
    return ((this.lo$2 === x2.lo$2) && (this.hi$2 === x2.hi$2))
  } else {
    return false
  }
});
$c_sjsr_RuntimeLong.prototype.$$less__sjsr_RuntimeLong__Z = (function(b) {
  var ahi = this.hi$2;
  var bhi = b.hi$2;
  return ((ahi === bhi) ? (((-2147483648) ^ this.lo$2) < ((-2147483648) ^ b.lo$2)) : (ahi < bhi))
});
$c_sjsr_RuntimeLong.prototype.$$times__sjsr_RuntimeLong__sjsr_RuntimeLong = (function(b) {
  var alo = this.lo$2;
  var blo = b.lo$2;
  var a0 = (65535 & alo);
  var a1 = ((alo >>> 16) | 0);
  var b0 = (65535 & blo);
  var b1 = ((blo >>> 16) | 0);
  var a0b0 = $imul(a0, b0);
  var a1b0 = $imul(a1, b0);
  var a0b1 = $imul(a0, b1);
  var lo = ((a0b0 + (((a1b0 + a0b1) | 0) << 16)) | 0);
  var c1part = ((((a0b0 >>> 16) | 0) + a0b1) | 0);
  var hi = (((((((($imul(alo, b.hi$2) + $imul(this.hi$2, blo)) | 0) + $imul(a1, b1)) | 0) + ((c1part >>> 16) | 0)) | 0) + (((((65535 & c1part) + a1b0) | 0) >>> 16) | 0)) | 0);
  return new $c_sjsr_RuntimeLong(lo, hi)
});
$c_sjsr_RuntimeLong.prototype.$$percent__sjsr_RuntimeLong__sjsr_RuntimeLong = (function(b) {
  var this$1 = $m_sjsr_RuntimeLong$();
  var lo = this$1.remainderImpl__I__I__I__I__I(this.lo$2, this.hi$2, b.lo$2, b.hi$2);
  return new $c_sjsr_RuntimeLong(lo, this$1.scala$scalajs$runtime$RuntimeLong$$hiReturn$f)
});
$c_sjsr_RuntimeLong.prototype.toString__T = (function() {
  return $m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toString__I__I__T(this.lo$2, this.hi$2)
});
$c_sjsr_RuntimeLong.prototype.compareTo__O__I = (function(x$1) {
  var that = $as_sjsr_RuntimeLong(x$1);
  return $m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$compare__I__I__I__I__I(this.lo$2, this.hi$2, that.lo$2, that.hi$2)
});
$c_sjsr_RuntimeLong.prototype.$$less$eq__sjsr_RuntimeLong__Z = (function(b) {
  var ahi = this.hi$2;
  var bhi = b.hi$2;
  return ((ahi === bhi) ? (((-2147483648) ^ this.lo$2) <= ((-2147483648) ^ b.lo$2)) : (ahi < bhi))
});
$c_sjsr_RuntimeLong.prototype.$$amp__sjsr_RuntimeLong__sjsr_RuntimeLong = (function(b) {
  return new $c_sjsr_RuntimeLong((this.lo$2 & b.lo$2), (this.hi$2 & b.hi$2))
});
$c_sjsr_RuntimeLong.prototype.$$greater$greater$greater__I__sjsr_RuntimeLong = (function(n) {
  return new $c_sjsr_RuntimeLong((((32 & n) === 0) ? (((this.lo$2 >>> n) | 0) | ((this.hi$2 << 1) << ((31 - n) | 0))) : ((this.hi$2 >>> n) | 0)), (((32 & n) === 0) ? ((this.hi$2 >>> n) | 0) : 0))
});
$c_sjsr_RuntimeLong.prototype.$$greater__sjsr_RuntimeLong__Z = (function(b) {
  var ahi = this.hi$2;
  var bhi = b.hi$2;
  return ((ahi === bhi) ? (((-2147483648) ^ this.lo$2) > ((-2147483648) ^ b.lo$2)) : (ahi > bhi))
});
$c_sjsr_RuntimeLong.prototype.$$less$less__I__sjsr_RuntimeLong = (function(n) {
  return new $c_sjsr_RuntimeLong((((32 & n) === 0) ? (this.lo$2 << n) : 0), (((32 & n) === 0) ? (((((this.lo$2 >>> 1) | 0) >>> ((31 - n) | 0)) | 0) | (this.hi$2 << n)) : (this.lo$2 << n)))
});
$c_sjsr_RuntimeLong.prototype.toInt__I = (function() {
  return this.lo$2
});
$c_sjsr_RuntimeLong.prototype.notEquals__sjsr_RuntimeLong__Z = (function(b) {
  return (!((this.lo$2 === b.lo$2) && (this.hi$2 === b.hi$2)))
});
$c_sjsr_RuntimeLong.prototype.unary$und$minus__sjsr_RuntimeLong = (function() {
  var lo = this.lo$2;
  var hi = this.hi$2;
  return new $c_sjsr_RuntimeLong(((-lo) | 0), ((lo !== 0) ? (~hi) : ((-hi) | 0)))
});
$c_sjsr_RuntimeLong.prototype.$$plus__sjsr_RuntimeLong__sjsr_RuntimeLong = (function(b) {
  var alo = this.lo$2;
  var ahi = this.hi$2;
  var bhi = b.hi$2;
  var lo = ((alo + b.lo$2) | 0);
  return new $c_sjsr_RuntimeLong(lo, ((((-2147483648) ^ lo) < ((-2147483648) ^ alo)) ? ((1 + ((ahi + bhi) | 0)) | 0) : ((ahi + bhi) | 0)))
});
$c_sjsr_RuntimeLong.prototype.shortValue__S = (function() {
  return ((this.lo$2 << 16) >> 16)
});
$c_sjsr_RuntimeLong.prototype.$$greater$greater__I__sjsr_RuntimeLong = (function(n) {
  return new $c_sjsr_RuntimeLong((((32 & n) === 0) ? (((this.lo$2 >>> n) | 0) | ((this.hi$2 << 1) << ((31 - n) | 0))) : (this.hi$2 >> n)), (((32 & n) === 0) ? (this.hi$2 >> n) : (this.hi$2 >> 31)))
});
$c_sjsr_RuntimeLong.prototype.toDouble__D = (function() {
  return $m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toDouble__I__I__D(this.lo$2, this.hi$2)
});
$c_sjsr_RuntimeLong.prototype.$$div__sjsr_RuntimeLong__sjsr_RuntimeLong = (function(b) {
  var this$1 = $m_sjsr_RuntimeLong$();
  var lo = this$1.divideImpl__I__I__I__I__I(this.lo$2, this.hi$2, b.lo$2, b.hi$2);
  return new $c_sjsr_RuntimeLong(lo, this$1.scala$scalajs$runtime$RuntimeLong$$hiReturn$f)
});
$c_sjsr_RuntimeLong.prototype.doubleValue__D = (function() {
  return $m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toDouble__I__I__D(this.lo$2, this.hi$2)
});
$c_sjsr_RuntimeLong.prototype.hashCode__I = (function() {
  return (this.lo$2 ^ this.hi$2)
});
$c_sjsr_RuntimeLong.prototype.intValue__I = (function() {
  return this.lo$2
});
$c_sjsr_RuntimeLong.prototype.unary$und$tilde__sjsr_RuntimeLong = (function() {
  return new $c_sjsr_RuntimeLong((~this.lo$2), (~this.hi$2))
});
$c_sjsr_RuntimeLong.prototype.compareTo__jl_Long__I = (function(that) {
  return $m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$compare__I__I__I__I__I(this.lo$2, this.hi$2, that.lo$2, that.hi$2)
});
$c_sjsr_RuntimeLong.prototype.floatValue__F = (function() {
  return $fround($m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toDouble__I__I__D(this.lo$2, this.hi$2))
});
$c_sjsr_RuntimeLong.prototype.$$minus__sjsr_RuntimeLong__sjsr_RuntimeLong = (function(b) {
  var alo = this.lo$2;
  var ahi = this.hi$2;
  var bhi = b.hi$2;
  var lo = ((alo - b.lo$2) | 0);
  return new $c_sjsr_RuntimeLong(lo, ((((-2147483648) ^ lo) > ((-2147483648) ^ alo)) ? (((-1) + ((ahi - bhi) | 0)) | 0) : ((ahi - bhi) | 0)))
});
$c_sjsr_RuntimeLong.prototype.$$up__sjsr_RuntimeLong__sjsr_RuntimeLong = (function(b) {
  return new $c_sjsr_RuntimeLong((this.lo$2 ^ b.lo$2), (this.hi$2 ^ b.hi$2))
});
$c_sjsr_RuntimeLong.prototype.equals__sjsr_RuntimeLong__Z = (function(b) {
  return ((this.lo$2 === b.lo$2) && (this.hi$2 === b.hi$2))
});
function $is_sjsr_RuntimeLong(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sjsr_RuntimeLong)))
}
function $as_sjsr_RuntimeLong(obj) {
  return (($is_sjsr_RuntimeLong(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.scalajs.runtime.RuntimeLong"))
}
function $isArrayOf_sjsr_RuntimeLong(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sjsr_RuntimeLong)))
}
function $asArrayOf_sjsr_RuntimeLong(obj, depth) {
  return (($isArrayOf_sjsr_RuntimeLong(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.scalajs.runtime.RuntimeLong;", depth))
}
var $d_sjsr_RuntimeLong = new $TypeData().initClass({
  sjsr_RuntimeLong: 0
}, false, "scala.scalajs.runtime.RuntimeLong", {
  sjsr_RuntimeLong: 1,
  jl_Number: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  jl_Comparable: 1
});
$c_sjsr_RuntimeLong.prototype.$classData = $d_sjsr_RuntimeLong;
/** @constructor */
function $c_Lcom_kos_wormpad_WormApp$() {
  this.dpad$1 = null;
  this.gravitation$1 = 0.0;
  this.random$1 = null;
  this.heroes$1 = null;
  this.wormHealthSpeed$1 = 0.0;
  this.hasInEarth$1 = false;
  this.drawer$1 = null;
  this.touchIdentifier$1 = 0.0;
  this.gameTime$1 = 0.0;
  this.screenView$1 = null;
  this.clouds$1 = null;
  this.pause$und$1 = false;
  this.isGameOver$und$1 = false;
  this.listener$und$1 = null;
  this.jslistener$1 = null;
  this.soundPlay$und$1 = false;
  this.musicPlay$und$1 = false;
  this.com$kos$wormpad$game$AudioState$$soundPath$1 = null;
  this.com$kos$wormpad$game$AudioState$$musicPath$1 = null;
  this.soundBank$1 = null;
  this.com$kos$wormpad$game$WormScore$$score$und$1 = 0;
  $n_Lcom_kos_wormpad_WormApp$ = this;
  this.com$kos$wormpad$game$WormScore$$score$und$1 = 0;
  $f_Lcom_kos_wormpad_game_AudioState__$$init$__V(this);
  $f_Lcom_kos_wormpad_game_GameState__$$init$__V(this);
  this.dpad$1 = new $c_Lcom_kos_wormpad_dpad_DPad(0.0, 0.0, 1.0, 1.0);
  this.gravitation$1 = 9.6;
  this.random$1 = new $c_s_util_Random().init___();
  this.heroes$1 = new $c_Lcom_kos_wormpad_GameHeroes();
  this.wormHealthSpeed$1 = 2.0;
  this.hasInEarth$1 = false;
  this.touchIdentifier$1 = (-1.0);
  this.gameTime$1 = 0.0;
  this.clouds$1 = this.generateClouds__p1__sci_IndexedSeq()
}
$c_Lcom_kos_wormpad_WormApp$.prototype = new $h_O();
$c_Lcom_kos_wormpad_WormApp$.prototype.constructor = $c_Lcom_kos_wormpad_WormApp$;
/** @constructor */
function $h_Lcom_kos_wormpad_WormApp$() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_WormApp$.prototype = $c_Lcom_kos_wormpad_WormApp$.prototype;
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$meth$gameOver__O = (function() {
  this.gameOver__V()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$meth$resize__O = (function() {
  this.resize__V()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.com$kos$wormpad$WormApp$$$anonfun$setupDPad$4__Lorg_scalajs_dom_raw_TouchEvent__V = (function(te) {
  var end = $uI(te.touches.length);
  var isEmpty$4 = (end <= 0);
  var scala$collection$immutable$Range$$lastElement$f = (((-1) + end) | 0);
  var b = $m_sci_IndexedSeq$().newBuilder__scm_Builder();
  var it = new $c_sci_RangeIterator(0, 1, scala$collection$immutable$Range$$lastElement$f, isEmpty$4);
  while (it.$$undhasNext$2) {
    var arg1 = it.next__I();
    var e = te.touches.item(arg1);
    var elem = new $c_T2(arg1, e);
    b.addOne__O__scm_Growable(elem)
  };
  $as_sc_IterableOps(b.result__O()).withFilter__F1__sc_WithFilter(new $c_sjsr_AnonFunction1((function(this$2$1) {
    return (function(x$2$2) {
      var x$2 = $as_T2(x$2$2);
      if ((x$2 !== null)) {
        var e$1 = x$2.$$und2$f;
        return ($m_Lcom_kos_wormpad_WormApp$().touchIdentifier$1 === $uD(e$1.identifier))
      } else {
        throw new $c_s_MatchError(x$2)
      }
    })
  })(this))).foreach__F1__V(new $c_sjsr_AnonFunction1((function(this$3$1) {
    return (function(x$3$2) {
      var x$3 = $as_T2(x$3$2);
      if ((x$3 !== null)) {
        var e$2 = x$3.$$und2$f;
        $m_Lcom_kos_wormpad_WormApp$().dpad$1.touchMove__D__D__V($uD(e$2.clientX), $uD(e$2.clientY))
      } else {
        throw new $c_s_MatchError(x$3)
      }
    })
  })(this)))
});
$c_Lcom_kos_wormpad_WormApp$.prototype.generateClouds__p1__sci_IndexedSeq = (function() {
  var b = $m_sci_IndexedSeq$().newBuilder__scm_Builder();
  var it = new $c_sci_RangeIterator(1, 1, 20, false);
  while (it.$$undhasNext$2) {
    var arg1 = it.next__I();
    var elem = new $c_Lcom_kos_wormpad_WormApp$$anon$1();
    b.addOne__O__scm_Growable(elem)
  };
  return $as_sci_IndexedSeq(b.result__O())
});
$c_Lcom_kos_wormpad_WormApp$.prototype.WormEatObjects__p1__D__V = (function(timeDelta) {
  var hero = this.heroes$1;
  var be = $as_sci_Set(hero.burgers$1.filter__F1__O(new $c_sjsr_AnonFunction1((function($this, hero$1) {
    return (function(b$2) {
      var b = $as_Lcom_kos_wormpad_heroes_Hero(b$2);
      return hero$1.worm$1.eat__Lcom_kos_wormpad_heroes_Hero__Z(b)
    })
  })(this, hero))));
  if ((!be.isEmpty__Z())) {
    var value = ((this.com$kos$wormpad$game$WormScore$$score$und$1 + $uI($as_sc_IterableOnceOps(be.map__F1__O(new $c_sjsr_AnonFunction1((function(this$2) {
      return (function(x$11$2) {
        var x$11 = $as_Lcom_kos_wormpad_heroes_Hero(x$11$2);
        return x$11.score$1
      })
    })(this)))).sum__s_math_Numeric__O($m_s_math_Numeric$IntIsIntegral$()))) | 0);
    $f_Lcom_kos_wormpad_game_WormScore__score$und$eq__I__V(this, value);
    hero.worm$1.health$2 = (hero.worm$1.health$2 + $uI($as_sc_IterableOnceOps(be.map__F1__O(new $c_sjsr_AnonFunction1((function(this$3) {
      return (function(x$12$2) {
        var x$12 = $as_Lcom_kos_wormpad_heroes_Hero(x$12$2);
        return x$12.energy$1
      })
    })(this)))).sum__s_math_Numeric__O($m_s_math_Numeric$IntIsIntegral$())));
    var this$1 = hero.burgers$1;
    hero.burgers$1 = $as_sci_Set($f_sci_SetOps__removeAll__sc_IterableOnce__sci_SetOps(this$1, be));
    if (this.hasInEarth$1) {
      this.wormHealthSpeed$1 = (this.wormHealthSpeed$1 + hero.LEVEL$undWORM$undHEALTH$undSPEED$undUPDATE$1);
      this.hasInEarth$1 = false
    }
  };
  var ee = $as_sci_Set(hero.enemies$1.filter__F1__O(new $c_sjsr_AnonFunction1((function(this$4, hero$2) {
    return (function(b$3$2) {
      var b$3 = $as_Lcom_kos_wormpad_heroes_Hero(b$3$2);
      return (b$3.ediible__Z() && hero$2.worm$1.eat__Lcom_kos_wormpad_heroes_Hero__Z(b$3))
    })
  })(this, hero))));
  if ((!ee.isEmpty__Z())) {
    var value$1 = ((this.com$kos$wormpad$game$WormScore$$score$und$1 + $uI($as_sc_IterableOnceOps(ee.map__F1__O(new $c_sjsr_AnonFunction1((function(this$5) {
      return (function(x$13$2) {
        var x$13 = $as_Lcom_kos_wormpad_heroes_Hero(x$13$2);
        return x$13.score$1
      })
    })(this)))).sum__s_math_Numeric__O($m_s_math_Numeric$IntIsIntegral$()))) | 0);
    $f_Lcom_kos_wormpad_game_WormScore__score$und$eq__I__V(this, value$1);
    hero.worm$1.health$2 = (hero.worm$1.health$2 + $uI($as_sc_IterableOnceOps(ee.map__F1__O(new $c_sjsr_AnonFunction1((function(this$6) {
      return (function(x$14$2) {
        var x$14 = $as_Lcom_kos_wormpad_heroes_Hero(x$14$2);
        return x$14.energy$1
      })
    })(this)))).sum__s_math_Numeric__O($m_s_math_Numeric$IntIsIntegral$())));
    var this$7 = hero.enemies$1;
    hero.enemies$1 = $as_sci_Set($f_sci_SetOps__removeAll__sc_IterableOnce__sci_SetOps(this$7, ee));
    if (this.hasInEarth$1) {
      this.wormHealthSpeed$1 = (this.wormHealthSpeed$1 + hero.LEVEL$undWORM$undHEALTH$undSPEED$undUPDATE$1);
      this.hasInEarth$1 = false
    }
  };
  if (this.inEarth__Lcom_kos_wormpad_heroes_Worm__Z(hero.worm$1)) {
    this.hasInEarth$1 = true;
    hero.worm$1.health$2 = (hero.worm$1.health$2 - (this.wormHealthSpeed$1 * timeDelta))
  };
  if ((hero.worm$1.health$2 > $m_Lcom_kos_wormpad_heroes_Worm$().MAX$undHEALTH$1)) {
    hero.worm$1.health$2 = $m_Lcom_kos_wormpad_heroes_Worm$().MAX$undHEALTH$1
  };
  if ((hero.worm$1.health$2 < 0.0)) {
    this.gameOver__V()
  }
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$meth$newGame__O = (function() {
  this.newGame__V()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$prop$listener$und__Lcom_kos_wormpad_game_GameListenerDelegate__O = (function(x$1) {
  this.listener$und$1 = x$1
});
$c_Lcom_kos_wormpad_WormApp$.prototype.moveWorm__p1__D__V = (function(timeDelta) {
  var hero = this.heroes$1;
  if (this.inEarth__Lcom_kos_wormpad_heroes_Worm__Z(hero.worm$1)) {
    var this$1 = this.dpad$1;
    if (this$1.pressed$1) {
      hero.worm$1.vx$1 = (hero.worm$1.vx$1 + (this.dpad$1.x__D() * timeDelta));
      hero.worm$1.vy$1 = (hero.worm$1.vy$1 + (this.dpad$1.y__D() * timeDelta))
    }
  } else {
    var a = new $c_Lcom_kos_wormpad_geometry_Force(0.0, (-this.gravitation$1), hero.worm$1.massa$1);
    hero.worm$1.vx$1 = ((((a.x$1 * a.mass$1) * timeDelta) + hero.worm$1.vx$1) + (0.25 * (this.dpad$1.x__D() * timeDelta)));
    hero.worm$1.vy$1 = (((a.y$1 * a.mass$1) * timeDelta) + hero.worm$1.vy$1)
  };
  var this$2 = hero.worm$1;
  var h = $m_jl_Math$().hypot__D__D__D(this$2.vx$1, this$2.vy$1);
  if ((h > $m_Lcom_kos_wormpad_heroes_Worm$().MAX$undSPEED$1)) {
    hero.worm$1.vx$1 = ((hero.worm$1.vx$1 * $m_Lcom_kos_wormpad_heroes_Worm$().MAX$undSPEED$1) / h);
    hero.worm$1.vy$1 = ((hero.worm$1.vy$1 * $m_Lcom_kos_wormpad_heroes_Worm$().MAX$undSPEED$1) / h)
  };
  hero.worm$1.move__D__V(timeDelta);
  if ((hero.worm$1.x$1 < hero.wormBorder$1.left$1)) {
    hero.worm$1.x$1 = hero.wormBorder$1.left$1;
    hero.worm$1.vx$1 = 0.0
  };
  if ((hero.worm$1.x$1 > hero.wormBorder$1.right$1)) {
    hero.worm$1.x$1 = hero.wormBorder$1.right$1;
    hero.worm$1.vx$1 = 0.0
  };
  if ((hero.worm$1.y$1 < hero.wormBorder$1.bottom$1)) {
    hero.worm$1.y$1 = hero.wormBorder$1.bottom$1;
    hero.worm$1.vy$1 = 0.0
  };
  if ((hero.worm$1.y$1 > hero.wormBorder$1.top$1)) {
    hero.worm$1.y$1 = hero.wormBorder$1.top$1;
    hero.worm$1.vy$1 = 0.0
  }
});
$c_Lcom_kos_wormpad_WormApp$.prototype.resize__V = (function() {
  var dpadView = $m_Lorg_scalajs_dom_package$().document__Lorg_scalajs_dom_raw_HTMLDocument().getElementById("display");
  var canvas = $m_Lorg_scalajs_dom_package$().document__Lorg_scalajs_dom_raw_HTMLDocument().getElementById("display");
  var jsx$2 = $uI(dpadView.clientWidth);
  var jsx$1 = $uI(dpadView.clientHeight);
  var a = $uI(dpadView.clientHeight);
  var b = $uI(dpadView.clientWidth);
  this.dpad$1 = new $c_Lcom_kos_wormpad_dpad_DPad(((jsx$2 / 2) | 0), ((jsx$1 / 2) | 0), ((((a < b) ? a : b) / 4) | 0), $m_Lcom_kos_wormpad_heroes_Worm$().WORM$undACCELERATION$1);
  canvas.width = $doubleToInt($uD(canvas.offsetWidth));
  canvas.height = $doubleToInt($uD(canvas.offsetHeight));
  this.drawer$1 = new $c_Lcom_kos_wormpad_game_WebWormGameDrawer(canvas)
});
$c_Lcom_kos_wormpad_WormApp$.prototype.com$kos$wormpad$WormApp$$$anonfun$setupDPad$19__Lorg_scalajs_dom_raw_MouseEvent__V = (function(e) {
  $m_Lcom_kos_wormpad_WormApp$().dpad$1.touchDown__D__D__V($uD(e.clientX), $uD(e.clientY))
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$meth$togglePause__O = (function() {
  $f_Lcom_kos_wormpad_game_GameState__togglePause__V(this)
});
$c_Lcom_kos_wormpad_WormApp$.prototype.com$kos$wormpad$WormApp$$$anonfun$setupDPad$21__Lorg_scalajs_dom_raw_MouseEvent__V = (function(e) {
  $m_Lcom_kos_wormpad_WormApp$().dpad$1.touchMove__D__D__V($uD(e.clientX), $uD(e.clientY))
});
$c_Lcom_kos_wormpad_WormApp$.prototype.inEarth__Lcom_kos_wormpad_heroes_Worm__Z = (function(worm) {
  return (worm.y$1 < this.heroes$1.earthBorder$1.top$1)
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$prop$listener$und__O = (function() {
  return this.listener$und$1
});
$c_Lcom_kos_wormpad_WormApp$.prototype.GenerateEnemies__D__D__V = (function(gameTime, timeDelta) {
  var ev$1 = this.heroes$1;
  var this$1 = ev$1.enemies$1;
  var that = $as_sc_Iterable(this.heroes$1.enemyCreatorList$1.map__F1__O(new $c_sjsr_AnonFunction1((function($this, gameTime$1) {
    return (function(x$8$2) {
      var x$8 = $as_Lcom_kos_wormpad_game_EnemyCreator(x$8$2);
      return x$8.createIfNeed__D__s_util_Random__Lcom_kos_wormpad_heroes_Hero(gameTime$1, $m_Lcom_kos_wormpad_WormApp$().random$1)
    })
  })(this, gameTime))));
  ev$1.enemies$1 = $as_sci_Set(this$1.concat__sc_IterableOnce__sc_SetOps(that))
});
$c_Lcom_kos_wormpad_WormApp$.prototype.update__J__V = (function(tick) {
  var timeDelta = (0.001 * $m_sjsr_RuntimeLong$().scala$scalajs$runtime$RuntimeLong$$toDouble__I__I__D(tick.lo$2, tick.hi$2));
  if ((!(this.pause$und$1 || this.isGameOver$und$1))) {
    this.gameTime$1 = (this.gameTime$1 + timeDelta);
    this.GenerateEnemies__D__D__V(this.gameTime$1, timeDelta);
    this.moveEnemies__D__V(timeDelta);
    this.moveWorm__p1__D__V(timeDelta);
    this.GenerateEatObjects__p1__V();
    this.WormEatObjects__p1__D__V(timeDelta)
  };
  this.moveClouds__D__V(timeDelta)
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$prop$jslistener__Lcom_kos_wormpad_game_GameListener__O = (function(x$1) {
  this.jslistener$1 = x$1
});
$c_Lcom_kos_wormpad_WormApp$.prototype.gameOver__V = (function() {
  this.heroes$1.worm$1.health$2 = 0.0;
  this.isGameOver$und$1 = true;
  var element = this.screenView$1;
  $m_Lcom_kos_wormpad_game_helpers_JSHelper$().removeClass__Lorg_scalajs_dom_raw_HTMLElement__T__V(element, "gone");
  var scoreText = $m_Lorg_scalajs_dom_package$().document__Lorg_scalajs_dom_raw_HTMLDocument().getElementById("gameOverScore");
  if ((scoreText !== null)) {
    scoreText.textContent = ("Score: " + this.com$kos$wormpad$game$WormScore$$score$und$1)
  };
  this.listener$und$1.onGameOver__V()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.com$kos$wormpad$WormApp$$$anonfun$setupDPad$2__Lorg_scalajs_dom_raw_TouchEvent__O = (function(te) {
  if (($uI(te.touches.length) > 0)) {
    var e = te.touches.item(0);
    $m_Lcom_kos_wormpad_WormApp$().touchIdentifier$1 = $uD(e.identifier);
    $m_Lcom_kos_wormpad_WormApp$().dpad$1.touchDown__D__D__V($uD(e.clientX), $uD(e.clientY));
    return (void 0)
  } else {
    return (void 0)
  }
});
$c_Lcom_kos_wormpad_WormApp$.prototype.render__V = (function() {
  var hero = this.heroes$1;
  var ctx = this.drawer$1;
  ctx.clear__V();
  ctx.ctx$1.save();
  ctx.ctx$1.save();
  ctx.setupCamera__Lcom_kos_wormpad_heroes_Worm__D__V(hero.worm$1, 0.5);
  ctx.drawSky__Lcom_kos_wormpad_geometry_RectF__V(hero.gameBorder$1);
  ctx.drawClouds__sci_Seq__V($m_Lcom_kos_wormpad_WormApp$().clouds$1);
  ctx.drawBackgroundLayers__Lcom_kos_wormpad_heroes_Worm__Lcom_kos_wormpad_geometry_RectF__V(hero.worm$1, hero.GAME$undBOARD$1);
  ctx.drawEarth__Lcom_kos_wormpad_geometry_RectF__V(hero.earthBorder$1);
  ctx.drawEnemies__sci_Set__V(hero.enemies$1);
  ctx.drawBurgers__sci_Set__V(hero.burgers$1);
  ctx.drawWorm__Lcom_kos_wormpad_heroes_Worm__V(hero.worm$1);
  ctx.drawFrameEdges__Lcom_kos_wormpad_geometry_RectF__D__V(hero.gameBorder$1, 0.5);
  ctx.ctx$1.restore();
  ctx.ctx$1.restore();
  ctx.drawWormHealth__Lcom_kos_wormpad_heroes_Worm__V(hero.worm$1)
});
$c_Lcom_kos_wormpad_WormApp$.prototype.newGame__V = (function() {
  this.isGameOver$und$1 = false;
  this.gameTime$1 = 0.0;
  this.heroes$1 = new $c_Lcom_kos_wormpad_GameHeroes();
  this.heroes$1.enemyCreatorList$1 = $as_sci_Seq(this.heroes$1.chastota$1.map__F1__O(new $c_sjsr_AnonFunction1((function($this) {
    return (function(x$2) {
      var x = $as_Lcom_kos_wormpad_game_EnemyCreatorExpression(x$2);
      return new $c_Lcom_kos_wormpad_game_EnemyCreator($m_Lcom_kos_wormpad_WormApp$().gameTime$1, x)
    })
  })(this))));
  $f_Lcom_kos_wormpad_game_WormScore__score$und$eq__I__V(this, 0);
  var element = this.screenView$1;
  $m_Lcom_kos_wormpad_game_helpers_JSHelper$().addClass__Lorg_scalajs_dom_raw_HTMLElement__T__V(element, "gone");
  this.listener$und$1.onNewGame__V()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.main__AT__V = (function(args) {
  var dpadView = $m_Lorg_scalajs_dom_package$().document__Lorg_scalajs_dom_raw_HTMLDocument().getElementById("display");
  $m_Lorg_scalajs_dom_package$().document__Lorg_scalajs_dom_raw_HTMLDocument().getElementById("display");
  this.screenView$1 = $m_Lorg_scalajs_dom_package$().document__Lorg_scalajs_dom_raw_HTMLDocument().getElementById("screens");
  $m_Lcom_kos_wormpad_WormApp$().addSvgOnClick__T__F0__V("gameOverBtnNewGame", new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      $m_Lcom_kos_wormpad_WormApp$().newGame__V()
    })
  })(this)));
  $m_Lorg_scalajs_dom_package$().window__Lorg_scalajs_dom_raw_Window().onresize = (function(arg1$2) {
    $m_Lcom_kos_wormpad_WormApp$();
    $m_Lcom_kos_wormpad_WormApp$().resize__V()
  });
  this.setupDPad__p1__Lorg_scalajs_dom_raw_HTMLDivElement__V(dpadView);
  this.resize__V();
  this.newGame__V();
  new $c_Lcom_kos_wormpad_game_GameLoop().start__F1__F0__V(new $c_sjsr_AnonFunction1((function(this$2$1) {
    return (function(tick$2) {
      var t = $uJ(tick$2);
      var lo = t.lo$2;
      var hi = t.hi$2;
      $m_Lcom_kos_wormpad_WormApp$().update__J__V(new $c_sjsr_RuntimeLong(lo, hi))
    })
  })(this)), new $c_sjsr_AnonFunction0((function(this$3) {
    return (function() {
      $m_Lcom_kos_wormpad_WormApp$().render__V()
    })
  })(this)))
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$meth$isPause__O = (function() {
  return this.pause$und$1
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$prop$listener__O = (function() {
  return this.listener$und$1
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$meth$resume__O = (function() {
  $f_Lcom_kos_wormpad_game_GameState__resume__V(this)
});
$c_Lcom_kos_wormpad_WormApp$.prototype.com$kos$wormpad$WormApp$$$anonfun$setupDPad$14__Lorg_scalajs_dom_raw_TouchEvent__V = (function(te) {
  var end = $uI(te.touches.length);
  var isEmpty$4 = (end <= 0);
  var scala$collection$immutable$Range$$lastElement$f = (((-1) + end) | 0);
  var b = $m_sci_IndexedSeq$().newBuilder__scm_Builder();
  var it = new $c_sci_RangeIterator(0, 1, scala$collection$immutable$Range$$lastElement$f, isEmpty$4);
  while (it.$$undhasNext$2) {
    var arg1 = it.next__I();
    var e = te.touches.item(arg1);
    var elem = new $c_T2(arg1, e);
    b.addOne__O__scm_Growable(elem)
  };
  $as_sc_IterableOps(b.result__O()).withFilter__F1__sc_WithFilter(new $c_sjsr_AnonFunction1((function(this$2$1) {
    return (function(x$6$2) {
      var x$6 = $as_T2(x$6$2);
      if ((x$6 !== null)) {
        var e$1 = x$6.$$und2$f;
        return ($m_Lcom_kos_wormpad_WormApp$().touchIdentifier$1 === $uD(e$1.identifier))
      } else {
        throw new $c_s_MatchError(x$6)
      }
    })
  })(this))).foreach__F1__V(new $c_sjsr_AnonFunction1((function(this$3$1) {
    return (function(x$7$2) {
      var x$7 = $as_T2(x$7$2);
      if ((x$7 !== null)) {
        $m_Lcom_kos_wormpad_WormApp$().dpad$1.touchUp__V();
        $m_Lcom_kos_wormpad_WormApp$().touchIdentifier$1 = (-1.0)
      } else {
        throw new $c_s_MatchError(x$7)
      }
    })
  })(this)))
});
$c_Lcom_kos_wormpad_WormApp$.prototype.moveEnemies__D__V = (function(timeDelta) {
  var hero = this.heroes$1;
  hero.enemies$1.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this, timeDelta$1, hero$1) {
    return (function(e$2) {
      var e = $as_Lcom_kos_wormpad_heroes_Hero(e$2);
      e.move__D__V(timeDelta$1);
      if ((!e.inArea__Lcom_kos_wormpad_geometry_RectF__Z(hero$1.heroObitanieArea$1))) {
        e.destroy$und$1 = true
      }
    })
  })(this, timeDelta, hero)));
  hero.burgers$1.foreach__F1__V(new $c_sjsr_AnonFunction1((function(this$2, timeDelta$2, hero$2) {
    return (function(e$3$2) {
      var e$3 = $as_Lcom_kos_wormpad_heroes_Hero(e$3$2);
      e$3.move__D__V(timeDelta$2);
      if ((!e$3.inArea__Lcom_kos_wormpad_geometry_RectF__Z(hero$2.burgersObitanieArea$1))) {
        e$3.destroy$und$1 = true
      }
    })
  })(this, timeDelta, hero)));
  hero.burgers$1 = $as_sci_Set(hero.burgers$1.filterNot__F1__O(new $c_sjsr_AnonFunction1((function(this$3) {
    return (function(x$9$2) {
      var x$9 = $as_Lcom_kos_wormpad_heroes_Hero(x$9$2);
      return x$9.destroy$und$1
    })
  })(this))));
  hero.enemies$1 = $as_sci_Set(hero.enemies$1.filterNot__F1__O(new $c_sjsr_AnonFunction1((function(this$4) {
    return (function(x$10$2) {
      var x$10 = $as_Lcom_kos_wormpad_heroes_Hero(x$10$2);
      return x$10.destroy$und$1
    })
  })(this))))
});
$c_Lcom_kos_wormpad_WormApp$.prototype.com$kos$wormpad$WormApp$$$anonfun$setupDPad$9__Lorg_scalajs_dom_raw_TouchEvent__V = (function(te) {
  var end = $uI(te.touches.length);
  var isEmpty$4 = (end <= 0);
  var scala$collection$immutable$Range$$lastElement$f = (((-1) + end) | 0);
  var b = $m_sci_IndexedSeq$().newBuilder__scm_Builder();
  var it = new $c_sci_RangeIterator(0, 1, scala$collection$immutable$Range$$lastElement$f, isEmpty$4);
  while (it.$$undhasNext$2) {
    var arg1 = it.next__I();
    var e = te.touches.item(arg1);
    var elem = new $c_T2(arg1, e);
    b.addOne__O__scm_Growable(elem)
  };
  $as_sc_IterableOps(b.result__O()).withFilter__F1__sc_WithFilter(new $c_sjsr_AnonFunction1((function(this$2$1) {
    return (function(x$4$2) {
      var x$4 = $as_T2(x$4$2);
      if ((x$4 !== null)) {
        var e$1 = x$4.$$und2$f;
        return ($m_Lcom_kos_wormpad_WormApp$().touchIdentifier$1 === $uD(e$1.identifier))
      } else {
        throw new $c_s_MatchError(x$4)
      }
    })
  })(this))).foreach__F1__V(new $c_sjsr_AnonFunction1((function(this$3$1) {
    return (function(x$5$2) {
      var x$5 = $as_T2(x$5$2);
      if ((x$5 !== null)) {
        $m_Lcom_kos_wormpad_WormApp$().dpad$1.touchUp__V();
        $m_Lcom_kos_wormpad_WormApp$().touchIdentifier$1 = (-1.0)
      } else {
        throw new $c_s_MatchError(x$5)
      }
    })
  })(this)))
});
$c_Lcom_kos_wormpad_WormApp$.prototype.GenerateEatObjects__p1__V = (function() {
  var hero = this.heroes$1;
  var this$1 = $m_s_util_Random$();
  var n = hero.RANDOM$undBURGER$1;
  if ((this$1.self$1.nextInt__I__I(n) === 0)) {
    var burger = new $c_Lcom_kos_wormpad_heroes_Burger().init___();
    var xp = $m_Lcom_kos_wormpad_geometry_Geometry$().randomX__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D(this.random$1, hero.burgersArea$1);
    var yp = $m_Lcom_kos_wormpad_geometry_Geometry$().randomY__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D(this.random$1, hero.burgersArea$1);
    if ((!hero.worm$1.inFreeZone__D__D__Z(xp, yp))) {
      burger.x$1 = xp;
      burger.y$1 = yp;
      burger.energy$1 = hero.ENERGY$undBURGER$1;
      var this$2 = hero.burgers$1;
      hero.burgers$1 = $as_sci_Set(this$2.incl__O__sci_SetOps(burger))
    }
  };
  var this$3 = $m_s_util_Random$();
  var n$1 = hero.RANDOM$undBOMB$1;
  if ((this$3.self$1.nextInt__I__I(n$1) === 0)) {
    var burger$2 = new $c_Lcom_kos_wormpad_heroes_Bomb();
    var xp$2 = $m_Lcom_kos_wormpad_geometry_Geometry$().randomX__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D(this.random$1, hero.burgersArea$1);
    var yp$2 = $m_Lcom_kos_wormpad_geometry_Geometry$().randomY__s_util_Random__Lcom_kos_wormpad_geometry_RectF__D(this.random$1, hero.burgersArea$1);
    if ((!hero.worm$1.inFreeZone__D__D__Z(xp$2, yp$2))) {
      burger$2.x$1 = xp$2;
      burger$2.y$1 = yp$2;
      burger$2.energy$1 = hero.ENERGY$undBOMB$1;
      var this$4 = hero.burgers$1;
      hero.burgers$1 = $as_sci_Set(this$4.incl__O__sci_SetOps(burger$2))
    }
  };
  var this$5 = $m_s_util_Random$();
  var n$2 = hero.RANDOM$undHIDE$undEAT$1;
  if ((this$5.self$1.nextInt__I__I(n$2) === 0)) {
    var this$6 = hero.burgers$1;
    if ((!this$6.isEmpty__Z())) {
      hero.burgers$1 = $as_sci_Set(hero.burgers$1.tail__O())
    }
  }
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$meth$isGameOver__O = (function() {
  return this.isGameOver$und$1
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$meth$pause__O = (function() {
  $f_Lcom_kos_wormpad_game_GameState__pause__V(this)
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$$js$exported$prop$jslistener__O = (function() {
  return this.jslistener$1
});
$c_Lcom_kos_wormpad_WormApp$.prototype.addSvgOnClick__T__F0__V = (function(id, action) {
  var x1 = $m_Lorg_scalajs_dom_package$().document__Lorg_scalajs_dom_raw_HTMLDocument().getElementById(id);
  if ($uZ((x1 instanceof SVGElement))) {
    x1.onclick = (function(action$1) {
      return (function(arg1$2) {
        $m_Lcom_kos_wormpad_WormApp$();
        action$1.apply__O()
      })
    })(action)
  }
});
$c_Lcom_kos_wormpad_WormApp$.prototype.setupDPad__p1__Lorg_scalajs_dom_raw_HTMLDivElement__V = (function(dpadView) {
  $m_Lcom_kos_wormpad_game_infrastructure_Keyboard$().init__sjs_js_Dynamic();
  addEventListener("keydown", $m_sjs_js_Any$().fromFunction1__F1__sjs_js_Function1(new $c_sjsr_AnonFunction1((function($this) {
    return (function(e$2) {
      if ((($uI(e$2.keyCode) === 32) || ($uI(e$2.keyCode) === 27))) {
        var this$2 = $m_Lcom_kos_wormpad_WormApp$();
        if (this$2.pause$und$1) {
          var this$3 = $m_Lcom_kos_wormpad_WormApp$();
          $f_Lcom_kos_wormpad_game_GameState__resume__V(this$3)
        } else {
          var this$4 = $m_Lcom_kos_wormpad_WormApp$();
          $f_Lcom_kos_wormpad_game_GameState__pause__V(this$4)
        }
      }
    })
  })(this))), false);
  var jsx$2 = $uI(dpadView.clientWidth);
  var jsx$1 = $uI(dpadView.clientHeight);
  var a = $uI(dpadView.clientHeight);
  var b = $uI(dpadView.clientWidth);
  this.dpad$1 = new $c_Lcom_kos_wormpad_dpad_DPad(((jsx$2 / 2) | 0), ((jsx$1 / 2) | 0), ((((a < b) ? a : b) / 4) | 0), $m_Lcom_kos_wormpad_heroes_Worm$().WORM$undACCELERATION$1);
  dpadView.addEventListener("touchstart", (function(arg1$2) {
    return $m_Lcom_kos_wormpad_WormApp$().com$kos$wormpad$WormApp$$$anonfun$setupDPad$2__Lorg_scalajs_dom_raw_TouchEvent__O(arg1$2)
  }), false);
  dpadView.addEventListener("touchmove", (function(arg1$2$1) {
    $m_Lcom_kos_wormpad_WormApp$().com$kos$wormpad$WormApp$$$anonfun$setupDPad$4__Lorg_scalajs_dom_raw_TouchEvent__V(arg1$2$1)
  }), false);
  dpadView.addEventListener("touchend", (function(arg1$2$2) {
    $m_Lcom_kos_wormpad_WormApp$().com$kos$wormpad$WormApp$$$anonfun$setupDPad$9__Lorg_scalajs_dom_raw_TouchEvent__V(arg1$2$2)
  }), false);
  dpadView.addEventListener("touchcancel", (function(arg1$2$3) {
    $m_Lcom_kos_wormpad_WormApp$().com$kos$wormpad$WormApp$$$anonfun$setupDPad$14__Lorg_scalajs_dom_raw_TouchEvent__V(arg1$2$3)
  }), false);
  dpadView.onmousedown = (function(arg1$2$4) {
    $m_Lcom_kos_wormpad_WormApp$().com$kos$wormpad$WormApp$$$anonfun$setupDPad$19__Lorg_scalajs_dom_raw_MouseEvent__V(arg1$2$4)
  });
  dpadView.onmousemove = (function(arg1$2$5) {
    $m_Lcom_kos_wormpad_WormApp$().com$kos$wormpad$WormApp$$$anonfun$setupDPad$21__Lorg_scalajs_dom_raw_MouseEvent__V(arg1$2$5)
  });
  dpadView.onmouseup = (function(arg1$2$6) {
    $m_Lcom_kos_wormpad_WormApp$();
    $m_Lcom_kos_wormpad_WormApp$().dpad$1.touchUp__V()
  });
  dpadView.onmouseout = (function(arg1$2$7) {
    $m_Lcom_kos_wormpad_WormApp$();
    $m_Lcom_kos_wormpad_WormApp$().dpad$1.touchUp__V()
  })
});
$c_Lcom_kos_wormpad_WormApp$.prototype.moveClouds__D__V = (function(timeDelta) {
  this.clouds$1.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this, timeDelta$1) {
    return (function(c$2) {
      var c = $as_Lcom_kos_wormpad_heroes_Cloud(c$2);
      c.x$1 = (c.x$1 + (timeDelta$1 * c.velocityX$2));
      if ((c.x$1 > $m_Lcom_kos_wormpad_WormApp$().heroes$1.GAME$undBOARD$1.right$1)) {
        c.x$1 = $fround(($m_Lcom_kos_wormpad_WormApp$().heroes$1.GAME$undBOARD$1.left$1 - $fround(c.width$2)))
      }
    })
  })(this, timeDelta)))
});
Object.defineProperty($c_Lcom_kos_wormpad_WormApp$.prototype, "listener", {
  "get": (function() {
    return this.$$js$exported$prop$listener__O()
  }),
  "configurable": true
});
Object.defineProperty($c_Lcom_kos_wormpad_WormApp$.prototype, "jslistener", {
  "get": (function() {
    return this.$$js$exported$prop$jslistener__O()
  }),
  "set": (function(arg$1) {
    var prep0 = $as_Lcom_kos_wormpad_game_GameListener(arg$1);
    this.$$js$exported$prop$jslistener__Lcom_kos_wormpad_game_GameListener__O(prep0)
  }),
  "configurable": true
});
Object.defineProperty($c_Lcom_kos_wormpad_WormApp$.prototype, "listener_", {
  "get": (function() {
    return this.$$js$exported$prop$listener$und__O()
  }),
  "set": (function(arg$1) {
    var prep0 = $as_Lcom_kos_wormpad_game_GameListenerDelegate(arg$1);
    this.$$js$exported$prop$listener$und__Lcom_kos_wormpad_game_GameListenerDelegate__O(prep0)
  }),
  "configurable": true
});
$c_Lcom_kos_wormpad_WormApp$.prototype.togglePause = (function() {
  return this.$$js$exported$meth$togglePause__O()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.resume = (function() {
  return this.$$js$exported$meth$resume__O()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.pause = (function() {
  return this.$$js$exported$meth$pause__O()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.isGameOver = (function() {
  return this.$$js$exported$meth$isGameOver__O()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.isPause = (function() {
  return this.$$js$exported$meth$isPause__O()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.resize = (function() {
  return this.$$js$exported$meth$resize__O()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.gameOver = (function() {
  return this.$$js$exported$meth$gameOver__O()
});
$c_Lcom_kos_wormpad_WormApp$.prototype.newGame = (function() {
  return this.$$js$exported$meth$newGame__O()
});
var $d_Lcom_kos_wormpad_WormApp$ = new $TypeData().initClass({
  Lcom_kos_wormpad_WormApp$: 0
}, false, "com.kos.wormpad.WormApp$", {
  Lcom_kos_wormpad_WormApp$: 1,
  O: 1,
  Lcom_kos_wormpad_game_GameState: 1,
  Lcom_kos_wormpad_game_WormScore: 1,
  Lcom_kos_wormpad_GameStateDelegate: 1,
  Lcom_kos_wormpad_game_AudioState: 1
});
$c_Lcom_kos_wormpad_WormApp$.prototype.$classData = $d_Lcom_kos_wormpad_WormApp$;
var $n_Lcom_kos_wormpad_WormApp$ = (void 0);
function $m_Lcom_kos_wormpad_WormApp$() {
  if ((!$n_Lcom_kos_wormpad_WormApp$)) {
    $n_Lcom_kos_wormpad_WormApp$ = new $c_Lcom_kos_wormpad_WormApp$()
  };
  return $n_Lcom_kos_wormpad_WormApp$
}
/** @constructor */
function $c_Lcom_kos_wormpad_game_EnemyCreatorExpression(deltaTime, creator, area) {
  this.deltaTime$1 = 0.0;
  this.creator$1 = null;
  this.area$1 = null;
  this.deltaTime$1 = deltaTime;
  this.creator$1 = creator;
  this.area$1 = area
}
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype = new $h_O();
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.constructor = $c_Lcom_kos_wormpad_game_EnemyCreatorExpression;
/** @constructor */
function $h_Lcom_kos_wormpad_game_EnemyCreatorExpression() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype = $c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype;
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.productPrefix__T = (function() {
  return "EnemyCreatorExpression"
});
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.productArity__I = (function() {
  return 3
});
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.equals__O__Z = (function(x$1) {
  if ((this === x$1)) {
    return true
  } else if ($is_Lcom_kos_wormpad_game_EnemyCreatorExpression(x$1)) {
    var EnemyCreatorExpression$1 = $as_Lcom_kos_wormpad_game_EnemyCreatorExpression(x$1);
    if ((this.deltaTime$1 === EnemyCreatorExpression$1.deltaTime$1)) {
      var x = this.creator$1;
      var x$2 = EnemyCreatorExpression$1.creator$1;
      var jsx$1 = (x === x$2)
    } else {
      var jsx$1 = false
    };
    if (jsx$1) {
      var x$3 = this.area$1;
      var x$4 = EnemyCreatorExpression$1.area$1;
      return ((x$3 === null) ? (x$4 === null) : x$3.equals__O__Z(x$4))
    } else {
      return false
    }
  } else {
    return false
  }
});
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.productElement__I__O = (function(x$1) {
  switch (x$1) {
    case 0: {
      return this.deltaTime$1;
      break
    }
    case 1: {
      return this.creator$1;
      break
    }
    case 2: {
      return this.area$1;
      break
    }
    default: {
      throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
    }
  }
});
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.toString__T = (function() {
  return $m_sr_ScalaRunTime$().$$undtoString__s_Product__T(this)
});
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.hashCode__I = (function() {
  var acc = (-889275714);
  acc = $m_sr_Statics$().mix__I__I__I(acc, $m_sr_Statics$().doubleHash__D__I(this.deltaTime$1));
  acc = $m_sr_Statics$().mix__I__I__I(acc, $m_sr_Statics$().anyHash__O__I(this.creator$1));
  acc = $m_sr_Statics$().mix__I__I__I(acc, $m_sr_Statics$().anyHash__O__I(this.area$1));
  return $m_sr_Statics$().finalizeHash__I__I__I(acc, 3)
});
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
function $is_Lcom_kos_wormpad_game_EnemyCreatorExpression(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_game_EnemyCreatorExpression)))
}
function $as_Lcom_kos_wormpad_game_EnemyCreatorExpression(obj) {
  return (($is_Lcom_kos_wormpad_game_EnemyCreatorExpression(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.game.EnemyCreatorExpression"))
}
function $isArrayOf_Lcom_kos_wormpad_game_EnemyCreatorExpression(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_game_EnemyCreatorExpression)))
}
function $asArrayOf_Lcom_kos_wormpad_game_EnemyCreatorExpression(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_game_EnemyCreatorExpression(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.game.EnemyCreatorExpression;", depth))
}
var $d_Lcom_kos_wormpad_game_EnemyCreatorExpression = new $TypeData().initClass({
  Lcom_kos_wormpad_game_EnemyCreatorExpression: 0
}, false, "com.kos.wormpad.game.EnemyCreatorExpression", {
  Lcom_kos_wormpad_game_EnemyCreatorExpression: 1,
  O: 1,
  s_Product: 1,
  s_Equals: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_Lcom_kos_wormpad_game_EnemyCreatorExpression.prototype.$classData = $d_Lcom_kos_wormpad_game_EnemyCreatorExpression;
/** @constructor */
function $c_Lcom_kos_wormpad_geometry_Force(x, y, mass) {
  this.x$1 = 0.0;
  this.y$1 = 0.0;
  this.mass$1 = 0.0;
  this.x$1 = x;
  this.y$1 = y;
  this.mass$1 = mass
}
$c_Lcom_kos_wormpad_geometry_Force.prototype = new $h_O();
$c_Lcom_kos_wormpad_geometry_Force.prototype.constructor = $c_Lcom_kos_wormpad_geometry_Force;
/** @constructor */
function $h_Lcom_kos_wormpad_geometry_Force() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_geometry_Force.prototype = $c_Lcom_kos_wormpad_geometry_Force.prototype;
$c_Lcom_kos_wormpad_geometry_Force.prototype.productPrefix__T = (function() {
  return "Force"
});
$c_Lcom_kos_wormpad_geometry_Force.prototype.productArity__I = (function() {
  return 3
});
$c_Lcom_kos_wormpad_geometry_Force.prototype.equals__O__Z = (function(x$1) {
  if ((this === x$1)) {
    return true
  } else if ($is_Lcom_kos_wormpad_geometry_Force(x$1)) {
    var Force$1 = $as_Lcom_kos_wormpad_geometry_Force(x$1);
    return (((this.x$1 === Force$1.x$1) && (this.y$1 === Force$1.y$1)) && (this.mass$1 === Force$1.mass$1))
  } else {
    return false
  }
});
$c_Lcom_kos_wormpad_geometry_Force.prototype.productElement__I__O = (function(x$1) {
  switch (x$1) {
    case 0: {
      return this.x$1;
      break
    }
    case 1: {
      return this.y$1;
      break
    }
    case 2: {
      return this.mass$1;
      break
    }
    default: {
      throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
    }
  }
});
$c_Lcom_kos_wormpad_geometry_Force.prototype.toString__T = (function() {
  return $m_sr_ScalaRunTime$().$$undtoString__s_Product__T(this)
});
$c_Lcom_kos_wormpad_geometry_Force.prototype.hashCode__I = (function() {
  var acc = (-889275714);
  acc = $m_sr_Statics$().mix__I__I__I(acc, $m_sr_Statics$().doubleHash__D__I(this.x$1));
  acc = $m_sr_Statics$().mix__I__I__I(acc, $m_sr_Statics$().doubleHash__D__I(this.y$1));
  acc = $m_sr_Statics$().mix__I__I__I(acc, $m_sr_Statics$().doubleHash__D__I(this.mass$1));
  return $m_sr_Statics$().finalizeHash__I__I__I(acc, 3)
});
$c_Lcom_kos_wormpad_geometry_Force.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
function $is_Lcom_kos_wormpad_geometry_Force(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_geometry_Force)))
}
function $as_Lcom_kos_wormpad_geometry_Force(obj) {
  return (($is_Lcom_kos_wormpad_geometry_Force(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.geometry.Force"))
}
function $isArrayOf_Lcom_kos_wormpad_geometry_Force(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_geometry_Force)))
}
function $asArrayOf_Lcom_kos_wormpad_geometry_Force(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_geometry_Force(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.geometry.Force;", depth))
}
var $d_Lcom_kos_wormpad_geometry_Force = new $TypeData().initClass({
  Lcom_kos_wormpad_geometry_Force: 0
}, false, "com.kos.wormpad.geometry.Force", {
  Lcom_kos_wormpad_geometry_Force: 1,
  O: 1,
  s_Product: 1,
  s_Equals: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_Lcom_kos_wormpad_geometry_Force.prototype.$classData = $d_Lcom_kos_wormpad_geometry_Force;
/** @constructor */
function $c_Lcom_kos_wormpad_geometry_RectF(left, bottom, right, top) {
  this.left$1 = 0.0;
  this.bottom$1 = 0.0;
  this.right$1 = 0.0;
  this.top$1 = 0.0;
  this.left$1 = left;
  this.bottom$1 = bottom;
  this.right$1 = right;
  this.top$1 = top
}
$c_Lcom_kos_wormpad_geometry_RectF.prototype = new $h_O();
$c_Lcom_kos_wormpad_geometry_RectF.prototype.constructor = $c_Lcom_kos_wormpad_geometry_RectF;
/** @constructor */
function $h_Lcom_kos_wormpad_geometry_RectF() {
  /*<skip>*/
}
$h_Lcom_kos_wormpad_geometry_RectF.prototype = $c_Lcom_kos_wormpad_geometry_RectF.prototype;
$c_Lcom_kos_wormpad_geometry_RectF.prototype.productPrefix__T = (function() {
  return "RectF"
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.productArity__I = (function() {
  return 4
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.width__F = (function() {
  return $fround((this.right$1 - this.left$1))
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.equals__O__Z = (function(x$1) {
  if ((this === x$1)) {
    return true
  } else if ($is_Lcom_kos_wormpad_geometry_RectF(x$1)) {
    var RectF$1 = $as_Lcom_kos_wormpad_geometry_RectF(x$1);
    return ((((this.left$1 === RectF$1.left$1) && (this.bottom$1 === RectF$1.bottom$1)) && (this.right$1 === RectF$1.right$1)) && (this.top$1 === RectF$1.top$1))
  } else {
    return false
  }
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.productElement__I__O = (function(x$1) {
  switch (x$1) {
    case 0: {
      return this.left$1;
      break
    }
    case 1: {
      return this.bottom$1;
      break
    }
    case 2: {
      return this.right$1;
      break
    }
    case 3: {
      return this.top$1;
      break
    }
    default: {
      throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
    }
  }
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.toString__T = (function() {
  return $m_sr_ScalaRunTime$().$$undtoString__s_Product__T(this)
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.height__F = (function() {
  return $fround((this.top$1 - this.bottom$1))
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.hashCode__I = (function() {
  var acc = (-889275714);
  var jsx$2 = $m_sr_Statics$();
  var jsx$1 = acc;
  var this$1 = $m_sr_Statics$();
  var fv = this.left$1;
  acc = jsx$2.mix__I__I__I(jsx$1, this$1.doubleHash__D__I(fv));
  var jsx$4 = $m_sr_Statics$();
  var jsx$3 = acc;
  var this$2 = $m_sr_Statics$();
  var fv$1 = this.bottom$1;
  acc = jsx$4.mix__I__I__I(jsx$3, this$2.doubleHash__D__I(fv$1));
  var jsx$6 = $m_sr_Statics$();
  var jsx$5 = acc;
  var this$3 = $m_sr_Statics$();
  var fv$2 = this.right$1;
  acc = jsx$6.mix__I__I__I(jsx$5, this$3.doubleHash__D__I(fv$2));
  var jsx$8 = $m_sr_Statics$();
  var jsx$7 = acc;
  var this$4 = $m_sr_Statics$();
  var fv$3 = this.top$1;
  acc = jsx$8.mix__I__I__I(jsx$7, this$4.doubleHash__D__I(fv$3));
  return $m_sr_Statics$().finalizeHash__I__I__I(acc, 4)
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
function $is_Lcom_kos_wormpad_geometry_RectF(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.Lcom_kos_wormpad_geometry_RectF)))
}
function $as_Lcom_kos_wormpad_geometry_RectF(obj) {
  return (($is_Lcom_kos_wormpad_geometry_RectF(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "com.kos.wormpad.geometry.RectF"))
}
function $isArrayOf_Lcom_kos_wormpad_geometry_RectF(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.Lcom_kos_wormpad_geometry_RectF)))
}
function $asArrayOf_Lcom_kos_wormpad_geometry_RectF(obj, depth) {
  return (($isArrayOf_Lcom_kos_wormpad_geometry_RectF(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lcom.kos.wormpad.geometry.RectF;", depth))
}
var $d_Lcom_kos_wormpad_geometry_RectF = new $TypeData().initClass({
  Lcom_kos_wormpad_geometry_RectF: 0
}, false, "com.kos.wormpad.geometry.RectF", {
  Lcom_kos_wormpad_geometry_RectF: 1,
  O: 1,
  s_Product: 1,
  s_Equals: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_Lcom_kos_wormpad_geometry_RectF.prototype.$classData = $d_Lcom_kos_wormpad_geometry_RectF;
/** @constructor */
function $c_Ljava_io_FilterOutputStream() {
  this.out$2 = null
}
$c_Ljava_io_FilterOutputStream.prototype = new $h_Ljava_io_OutputStream();
$c_Ljava_io_FilterOutputStream.prototype.constructor = $c_Ljava_io_FilterOutputStream;
/** @constructor */
function $h_Ljava_io_FilterOutputStream() {
  /*<skip>*/
}
$h_Ljava_io_FilterOutputStream.prototype = $c_Ljava_io_FilterOutputStream.prototype;
$c_Ljava_io_FilterOutputStream.prototype.init___Ljava_io_OutputStream = (function(out) {
  this.out$2 = out;
  return this
});
/** @constructor */
function $c_jl_ArithmeticException(s) {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null;
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, s, null, true, true)
}
$c_jl_ArithmeticException.prototype = new $h_jl_RuntimeException();
$c_jl_ArithmeticException.prototype.constructor = $c_jl_ArithmeticException;
/** @constructor */
function $h_jl_ArithmeticException() {
  /*<skip>*/
}
$h_jl_ArithmeticException.prototype = $c_jl_ArithmeticException.prototype;
var $d_jl_ArithmeticException = new $TypeData().initClass({
  jl_ArithmeticException: 0
}, false, "java.lang.ArithmeticException", {
  jl_ArithmeticException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_ArithmeticException.prototype.$classData = $d_jl_ArithmeticException;
/** @constructor */
function $c_jl_ClassCastException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_ClassCastException.prototype = new $h_jl_RuntimeException();
$c_jl_ClassCastException.prototype.constructor = $c_jl_ClassCastException;
/** @constructor */
function $h_jl_ClassCastException() {
  /*<skip>*/
}
$h_jl_ClassCastException.prototype = $c_jl_ClassCastException.prototype;
$c_jl_ClassCastException.prototype.init___T = (function(s) {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, s, null, true, true);
  return this
});
function $is_jl_ClassCastException(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.jl_ClassCastException)))
}
function $as_jl_ClassCastException(obj) {
  return (($is_jl_ClassCastException(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "java.lang.ClassCastException"))
}
function $isArrayOf_jl_ClassCastException(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.jl_ClassCastException)))
}
function $asArrayOf_jl_ClassCastException(obj, depth) {
  return (($isArrayOf_jl_ClassCastException(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Ljava.lang.ClassCastException;", depth))
}
var $d_jl_ClassCastException = new $TypeData().initClass({
  jl_ClassCastException: 0
}, false, "java.lang.ClassCastException", {
  jl_ClassCastException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_ClassCastException.prototype.$classData = $d_jl_ClassCastException;
/** @constructor */
function $c_jl_IllegalArgumentException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_IllegalArgumentException.prototype = new $h_jl_RuntimeException();
$c_jl_IllegalArgumentException.prototype.constructor = $c_jl_IllegalArgumentException;
/** @constructor */
function $h_jl_IllegalArgumentException() {
  /*<skip>*/
}
$h_jl_IllegalArgumentException.prototype = $c_jl_IllegalArgumentException.prototype;
$c_jl_IllegalArgumentException.prototype.init___ = (function() {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true);
  return this
});
$c_jl_IllegalArgumentException.prototype.init___T = (function(s) {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, s, null, true, true);
  return this
});
var $d_jl_IllegalArgumentException = new $TypeData().initClass({
  jl_IllegalArgumentException: 0
}, false, "java.lang.IllegalArgumentException", {
  jl_IllegalArgumentException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_IllegalArgumentException.prototype.$classData = $d_jl_IllegalArgumentException;
/** @constructor */
function $c_jl_IndexOutOfBoundsException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_IndexOutOfBoundsException.prototype = new $h_jl_RuntimeException();
$c_jl_IndexOutOfBoundsException.prototype.constructor = $c_jl_IndexOutOfBoundsException;
/** @constructor */
function $h_jl_IndexOutOfBoundsException() {
  /*<skip>*/
}
$h_jl_IndexOutOfBoundsException.prototype = $c_jl_IndexOutOfBoundsException.prototype;
$c_jl_IndexOutOfBoundsException.prototype.init___T = (function(s) {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, s, null, true, true);
  return this
});
var $d_jl_IndexOutOfBoundsException = new $TypeData().initClass({
  jl_IndexOutOfBoundsException: 0
}, false, "java.lang.IndexOutOfBoundsException", {
  jl_IndexOutOfBoundsException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_IndexOutOfBoundsException.prototype.$classData = $d_jl_IndexOutOfBoundsException;
/** @constructor */
function $c_jl_JSConsoleBasedPrintStream$DummyOutputStream() {
  /*<skip>*/
}
$c_jl_JSConsoleBasedPrintStream$DummyOutputStream.prototype = new $h_Ljava_io_OutputStream();
$c_jl_JSConsoleBasedPrintStream$DummyOutputStream.prototype.constructor = $c_jl_JSConsoleBasedPrintStream$DummyOutputStream;
/** @constructor */
function $h_jl_JSConsoleBasedPrintStream$DummyOutputStream() {
  /*<skip>*/
}
$h_jl_JSConsoleBasedPrintStream$DummyOutputStream.prototype = $c_jl_JSConsoleBasedPrintStream$DummyOutputStream.prototype;
var $d_jl_JSConsoleBasedPrintStream$DummyOutputStream = new $TypeData().initClass({
  jl_JSConsoleBasedPrintStream$DummyOutputStream: 0
}, false, "java.lang.JSConsoleBasedPrintStream$DummyOutputStream", {
  jl_JSConsoleBasedPrintStream$DummyOutputStream: 1,
  Ljava_io_OutputStream: 1,
  O: 1,
  Ljava_io_Closeable: 1,
  jl_AutoCloseable: 1,
  Ljava_io_Flushable: 1
});
$c_jl_JSConsoleBasedPrintStream$DummyOutputStream.prototype.$classData = $d_jl_JSConsoleBasedPrintStream$DummyOutputStream;
/** @constructor */
function $c_jl_NegativeArraySizeException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null;
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true)
}
$c_jl_NegativeArraySizeException.prototype = new $h_jl_RuntimeException();
$c_jl_NegativeArraySizeException.prototype.constructor = $c_jl_NegativeArraySizeException;
/** @constructor */
function $h_jl_NegativeArraySizeException() {
  /*<skip>*/
}
$h_jl_NegativeArraySizeException.prototype = $c_jl_NegativeArraySizeException.prototype;
var $d_jl_NegativeArraySizeException = new $TypeData().initClass({
  jl_NegativeArraySizeException: 0
}, false, "java.lang.NegativeArraySizeException", {
  jl_NegativeArraySizeException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_NegativeArraySizeException.prototype.$classData = $d_jl_NegativeArraySizeException;
/** @constructor */
function $c_jl_NullPointerException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null;
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true)
}
$c_jl_NullPointerException.prototype = new $h_jl_RuntimeException();
$c_jl_NullPointerException.prototype.constructor = $c_jl_NullPointerException;
/** @constructor */
function $h_jl_NullPointerException() {
  /*<skip>*/
}
$h_jl_NullPointerException.prototype = $c_jl_NullPointerException.prototype;
var $d_jl_NullPointerException = new $TypeData().initClass({
  jl_NullPointerException: 0
}, false, "java.lang.NullPointerException", {
  jl_NullPointerException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_NullPointerException.prototype.$classData = $d_jl_NullPointerException;
/** @constructor */
function $c_jl_UnsupportedOperationException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_UnsupportedOperationException.prototype = new $h_jl_RuntimeException();
$c_jl_UnsupportedOperationException.prototype.constructor = $c_jl_UnsupportedOperationException;
/** @constructor */
function $h_jl_UnsupportedOperationException() {
  /*<skip>*/
}
$h_jl_UnsupportedOperationException.prototype = $c_jl_UnsupportedOperationException.prototype;
$c_jl_UnsupportedOperationException.prototype.init___ = (function() {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true);
  return this
});
$c_jl_UnsupportedOperationException.prototype.init___T = (function(s) {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, s, null, true, true);
  return this
});
var $d_jl_UnsupportedOperationException = new $TypeData().initClass({
  jl_UnsupportedOperationException: 0
}, false, "java.lang.UnsupportedOperationException", {
  jl_UnsupportedOperationException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_UnsupportedOperationException.prototype.$classData = $d_jl_UnsupportedOperationException;
/** @constructor */
function $c_ju_NoSuchElementException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_ju_NoSuchElementException.prototype = new $h_jl_RuntimeException();
$c_ju_NoSuchElementException.prototype.constructor = $c_ju_NoSuchElementException;
/** @constructor */
function $h_ju_NoSuchElementException() {
  /*<skip>*/
}
$h_ju_NoSuchElementException.prototype = $c_ju_NoSuchElementException.prototype;
$c_ju_NoSuchElementException.prototype.init___ = (function() {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true);
  return this
});
$c_ju_NoSuchElementException.prototype.init___T = (function(s) {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, s, null, true, true);
  return this
});
var $d_ju_NoSuchElementException = new $TypeData().initClass({
  ju_NoSuchElementException: 0
}, false, "java.util.NoSuchElementException", {
  ju_NoSuchElementException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_ju_NoSuchElementException.prototype.$classData = $d_ju_NoSuchElementException;
/** @constructor */
function $c_s_MatchError(obj) {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null;
  this.objString$4 = null;
  this.obj$4 = null;
  this.bitmap$0$4 = false;
  this.obj$4 = obj;
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true)
}
$c_s_MatchError.prototype = new $h_jl_RuntimeException();
$c_s_MatchError.prototype.constructor = $c_s_MatchError;
/** @constructor */
function $h_s_MatchError() {
  /*<skip>*/
}
$h_s_MatchError.prototype = $c_s_MatchError.prototype;
$c_s_MatchError.prototype.objString$lzycompute__p4__T = (function() {
  if ((!this.bitmap$0$4)) {
    this.objString$4 = ((this.obj$4 === null) ? "null" : this.liftedTree1$1__p4__T());
    this.bitmap$0$4 = true
  };
  return this.objString$4
});
$c_s_MatchError.prototype.ofClass$1__p4__T = (function() {
  var this$1 = this.obj$4;
  return ("of class " + $objectGetClass(this$1).getName__T())
});
$c_s_MatchError.prototype.liftedTree1$1__p4__T = (function() {
  try {
    return ((($dp_toString__T(this.obj$4) + " (") + this.ofClass$1__p4__T()) + ")")
  } catch (e) {
    var e$2 = $m_sjsr_package$().wrapJavaScriptException__O__jl_Throwable(e);
    if ((e$2 !== null)) {
      return ("an instance " + this.ofClass$1__p4__T())
    } else {
      throw e
    }
  }
});
$c_s_MatchError.prototype.getMessage__T = (function() {
  return this.objString__p4__T()
});
$c_s_MatchError.prototype.objString__p4__T = (function() {
  return ((!this.bitmap$0$4) ? this.objString$lzycompute__p4__T() : this.objString$4)
});
var $d_s_MatchError = new $TypeData().initClass({
  s_MatchError: 0
}, false, "scala.MatchError", {
  s_MatchError: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_s_MatchError.prototype.$classData = $d_s_MatchError;
/** @constructor */
function $c_s_Option() {
  /*<skip>*/
}
$c_s_Option.prototype = new $h_O();
$c_s_Option.prototype.constructor = $c_s_Option;
/** @constructor */
function $h_s_Option() {
  /*<skip>*/
}
$h_s_Option.prototype = $c_s_Option.prototype;
/** @constructor */
function $c_s_Predef$$eq$colon$eq() {
  /*<skip>*/
}
$c_s_Predef$$eq$colon$eq.prototype = new $h_s_Predef$$less$colon$less();
$c_s_Predef$$eq$colon$eq.prototype.constructor = $c_s_Predef$$eq$colon$eq;
/** @constructor */
function $h_s_Predef$$eq$colon$eq() {
  /*<skip>*/
}
$h_s_Predef$$eq$colon$eq.prototype = $c_s_Predef$$eq$colon$eq.prototype;
/** @constructor */
function $c_s_Product$$anon$1($$outer) {
  this.c$2 = 0;
  this.cmax$2 = 0;
  this.$$outer$2 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.c$2 = 0;
  this.cmax$2 = $$outer.productArity__I()
}
$c_s_Product$$anon$1.prototype = new $h_sc_AbstractIterator();
$c_s_Product$$anon$1.prototype.constructor = $c_s_Product$$anon$1;
/** @constructor */
function $h_s_Product$$anon$1() {
  /*<skip>*/
}
$h_s_Product$$anon$1.prototype = $c_s_Product$$anon$1.prototype;
$c_s_Product$$anon$1.prototype.next__O = (function() {
  var result = this.$$outer$2.productElement__I__O(this.c$2);
  this.c$2 = ((1 + this.c$2) | 0);
  return result
});
$c_s_Product$$anon$1.prototype.hasNext__Z = (function() {
  return (this.c$2 < this.cmax$2)
});
var $d_s_Product$$anon$1 = new $TypeData().initClass({
  s_Product$$anon$1: 0
}, false, "scala.Product$$anon$1", {
  s_Product$$anon$1: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_s_Product$$anon$1.prototype.$classData = $d_s_Product$$anon$1;
function $f_s_math_Ordering__lteq__O__O__Z($thiz, x, y) {
  return ($thiz.compare__O__O__I(x, y) <= 0)
}
function $f_s_reflect_ClassTag__equals__O__Z($thiz, x) {
  if ($is_s_reflect_ClassTag(x)) {
    var x$2 = $thiz.runtimeClass__jl_Class();
    var x$3 = $as_s_reflect_ClassTag(x).runtimeClass__jl_Class();
    return (x$2 === x$3)
  } else {
    return false
  }
}
function $f_s_reflect_ClassTag__prettyprint$1__ps_reflect_ClassTag__jl_Class__T($thiz, clazz) {
  if (clazz.isArray__Z()) {
    var clazz$1 = clazz.getComponentType__jl_Class();
    return (("Array[" + $f_s_reflect_ClassTag__prettyprint$1__ps_reflect_ClassTag__jl_Class__T($thiz, clazz$1)) + "]")
  } else {
    return clazz.getName__T()
  }
}
function $is_s_reflect_ClassTag(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.s_reflect_ClassTag)))
}
function $as_s_reflect_ClassTag(obj) {
  return (($is_s_reflect_ClassTag(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.reflect.ClassTag"))
}
function $isArrayOf_s_reflect_ClassTag(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.s_reflect_ClassTag)))
}
function $asArrayOf_s_reflect_ClassTag(obj, depth) {
  return (($isArrayOf_s_reflect_ClassTag(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.reflect.ClassTag;", depth))
}
/** @constructor */
function $c_sc_IndexedSeqOps$$anon$1($$outer) {
  this.i$2 = 0;
  this.$$outer$2 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.i$2 = $$outer.length__I()
}
$c_sc_IndexedSeqOps$$anon$1.prototype = new $h_sc_AbstractIterator();
$c_sc_IndexedSeqOps$$anon$1.prototype.constructor = $c_sc_IndexedSeqOps$$anon$1;
/** @constructor */
function $h_sc_IndexedSeqOps$$anon$1() {
  /*<skip>*/
}
$h_sc_IndexedSeqOps$$anon$1.prototype = $c_sc_IndexedSeqOps$$anon$1.prototype;
$c_sc_IndexedSeqOps$$anon$1.prototype.next__O = (function() {
  if ((this.i$2 > 0)) {
    this.i$2 = (((-1) + this.i$2) | 0);
    return this.$$outer$2.apply__I__O(this.i$2)
  } else {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  }
});
$c_sc_IndexedSeqOps$$anon$1.prototype.hasNext__Z = (function() {
  return (this.i$2 > 0)
});
var $d_sc_IndexedSeqOps$$anon$1 = new $TypeData().initClass({
  sc_IndexedSeqOps$$anon$1: 0
}, false, "scala.collection.IndexedSeqOps$$anon$1", {
  sc_IndexedSeqOps$$anon$1: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_IndexedSeqOps$$anon$1.prototype.$classData = $d_sc_IndexedSeqOps$$anon$1;
function $f_sc_Iterable__toString__T($thiz) {
  var start = ($thiz.className__T() + "(");
  return $f_sc_IterableOnceOps__mkString__T__T__T__T($thiz, start, ", ", ")")
}
function $is_sc_Iterable(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_Iterable)))
}
function $as_sc_Iterable(obj) {
  return (($is_sc_Iterable(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.Iterable"))
}
function $isArrayOf_sc_Iterable(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_Iterable)))
}
function $asArrayOf_sc_Iterable(obj, depth) {
  return (($isArrayOf_sc_Iterable(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.Iterable;", depth))
}
/** @constructor */
function $c_sc_Iterable$() {
  this.delegate$1 = null;
  $c_sc_IterableFactory$Delegate.prototype.init___sc_IterableFactory.call(this, $m_sci_Iterable$())
}
$c_sc_Iterable$.prototype = new $h_sc_IterableFactory$Delegate();
$c_sc_Iterable$.prototype.constructor = $c_sc_Iterable$;
/** @constructor */
function $h_sc_Iterable$() {
  /*<skip>*/
}
$h_sc_Iterable$.prototype = $c_sc_Iterable$.prototype;
var $d_sc_Iterable$ = new $TypeData().initClass({
  sc_Iterable$: 0
}, false, "scala.collection.Iterable$", {
  sc_Iterable$: 1,
  sc_IterableFactory$Delegate: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sc_Iterable$.prototype.$classData = $d_sc_Iterable$;
var $n_sc_Iterable$ = (void 0);
function $m_sc_Iterable$() {
  if ((!$n_sc_Iterable$)) {
    $n_sc_Iterable$ = new $c_sc_Iterable$()
  };
  return $n_sc_Iterable$
}
/** @constructor */
function $c_sc_Iterator$$anon$10($$outer, f$3) {
  this.myCurrent$2 = null;
  this.$$outer$2 = null;
  this.f$3$2 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.f$3$2 = f$3;
  this.myCurrent$2 = $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
}
$c_sc_Iterator$$anon$10.prototype = new $h_sc_AbstractIterator();
$c_sc_Iterator$$anon$10.prototype.constructor = $c_sc_Iterator$$anon$10;
/** @constructor */
function $h_sc_Iterator$$anon$10() {
  /*<skip>*/
}
$h_sc_Iterator$$anon$10.prototype = $c_sc_Iterator$$anon$10.prototype;
$c_sc_Iterator$$anon$10.prototype.next__O = (function() {
  return this.current__p2__sc_Iterator().next__O()
});
$c_sc_Iterator$$anon$10.prototype.hasNext__Z = (function() {
  return this.current__p2__sc_Iterator().hasNext__Z()
});
$c_sc_Iterator$$anon$10.prototype.current__p2__sc_Iterator = (function() {
  while (((!this.myCurrent$2.hasNext__Z()) && this.$$outer$2.hasNext__Z())) {
    this.myCurrent$2 = $as_sc_IterableOnce(this.f$3$2.apply__O__O(this.$$outer$2.next__O())).iterator__sc_Iterator()
  };
  return this.myCurrent$2
});
var $d_sc_Iterator$$anon$10 = new $TypeData().initClass({
  sc_Iterator$$anon$10: 0
}, false, "scala.collection.Iterator$$anon$10", {
  sc_Iterator$$anon$10: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_Iterator$$anon$10.prototype.$classData = $d_sc_Iterator$$anon$10;
/** @constructor */
function $c_sc_Iterator$$anon$18() {
  /*<skip>*/
}
$c_sc_Iterator$$anon$18.prototype = new $h_sc_AbstractIterator();
$c_sc_Iterator$$anon$18.prototype.constructor = $c_sc_Iterator$$anon$18;
/** @constructor */
function $h_sc_Iterator$$anon$18() {
  /*<skip>*/
}
$h_sc_Iterator$$anon$18.prototype = $c_sc_Iterator$$anon$18.prototype;
$c_sc_Iterator$$anon$18.prototype.next__O = (function() {
  this.next__E()
});
$c_sc_Iterator$$anon$18.prototype.next__E = (function() {
  throw new $c_ju_NoSuchElementException().init___T("next on empty iterator")
});
$c_sc_Iterator$$anon$18.prototype.hasNext__Z = (function() {
  return false
});
$c_sc_Iterator$$anon$18.prototype.knownSize__I = (function() {
  return 0
});
var $d_sc_Iterator$$anon$18 = new $TypeData().initClass({
  sc_Iterator$$anon$18: 0
}, false, "scala.collection.Iterator$$anon$18", {
  sc_Iterator$$anon$18: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_Iterator$$anon$18.prototype.$classData = $d_sc_Iterator$$anon$18;
/** @constructor */
function $c_sc_Iterator$$anon$19(a$1) {
  this.consumed$2 = false;
  this.a$1$2 = null;
  this.a$1$2 = a$1;
  this.consumed$2 = false
}
$c_sc_Iterator$$anon$19.prototype = new $h_sc_AbstractIterator();
$c_sc_Iterator$$anon$19.prototype.constructor = $c_sc_Iterator$$anon$19;
/** @constructor */
function $h_sc_Iterator$$anon$19() {
  /*<skip>*/
}
$h_sc_Iterator$$anon$19.prototype = $c_sc_Iterator$$anon$19.prototype;
$c_sc_Iterator$$anon$19.prototype.next__O = (function() {
  if (this.consumed$2) {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  } else {
    this.consumed$2 = true;
    return this.a$1$2
  }
});
$c_sc_Iterator$$anon$19.prototype.hasNext__Z = (function() {
  return (!this.consumed$2)
});
var $d_sc_Iterator$$anon$19 = new $TypeData().initClass({
  sc_Iterator$$anon$19: 0
}, false, "scala.collection.Iterator$$anon$19", {
  sc_Iterator$$anon$19: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_Iterator$$anon$19.prototype.$classData = $d_sc_Iterator$$anon$19;
/** @constructor */
function $c_sc_Iterator$$anon$21(len$3, elem$4) {
  this.i$2 = 0;
  this.len$3$2 = 0;
  this.elem$4$2 = null;
  this.len$3$2 = len$3;
  this.elem$4$2 = elem$4;
  this.i$2 = 0
}
$c_sc_Iterator$$anon$21.prototype = new $h_sc_AbstractIterator();
$c_sc_Iterator$$anon$21.prototype.constructor = $c_sc_Iterator$$anon$21;
/** @constructor */
function $h_sc_Iterator$$anon$21() {
  /*<skip>*/
}
$h_sc_Iterator$$anon$21.prototype = $c_sc_Iterator$$anon$21.prototype;
$c_sc_Iterator$$anon$21.prototype.next__O = (function() {
  if (this.hasNext__Z()) {
    this.i$2 = ((1 + this.i$2) | 0);
    return this.elem$4$2.apply__O()
  } else {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  }
});
$c_sc_Iterator$$anon$21.prototype.hasNext__Z = (function() {
  return (this.i$2 < this.len$3$2)
});
var $d_sc_Iterator$$anon$21 = new $TypeData().initClass({
  sc_Iterator$$anon$21: 0
}, false, "scala.collection.Iterator$$anon$21", {
  sc_Iterator$$anon$21: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_Iterator$$anon$21.prototype.$classData = $d_sc_Iterator$$anon$21;
/** @constructor */
function $c_sc_Iterator$$anon$6($$outer, p$1, isFlipped$1) {
  this.hd$2 = null;
  this.hdDefined$2 = false;
  this.$$outer$2 = null;
  this.p$1$2 = null;
  this.isFlipped$1$2 = false;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.p$1$2 = p$1;
  this.isFlipped$1$2 = isFlipped$1;
  this.hdDefined$2 = false
}
$c_sc_Iterator$$anon$6.prototype = new $h_sc_AbstractIterator();
$c_sc_Iterator$$anon$6.prototype.constructor = $c_sc_Iterator$$anon$6;
/** @constructor */
function $h_sc_Iterator$$anon$6() {
  /*<skip>*/
}
$h_sc_Iterator$$anon$6.prototype = $c_sc_Iterator$$anon$6.prototype;
$c_sc_Iterator$$anon$6.prototype.next__O = (function() {
  if (this.hasNext__Z()) {
    this.hdDefined$2 = false;
    return this.hd$2
  } else {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  }
});
$c_sc_Iterator$$anon$6.prototype.hasNext__Z = (function() {
  if (this.hdDefined$2) {
    return true
  } else {
    do {
      if ((!this.$$outer$2.hasNext__Z())) {
        return false
      };
      this.hd$2 = this.$$outer$2.next__O()
    } while (($uZ(this.p$1$2.apply__O__O(this.hd$2)) === this.isFlipped$1$2));
    this.hdDefined$2 = true;
    return true
  }
});
var $d_sc_Iterator$$anon$6 = new $TypeData().initClass({
  sc_Iterator$$anon$6: 0
}, false, "scala.collection.Iterator$$anon$6", {
  sc_Iterator$$anon$6: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_Iterator$$anon$6.prototype.$classData = $d_sc_Iterator$$anon$6;
/** @constructor */
function $c_sc_Iterator$$anon$9($$outer, f$2) {
  this.$$outer$2 = null;
  this.f$2$2 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.f$2$2 = f$2
}
$c_sc_Iterator$$anon$9.prototype = new $h_sc_AbstractIterator();
$c_sc_Iterator$$anon$9.prototype.constructor = $c_sc_Iterator$$anon$9;
/** @constructor */
function $h_sc_Iterator$$anon$9() {
  /*<skip>*/
}
$h_sc_Iterator$$anon$9.prototype = $c_sc_Iterator$$anon$9.prototype;
$c_sc_Iterator$$anon$9.prototype.next__O = (function() {
  return this.f$2$2.apply__O__O(this.$$outer$2.next__O())
});
$c_sc_Iterator$$anon$9.prototype.hasNext__Z = (function() {
  return this.$$outer$2.hasNext__Z()
});
var $d_sc_Iterator$$anon$9 = new $TypeData().initClass({
  sc_Iterator$$anon$9: 0
}, false, "scala.collection.Iterator$$anon$9", {
  sc_Iterator$$anon$9: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_Iterator$$anon$9.prototype.$classData = $d_sc_Iterator$$anon$9;
/** @constructor */
function $c_sc_Iterator$ConcatIterator(current) {
  this.current$2 = null;
  this.tail$2 = null;
  this.last$2 = null;
  this.currentHasNextChecked$2 = false;
  this.current$2 = current;
  this.tail$2 = null;
  this.last$2 = null;
  this.currentHasNextChecked$2 = false
}
$c_sc_Iterator$ConcatIterator.prototype = new $h_sc_AbstractIterator();
$c_sc_Iterator$ConcatIterator.prototype.constructor = $c_sc_Iterator$ConcatIterator;
/** @constructor */
function $h_sc_Iterator$ConcatIterator() {
  /*<skip>*/
}
$h_sc_Iterator$ConcatIterator.prototype = $c_sc_Iterator$ConcatIterator.prototype;
$c_sc_Iterator$ConcatIterator.prototype.next__O = (function() {
  if (this.hasNext__Z()) {
    this.currentHasNextChecked$2 = false;
    return this.current$2.next__O()
  } else {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  }
});
$c_sc_Iterator$ConcatIterator.prototype.concat__F0__sc_Iterator = (function(that) {
  var c = new $c_sc_Iterator$ConcatIteratorCell(that, null);
  if ((this.tail$2 === null)) {
    this.tail$2 = c;
    this.last$2 = c
  } else {
    this.last$2.tail$1 = c;
    this.last$2 = c
  };
  if ((this.current$2 === null)) {
    this.current$2 = $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
  };
  return this
});
$c_sc_Iterator$ConcatIterator.prototype.merge__p2__V = (function() {
  while (true) {
    if ($is_sc_Iterator$ConcatIterator(this.current$2)) {
      var c = $as_sc_Iterator$ConcatIterator(this.current$2);
      this.current$2 = c.current$2;
      this.currentHasNextChecked$2 = c.currentHasNextChecked$2;
      if ((c.tail$2 !== null)) {
        c.last$2.tail$1 = this.tail$2;
        this.tail$2 = c.tail$2
      };
      continue
    };
    break
  }
});
$c_sc_Iterator$ConcatIterator.prototype.advance__p2__Z = (function() {
  while (true) {
    if ((this.tail$2 === null)) {
      this.current$2 = null;
      this.last$2 = null;
      return false
    } else {
      this.current$2 = this.tail$2.headIterator__sc_Iterator();
      this.tail$2 = this.tail$2.tail$1;
      this.merge__p2__V();
      if (this.currentHasNextChecked$2) {
        return true
      } else if (this.current$2.hasNext__Z()) {
        this.currentHasNextChecked$2 = true;
        return true
      }
    }
  }
});
$c_sc_Iterator$ConcatIterator.prototype.hasNext__Z = (function() {
  if (this.currentHasNextChecked$2) {
    return true
  } else if ((this.current$2 !== null)) {
    if (this.current$2.hasNext__Z()) {
      this.currentHasNextChecked$2 = true;
      return true
    } else {
      return this.advance__p2__Z()
    }
  } else {
    return false
  }
});
function $is_sc_Iterator$ConcatIterator(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_Iterator$ConcatIterator)))
}
function $as_sc_Iterator$ConcatIterator(obj) {
  return (($is_sc_Iterator$ConcatIterator(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.Iterator$ConcatIterator"))
}
function $isArrayOf_sc_Iterator$ConcatIterator(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_Iterator$ConcatIterator)))
}
function $asArrayOf_sc_Iterator$ConcatIterator(obj, depth) {
  return (($isArrayOf_sc_Iterator$ConcatIterator(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.Iterator$ConcatIterator;", depth))
}
var $d_sc_Iterator$ConcatIterator = new $TypeData().initClass({
  sc_Iterator$ConcatIterator: 0
}, false, "scala.collection.Iterator$ConcatIterator", {
  sc_Iterator$ConcatIterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_Iterator$ConcatIterator.prototype.$classData = $d_sc_Iterator$ConcatIterator;
/** @constructor */
function $c_sc_Iterator$SliceIterator(underlying, start, limit) {
  this.underlying$2 = null;
  this.scala$collection$Iterator$SliceIterator$$remaining$f = 0;
  this.dropping$2 = 0;
  this.underlying$2 = underlying;
  this.scala$collection$Iterator$SliceIterator$$remaining$f = limit;
  this.dropping$2 = start
}
$c_sc_Iterator$SliceIterator.prototype = new $h_sc_AbstractIterator();
$c_sc_Iterator$SliceIterator.prototype.constructor = $c_sc_Iterator$SliceIterator;
/** @constructor */
function $h_sc_Iterator$SliceIterator() {
  /*<skip>*/
}
$h_sc_Iterator$SliceIterator.prototype = $c_sc_Iterator$SliceIterator.prototype;
$c_sc_Iterator$SliceIterator.prototype.next__O = (function() {
  this.skip__p2__V();
  if ((this.scala$collection$Iterator$SliceIterator$$remaining$f > 0)) {
    this.scala$collection$Iterator$SliceIterator$$remaining$f = (((-1) + this.scala$collection$Iterator$SliceIterator$$remaining$f) | 0);
    return this.underlying$2.next__O()
  } else {
    return ((this.scala$collection$Iterator$SliceIterator$$remaining$f < 0) ? this.underlying$2.next__O() : $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O())
  }
});
$c_sc_Iterator$SliceIterator.prototype.adjustedBound$1__p2__I__I = (function(lo$1) {
  if ((this.scala$collection$Iterator$SliceIterator$$remaining$f < 0)) {
    return (-1)
  } else {
    var that = ((this.scala$collection$Iterator$SliceIterator$$remaining$f - lo$1) | 0);
    return ((that < 0) ? 0 : that)
  }
});
$c_sc_Iterator$SliceIterator.prototype.sliceIterator__I__I__sc_Iterator = (function(from, until) {
  var lo = ((from > 0) ? from : 0);
  if ((until < 0)) {
    var rest = this.adjustedBound$1__p2__I__I(lo)
  } else if ((until <= lo)) {
    var rest = 0
  } else if ((this.scala$collection$Iterator$SliceIterator$$remaining$f < 0)) {
    var rest = ((until - lo) | 0)
  } else {
    var x = this.adjustedBound$1__p2__I__I(lo);
    var that = ((until - lo) | 0);
    var rest = ((x < that) ? x : that)
  };
  if ((rest === 0)) {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
  } else {
    this.dropping$2 = ((this.dropping$2 + lo) | 0);
    this.scala$collection$Iterator$SliceIterator$$remaining$f = rest;
    return this
  }
});
$c_sc_Iterator$SliceIterator.prototype.skip__p2__V = (function() {
  while ((this.dropping$2 > 0)) {
    if (this.underlying$2.hasNext__Z()) {
      this.underlying$2.next__O();
      this.dropping$2 = (((-1) + this.dropping$2) | 0)
    } else {
      this.dropping$2 = 0
    }
  }
});
$c_sc_Iterator$SliceIterator.prototype.hasNext__Z = (function() {
  this.skip__p2__V();
  return ((this.scala$collection$Iterator$SliceIterator$$remaining$f !== 0) && this.underlying$2.hasNext__Z())
});
var $d_sc_Iterator$SliceIterator = new $TypeData().initClass({
  sc_Iterator$SliceIterator: 0
}, false, "scala.collection.Iterator$SliceIterator", {
  sc_Iterator$SliceIterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_Iterator$SliceIterator.prototype.$classData = $d_sc_Iterator$SliceIterator;
/** @constructor */
function $c_sc_LinearSeqIterator(coll) {
  this.coll$2 = null;
  this.these$2 = null;
  this.coll$2 = coll;
  this.these$2 = new $c_sc_LinearSeqIterator$LazyCell(this, new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      return $this.coll$2
    })
  })(this)))
}
$c_sc_LinearSeqIterator.prototype = new $h_sc_AbstractIterator();
$c_sc_LinearSeqIterator.prototype.constructor = $c_sc_LinearSeqIterator;
/** @constructor */
function $h_sc_LinearSeqIterator() {
  /*<skip>*/
}
$h_sc_LinearSeqIterator.prototype = $c_sc_LinearSeqIterator.prototype;
$c_sc_LinearSeqIterator.prototype.next__O = (function() {
  if ((!this.hasNext__Z())) {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  } else {
    var cur = this.these$2.v__sc_Seq();
    var result = cur.head__O();
    this.these$2 = new $c_sc_LinearSeqIterator$LazyCell(this, new $c_sjsr_AnonFunction0((function($this, cur$1) {
      return (function() {
        return $as_sc_Seq(cur$1.tail__O())
      })
    })(this, cur)));
    return result
  }
});
$c_sc_LinearSeqIterator.prototype.hasNext__Z = (function() {
  var this$1 = this.these$2.v__sc_Seq();
  return (!this$1.isEmpty__Z())
});
var $d_sc_LinearSeqIterator = new $TypeData().initClass({
  sc_LinearSeqIterator: 0
}, false, "scala.collection.LinearSeqIterator", {
  sc_LinearSeqIterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_LinearSeqIterator.prototype.$classData = $d_sc_LinearSeqIterator;
/** @constructor */
function $c_sc_Map$() {
  this.delegate$1 = null;
  this.scala$collection$Map$$DefaultSentinel$2 = null;
  $c_sc_MapFactory$Delegate.prototype.init___sc_MapFactory.call(this, $m_sci_Map$());
  $n_sc_Map$ = this;
  this.scala$collection$Map$$DefaultSentinel$2 = new $c_O().init___()
}
$c_sc_Map$.prototype = new $h_sc_MapFactory$Delegate();
$c_sc_Map$.prototype.constructor = $c_sc_Map$;
/** @constructor */
function $h_sc_Map$() {
  /*<skip>*/
}
$h_sc_Map$.prototype = $c_sc_Map$.prototype;
var $d_sc_Map$ = new $TypeData().initClass({
  sc_Map$: 0
}, false, "scala.collection.Map$", {
  sc_Map$: 1,
  sc_MapFactory$Delegate: 1,
  O: 1,
  sc_MapFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sc_Map$.prototype.$classData = $d_sc_Map$;
var $n_sc_Map$ = (void 0);
function $m_sc_Map$() {
  if ((!$n_sc_Map$)) {
    $n_sc_Map$ = new $c_sc_Map$()
  };
  return $n_sc_Map$
}
function $f_sc_MapOps__apply__O__O($thiz, key) {
  var x1 = $thiz.get__O__s_Option(key);
  var x = $m_s_None$();
  if ((x === x1)) {
    return $f_sc_MapOps__$default__O__O($thiz, key)
  } else if ($is_s_Some(x1)) {
    var x2 = $as_s_Some(x1);
    var value = x2.value$2;
    return value
  } else {
    throw new $c_s_MatchError(x1)
  }
}
function $f_sc_MapOps__getOrElse__O__F0__O($thiz, key, $default) {
  var x1 = $thiz.get__O__s_Option(key);
  if ($is_s_Some(x1)) {
    var x2 = $as_s_Some(x1);
    var v = x2.value$2;
    return v
  } else {
    var x = $m_s_None$();
    if ((x === x1)) {
      return $default.apply__O()
    } else {
      throw new $c_s_MatchError(x1)
    }
  }
}
function $f_sc_MapOps__$default__O__O($thiz, key) {
  throw new $c_ju_NoSuchElementException().init___T(("key not found: " + key))
}
function $f_sc_MapOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder($thiz, sb, start, sep, end) {
  var this$1 = $thiz.iterator__sc_Iterator();
  var f = new $c_sjsr_AnonFunction1((function($this) {
    return (function(x0$1$2) {
      var x0$1 = $as_T2(x0$1$2);
      if ((x0$1 !== null)) {
        var k = x0$1.$$und1$f;
        var v = x0$1.$$und2$f;
        return ((k + " -> ") + v)
      } else {
        throw new $c_s_MatchError(x0$1)
      }
    })
  })($thiz));
  var this$2 = new $c_sc_Iterator$$anon$9(this$1, f);
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this$2, sb, start, sep, end)
}
function $f_sc_MapOps__contains__O__Z($thiz, key) {
  var this$1 = $thiz.get__O__s_Option(key);
  return (!this$1.isEmpty__Z())
}
/** @constructor */
function $c_sc_SeqFactory$Delegate() {
  this.delegate$1 = null
}
$c_sc_SeqFactory$Delegate.prototype = new $h_O();
$c_sc_SeqFactory$Delegate.prototype.constructor = $c_sc_SeqFactory$Delegate;
/** @constructor */
function $h_sc_SeqFactory$Delegate() {
  /*<skip>*/
}
$h_sc_SeqFactory$Delegate.prototype = $c_sc_SeqFactory$Delegate.prototype;
$c_sc_SeqFactory$Delegate.prototype.init___sc_SeqFactory = (function(delegate) {
  this.delegate$1 = delegate;
  return this
});
$c_sc_SeqFactory$Delegate.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sc_SeqOps(source)
});
$c_sc_SeqFactory$Delegate.prototype.from__sc_IterableOnce__sc_SeqOps = (function(it) {
  return $as_sc_SeqOps(this.delegate$1.from__sc_IterableOnce__O(it))
});
$c_sc_SeqFactory$Delegate.prototype.newBuilder__scm_Builder = (function() {
  return this.delegate$1.newBuilder__scm_Builder()
});
/** @constructor */
function $c_sc_StrictOptimizedLinearSeqOps$$anon$1($$outer) {
  this.current$2 = null;
  this.current$2 = $$outer
}
$c_sc_StrictOptimizedLinearSeqOps$$anon$1.prototype = new $h_sc_AbstractIterator();
$c_sc_StrictOptimizedLinearSeqOps$$anon$1.prototype.constructor = $c_sc_StrictOptimizedLinearSeqOps$$anon$1;
/** @constructor */
function $h_sc_StrictOptimizedLinearSeqOps$$anon$1() {
  /*<skip>*/
}
$h_sc_StrictOptimizedLinearSeqOps$$anon$1.prototype = $c_sc_StrictOptimizedLinearSeqOps$$anon$1.prototype;
$c_sc_StrictOptimizedLinearSeqOps$$anon$1.prototype.next__O = (function() {
  var r = this.current$2.head__O();
  this.current$2 = $as_sc_Iterable(this.current$2.tail__O());
  return r
});
$c_sc_StrictOptimizedLinearSeqOps$$anon$1.prototype.hasNext__Z = (function() {
  return (!this.current$2.isEmpty__Z())
});
var $d_sc_StrictOptimizedLinearSeqOps$$anon$1 = new $TypeData().initClass({
  sc_StrictOptimizedLinearSeqOps$$anon$1: 0
}, false, "scala.collection.StrictOptimizedLinearSeqOps$$anon$1", {
  sc_StrictOptimizedLinearSeqOps$$anon$1: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sc_StrictOptimizedLinearSeqOps$$anon$1.prototype.$classData = $d_sc_StrictOptimizedLinearSeqOps$$anon$1;
function $f_sc_StrictOptimizedSeqOps__appendedAll__sc_IterableOnce__O($thiz, suffix) {
  var b = $thiz.iterableFactory__sc_SeqFactory().newBuilder__scm_Builder();
  var it1 = $thiz.iterator__sc_Iterator();
  var it2 = suffix.iterator__sc_Iterator();
  b.addAll__sc_IterableOnce__scm_Growable(it1);
  b.addAll__sc_IterableOnce__scm_Growable(it2);
  return b.result__O()
}
/** @constructor */
function $c_sci_Iterable$() {
  this.delegate$1 = null;
  $c_sc_IterableFactory$Delegate.prototype.init___sc_IterableFactory.call(this, $m_sci_List$())
}
$c_sci_Iterable$.prototype = new $h_sc_IterableFactory$Delegate();
$c_sci_Iterable$.prototype.constructor = $c_sci_Iterable$;
/** @constructor */
function $h_sci_Iterable$() {
  /*<skip>*/
}
$h_sci_Iterable$.prototype = $c_sci_Iterable$.prototype;
var $d_sci_Iterable$ = new $TypeData().initClass({
  sci_Iterable$: 0
}, false, "scala.collection.immutable.Iterable$", {
  sci_Iterable$: 1,
  sc_IterableFactory$Delegate: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_Iterable$.prototype.$classData = $d_sci_Iterable$;
var $n_sci_Iterable$ = (void 0);
function $m_sci_Iterable$() {
  if ((!$n_sci_Iterable$)) {
    $n_sci_Iterable$ = new $c_sci_Iterable$()
  };
  return $n_sci_Iterable$
}
/** @constructor */
function $c_sci_LazyList$() {
  this.$$undempty$1 = null;
  $n_sci_LazyList$ = this;
  var state = new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      return $m_sci_LazyList$State$Empty$()
    })
  })(this));
  this.$$undempty$1 = new $c_sci_LazyList(state).force__sci_LazyList()
}
$c_sci_LazyList$.prototype = new $h_O();
$c_sci_LazyList$.prototype.constructor = $c_sci_LazyList$;
/** @constructor */
function $h_sci_LazyList$() {
  /*<skip>*/
}
$h_sci_LazyList$.prototype = $c_sci_LazyList$.prototype;
$c_sci_LazyList$.prototype.evaluatedElem$1__p1__sr_LazyRef__sc_Iterator__O = (function(evaluatedElem$lzy$1, it$1) {
  return (evaluatedElem$lzy$1.$$undinitialized$1 ? evaluatedElem$lzy$1.$$undvalue$1 : this.evaluatedElem$lzycompute$1__p1__sr_LazyRef__sc_Iterator__O(evaluatedElem$lzy$1, it$1))
});
$c_sci_LazyList$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sci_LazyList(source)
});
$c_sci_LazyList$.prototype.from__sc_IterableOnce__sci_LazyList = (function(coll) {
  if ($is_sci_LazyList(coll)) {
    var x2 = $as_sci_LazyList(coll);
    return x2
  } else if ((coll.knownSize__I() === 0)) {
    return this.$$undempty$1
  } else {
    var state = new $c_sjsr_AnonFunction0((function($this, coll$1) {
      return (function() {
        return $m_sci_LazyList$().scala$collection$immutable$LazyList$$stateFromIterator__sc_Iterator__sci_LazyList$State(coll$1.iterator__sc_Iterator())
      })
    })(this, coll));
    return new $c_sci_LazyList(state)
  }
});
$c_sci_LazyList$.prototype.scala$collection$immutable$LazyList$$stateFromIterator__sc_Iterator__sci_LazyList$State = (function(it) {
  var suffix = new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      return $m_sci_LazyList$State$Empty$()
    })
  })(this));
  return this.nextState$1__p1__sc_Iterator__F0__sci_LazyList$State(it, suffix)
});
$c_sci_LazyList$.prototype.evaluatedElem$lzycompute$1__p1__sr_LazyRef__sc_Iterator__O = (function(evaluatedElem$lzy$1, it$1) {
  if ((evaluatedElem$lzy$1 === null)) {
    throw new $c_jl_NullPointerException()
  };
  return (evaluatedElem$lzy$1.$$undinitialized$1 ? evaluatedElem$lzy$1.$$undvalue$1 : evaluatedElem$lzy$1.initialize__O__O(it$1.next__O()))
});
$c_sci_LazyList$.prototype.nextState$1__p1__sc_Iterator__F0__sci_LazyList$State = (function(it$1, suffix$2) {
  if (it$1.hasNext__Z()) {
    var evaluatedElem$lzy = new $c_sr_LazyRef();
    var hd = new $c_sjsr_AnonFunction0((function($this, evaluatedElem$lzy$1, it$1$1) {
      return (function() {
        return $this.evaluatedElem$1__p1__sr_LazyRef__sc_Iterator__O(evaluatedElem$lzy$1, it$1$1)
      })
    })(this, evaluatedElem$lzy, it$1));
    var state = new $c_sjsr_AnonFunction0((function(this$2, evaluatedElem$lzy$2, it$1$2, suffix$2$1) {
      return (function() {
        this$2.evaluatedElem$1__p1__sr_LazyRef__sc_Iterator__O(evaluatedElem$lzy$2, it$1$2);
        return this$2.nextState$1__p1__sc_Iterator__F0__sci_LazyList$State(it$1$2, suffix$2$1)
      })
    })(this, evaluatedElem$lzy, it$1, suffix$2));
    var tl = new $c_sci_LazyList(state);
    return new $c_sci_LazyList$State$Cons(hd, tl)
  } else {
    return $as_sci_LazyList$State(suffix$2.apply__O())
  }
});
$c_sci_LazyList$.prototype.newBuilder__scm_Builder = (function() {
  var this$2 = new $c_scm_ArrayBuffer$$anon$1();
  var f = new $c_sjsr_AnonFunction1((function($this) {
    return (function(array$2) {
      var array = $as_scm_ArrayBuffer(array$2);
      return $m_sci_LazyList$().from__sc_IterableOnce__sci_LazyList(array)
    })
  })(this));
  return new $c_scm_Builder$$anon$1(this$2, f)
});
var $d_sci_LazyList$ = new $TypeData().initClass({
  sci_LazyList$: 0
}, false, "scala.collection.immutable.LazyList$", {
  sci_LazyList$: 1,
  O: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_LazyList$.prototype.$classData = $d_sci_LazyList$;
var $n_sci_LazyList$ = (void 0);
function $m_sci_LazyList$() {
  if ((!$n_sci_LazyList$)) {
    $n_sci_LazyList$ = new $c_sci_LazyList$()
  };
  return $n_sci_LazyList$
}
/** @constructor */
function $c_sci_LazyList$LazyIterator(lazyList) {
  this.lazyList$2 = null;
  this.lazyList$2 = lazyList
}
$c_sci_LazyList$LazyIterator.prototype = new $h_sc_AbstractIterator();
$c_sci_LazyList$LazyIterator.prototype.constructor = $c_sci_LazyList$LazyIterator;
/** @constructor */
function $h_sci_LazyList$LazyIterator() {
  /*<skip>*/
}
$h_sci_LazyList$LazyIterator.prototype = $c_sci_LazyList$LazyIterator.prototype;
$c_sci_LazyList$LazyIterator.prototype.next__O = (function() {
  if (this.lazyList$2.isEmpty__Z()) {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  } else {
    var this$1 = this.lazyList$2;
    var res = this$1.state__p4__sci_LazyList$State().head__O();
    var this$2 = this.lazyList$2;
    this.lazyList$2 = this$2.state__p4__sci_LazyList$State().tail__sci_LazyList();
    return res
  }
});
$c_sci_LazyList$LazyIterator.prototype.hasNext__Z = (function() {
  var this$1 = this.lazyList$2;
  return (!this$1.isEmpty__Z())
});
var $d_sci_LazyList$LazyIterator = new $TypeData().initClass({
  sci_LazyList$LazyIterator: 0
}, false, "scala.collection.immutable.LazyList$LazyIterator", {
  sci_LazyList$LazyIterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_LazyList$LazyIterator.prototype.$classData = $d_sci_LazyList$LazyIterator;
/** @constructor */
function $c_sci_Map$Map2$Map2Iterator() {
  this.i$2 = 0;
  this.$$outer$2 = null
}
$c_sci_Map$Map2$Map2Iterator.prototype = new $h_sc_AbstractIterator();
$c_sci_Map$Map2$Map2Iterator.prototype.constructor = $c_sci_Map$Map2$Map2Iterator;
/** @constructor */
function $h_sci_Map$Map2$Map2Iterator() {
  /*<skip>*/
}
$h_sci_Map$Map2$Map2Iterator.prototype = $c_sci_Map$Map2$Map2Iterator.prototype;
$c_sci_Map$Map2$Map2Iterator.prototype.next__O = (function() {
  var x1 = this.i$2;
  switch (x1) {
    case 0: {
      var k = this.$$outer$2.scala$collection$immutable$Map$Map2$$key1$f;
      var v = this.$$outer$2.scala$collection$immutable$Map$Map2$$value1$f;
      var result = new $c_T2(k, v);
      break
    }
    case 1: {
      var k$1 = this.$$outer$2.scala$collection$immutable$Map$Map2$$key2$f;
      var v$1 = this.$$outer$2.scala$collection$immutable$Map$Map2$$value2$f;
      var result = new $c_T2(k$1, v$1);
      break
    }
    default: {
      var result = $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
    }
  };
  this.i$2 = ((1 + this.i$2) | 0);
  return result
});
$c_sci_Map$Map2$Map2Iterator.prototype.hasNext__Z = (function() {
  return (this.i$2 < 2)
});
$c_sci_Map$Map2$Map2Iterator.prototype.init___sci_Map$Map2 = (function($$outer) {
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.i$2 = 0;
  return this
});
/** @constructor */
function $c_sci_Map$Map3$Map3Iterator() {
  this.i$2 = 0;
  this.$$outer$2 = null
}
$c_sci_Map$Map3$Map3Iterator.prototype = new $h_sc_AbstractIterator();
$c_sci_Map$Map3$Map3Iterator.prototype.constructor = $c_sci_Map$Map3$Map3Iterator;
/** @constructor */
function $h_sci_Map$Map3$Map3Iterator() {
  /*<skip>*/
}
$h_sci_Map$Map3$Map3Iterator.prototype = $c_sci_Map$Map3$Map3Iterator.prototype;
$c_sci_Map$Map3$Map3Iterator.prototype.next__O = (function() {
  var x1 = this.i$2;
  switch (x1) {
    case 0: {
      var k = this.$$outer$2.scala$collection$immutable$Map$Map3$$key1$f;
      var v = this.$$outer$2.scala$collection$immutable$Map$Map3$$value1$f;
      var result = new $c_T2(k, v);
      break
    }
    case 1: {
      var k$1 = this.$$outer$2.scala$collection$immutable$Map$Map3$$key2$f;
      var v$1 = this.$$outer$2.scala$collection$immutable$Map$Map3$$value2$f;
      var result = new $c_T2(k$1, v$1);
      break
    }
    case 2: {
      var k$2 = this.$$outer$2.scala$collection$immutable$Map$Map3$$key3$f;
      var v$2 = this.$$outer$2.scala$collection$immutable$Map$Map3$$value3$f;
      var result = new $c_T2(k$2, v$2);
      break
    }
    default: {
      var result = $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
    }
  };
  this.i$2 = ((1 + this.i$2) | 0);
  return result
});
$c_sci_Map$Map3$Map3Iterator.prototype.init___sci_Map$Map3 = (function($$outer) {
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.i$2 = 0;
  return this
});
$c_sci_Map$Map3$Map3Iterator.prototype.hasNext__Z = (function() {
  return (this.i$2 < 3)
});
/** @constructor */
function $c_sci_Map$Map4$Map4Iterator() {
  this.i$2 = 0;
  this.$$outer$2 = null
}
$c_sci_Map$Map4$Map4Iterator.prototype = new $h_sc_AbstractIterator();
$c_sci_Map$Map4$Map4Iterator.prototype.constructor = $c_sci_Map$Map4$Map4Iterator;
/** @constructor */
function $h_sci_Map$Map4$Map4Iterator() {
  /*<skip>*/
}
$h_sci_Map$Map4$Map4Iterator.prototype = $c_sci_Map$Map4$Map4Iterator.prototype;
$c_sci_Map$Map4$Map4Iterator.prototype.next__O = (function() {
  var x1 = this.i$2;
  switch (x1) {
    case 0: {
      var k = this.$$outer$2.scala$collection$immutable$Map$Map4$$key1$f;
      var v = this.$$outer$2.scala$collection$immutable$Map$Map4$$value1$f;
      var result = new $c_T2(k, v);
      break
    }
    case 1: {
      var k$1 = this.$$outer$2.scala$collection$immutable$Map$Map4$$key2$f;
      var v$1 = this.$$outer$2.scala$collection$immutable$Map$Map4$$value2$f;
      var result = new $c_T2(k$1, v$1);
      break
    }
    case 2: {
      var k$2 = this.$$outer$2.scala$collection$immutable$Map$Map4$$key3$f;
      var v$2 = this.$$outer$2.scala$collection$immutable$Map$Map4$$value3$f;
      var result = new $c_T2(k$2, v$2);
      break
    }
    case 3: {
      var k$3 = this.$$outer$2.scala$collection$immutable$Map$Map4$$key4$f;
      var v$3 = this.$$outer$2.scala$collection$immutable$Map$Map4$$value4$f;
      var result = new $c_T2(k$3, v$3);
      break
    }
    default: {
      var result = $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
    }
  };
  this.i$2 = ((1 + this.i$2) | 0);
  return result
});
$c_sci_Map$Map4$Map4Iterator.prototype.init___sci_Map$Map4 = (function($$outer) {
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.i$2 = 0;
  return this
});
$c_sci_Map$Map4$Map4Iterator.prototype.hasNext__Z = (function() {
  return (this.i$2 < 4)
});
/** @constructor */
function $c_sci_MapKeyValueTupleIterator(rootNode) {
  this.currentValueCursor$1 = 0;
  this.currentValueLength$1 = 0;
  this.currentValueNode$1 = null;
  this.currentStackLevel$1 = 0;
  this.nodeCursorsAndLengths$1 = null;
  this.nodes$1 = null;
  $c_sci_ChampBaseIterator.prototype.init___sci_Node.call(this, rootNode)
}
$c_sci_MapKeyValueTupleIterator.prototype = new $h_sci_ChampBaseIterator();
$c_sci_MapKeyValueTupleIterator.prototype.constructor = $c_sci_MapKeyValueTupleIterator;
/** @constructor */
function $h_sci_MapKeyValueTupleIterator() {
  /*<skip>*/
}
$h_sci_MapKeyValueTupleIterator.prototype = $c_sci_MapKeyValueTupleIterator.prototype;
$c_sci_MapKeyValueTupleIterator.prototype.next__O = (function() {
  return this.next__T2()
});
$c_sci_MapKeyValueTupleIterator.prototype.concat__F0__sc_Iterator = (function(xs) {
  return $f_sc_Iterator__concat__F0__sc_Iterator(this, xs)
});
$c_sci_MapKeyValueTupleIterator.prototype.isEmpty__Z = (function() {
  return (!this.hasNext__Z())
});
$c_sci_MapKeyValueTupleIterator.prototype.toString__T = (function() {
  return "<iterator>"
});
$c_sci_MapKeyValueTupleIterator.prototype.sliceIterator__I__I__sc_Iterator = (function(from, until) {
  return $f_sc_Iterator__sliceIterator__I__I__sc_Iterator(this, from, until)
});
$c_sci_MapKeyValueTupleIterator.prototype.foreach__F1__V = (function(f) {
  $f_sc_IterableOnceOps__foreach__F1__V(this, f)
});
$c_sci_MapKeyValueTupleIterator.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_IterableOnceOps__foldLeft__O__F2__O(this, z, op)
});
$c_sci_MapKeyValueTupleIterator.prototype.copyToArray__O__I__I = (function(xs, start) {
  return $f_sc_IterableOnceOps__copyToArray__O__I__I(this, xs, start)
});
$c_sci_MapKeyValueTupleIterator.prototype.iterator__sc_Iterator = (function() {
  return this
});
$c_sci_MapKeyValueTupleIterator.prototype.next__T2 = (function() {
  if ((!this.hasNext__Z())) {
    throw new $c_ju_NoSuchElementException().init___()
  };
  var payload = $as_sci_MapNode(this.currentValueNode$1).getPayload__I__T2(this.currentValueCursor$1);
  this.currentValueCursor$1 = ((1 + this.currentValueCursor$1) | 0);
  return payload
});
$c_sci_MapKeyValueTupleIterator.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(b, start, sep, end) {
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, b, start, sep, end)
});
$c_sci_MapKeyValueTupleIterator.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return $m_sci_Map$().from__sc_IterableOnce__sci_Map(this)
});
$c_sci_MapKeyValueTupleIterator.prototype.sum__s_math_Numeric__O = (function(num) {
  return $f_sc_IterableOnceOps__sum__s_math_Numeric__O(this, num)
});
$c_sci_MapKeyValueTupleIterator.prototype.knownSize__I = (function() {
  return (-1)
});
var $d_sci_MapKeyValueTupleIterator = new $TypeData().initClass({
  sci_MapKeyValueTupleIterator: 0
}, false, "scala.collection.immutable.MapKeyValueTupleIterator", {
  sci_MapKeyValueTupleIterator: 1,
  sci_ChampBaseIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_MapKeyValueTupleIterator.prototype.$classData = $d_sci_MapKeyValueTupleIterator;
/** @constructor */
function $c_sci_OldHashMap$HashTrieMap$$anon$4($$outer) {
  this.elems$1 = null;
  this.scala$collection$immutable$TrieIterator$$depth$f = 0;
  this.scala$collection$immutable$TrieIterator$$arrayStack$f = null;
  this.scala$collection$immutable$TrieIterator$$posStack$f = null;
  this.scala$collection$immutable$TrieIterator$$arrayD$f = null;
  this.scala$collection$immutable$TrieIterator$$posD$f = 0;
  this.scala$collection$immutable$TrieIterator$$subIter$f = null;
  $c_sci_TrieIterator.prototype.init___Asci_Iterable.call(this, $$outer.elems$5)
}
$c_sci_OldHashMap$HashTrieMap$$anon$4.prototype = new $h_sci_TrieIterator();
$c_sci_OldHashMap$HashTrieMap$$anon$4.prototype.constructor = $c_sci_OldHashMap$HashTrieMap$$anon$4;
/** @constructor */
function $h_sci_OldHashMap$HashTrieMap$$anon$4() {
  /*<skip>*/
}
$h_sci_OldHashMap$HashTrieMap$$anon$4.prototype = $c_sci_OldHashMap$HashTrieMap$$anon$4.prototype;
$c_sci_OldHashMap$HashTrieMap$$anon$4.prototype.getElem__O__O = (function(x) {
  return $as_sci_OldHashMap$OldHashMap1(x).ensurePair__T2()
});
var $d_sci_OldHashMap$HashTrieMap$$anon$4 = new $TypeData().initClass({
  sci_OldHashMap$HashTrieMap$$anon$4: 0
}, false, "scala.collection.immutable.OldHashMap$HashTrieMap$$anon$4", {
  sci_OldHashMap$HashTrieMap$$anon$4: 1,
  sci_TrieIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_OldHashMap$HashTrieMap$$anon$4.prototype.$classData = $d_sci_OldHashMap$HashTrieMap$$anon$4;
/** @constructor */
function $c_sci_OldHashSet$HashTrieSet$$anon$2($$outer) {
  this.elems$1 = null;
  this.scala$collection$immutable$TrieIterator$$depth$f = 0;
  this.scala$collection$immutable$TrieIterator$$arrayStack$f = null;
  this.scala$collection$immutable$TrieIterator$$posStack$f = null;
  this.scala$collection$immutable$TrieIterator$$arrayD$f = null;
  this.scala$collection$immutable$TrieIterator$$posD$f = 0;
  this.scala$collection$immutable$TrieIterator$$subIter$f = null;
  $c_sci_TrieIterator.prototype.init___Asci_Iterable.call(this, $$outer.elems$5)
}
$c_sci_OldHashSet$HashTrieSet$$anon$2.prototype = new $h_sci_TrieIterator();
$c_sci_OldHashSet$HashTrieSet$$anon$2.prototype.constructor = $c_sci_OldHashSet$HashTrieSet$$anon$2;
/** @constructor */
function $h_sci_OldHashSet$HashTrieSet$$anon$2() {
  /*<skip>*/
}
$h_sci_OldHashSet$HashTrieSet$$anon$2.prototype = $c_sci_OldHashSet$HashTrieSet$$anon$2.prototype;
$c_sci_OldHashSet$HashTrieSet$$anon$2.prototype.getElem__O__O = (function(cc) {
  return $as_sci_OldHashSet$OldHashSet1(cc).key$6
});
var $d_sci_OldHashSet$HashTrieSet$$anon$2 = new $TypeData().initClass({
  sci_OldHashSet$HashTrieSet$$anon$2: 0
}, false, "scala.collection.immutable.OldHashSet$HashTrieSet$$anon$2", {
  sci_OldHashSet$HashTrieSet$$anon$2: 1,
  sci_TrieIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_OldHashSet$HashTrieSet$$anon$2.prototype.$classData = $d_sci_OldHashSet$HashTrieSet$$anon$2;
/** @constructor */
function $c_sci_SetHashIterator(rootNode) {
  this.currentValueCursor$1 = 0;
  this.currentValueLength$1 = 0;
  this.currentValueNode$1 = null;
  this.currentStackLevel$1 = 0;
  this.nodeCursorsAndLengths$1 = null;
  this.nodes$1 = null;
  this.hash$2 = 0;
  $c_sci_ChampBaseIterator.prototype.init___sci_Node.call(this, rootNode);
  this.hash$2 = 0
}
$c_sci_SetHashIterator.prototype = new $h_sci_ChampBaseIterator();
$c_sci_SetHashIterator.prototype.constructor = $c_sci_SetHashIterator;
/** @constructor */
function $h_sci_SetHashIterator() {
  /*<skip>*/
}
$h_sci_SetHashIterator.prototype = $c_sci_SetHashIterator.prototype;
$c_sci_SetHashIterator.prototype.next__O = (function() {
  if ((!this.hasNext__Z())) {
    throw new $c_ju_NoSuchElementException().init___()
  };
  this.hash$2 = this.currentValueNode$1.getHash__I__I(this.currentValueCursor$1);
  this.currentValueCursor$1 = ((1 + this.currentValueCursor$1) | 0);
  return this
});
$c_sci_SetHashIterator.prototype.concat__F0__sc_Iterator = (function(xs) {
  return $f_sc_Iterator__concat__F0__sc_Iterator(this, xs)
});
$c_sci_SetHashIterator.prototype.isEmpty__Z = (function() {
  return (!this.hasNext__Z())
});
$c_sci_SetHashIterator.prototype.toString__T = (function() {
  return "<iterator>"
});
$c_sci_SetHashIterator.prototype.sliceIterator__I__I__sc_Iterator = (function(from, until) {
  return $f_sc_Iterator__sliceIterator__I__I__sc_Iterator(this, from, until)
});
$c_sci_SetHashIterator.prototype.foreach__F1__V = (function(f) {
  $f_sc_IterableOnceOps__foreach__F1__V(this, f)
});
$c_sci_SetHashIterator.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_IterableOnceOps__foldLeft__O__F2__O(this, z, op)
});
$c_sci_SetHashIterator.prototype.copyToArray__O__I__I = (function(xs, start) {
  return $f_sc_IterableOnceOps__copyToArray__O__I__I(this, xs, start)
});
$c_sci_SetHashIterator.prototype.iterator__sc_Iterator = (function() {
  return this
});
$c_sci_SetHashIterator.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(b, start, sep, end) {
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, b, start, sep, end)
});
$c_sci_SetHashIterator.prototype.hashCode__I = (function() {
  return this.hash$2
});
$c_sci_SetHashIterator.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return $m_sci_Map$().from__sc_IterableOnce__sci_Map(this)
});
$c_sci_SetHashIterator.prototype.sum__s_math_Numeric__O = (function(num) {
  return $f_sc_IterableOnceOps__sum__s_math_Numeric__O(this, num)
});
$c_sci_SetHashIterator.prototype.knownSize__I = (function() {
  return (-1)
});
var $d_sci_SetHashIterator = new $TypeData().initClass({
  sci_SetHashIterator: 0
}, false, "scala.collection.immutable.SetHashIterator", {
  sci_SetHashIterator: 1,
  sci_ChampBaseIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_SetHashIterator.prototype.$classData = $d_sci_SetHashIterator;
/** @constructor */
function $c_sci_SetIterator(rootNode) {
  this.currentValueCursor$1 = 0;
  this.currentValueLength$1 = 0;
  this.currentValueNode$1 = null;
  this.currentStackLevel$1 = 0;
  this.nodeCursorsAndLengths$1 = null;
  this.nodes$1 = null;
  $c_sci_ChampBaseIterator.prototype.init___sci_Node.call(this, rootNode)
}
$c_sci_SetIterator.prototype = new $h_sci_ChampBaseIterator();
$c_sci_SetIterator.prototype.constructor = $c_sci_SetIterator;
/** @constructor */
function $h_sci_SetIterator() {
  /*<skip>*/
}
$h_sci_SetIterator.prototype = $c_sci_SetIterator.prototype;
$c_sci_SetIterator.prototype.next__O = (function() {
  if ((!this.hasNext__Z())) {
    throw new $c_ju_NoSuchElementException().init___()
  };
  var payload = $as_sci_SetNode(this.currentValueNode$1).getPayload__I__O(this.currentValueCursor$1);
  this.currentValueCursor$1 = ((1 + this.currentValueCursor$1) | 0);
  return payload
});
$c_sci_SetIterator.prototype.concat__F0__sc_Iterator = (function(xs) {
  return $f_sc_Iterator__concat__F0__sc_Iterator(this, xs)
});
$c_sci_SetIterator.prototype.isEmpty__Z = (function() {
  return (!this.hasNext__Z())
});
$c_sci_SetIterator.prototype.toString__T = (function() {
  return "<iterator>"
});
$c_sci_SetIterator.prototype.sliceIterator__I__I__sc_Iterator = (function(from, until) {
  return $f_sc_Iterator__sliceIterator__I__I__sc_Iterator(this, from, until)
});
$c_sci_SetIterator.prototype.foreach__F1__V = (function(f) {
  $f_sc_IterableOnceOps__foreach__F1__V(this, f)
});
$c_sci_SetIterator.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_IterableOnceOps__foldLeft__O__F2__O(this, z, op)
});
$c_sci_SetIterator.prototype.copyToArray__O__I__I = (function(xs, start) {
  return $f_sc_IterableOnceOps__copyToArray__O__I__I(this, xs, start)
});
$c_sci_SetIterator.prototype.iterator__sc_Iterator = (function() {
  return this
});
$c_sci_SetIterator.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(b, start, sep, end) {
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, b, start, sep, end)
});
$c_sci_SetIterator.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return $m_sci_Map$().from__sc_IterableOnce__sci_Map(this)
});
$c_sci_SetIterator.prototype.sum__s_math_Numeric__O = (function(num) {
  return $f_sc_IterableOnceOps__sum__s_math_Numeric__O(this, num)
});
$c_sci_SetIterator.prototype.knownSize__I = (function() {
  return (-1)
});
var $d_sci_SetIterator = new $TypeData().initClass({
  sci_SetIterator: 0
}, false, "scala.collection.immutable.SetIterator", {
  sci_SetIterator: 1,
  sci_ChampBaseIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_SetIterator.prototype.$classData = $d_sci_SetIterator;
function $f_sci_SetOps__removeAll__sc_IterableOnce__sci_SetOps($thiz, that) {
  var this$1 = that.iterator__sc_Iterator();
  var result = $thiz;
  while (this$1.hasNext__Z()) {
    var arg1 = result;
    var arg2 = this$1.next__O();
    var x$1 = $as_sci_SetOps(arg1);
    result = x$1.excl__O__sci_SetOps(arg2)
  };
  return $as_sci_SetOps(result)
}
function $f_sci_SetOps__concat__sc_IterableOnce__sci_SetOps($thiz, that) {
  var result = $thiz;
  var it = that.iterator__sc_Iterator();
  while (it.hasNext__Z()) {
    var this$1 = result;
    var elem = it.next__O();
    result = this$1.incl__O__sci_SetOps(elem)
  };
  return result
}
function $is_sci_SetOps(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_SetOps)))
}
function $as_sci_SetOps(obj) {
  return (($is_sci_SetOps(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.SetOps"))
}
function $isArrayOf_sci_SetOps(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_SetOps)))
}
function $asArrayOf_sci_SetOps(obj, depth) {
  return (($isArrayOf_sci_SetOps(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.SetOps;", depth))
}
/** @constructor */
function $c_sci_Stream$() {
  /*<skip>*/
}
$c_sci_Stream$.prototype = new $h_O();
$c_sci_Stream$.prototype.constructor = $c_sci_Stream$;
/** @constructor */
function $h_sci_Stream$() {
  /*<skip>*/
}
$h_sci_Stream$.prototype = $c_sci_Stream$.prototype;
$c_sci_Stream$.prototype.fromIterator__sc_Iterator__sci_Stream = (function(it) {
  return (it.hasNext__Z() ? new $c_sci_Stream$Cons(it.next__O(), new $c_sjsr_AnonFunction0((function($this, it$1) {
    return (function() {
      return $m_sci_Stream$().fromIterator__sc_Iterator__sci_Stream(it$1)
    })
  })(this, it))) : $m_sci_Stream$Empty$())
});
$c_sci_Stream$.prototype.from__sc_IterableOnce__sci_Stream = (function(coll) {
  if ($is_sci_Stream(coll)) {
    var x2 = $as_sci_Stream(coll);
    return x2
  } else {
    return this.fromIterator__sc_Iterator__sci_Stream(coll.iterator__sc_Iterator())
  }
});
$c_sci_Stream$.prototype.filteredTail__sci_Stream__F1__Z__sci_Stream = (function(stream, p, isFlipped) {
  var tl = new $c_sjsr_AnonFunction0((function(this$2, stream$1, p$1, isFlipped$1) {
    return (function() {
      return $as_sci_Stream(stream$1.tail__O()).filterImpl__F1__Z__sci_Stream(p$1, isFlipped$1)
    })
  })(this, stream, p, isFlipped));
  return new $c_sci_Stream$Cons(stream.head__O(), tl)
});
$c_sci_Stream$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sci_Stream(source)
});
$c_sci_Stream$.prototype.newBuilder__scm_Builder = (function() {
  var this$2 = new $c_scm_ArrayBuffer$$anon$1();
  var f = new $c_sjsr_AnonFunction1((function($this) {
    return (function(array$2) {
      var array = $as_scm_ArrayBuffer(array$2);
      return $m_sci_Stream$().from__sc_IterableOnce__sci_Stream(array)
    })
  })(this));
  return new $c_scm_Builder$$anon$1(this$2, f)
});
var $d_sci_Stream$ = new $TypeData().initClass({
  sci_Stream$: 0
}, false, "scala.collection.immutable.Stream$", {
  sci_Stream$: 1,
  O: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_Stream$.prototype.$classData = $d_sci_Stream$;
var $n_sci_Stream$ = (void 0);
function $m_sci_Stream$() {
  if ((!$n_sci_Stream$)) {
    $n_sci_Stream$ = new $c_sci_Stream$()
  };
  return $n_sci_Stream$
}
/** @constructor */
function $c_sci_WrappedString$() {
  this.empty$1 = null;
  $n_sci_WrappedString$ = this;
  this.empty$1 = new $c_sci_WrappedString("")
}
$c_sci_WrappedString$.prototype = new $h_O();
$c_sci_WrappedString$.prototype.constructor = $c_sci_WrappedString$;
/** @constructor */
function $h_sci_WrappedString$() {
  /*<skip>*/
}
$h_sci_WrappedString$.prototype = $c_sci_WrappedString$.prototype;
$c_sci_WrappedString$.prototype.fromSpecific__sc_IterableOnce__sci_WrappedString = (function(it) {
  var b = this.newBuilder__scm_Builder();
  var s = it.knownSize__I();
  if ((s >= 0)) {
    b.sizeHint__I__V(s)
  };
  b.addAll__sc_IterableOnce__scm_Growable(it);
  return $as_sci_WrappedString(b.result__O())
});
$c_sci_WrappedString$.prototype.newBuilder__scm_Builder = (function() {
  var this$1 = new $c_scm_StringBuilder().init___();
  var f = new $c_sjsr_AnonFunction1((function($this) {
    return (function(x$2) {
      var x = $as_T(x$2);
      return new $c_sci_WrappedString(x)
    })
  })(this));
  return new $c_scm_Builder$$anon$1(this$1, f)
});
var $d_sci_WrappedString$ = new $TypeData().initClass({
  sci_WrappedString$: 0
}, false, "scala.collection.immutable.WrappedString$", {
  sci_WrappedString$: 1,
  O: 1,
  sc_SpecificIterableFactory: 1,
  sc_Factory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_WrappedString$.prototype.$classData = $d_sci_WrappedString$;
var $n_sci_WrappedString$ = (void 0);
function $m_sci_WrappedString$() {
  if ((!$n_sci_WrappedString$)) {
    $n_sci_WrappedString$ = new $c_sci_WrappedString$()
  };
  return $n_sci_WrappedString$
}
/** @constructor */
function $c_scm_ArrayBuffer$$anon$1() {
  this.elems$1 = null;
  $c_scm_GrowableBuilder.prototype.init___scm_Growable.call(this, new $c_scm_ArrayBuffer().init___())
}
$c_scm_ArrayBuffer$$anon$1.prototype = new $h_scm_GrowableBuilder();
$c_scm_ArrayBuffer$$anon$1.prototype.constructor = $c_scm_ArrayBuffer$$anon$1;
/** @constructor */
function $h_scm_ArrayBuffer$$anon$1() {
  /*<skip>*/
}
$h_scm_ArrayBuffer$$anon$1.prototype = $c_scm_ArrayBuffer$$anon$1.prototype;
$c_scm_ArrayBuffer$$anon$1.prototype.sizeHint__I__V = (function(size) {
  $as_scm_ArrayBuffer(this.elems$1).ensureSize__I__V(size)
});
var $d_scm_ArrayBuffer$$anon$1 = new $TypeData().initClass({
  scm_ArrayBuffer$$anon$1: 0
}, false, "scala.collection.mutable.ArrayBuffer$$anon$1", {
  scm_ArrayBuffer$$anon$1: 1,
  scm_GrowableBuilder: 1,
  O: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_scm_ArrayBuffer$$anon$1.prototype.$classData = $d_scm_ArrayBuffer$$anon$1;
/** @constructor */
function $c_scm_FlatHashTable$$anon$1($$outer) {
  this.i$2 = 0;
  this.$$outer$2 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$2 = $$outer
  };
  this.i$2 = 0
}
$c_scm_FlatHashTable$$anon$1.prototype = new $h_sc_AbstractIterator();
$c_scm_FlatHashTable$$anon$1.prototype.constructor = $c_scm_FlatHashTable$$anon$1;
/** @constructor */
function $h_scm_FlatHashTable$$anon$1() {
  /*<skip>*/
}
$h_scm_FlatHashTable$$anon$1.prototype = $c_scm_FlatHashTable$$anon$1.prototype;
$c_scm_FlatHashTable$$anon$1.prototype.next__O = (function() {
  if (this.hasNext__Z()) {
    this.i$2 = ((1 + this.i$2) | 0);
    var this$1 = this.$$outer$2;
    var entry = this.$$outer$2.table$1.get((((-1) + this.i$2) | 0));
    return $f_scm_FlatHashTable$HashUtils__entryToElem__O__O(this$1, entry)
  } else {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  }
});
$c_scm_FlatHashTable$$anon$1.prototype.hasNext__Z = (function() {
  while (((this.i$2 < this.$$outer$2.table$1.u.length) && (this.$$outer$2.table$1.get(this.i$2) === null))) {
    this.i$2 = ((1 + this.i$2) | 0)
  };
  return (this.i$2 < this.$$outer$2.table$1.u.length)
});
var $d_scm_FlatHashTable$$anon$1 = new $TypeData().initClass({
  scm_FlatHashTable$$anon$1: 0
}, false, "scala.collection.mutable.FlatHashTable$$anon$1", {
  scm_FlatHashTable$$anon$1: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_scm_FlatHashTable$$anon$1.prototype.$classData = $d_scm_FlatHashTable$$anon$1;
/** @constructor */
function $c_scm_ImmutableBuilder() {
  this.empty$1 = null;
  this.elems$1 = null
}
$c_scm_ImmutableBuilder.prototype = new $h_O();
$c_scm_ImmutableBuilder.prototype.constructor = $c_scm_ImmutableBuilder;
/** @constructor */
function $h_scm_ImmutableBuilder() {
  /*<skip>*/
}
$h_scm_ImmutableBuilder.prototype = $c_scm_ImmutableBuilder.prototype;
$c_scm_ImmutableBuilder.prototype.init___O = (function(empty) {
  this.empty$1 = empty;
  this.elems$1 = empty;
  return this
});
$c_scm_ImmutableBuilder.prototype.result__O = (function() {
  return this.elems$1
});
$c_scm_ImmutableBuilder.prototype.addAll__sc_IterableOnce__scm_Growable = (function(xs) {
  return $f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this, xs)
});
$c_scm_ImmutableBuilder.prototype.sizeHint__I__V = (function(size) {
  /*<skip>*/
});
/** @constructor */
function $c_scm_Set$() {
  this.delegate$1 = null;
  $c_sc_IterableFactory$Delegate.prototype.init___sc_IterableFactory.call(this, $m_scm_HashSet$())
}
$c_scm_Set$.prototype = new $h_sc_IterableFactory$Delegate();
$c_scm_Set$.prototype.constructor = $c_scm_Set$;
/** @constructor */
function $h_scm_Set$() {
  /*<skip>*/
}
$h_scm_Set$.prototype = $c_scm_Set$.prototype;
var $d_scm_Set$ = new $TypeData().initClass({
  scm_Set$: 0
}, false, "scala.collection.mutable.Set$", {
  scm_Set$: 1,
  sc_IterableFactory$Delegate: 1,
  O: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_scm_Set$.prototype.$classData = $d_scm_Set$;
var $n_scm_Set$ = (void 0);
function $m_scm_Set$() {
  if ((!$n_scm_Set$)) {
    $n_scm_Set$ = new $c_scm_Set$()
  };
  return $n_scm_Set$
}
/** @constructor */
function $c_sjsr_UndefinedBehaviorError() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_sjsr_UndefinedBehaviorError.prototype = new $h_jl_VirtualMachineError();
$c_sjsr_UndefinedBehaviorError.prototype.constructor = $c_sjsr_UndefinedBehaviorError;
/** @constructor */
function $h_sjsr_UndefinedBehaviorError() {
  /*<skip>*/
}
$h_sjsr_UndefinedBehaviorError.prototype = $c_sjsr_UndefinedBehaviorError.prototype;
$c_sjsr_UndefinedBehaviorError.prototype.init___jl_Throwable = (function(cause) {
  var message = ((cause === null) ? null : cause.toString__T());
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, message, cause, true, true);
  return this
});
var $d_sjsr_UndefinedBehaviorError = new $TypeData().initClass({
  sjsr_UndefinedBehaviorError: 0
}, false, "scala.scalajs.runtime.UndefinedBehaviorError", {
  sjsr_UndefinedBehaviorError: 1,
  jl_VirtualMachineError: 1,
  jl_Error: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_sjsr_UndefinedBehaviorError.prototype.$classData = $d_sjsr_UndefinedBehaviorError;
/** @constructor */
function $c_sr_ScalaRunTime$$anon$1(x$2) {
  this.c$2 = 0;
  this.cmax$2 = 0;
  this.x$2$2 = null;
  this.x$2$2 = x$2;
  this.c$2 = 0;
  this.cmax$2 = x$2.productArity__I()
}
$c_sr_ScalaRunTime$$anon$1.prototype = new $h_sc_AbstractIterator();
$c_sr_ScalaRunTime$$anon$1.prototype.constructor = $c_sr_ScalaRunTime$$anon$1;
/** @constructor */
function $h_sr_ScalaRunTime$$anon$1() {
  /*<skip>*/
}
$h_sr_ScalaRunTime$$anon$1.prototype = $c_sr_ScalaRunTime$$anon$1.prototype;
$c_sr_ScalaRunTime$$anon$1.prototype.next__O = (function() {
  var result = this.x$2$2.productElement__I__O(this.c$2);
  this.c$2 = ((1 + this.c$2) | 0);
  return result
});
$c_sr_ScalaRunTime$$anon$1.prototype.hasNext__Z = (function() {
  return (this.c$2 < this.cmax$2)
});
var $d_sr_ScalaRunTime$$anon$1 = new $TypeData().initClass({
  sr_ScalaRunTime$$anon$1: 0
}, false, "scala.runtime.ScalaRunTime$$anon$1", {
  sr_ScalaRunTime$$anon$1: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sr_ScalaRunTime$$anon$1.prototype.$classData = $d_sr_ScalaRunTime$$anon$1;
/** @constructor */
function $c_T2(_1, _2) {
  this.$$und1$f = null;
  this.$$und2$f = null;
  this.$$und1$f = _1;
  this.$$und2$f = _2
}
$c_T2.prototype = new $h_O();
$c_T2.prototype.constructor = $c_T2;
/** @constructor */
function $h_T2() {
  /*<skip>*/
}
$h_T2.prototype = $c_T2.prototype;
$c_T2.prototype.productPrefix__T = (function() {
  return "Tuple2"
});
$c_T2.prototype.productArity__I = (function() {
  return 2
});
$c_T2.prototype.equals__O__Z = (function(x$1) {
  if ((this === x$1)) {
    return true
  } else if ($is_T2(x$1)) {
    var Tuple2$1 = $as_T2(x$1);
    return ($m_sr_BoxesRunTime$().equals__O__O__Z(this.$$und1$f, Tuple2$1.$$und1$f) && $m_sr_BoxesRunTime$().equals__O__O__Z(this.$$und2$f, Tuple2$1.$$und2$f))
  } else {
    return false
  }
});
$c_T2.prototype.productElement__I__O = (function(n) {
  return $f_s_Product2__productElement__I__O(this, n)
});
$c_T2.prototype.toString__T = (function() {
  return (((("(" + this.$$und1$f) + ",") + this.$$und2$f) + ")")
});
$c_T2.prototype.$$und2__O = (function() {
  return this.$$und2$f
});
$c_T2.prototype.hashCode__I = (function() {
  var this$2 = $m_s_util_hashing_MurmurHash3$();
  return this$2.productHash__s_Product__I__I(this, (-889275714))
});
$c_T2.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
$c_T2.prototype.$$und1__O = (function() {
  return this.$$und1$f
});
function $is_T2(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.T2)))
}
function $as_T2(obj) {
  return (($is_T2(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.Tuple2"))
}
function $isArrayOf_T2(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.T2)))
}
function $asArrayOf_T2(obj, depth) {
  return (($isArrayOf_T2(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.Tuple2;", depth))
}
var $d_T2 = new $TypeData().initClass({
  T2: 0
}, false, "scala.Tuple2", {
  T2: 1,
  O: 1,
  s_Product2: 1,
  s_Product: 1,
  s_Equals: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_T2.prototype.$classData = $d_T2;
/** @constructor */
function $c_T3(_1, _2, _3) {
  this.$$und1$1 = null;
  this.$$und2$1 = null;
  this.$$und3$1 = null;
  this.$$und1$1 = _1;
  this.$$und2$1 = _2;
  this.$$und3$1 = _3
}
$c_T3.prototype = new $h_O();
$c_T3.prototype.constructor = $c_T3;
/** @constructor */
function $h_T3() {
  /*<skip>*/
}
$h_T3.prototype = $c_T3.prototype;
$c_T3.prototype.productPrefix__T = (function() {
  return "Tuple3"
});
$c_T3.prototype.productArity__I = (function() {
  return 3
});
$c_T3.prototype.equals__O__Z = (function(x$1) {
  if ((this === x$1)) {
    return true
  } else if ($is_T3(x$1)) {
    var Tuple3$1 = $as_T3(x$1);
    return (($m_sr_BoxesRunTime$().equals__O__O__Z(this.$$und1$1, Tuple3$1.$$und1$1) && $m_sr_BoxesRunTime$().equals__O__O__Z(this.$$und2$1, Tuple3$1.$$und2$1)) && $m_sr_BoxesRunTime$().equals__O__O__Z(this.$$und3$1, Tuple3$1.$$und3$1))
  } else {
    return false
  }
});
$c_T3.prototype.productElement__I__O = (function(n) {
  return $f_s_Product3__productElement__I__O(this, n)
});
$c_T3.prototype.toString__T = (function() {
  return (((((("(" + this.$$und1$1) + ",") + this.$$und2$1) + ",") + this.$$und3$1) + ")")
});
$c_T3.prototype.hashCode__I = (function() {
  var this$2 = $m_s_util_hashing_MurmurHash3$();
  return this$2.productHash__s_Product__I__I(this, (-889275714))
});
$c_T3.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
function $is_T3(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.T3)))
}
function $as_T3(obj) {
  return (($is_T3(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.Tuple3"))
}
function $isArrayOf_T3(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.T3)))
}
function $asArrayOf_T3(obj, depth) {
  return (($isArrayOf_T3(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.Tuple3;", depth))
}
var $d_T3 = new $TypeData().initClass({
  T3: 0
}, false, "scala.Tuple3", {
  T3: 1,
  O: 1,
  s_Product3: 1,
  s_Product: 1,
  s_Equals: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_T3.prototype.$classData = $d_T3;
/** @constructor */
function $c_jl_ArrayIndexOutOfBoundsException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null
}
$c_jl_ArrayIndexOutOfBoundsException.prototype = new $h_jl_IndexOutOfBoundsException();
$c_jl_ArrayIndexOutOfBoundsException.prototype.constructor = $c_jl_ArrayIndexOutOfBoundsException;
/** @constructor */
function $h_jl_ArrayIndexOutOfBoundsException() {
  /*<skip>*/
}
$h_jl_ArrayIndexOutOfBoundsException.prototype = $c_jl_ArrayIndexOutOfBoundsException.prototype;
$c_jl_ArrayIndexOutOfBoundsException.prototype.init___ = (function() {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true);
  return this
});
$c_jl_ArrayIndexOutOfBoundsException.prototype.init___T = (function(s) {
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, s, null, true, true);
  return this
});
var $d_jl_ArrayIndexOutOfBoundsException = new $TypeData().initClass({
  jl_ArrayIndexOutOfBoundsException: 0
}, false, "java.lang.ArrayIndexOutOfBoundsException", {
  jl_ArrayIndexOutOfBoundsException: 1,
  jl_IndexOutOfBoundsException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_ArrayIndexOutOfBoundsException.prototype.$classData = $d_jl_ArrayIndexOutOfBoundsException;
/** @constructor */
function $c_jl_StringIndexOutOfBoundsException() {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null;
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true)
}
$c_jl_StringIndexOutOfBoundsException.prototype = new $h_jl_IndexOutOfBoundsException();
$c_jl_StringIndexOutOfBoundsException.prototype.constructor = $c_jl_StringIndexOutOfBoundsException;
/** @constructor */
function $h_jl_StringIndexOutOfBoundsException() {
  /*<skip>*/
}
$h_jl_StringIndexOutOfBoundsException.prototype = $c_jl_StringIndexOutOfBoundsException.prototype;
var $d_jl_StringIndexOutOfBoundsException = new $TypeData().initClass({
  jl_StringIndexOutOfBoundsException: 0
}, false, "java.lang.StringIndexOutOfBoundsException", {
  jl_StringIndexOutOfBoundsException: 1,
  jl_IndexOutOfBoundsException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1
});
$c_jl_StringIndexOutOfBoundsException.prototype.$classData = $d_jl_StringIndexOutOfBoundsException;
/** @constructor */
function $c_s_None$() {
  /*<skip>*/
}
$c_s_None$.prototype = new $h_s_Option();
$c_s_None$.prototype.constructor = $c_s_None$;
/** @constructor */
function $h_s_None$() {
  /*<skip>*/
}
$h_s_None$.prototype = $c_s_None$.prototype;
$c_s_None$.prototype.productPrefix__T = (function() {
  return "None"
});
$c_s_None$.prototype.productArity__I = (function() {
  return 0
});
$c_s_None$.prototype.isEmpty__Z = (function() {
  return true
});
$c_s_None$.prototype.get__O = (function() {
  this.get__E()
});
$c_s_None$.prototype.productElement__I__O = (function(x$1) {
  throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
});
$c_s_None$.prototype.toString__T = (function() {
  return "None"
});
$c_s_None$.prototype.get__E = (function() {
  throw new $c_ju_NoSuchElementException().init___T("None.get")
});
$c_s_None$.prototype.hashCode__I = (function() {
  return 2433880
});
$c_s_None$.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
var $d_s_None$ = new $TypeData().initClass({
  s_None$: 0
}, false, "scala.None$", {
  s_None$: 1,
  s_Option: 1,
  O: 1,
  s_Product: 1,
  s_Equals: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_None$.prototype.$classData = $d_s_None$;
var $n_s_None$ = (void 0);
function $m_s_None$() {
  if ((!$n_s_None$)) {
    $n_s_None$ = new $c_s_None$()
  };
  return $n_s_None$
}
/** @constructor */
function $c_s_Predef$$eq$colon$eq$$anon$1() {
  /*<skip>*/
}
$c_s_Predef$$eq$colon$eq$$anon$1.prototype = new $h_s_Predef$$eq$colon$eq();
$c_s_Predef$$eq$colon$eq$$anon$1.prototype.constructor = $c_s_Predef$$eq$colon$eq$$anon$1;
/** @constructor */
function $h_s_Predef$$eq$colon$eq$$anon$1() {
  /*<skip>*/
}
$h_s_Predef$$eq$colon$eq$$anon$1.prototype = $c_s_Predef$$eq$colon$eq$$anon$1.prototype;
$c_s_Predef$$eq$colon$eq$$anon$1.prototype.apply__O__O = (function(x) {
  return x
});
$c_s_Predef$$eq$colon$eq$$anon$1.prototype.toString__T = (function() {
  return "generalized constraint"
});
var $d_s_Predef$$eq$colon$eq$$anon$1 = new $TypeData().initClass({
  s_Predef$$eq$colon$eq$$anon$1: 0
}, false, "scala.Predef$$eq$colon$eq$$anon$1", {
  s_Predef$$eq$colon$eq$$anon$1: 1,
  s_Predef$$eq$colon$eq: 1,
  s_Predef$$less$colon$less: 1,
  O: 1,
  F1: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_Predef$$eq$colon$eq$$anon$1.prototype.$classData = $d_s_Predef$$eq$colon$eq$$anon$1;
/** @constructor */
function $c_s_Some(value) {
  this.value$2 = null;
  this.value$2 = value
}
$c_s_Some.prototype = new $h_s_Option();
$c_s_Some.prototype.constructor = $c_s_Some;
/** @constructor */
function $h_s_Some() {
  /*<skip>*/
}
$h_s_Some.prototype = $c_s_Some.prototype;
$c_s_Some.prototype.productPrefix__T = (function() {
  return "Some"
});
$c_s_Some.prototype.productArity__I = (function() {
  return 1
});
$c_s_Some.prototype.equals__O__Z = (function(x$1) {
  if ((this === x$1)) {
    return true
  } else if ($is_s_Some(x$1)) {
    var Some$1 = $as_s_Some(x$1);
    return $m_sr_BoxesRunTime$().equals__O__O__Z(this.value$2, Some$1.value$2)
  } else {
    return false
  }
});
$c_s_Some.prototype.isEmpty__Z = (function() {
  return false
});
$c_s_Some.prototype.productElement__I__O = (function(x$1) {
  if ((x$1 === 0)) {
    return this.value$2
  } else {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
  }
});
$c_s_Some.prototype.get__O = (function() {
  return this.value$2
});
$c_s_Some.prototype.toString__T = (function() {
  return $m_sr_ScalaRunTime$().$$undtoString__s_Product__T(this)
});
$c_s_Some.prototype.hashCode__I = (function() {
  var this$2 = $m_s_util_hashing_MurmurHash3$();
  return this$2.productHash__s_Product__I__I(this, (-889275714))
});
$c_s_Some.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
function $is_s_Some(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.s_Some)))
}
function $as_s_Some(obj) {
  return (($is_s_Some(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.Some"))
}
function $isArrayOf_s_Some(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.s_Some)))
}
function $asArrayOf_s_Some(obj, depth) {
  return (($isArrayOf_s_Some(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.Some;", depth))
}
var $d_s_Some = new $TypeData().initClass({
  s_Some: 0
}, false, "scala.Some", {
  s_Some: 1,
  s_Option: 1,
  O: 1,
  s_Product: 1,
  s_Equals: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_Some.prototype.$classData = $d_s_Some;
/** @constructor */
function $c_sc_Iterator$$anon$20() {
  this.empty$1 = null;
  this.elems$1 = null;
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f)
}
$c_sc_Iterator$$anon$20.prototype = new $h_scm_ImmutableBuilder();
$c_sc_Iterator$$anon$20.prototype.constructor = $c_sc_Iterator$$anon$20;
/** @constructor */
function $h_sc_Iterator$$anon$20() {
  /*<skip>*/
}
$h_sc_Iterator$$anon$20.prototype = $c_sc_Iterator$$anon$20.prototype;
$c_sc_Iterator$$anon$20.prototype.addOne__O__sc_Iterator$$anon$20 = (function(elem) {
  var this$2 = $as_sc_Iterator(this.elems$1);
  var xs = new $c_sjsr_AnonFunction0((function($this, elem$1) {
    return (function() {
      $m_sc_Iterator$();
      return new $c_sc_Iterator$$anon$19(elem$1)
    })
  })(this, elem));
  this.elems$1 = this$2.concat__F0__sc_Iterator(xs);
  return this
});
$c_sc_Iterator$$anon$20.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__sc_Iterator$$anon$20(elem)
});
var $d_sc_Iterator$$anon$20 = new $TypeData().initClass({
  sc_Iterator$$anon$20: 0
}, false, "scala.collection.Iterator$$anon$20", {
  sc_Iterator$$anon$20: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sc_Iterator$$anon$20.prototype.$classData = $d_sc_Iterator$$anon$20;
function $f_sc_View__toString__T($thiz) {
  return "View(?)"
}
function $is_sc_View(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_View)))
}
function $as_sc_View(obj) {
  return (($is_sc_View(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.View"))
}
function $isArrayOf_sc_View(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_View)))
}
function $asArrayOf_sc_View(obj, depth) {
  return (($isArrayOf_sc_View(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.View;", depth))
}
/** @constructor */
function $c_sci_HashMap$$anon$2() {
  this.empty$1 = null;
  this.elems$1 = null;
  var this$1 = $m_sci_HashMap$();
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, this$1.EmptyMap$1)
}
$c_sci_HashMap$$anon$2.prototype = new $h_scm_ImmutableBuilder();
$c_sci_HashMap$$anon$2.prototype.constructor = $c_sci_HashMap$$anon$2;
/** @constructor */
function $h_sci_HashMap$$anon$2() {
  /*<skip>*/
}
$h_sci_HashMap$$anon$2.prototype = $c_sci_HashMap$$anon$2.prototype;
$c_sci_HashMap$$anon$2.prototype.addOne__T2__sci_HashMap$$anon$2 = (function(element) {
  this.elems$1 = $as_sci_MapOps(this.elems$1).$$plus__T2__sci_MapOps(element);
  return this
});
$c_sci_HashMap$$anon$2.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__T2__sci_HashMap$$anon$2($as_T2(elem))
});
var $d_sci_HashMap$$anon$2 = new $TypeData().initClass({
  sci_HashMap$$anon$2: 0
}, false, "scala.collection.immutable.HashMap$$anon$2", {
  sci_HashMap$$anon$2: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sci_HashMap$$anon$2.prototype.$classData = $d_sci_HashMap$$anon$2;
/** @constructor */
function $c_sci_HashSet$$anon$1() {
  this.empty$1 = null;
  this.elems$1 = null;
  var this$1 = $m_sci_HashSet$();
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, this$1.EmptySet$1)
}
$c_sci_HashSet$$anon$1.prototype = new $h_scm_ImmutableBuilder();
$c_sci_HashSet$$anon$1.prototype.constructor = $c_sci_HashSet$$anon$1;
/** @constructor */
function $h_sci_HashSet$$anon$1() {
  /*<skip>*/
}
$h_sci_HashSet$$anon$1.prototype = $c_sci_HashSet$$anon$1.prototype;
$c_sci_HashSet$$anon$1.prototype.addOne__O__sci_HashSet$$anon$1 = (function(element) {
  var this$1 = $as_sci_SetOps(this.elems$1);
  this.elems$1 = this$1.incl__O__sci_SetOps(element);
  return this
});
$c_sci_HashSet$$anon$1.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__sci_HashSet$$anon$1(elem)
});
var $d_sci_HashSet$$anon$1 = new $TypeData().initClass({
  sci_HashSet$$anon$1: 0
}, false, "scala.collection.immutable.HashSet$$anon$1", {
  sci_HashSet$$anon$1: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sci_HashSet$$anon$1.prototype.$classData = $d_sci_HashSet$$anon$1;
/** @constructor */
function $c_sci_IndexedSeq$() {
  this.delegate$1 = null;
  $c_sc_SeqFactory$Delegate.prototype.init___sc_SeqFactory.call(this, $m_sci_Vector$())
}
$c_sci_IndexedSeq$.prototype = new $h_sc_SeqFactory$Delegate();
$c_sci_IndexedSeq$.prototype.constructor = $c_sci_IndexedSeq$;
/** @constructor */
function $h_sci_IndexedSeq$() {
  /*<skip>*/
}
$h_sci_IndexedSeq$.prototype = $c_sci_IndexedSeq$.prototype;
var $d_sci_IndexedSeq$ = new $TypeData().initClass({
  sci_IndexedSeq$: 0
}, false, "scala.collection.immutable.IndexedSeq$", {
  sci_IndexedSeq$: 1,
  sc_SeqFactory$Delegate: 1,
  O: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_IndexedSeq$.prototype.$classData = $d_sci_IndexedSeq$;
var $n_sci_IndexedSeq$ = (void 0);
function $m_sci_IndexedSeq$() {
  if ((!$n_sci_IndexedSeq$)) {
    $n_sci_IndexedSeq$ = new $c_sci_IndexedSeq$()
  };
  return $n_sci_IndexedSeq$
}
function $is_sci_Iterable(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_Iterable)))
}
function $as_sci_Iterable(obj) {
  return (($is_sci_Iterable(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.Iterable"))
}
function $isArrayOf_sci_Iterable(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_Iterable)))
}
function $asArrayOf_sci_Iterable(obj, depth) {
  return (($isArrayOf_sci_Iterable(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.Iterable;", depth))
}
var $d_sci_Iterable = new $TypeData().initClass({
  sci_Iterable: 0
}, true, "scala.collection.immutable.Iterable", {
  sci_Iterable: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
/** @constructor */
function $c_sci_List$() {
  this.partialNotApplied$1 = null;
  $n_sci_List$ = this;
  this.partialNotApplied$1 = new $c_sci_List$$anon$1()
}
$c_sci_List$.prototype = new $h_O();
$c_sci_List$.prototype.constructor = $c_sci_List$;
/** @constructor */
function $h_sci_List$() {
  /*<skip>*/
}
$h_sci_List$.prototype = $c_sci_List$.prototype;
$c_sci_List$.prototype.from__sc_IterableOnce__sci_List = (function(coll) {
  if ($is_sci_List(coll)) {
    var x2 = $as_sci_List(coll);
    return x2
  } else if ((coll.knownSize__I() === 0)) {
    return $m_sci_Nil$()
  } else {
    var this$2 = new $c_scm_ListBuffer();
    return $as_scm_ListBuffer($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$2, coll)).toList__sci_List()
  }
});
$c_sci_List$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sci_List(source)
});
$c_sci_List$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_scm_ListBuffer()
});
var $d_sci_List$ = new $TypeData().initClass({
  sci_List$: 0
}, false, "scala.collection.immutable.List$", {
  sci_List$: 1,
  O: 1,
  sc_StrictOptimizedSeqFactory: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_List$.prototype.$classData = $d_sci_List$;
var $n_sci_List$ = (void 0);
function $m_sci_List$() {
  if ((!$n_sci_List$)) {
    $n_sci_List$ = new $c_sci_List$()
  };
  return $n_sci_List$
}
/** @constructor */
function $c_sci_ListMap$$anon$1() {
  this.empty$1 = null;
  this.elems$1 = null;
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, $m_sci_ListMap$EmptyListMap$())
}
$c_sci_ListMap$$anon$1.prototype = new $h_scm_ImmutableBuilder();
$c_sci_ListMap$$anon$1.prototype.constructor = $c_sci_ListMap$$anon$1;
/** @constructor */
function $h_sci_ListMap$$anon$1() {
  /*<skip>*/
}
$h_sci_ListMap$$anon$1.prototype = $c_sci_ListMap$$anon$1.prototype;
$c_sci_ListMap$$anon$1.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__T2__sci_ListMap$$anon$1($as_T2(elem))
});
$c_sci_ListMap$$anon$1.prototype.addOne__T2__sci_ListMap$$anon$1 = (function(elem) {
  this.elems$1 = $as_sci_MapOps(this.elems$1).$$plus__T2__sci_MapOps(elem);
  return this
});
var $d_sci_ListMap$$anon$1 = new $TypeData().initClass({
  sci_ListMap$$anon$1: 0
}, false, "scala.collection.immutable.ListMap$$anon$1", {
  sci_ListMap$$anon$1: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sci_ListMap$$anon$1.prototype.$classData = $d_sci_ListMap$$anon$1;
/** @constructor */
function $c_sci_ListSet$$anon$1() {
  this.empty$1 = null;
  this.elems$1 = null;
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, $m_sci_ListSet$EmptyListSet$())
}
$c_sci_ListSet$$anon$1.prototype = new $h_scm_ImmutableBuilder();
$c_sci_ListSet$$anon$1.prototype.constructor = $c_sci_ListSet$$anon$1;
/** @constructor */
function $h_sci_ListSet$$anon$1() {
  /*<skip>*/
}
$h_sci_ListSet$$anon$1.prototype = $c_sci_ListSet$$anon$1.prototype;
$c_sci_ListSet$$anon$1.prototype.addOne__O__sci_ListSet$$anon$1 = (function(elem) {
  var this$1 = $as_sci_SetOps(this.elems$1);
  this.elems$1 = this$1.incl__O__sci_SetOps(elem);
  return this
});
$c_sci_ListSet$$anon$1.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__sci_ListSet$$anon$1(elem)
});
var $d_sci_ListSet$$anon$1 = new $TypeData().initClass({
  sci_ListSet$$anon$1: 0
}, false, "scala.collection.immutable.ListSet$$anon$1", {
  sci_ListSet$$anon$1: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sci_ListSet$$anon$1.prototype.$classData = $d_sci_ListSet$$anon$1;
/** @constructor */
function $c_sci_Map$$anon$1() {
  this.empty$1 = null;
  this.elems$1 = null;
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, ($m_sci_Map$(), $m_sci_Map$EmptyMap$()))
}
$c_sci_Map$$anon$1.prototype = new $h_scm_ImmutableBuilder();
$c_sci_Map$$anon$1.prototype.constructor = $c_sci_Map$$anon$1;
/** @constructor */
function $h_sci_Map$$anon$1() {
  /*<skip>*/
}
$h_sci_Map$$anon$1.prototype = $c_sci_Map$$anon$1.prototype;
$c_sci_Map$$anon$1.prototype.addOne__T2__sci_Map$$anon$1 = (function(elem) {
  this.elems$1 = $as_sci_MapOps(this.elems$1).$$plus__T2__sci_MapOps(elem);
  return this
});
$c_sci_Map$$anon$1.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__T2__sci_Map$$anon$1($as_T2(elem))
});
var $d_sci_Map$$anon$1 = new $TypeData().initClass({
  sci_Map$$anon$1: 0
}, false, "scala.collection.immutable.Map$$anon$1", {
  sci_Map$$anon$1: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sci_Map$$anon$1.prototype.$classData = $d_sci_Map$$anon$1;
/** @constructor */
function $c_sci_Map$Map2$$anon$2($$outer) {
  this.i$2 = 0;
  this.$$outer$2 = null;
  $c_sci_Map$Map2$Map2Iterator.prototype.init___sci_Map$Map2.call(this, $$outer)
}
$c_sci_Map$Map2$$anon$2.prototype = new $h_sci_Map$Map2$Map2Iterator();
$c_sci_Map$Map2$$anon$2.prototype.constructor = $c_sci_Map$Map2$$anon$2;
/** @constructor */
function $h_sci_Map$Map2$$anon$2() {
  /*<skip>*/
}
$h_sci_Map$Map2$$anon$2.prototype = $c_sci_Map$Map2$$anon$2.prototype;
var $d_sci_Map$Map2$$anon$2 = new $TypeData().initClass({
  sci_Map$Map2$$anon$2: 0
}, false, "scala.collection.immutable.Map$Map2$$anon$2", {
  sci_Map$Map2$$anon$2: 1,
  sci_Map$Map2$Map2Iterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_Map$Map2$$anon$2.prototype.$classData = $d_sci_Map$Map2$$anon$2;
/** @constructor */
function $c_sci_Map$Map3$$anon$5($$outer) {
  this.i$2 = 0;
  this.$$outer$2 = null;
  $c_sci_Map$Map3$Map3Iterator.prototype.init___sci_Map$Map3.call(this, $$outer)
}
$c_sci_Map$Map3$$anon$5.prototype = new $h_sci_Map$Map3$Map3Iterator();
$c_sci_Map$Map3$$anon$5.prototype.constructor = $c_sci_Map$Map3$$anon$5;
/** @constructor */
function $h_sci_Map$Map3$$anon$5() {
  /*<skip>*/
}
$h_sci_Map$Map3$$anon$5.prototype = $c_sci_Map$Map3$$anon$5.prototype;
var $d_sci_Map$Map3$$anon$5 = new $TypeData().initClass({
  sci_Map$Map3$$anon$5: 0
}, false, "scala.collection.immutable.Map$Map3$$anon$5", {
  sci_Map$Map3$$anon$5: 1,
  sci_Map$Map3$Map3Iterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_Map$Map3$$anon$5.prototype.$classData = $d_sci_Map$Map3$$anon$5;
/** @constructor */
function $c_sci_Map$Map4$$anon$8($$outer) {
  this.i$2 = 0;
  this.$$outer$2 = null;
  $c_sci_Map$Map4$Map4Iterator.prototype.init___sci_Map$Map4.call(this, $$outer)
}
$c_sci_Map$Map4$$anon$8.prototype = new $h_sci_Map$Map4$Map4Iterator();
$c_sci_Map$Map4$$anon$8.prototype.constructor = $c_sci_Map$Map4$$anon$8;
/** @constructor */
function $h_sci_Map$Map4$$anon$8() {
  /*<skip>*/
}
$h_sci_Map$Map4$$anon$8.prototype = $c_sci_Map$Map4$$anon$8.prototype;
var $d_sci_Map$Map4$$anon$8 = new $TypeData().initClass({
  sci_Map$Map4$$anon$8: 0
}, false, "scala.collection.immutable.Map$Map4$$anon$8", {
  sci_Map$Map4$$anon$8: 1,
  sci_Map$Map4$Map4Iterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1
});
$c_sci_Map$Map4$$anon$8.prototype.$classData = $d_sci_Map$Map4$$anon$8;
function $is_sci_MapOps(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_MapOps)))
}
function $as_sci_MapOps(obj) {
  return (($is_sci_MapOps(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.MapOps"))
}
function $isArrayOf_sci_MapOps(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_MapOps)))
}
function $asArrayOf_sci_MapOps(obj, depth) {
  return (($isArrayOf_sci_MapOps(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.MapOps;", depth))
}
/** @constructor */
function $c_sci_OldHashMap$$anon$1() {
  this.empty$1 = null;
  this.elems$1 = null;
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, ($m_sci_OldHashMap$(), $m_sci_OldHashMap$EmptyOldHashMap$()))
}
$c_sci_OldHashMap$$anon$1.prototype = new $h_scm_ImmutableBuilder();
$c_sci_OldHashMap$$anon$1.prototype.constructor = $c_sci_OldHashMap$$anon$1;
/** @constructor */
function $h_sci_OldHashMap$$anon$1() {
  /*<skip>*/
}
$h_sci_OldHashMap$$anon$1.prototype = $c_sci_OldHashMap$$anon$1.prototype;
$c_sci_OldHashMap$$anon$1.prototype.addOne__T2__sci_OldHashMap$$anon$1 = (function(elem) {
  var this$1 = $as_sci_OldHashMap(this.elems$1);
  this.elems$1 = this$1.updated__O__O__sci_OldHashMap(elem.$$und1$f, elem.$$und2$f);
  return this
});
$c_sci_OldHashMap$$anon$1.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__T2__sci_OldHashMap$$anon$1($as_T2(elem))
});
var $d_sci_OldHashMap$$anon$1 = new $TypeData().initClass({
  sci_OldHashMap$$anon$1: 0
}, false, "scala.collection.immutable.OldHashMap$$anon$1", {
  sci_OldHashMap$$anon$1: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sci_OldHashMap$$anon$1.prototype.$classData = $d_sci_OldHashMap$$anon$1;
/** @constructor */
function $c_sci_OldHashSet$$anon$1() {
  this.empty$1 = null;
  this.elems$1 = null;
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, $m_sci_OldHashSet$EmptyOldHashSet$())
}
$c_sci_OldHashSet$$anon$1.prototype = new $h_scm_ImmutableBuilder();
$c_sci_OldHashSet$$anon$1.prototype.constructor = $c_sci_OldHashSet$$anon$1;
/** @constructor */
function $h_sci_OldHashSet$$anon$1() {
  /*<skip>*/
}
$h_sci_OldHashSet$$anon$1.prototype = $c_sci_OldHashSet$$anon$1.prototype;
$c_sci_OldHashSet$$anon$1.prototype.addOne__O__sci_OldHashSet$$anon$1 = (function(elem) {
  var this$1 = $as_sci_SetOps(this.elems$1);
  this.elems$1 = this$1.incl__O__sci_SetOps(elem);
  return this
});
$c_sci_OldHashSet$$anon$1.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__sci_OldHashSet$$anon$1(elem)
});
var $d_sci_OldHashSet$$anon$1 = new $TypeData().initClass({
  sci_OldHashSet$$anon$1: 0
}, false, "scala.collection.immutable.OldHashSet$$anon$1", {
  sci_OldHashSet$$anon$1: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sci_OldHashSet$$anon$1.prototype.$classData = $d_sci_OldHashSet$$anon$1;
/** @constructor */
function $c_sci_Seq$() {
  this.delegate$1 = null;
  $c_sc_SeqFactory$Delegate.prototype.init___sc_SeqFactory.call(this, $m_sci_List$())
}
$c_sci_Seq$.prototype = new $h_sc_SeqFactory$Delegate();
$c_sci_Seq$.prototype.constructor = $c_sci_Seq$;
/** @constructor */
function $h_sci_Seq$() {
  /*<skip>*/
}
$h_sci_Seq$.prototype = $c_sci_Seq$.prototype;
var $d_sci_Seq$ = new $TypeData().initClass({
  sci_Seq$: 0
}, false, "scala.collection.immutable.Seq$", {
  sci_Seq$: 1,
  sc_SeqFactory$Delegate: 1,
  O: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_Seq$.prototype.$classData = $d_sci_Seq$;
var $n_sci_Seq$ = (void 0);
function $m_sci_Seq$() {
  if ((!$n_sci_Seq$)) {
    $n_sci_Seq$ = new $c_sci_Seq$()
  };
  return $n_sci_Seq$
}
/** @constructor */
function $c_sci_Set$$anon$1() {
  this.empty$1 = null;
  this.elems$1 = null;
  $c_scm_ImmutableBuilder.prototype.init___O.call(this, ($m_sci_Set$(), $m_sci_Set$EmptySet$()))
}
$c_sci_Set$$anon$1.prototype = new $h_scm_ImmutableBuilder();
$c_sci_Set$$anon$1.prototype.constructor = $c_sci_Set$$anon$1;
/** @constructor */
function $h_sci_Set$$anon$1() {
  /*<skip>*/
}
$h_sci_Set$$anon$1.prototype = $c_sci_Set$$anon$1.prototype;
$c_sci_Set$$anon$1.prototype.addOne__O__sci_Set$$anon$1 = (function(elem) {
  var this$1 = $as_sci_SetOps(this.elems$1);
  this.elems$1 = this$1.incl__O__sci_SetOps(elem);
  return this
});
$c_sci_Set$$anon$1.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__sci_Set$$anon$1(elem)
});
var $d_sci_Set$$anon$1 = new $TypeData().initClass({
  sci_Set$$anon$1: 0
}, false, "scala.collection.immutable.Set$$anon$1", {
  sci_Set$$anon$1: 1,
  scm_ImmutableBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1
});
$c_sci_Set$$anon$1.prototype.$classData = $d_sci_Set$$anon$1;
/** @constructor */
function $c_sci_Vector$() {
  this.NIL$1 = null;
  $n_sci_Vector$ = this;
  this.NIL$1 = new $c_sci_Vector(0, 0, 0)
}
$c_sci_Vector$.prototype = new $h_O();
$c_sci_Vector$.prototype.constructor = $c_sci_Vector$;
/** @constructor */
function $h_sci_Vector$() {
  /*<skip>*/
}
$h_sci_Vector$.prototype = $c_sci_Vector$.prototype;
$c_sci_Vector$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sci_Vector(source)
});
$c_sci_Vector$.prototype.from__sc_IterableOnce__sci_Vector = (function(it) {
  if ($is_sci_Vector(it)) {
    var x2 = $as_sci_Vector(it);
    return x2
  } else if ((it.knownSize__I() === 0)) {
    return this.NIL$1
  } else {
    var this$1 = new $c_sci_VectorBuilder();
    return $as_sci_Vector($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, it)).result__O())
  }
});
$c_sci_Vector$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sci_VectorBuilder()
});
var $d_sci_Vector$ = new $TypeData().initClass({
  sci_Vector$: 0
}, false, "scala.collection.immutable.Vector$", {
  sci_Vector$: 1,
  O: 1,
  sc_StrictOptimizedSeqFactory: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_Vector$.prototype.$classData = $d_sci_Vector$;
var $n_sci_Vector$ = (void 0);
function $m_sci_Vector$() {
  if ((!$n_sci_Vector$)) {
    $n_sci_Vector$ = new $c_sci_Vector$()
  };
  return $n_sci_Vector$
}
/** @constructor */
function $c_sci_VectorBuilder() {
  this.blockIndex$1 = 0;
  this.lo$1 = 0;
  this.depth$1 = 0;
  this.display0$1 = null;
  this.display1$1 = null;
  this.display2$1 = null;
  this.display3$1 = null;
  this.display4$1 = null;
  this.display5$1 = null;
  this.display0$1 = $newArrayObject($d_O.getArrayOf(), [32]);
  this.depth$1 = 1;
  this.blockIndex$1 = 0;
  this.lo$1 = 0
}
$c_sci_VectorBuilder.prototype = new $h_O();
$c_sci_VectorBuilder.prototype.constructor = $c_sci_VectorBuilder;
/** @constructor */
function $h_sci_VectorBuilder() {
  /*<skip>*/
}
$h_sci_VectorBuilder.prototype = $c_sci_VectorBuilder.prototype;
$c_sci_VectorBuilder.prototype.display3__AO = (function() {
  return this.display3$1
});
$c_sci_VectorBuilder.prototype.addOne__O__sci_VectorBuilder = (function(elem) {
  if ((this.lo$1 >= this.display0$1.u.length)) {
    var newBlockIndex = ((32 + this.blockIndex$1) | 0);
    var xor = (this.blockIndex$1 ^ newBlockIndex);
    $f_sci_VectorPointer__gotoNextBlockStartWritable__I__I__V(this, newBlockIndex, xor);
    this.blockIndex$1 = newBlockIndex;
    this.lo$1 = 0
  };
  this.display0$1.set(this.lo$1, elem);
  this.lo$1 = ((1 + this.lo$1) | 0);
  return this
});
$c_sci_VectorBuilder.prototype.depth__I = (function() {
  return this.depth$1
});
$c_sci_VectorBuilder.prototype.display5$und$eq__AO__V = (function(x$1) {
  this.display5$1 = x$1
});
$c_sci_VectorBuilder.prototype.display0__AO = (function() {
  return this.display0$1
});
$c_sci_VectorBuilder.prototype.display2$und$eq__AO__V = (function(x$1) {
  this.display2$1 = x$1
});
$c_sci_VectorBuilder.prototype.display4__AO = (function() {
  return this.display4$1
});
$c_sci_VectorBuilder.prototype.size__I = (function() {
  return ((this.blockIndex$1 + this.lo$1) | 0)
});
$c_sci_VectorBuilder.prototype.result__O = (function() {
  return this.result__sci_Vector()
});
$c_sci_VectorBuilder.prototype.display1$und$eq__AO__V = (function(x$1) {
  this.display1$1 = x$1
});
$c_sci_VectorBuilder.prototype.display4$und$eq__AO__V = (function(x$1) {
  this.display4$1 = x$1
});
$c_sci_VectorBuilder.prototype.display1__AO = (function() {
  return this.display1$1
});
$c_sci_VectorBuilder.prototype.display5__AO = (function() {
  return this.display5$1
});
$c_sci_VectorBuilder.prototype.addAll__sc_IterableOnce__scm_Growable = (function(xs) {
  return $f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this, xs)
});
$c_sci_VectorBuilder.prototype.result__sci_Vector = (function() {
  var size = this.size__I();
  if ((size === 0)) {
    var this$1 = $m_sci_Vector$();
    return this$1.NIL$1
  };
  var s = new $c_sci_Vector(0, size, 0);
  var depth = this.depth$1;
  $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s, this, depth);
  if ((this.depth$1 > 1)) {
    var xor = (((-1) + size) | 0);
    $f_sci_VectorPointer__gotoPos__I__I__V(s, 0, xor)
  };
  return s
});
$c_sci_VectorBuilder.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__sci_VectorBuilder(elem)
});
$c_sci_VectorBuilder.prototype.sizeHint__I__V = (function(size) {
  /*<skip>*/
});
$c_sci_VectorBuilder.prototype.depth$und$eq__I__V = (function(x$1) {
  this.depth$1 = x$1
});
$c_sci_VectorBuilder.prototype.display2__AO = (function() {
  return this.display2$1
});
$c_sci_VectorBuilder.prototype.display0$und$eq__AO__V = (function(x$1) {
  this.display0$1 = x$1
});
$c_sci_VectorBuilder.prototype.display3$und$eq__AO__V = (function(x$1) {
  this.display3$1 = x$1
});
var $d_sci_VectorBuilder = new $TypeData().initClass({
  sci_VectorBuilder: 0
}, false, "scala.collection.immutable.VectorBuilder", {
  sci_VectorBuilder: 1,
  O: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1,
  sci_VectorPointer: 1
});
$c_sci_VectorBuilder.prototype.$classData = $d_sci_VectorBuilder;
/** @constructor */
function $c_sci_VectorIterator(_startIndex, endIndex) {
  this.endIndex$2 = 0;
  this.blockIndex$2 = 0;
  this.lo$2 = 0;
  this.endLo$2 = 0;
  this.$$undhasNext$2 = false;
  this.depth$2 = 0;
  this.display0$2 = null;
  this.display1$2 = null;
  this.display2$2 = null;
  this.display3$2 = null;
  this.display4$2 = null;
  this.display5$2 = null;
  this.endIndex$2 = endIndex;
  this.blockIndex$2 = ((-32) & _startIndex);
  this.lo$2 = (31 & _startIndex);
  var x = ((endIndex - this.blockIndex$2) | 0);
  this.endLo$2 = ((x < 32) ? x : 32);
  this.$$undhasNext$2 = (((this.blockIndex$2 + this.lo$2) | 0) < endIndex)
}
$c_sci_VectorIterator.prototype = new $h_sc_AbstractIterator();
$c_sci_VectorIterator.prototype.constructor = $c_sci_VectorIterator;
/** @constructor */
function $h_sci_VectorIterator() {
  /*<skip>*/
}
$h_sci_VectorIterator.prototype = $c_sci_VectorIterator.prototype;
$c_sci_VectorIterator.prototype.remainingElementCount__I = (function() {
  var x = ((this.endIndex$2 - ((this.blockIndex$2 + this.lo$2) | 0)) | 0);
  return ((x > 0) ? x : 0)
});
$c_sci_VectorIterator.prototype.display3__AO = (function() {
  return this.display3$2
});
$c_sci_VectorIterator.prototype.next__O = (function() {
  if ((!this.$$undhasNext$2)) {
    throw new $c_ju_NoSuchElementException().init___T("reached iterator end")
  };
  var res = this.display0$2.get(this.lo$2);
  this.lo$2 = ((1 + this.lo$2) | 0);
  if ((this.lo$2 === this.endLo$2)) {
    if ((((this.blockIndex$2 + this.lo$2) | 0) < this.endIndex$2)) {
      var newBlockIndex = ((32 + this.blockIndex$2) | 0);
      var xor = (this.blockIndex$2 ^ newBlockIndex);
      $f_sci_VectorPointer__gotoNextBlockStart__I__I__V(this, newBlockIndex, xor);
      this.blockIndex$2 = newBlockIndex;
      var x = ((this.endIndex$2 - this.blockIndex$2) | 0);
      this.endLo$2 = ((x < 32) ? x : 32);
      this.lo$2 = 0
    } else {
      this.$$undhasNext$2 = false
    }
  };
  return res
});
$c_sci_VectorIterator.prototype.depth__I = (function() {
  return this.depth$2
});
$c_sci_VectorIterator.prototype.display5$und$eq__AO__V = (function(x$1) {
  this.display5$2 = x$1
});
$c_sci_VectorIterator.prototype.display0__AO = (function() {
  return this.display0$2
});
$c_sci_VectorIterator.prototype.display2$und$eq__AO__V = (function(x$1) {
  this.display2$2 = x$1
});
$c_sci_VectorIterator.prototype.display4__AO = (function() {
  return this.display4$2
});
$c_sci_VectorIterator.prototype.display1$und$eq__AO__V = (function(x$1) {
  this.display1$2 = x$1
});
$c_sci_VectorIterator.prototype.hasNext__Z = (function() {
  return this.$$undhasNext$2
});
$c_sci_VectorIterator.prototype.display4$und$eq__AO__V = (function(x$1) {
  this.display4$2 = x$1
});
$c_sci_VectorIterator.prototype.display1__AO = (function() {
  return this.display1$2
});
$c_sci_VectorIterator.prototype.display5__AO = (function() {
  return this.display5$2
});
$c_sci_VectorIterator.prototype.depth$und$eq__I__V = (function(x$1) {
  this.depth$2 = x$1
});
$c_sci_VectorIterator.prototype.display2__AO = (function() {
  return this.display2$2
});
$c_sci_VectorIterator.prototype.display0$und$eq__AO__V = (function(x$1) {
  this.display0$2 = x$1
});
$c_sci_VectorIterator.prototype.knownSize__I = (function() {
  return this.remainingElementCount__I()
});
$c_sci_VectorIterator.prototype.display3$und$eq__AO__V = (function(x$1) {
  this.display3$2 = x$1
});
var $d_sci_VectorIterator = new $TypeData().initClass({
  sci_VectorIterator: 0
}, false, "scala.collection.immutable.VectorIterator", {
  sci_VectorIterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1,
  sci_VectorPointer: 1
});
$c_sci_VectorIterator.prototype.$classData = $d_sci_VectorIterator;
/** @constructor */
function $c_scm_ArrayBuffer$() {
  /*<skip>*/
}
$c_scm_ArrayBuffer$.prototype = new $h_O();
$c_scm_ArrayBuffer$.prototype.constructor = $c_scm_ArrayBuffer$;
/** @constructor */
function $h_scm_ArrayBuffer$() {
  /*<skip>*/
}
$h_scm_ArrayBuffer$.prototype = $c_scm_ArrayBuffer$.prototype;
$c_scm_ArrayBuffer$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__scm_ArrayBuffer(source)
});
$c_scm_ArrayBuffer$.prototype.from__sc_IterableOnce__scm_ArrayBuffer = (function(coll) {
  if ((coll.knownSize__I() >= 0)) {
    var array = $newArrayObject($d_O.getArrayOf(), [coll.knownSize__I()]);
    var it = coll.iterator__sc_Iterator();
    var end = array.u.length;
    var isEmpty$4 = (end <= 0);
    var scala$collection$immutable$Range$$lastElement$f = (((-1) + end) | 0);
    if ((!isEmpty$4)) {
      var i = 0;
      while (true) {
        var v1 = i;
        array.set(v1, it.next__O());
        if ((i === scala$collection$immutable$Range$$lastElement$f)) {
          break
        };
        i = ((1 + i) | 0)
      }
    };
    return new $c_scm_ArrayBuffer().init___AO__I(array, array.u.length)
  } else {
    var this$6 = new $c_scm_ArrayBuffer().init___();
    return this$6.addAll__sc_IterableOnce__scm_ArrayBuffer(coll)
  }
});
$c_scm_ArrayBuffer$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_scm_ArrayBuffer$$anon$1()
});
var $d_scm_ArrayBuffer$ = new $TypeData().initClass({
  scm_ArrayBuffer$: 0
}, false, "scala.collection.mutable.ArrayBuffer$", {
  scm_ArrayBuffer$: 1,
  O: 1,
  sc_StrictOptimizedSeqFactory: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_scm_ArrayBuffer$.prototype.$classData = $d_scm_ArrayBuffer$;
var $n_scm_ArrayBuffer$ = (void 0);
function $m_scm_ArrayBuffer$() {
  if ((!$n_scm_ArrayBuffer$)) {
    $n_scm_ArrayBuffer$ = new $c_scm_ArrayBuffer$()
  };
  return $n_scm_ArrayBuffer$
}
/** @constructor */
function $c_scm_IndexedSeq$() {
  this.delegate$1 = null;
  $c_sc_SeqFactory$Delegate.prototype.init___sc_SeqFactory.call(this, $m_scm_ArrayBuffer$())
}
$c_scm_IndexedSeq$.prototype = new $h_sc_SeqFactory$Delegate();
$c_scm_IndexedSeq$.prototype.constructor = $c_scm_IndexedSeq$;
/** @constructor */
function $h_scm_IndexedSeq$() {
  /*<skip>*/
}
$h_scm_IndexedSeq$.prototype = $c_scm_IndexedSeq$.prototype;
var $d_scm_IndexedSeq$ = new $TypeData().initClass({
  scm_IndexedSeq$: 0
}, false, "scala.collection.mutable.IndexedSeq$", {
  scm_IndexedSeq$: 1,
  sc_SeqFactory$Delegate: 1,
  O: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_scm_IndexedSeq$.prototype.$classData = $d_scm_IndexedSeq$;
var $n_scm_IndexedSeq$ = (void 0);
function $m_scm_IndexedSeq$() {
  if ((!$n_scm_IndexedSeq$)) {
    $n_scm_IndexedSeq$ = new $c_scm_IndexedSeq$()
  };
  return $n_scm_IndexedSeq$
}
/** @constructor */
function $c_scm_ListBuffer$() {
  /*<skip>*/
}
$c_scm_ListBuffer$.prototype = new $h_O();
$c_scm_ListBuffer$.prototype.constructor = $c_scm_ListBuffer$;
/** @constructor */
function $h_scm_ListBuffer$() {
  /*<skip>*/
}
$h_scm_ListBuffer$.prototype = $c_scm_ListBuffer$.prototype;
$c_scm_ListBuffer$.prototype.from__sc_IterableOnce__O = (function(source) {
  var this$1 = new $c_scm_ListBuffer();
  return $as_scm_ListBuffer($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, source))
});
$c_scm_ListBuffer$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_scm_GrowableBuilder().init___scm_Growable(new $c_scm_ListBuffer())
});
var $d_scm_ListBuffer$ = new $TypeData().initClass({
  scm_ListBuffer$: 0
}, false, "scala.collection.mutable.ListBuffer$", {
  scm_ListBuffer$: 1,
  O: 1,
  sc_StrictOptimizedSeqFactory: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_scm_ListBuffer$.prototype.$classData = $d_scm_ListBuffer$;
var $n_scm_ListBuffer$ = (void 0);
function $m_scm_ListBuffer$() {
  if ((!$n_scm_ListBuffer$)) {
    $n_scm_ListBuffer$ = new $c_scm_ListBuffer$()
  };
  return $n_scm_ListBuffer$
}
/** @constructor */
function $c_sjs_js_WrappedArray$() {
  /*<skip>*/
}
$c_sjs_js_WrappedArray$.prototype = new $h_O();
$c_sjs_js_WrappedArray$.prototype.constructor = $c_sjs_js_WrappedArray$;
/** @constructor */
function $h_sjs_js_WrappedArray$() {
  /*<skip>*/
}
$h_sjs_js_WrappedArray$.prototype = $c_sjs_js_WrappedArray$.prototype;
$c_sjs_js_WrappedArray$.prototype.from__sc_IterableOnce__sjs_js_WrappedArray = (function(source) {
  var this$1 = new $c_sjs_js_WrappedArray().init___();
  return $as_sjs_js_WrappedArray($as_scm_Builder($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$1, source)).result__O())
});
$c_sjs_js_WrappedArray$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sjs_js_WrappedArray(source)
});
$c_sjs_js_WrappedArray$.prototype.newBuilder__scm_Builder = (function() {
  return new $c_sjs_js_WrappedArray().init___()
});
var $d_sjs_js_WrappedArray$ = new $TypeData().initClass({
  sjs_js_WrappedArray$: 0
}, false, "scala.scalajs.js.WrappedArray$", {
  sjs_js_WrappedArray$: 1,
  O: 1,
  sc_StrictOptimizedSeqFactory: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sjs_js_WrappedArray$.prototype.$classData = $d_sjs_js_WrappedArray$;
var $n_sjs_js_WrappedArray$ = (void 0);
function $m_sjs_js_WrappedArray$() {
  if ((!$n_sjs_js_WrappedArray$)) {
    $n_sjs_js_WrappedArray$ = new $c_sjs_js_WrappedArray$()
  };
  return $n_sjs_js_WrappedArray$
}
/** @constructor */
function $c_sjsr_WrappedVarArgs$() {
  /*<skip>*/
}
$c_sjsr_WrappedVarArgs$.prototype = new $h_O();
$c_sjsr_WrappedVarArgs$.prototype.constructor = $c_sjsr_WrappedVarArgs$;
/** @constructor */
function $h_sjsr_WrappedVarArgs$() {
  /*<skip>*/
}
$h_sjsr_WrappedVarArgs$.prototype = $c_sjsr_WrappedVarArgs$.prototype;
$c_sjsr_WrappedVarArgs$.prototype.from__sc_IterableOnce__sjsr_WrappedVarArgs = (function(source) {
  var this$1 = this.newBuilder__scm_Builder();
  return $as_sjsr_WrappedVarArgs($as_scm_Builder(this$1.addAll__sc_IterableOnce__scm_Growable(source)).result__O())
});
$c_sjsr_WrappedVarArgs$.prototype.from__sc_IterableOnce__O = (function(source) {
  return this.from__sc_IterableOnce__sjsr_WrappedVarArgs(source)
});
$c_sjsr_WrappedVarArgs$.prototype.newBuilder__scm_Builder = (function() {
  var array = [];
  var this$3 = new $c_sjs_js_WrappedArray().init___sjs_js_Array(array);
  var f = new $c_sjsr_AnonFunction1((function($this) {
    return (function(x$1$2) {
      var x$1 = $as_sjs_js_WrappedArray(x$1$2);
      return new $c_sjsr_WrappedVarArgs(x$1.array$5)
    })
  })(this));
  return new $c_scm_Builder$$anon$1(this$3, f)
});
var $d_sjsr_WrappedVarArgs$ = new $TypeData().initClass({
  sjsr_WrappedVarArgs$: 0
}, false, "scala.scalajs.runtime.WrappedVarArgs$", {
  sjsr_WrappedVarArgs$: 1,
  O: 1,
  sc_StrictOptimizedSeqFactory: 1,
  sc_SeqFactory: 1,
  sc_IterableFactory: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sjsr_WrappedVarArgs$.prototype.$classData = $d_sjsr_WrappedVarArgs$;
var $n_sjsr_WrappedVarArgs$ = (void 0);
function $m_sjsr_WrappedVarArgs$() {
  if ((!$n_sjsr_WrappedVarArgs$)) {
    $n_sjsr_WrappedVarArgs$ = new $c_sjsr_WrappedVarArgs$()
  };
  return $n_sjsr_WrappedVarArgs$
}
/** @constructor */
function $c_Ljava_io_PrintStream() {
  this.out$2 = null;
  this.encoder$3 = null;
  this.autoFlush$3 = false;
  this.charset$3 = null;
  this.closing$3 = false;
  this.java$io$PrintStream$$closed$3 = false;
  this.errorFlag$3 = false;
  this.bitmap$0$3 = false
}
$c_Ljava_io_PrintStream.prototype = new $h_Ljava_io_FilterOutputStream();
$c_Ljava_io_PrintStream.prototype.constructor = $c_Ljava_io_PrintStream;
/** @constructor */
function $h_Ljava_io_PrintStream() {
  /*<skip>*/
}
$h_Ljava_io_PrintStream.prototype = $c_Ljava_io_PrintStream.prototype;
$c_Ljava_io_PrintStream.prototype.init___Ljava_io_OutputStream__Z__Ljava_nio_charset_Charset = (function(_out, autoFlush, charset) {
  this.autoFlush$3 = autoFlush;
  this.charset$3 = charset;
  $c_Ljava_io_FilterOutputStream.prototype.init___Ljava_io_OutputStream.call(this, _out);
  this.closing$3 = false;
  this.java$io$PrintStream$$closed$3 = false;
  this.errorFlag$3 = false;
  return this
});
/** @constructor */
function $c_ju_Arrays$$anon$3(cmp$1) {
  this.cmp$1$1 = null;
  this.cmp$1$1 = cmp$1
}
$c_ju_Arrays$$anon$3.prototype = new $h_O();
$c_ju_Arrays$$anon$3.prototype.constructor = $c_ju_Arrays$$anon$3;
/** @constructor */
function $h_ju_Arrays$$anon$3() {
  /*<skip>*/
}
$h_ju_Arrays$$anon$3.prototype = $c_ju_Arrays$$anon$3.prototype;
$c_ju_Arrays$$anon$3.prototype.compare__O__O__I = (function(x, y) {
  return this.cmp$1$1.compare__O__O__I(x, y)
});
var $d_ju_Arrays$$anon$3 = new $TypeData().initClass({
  ju_Arrays$$anon$3: 0
}, false, "java.util.Arrays$$anon$3", {
  ju_Arrays$$anon$3: 1,
  O: 1,
  s_math_Ordering: 1,
  ju_Comparator: 1,
  s_math_PartialOrdering: 1,
  s_math_Equiv: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_ju_Arrays$$anon$3.prototype.$classData = $d_ju_Arrays$$anon$3;
/** @constructor */
function $c_s_math_Ordering$$anon$2($$outer, f$1) {
  this.$$outer$1 = null;
  this.f$1$1 = null;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$1 = $$outer
  };
  this.f$1$1 = f$1
}
$c_s_math_Ordering$$anon$2.prototype = new $h_O();
$c_s_math_Ordering$$anon$2.prototype.constructor = $c_s_math_Ordering$$anon$2;
/** @constructor */
function $h_s_math_Ordering$$anon$2() {
  /*<skip>*/
}
$h_s_math_Ordering$$anon$2.prototype = $c_s_math_Ordering$$anon$2.prototype;
$c_s_math_Ordering$$anon$2.prototype.compare__O__O__I = (function(x, y) {
  return this.$$outer$1.compare__O__O__I(this.f$1$1.apply__O__O(x), this.f$1$1.apply__O__O(y))
});
var $d_s_math_Ordering$$anon$2 = new $TypeData().initClass({
  s_math_Ordering$$anon$2: 0
}, false, "scala.math.Ordering$$anon$2", {
  s_math_Ordering$$anon$2: 1,
  O: 1,
  s_math_Ordering: 1,
  ju_Comparator: 1,
  s_math_PartialOrdering: 1,
  s_math_Equiv: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_math_Ordering$$anon$2.prototype.$classData = $d_s_math_Ordering$$anon$2;
/** @constructor */
function $c_s_reflect_ClassTag$GenericClassTag(runtimeClass) {
  this.runtimeClass$1 = null;
  this.runtimeClass$1 = runtimeClass
}
$c_s_reflect_ClassTag$GenericClassTag.prototype = new $h_O();
$c_s_reflect_ClassTag$GenericClassTag.prototype.constructor = $c_s_reflect_ClassTag$GenericClassTag;
/** @constructor */
function $h_s_reflect_ClassTag$GenericClassTag() {
  /*<skip>*/
}
$h_s_reflect_ClassTag$GenericClassTag.prototype = $c_s_reflect_ClassTag$GenericClassTag.prototype;
$c_s_reflect_ClassTag$GenericClassTag.prototype.newArray__I__O = (function(len) {
  return $m_jl_reflect_Array$().newInstance__jl_Class__I__O(this.runtimeClass$1, len)
});
$c_s_reflect_ClassTag$GenericClassTag.prototype.equals__O__Z = (function(x) {
  return $f_s_reflect_ClassTag__equals__O__Z(this, x)
});
$c_s_reflect_ClassTag$GenericClassTag.prototype.toString__T = (function() {
  var clazz = this.runtimeClass$1;
  return $f_s_reflect_ClassTag__prettyprint$1__ps_reflect_ClassTag__jl_Class__T(this, clazz)
});
$c_s_reflect_ClassTag$GenericClassTag.prototype.runtimeClass__jl_Class = (function() {
  return this.runtimeClass$1
});
$c_s_reflect_ClassTag$GenericClassTag.prototype.hashCode__I = (function() {
  return $m_sr_Statics$().anyHash__O__I(this.runtimeClass$1)
});
var $d_s_reflect_ClassTag$GenericClassTag = new $TypeData().initClass({
  s_reflect_ClassTag$GenericClassTag: 0
}, false, "scala.reflect.ClassTag$GenericClassTag", {
  s_reflect_ClassTag$GenericClassTag: 1,
  O: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ClassTag$GenericClassTag.prototype.$classData = $d_s_reflect_ClassTag$GenericClassTag;
/** @constructor */
function $c_sc_AbstractIterable() {
  /*<skip>*/
}
$c_sc_AbstractIterable.prototype = new $h_O();
$c_sc_AbstractIterable.prototype.constructor = $c_sc_AbstractIterable;
/** @constructor */
function $h_sc_AbstractIterable() {
  /*<skip>*/
}
$h_sc_AbstractIterable.prototype = $c_sc_AbstractIterable.prototype;
$c_sc_AbstractIterable.prototype.head__O = (function() {
  return this.iterator__sc_Iterator().next__O()
});
$c_sc_AbstractIterable.prototype.exists__F1__Z = (function(p) {
  return $f_sc_IterableOnceOps__exists__F1__Z(this, p)
});
$c_sc_AbstractIterable.prototype.isEmpty__Z = (function() {
  return $f_sc_IterableOnceOps__isEmpty__Z(this)
});
$c_sc_AbstractIterable.prototype.fromSpecific__sc_IterableOnce__O = (function(coll) {
  return this.fromSpecific__sc_IterableOnce__sc_Iterable(coll)
});
$c_sc_AbstractIterable.prototype.forall__F1__Z = (function(p) {
  return $f_sc_IterableOnceOps__forall__F1__Z(this, p)
});
$c_sc_AbstractIterable.prototype.foreach__F1__V = (function(f) {
  $f_sc_IterableOnceOps__foreach__F1__V(this, f)
});
$c_sc_AbstractIterable.prototype.flatMap__F1__O = (function(f) {
  return $f_sc_IterableOps__flatMap__F1__O(this, f)
});
$c_sc_AbstractIterable.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_IterableOnceOps__foldLeft__O__F2__O(this, z, op)
});
$c_sc_AbstractIterable.prototype.copyToArray__O__I__I = (function(xs, start) {
  return $f_sc_IterableOnceOps__copyToArray__O__I__I(this, xs, start)
});
$c_sc_AbstractIterable.prototype.filter__F1__O = (function(pred) {
  return $f_sc_IterableOps__filter__F1__O(this, pred)
});
$c_sc_AbstractIterable.prototype.newSpecificBuilder__scm_Builder = (function() {
  return this.iterableFactory__sc_IterableFactory().newBuilder__scm_Builder()
});
$c_sc_AbstractIterable.prototype.fromSpecific__sc_IterableOnce__sc_Iterable = (function(coll) {
  return $as_sc_Iterable(this.iterableFactory__sc_IterableFactory().from__sc_IterableOnce__O(coll))
});
$c_sc_AbstractIterable.prototype.size__I = (function() {
  return $f_sc_IterableOnceOps__size__I(this)
});
$c_sc_AbstractIterable.prototype.filterNot__F1__O = (function(pred) {
  return $f_sc_IterableOps__filterNot__F1__O(this, pred)
});
$c_sc_AbstractIterable.prototype.take__I__O = (function(n) {
  return $f_sc_IterableOps__take__I__O(this, n)
});
$c_sc_AbstractIterable.prototype.drop__I__O = (function(n) {
  return $f_sc_IterableOps__drop__I__O(this, n)
});
$c_sc_AbstractIterable.prototype.last__O = (function() {
  return $f_sc_IterableOps__last__O(this)
});
$c_sc_AbstractIterable.prototype.tail__O = (function() {
  return $f_sc_IterableOps__tail__O(this)
});
$c_sc_AbstractIterable.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(b, start, sep, end) {
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, b, start, sep, end)
});
$c_sc_AbstractIterable.prototype.map__F1__O = (function(f) {
  return $f_sc_IterableOps__map__F1__O(this, f)
});
$c_sc_AbstractIterable.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return $m_sci_Map$().from__sc_IterableOnce__sci_Map(this)
});
$c_sc_AbstractIterable.prototype.sum__s_math_Numeric__O = (function(num) {
  return $f_sc_IterableOnceOps__sum__s_math_Numeric__O(this, num)
});
$c_sc_AbstractIterable.prototype.toArray__s_reflect_ClassTag__O = (function(evidence$2) {
  return $f_sc_IterableOnceOps__toArray__s_reflect_ClassTag__O(this, evidence$2)
});
$c_sc_AbstractIterable.prototype.withFilter__F1__sc_WithFilter = (function(p) {
  return new $c_sc_IterableOps$WithFilter().init___sc_IterableOps__F1(this, p)
});
$c_sc_AbstractIterable.prototype.className__T = (function() {
  return this.stringPrefix__T()
});
$c_sc_AbstractIterable.prototype.knownSize__I = (function() {
  return (-1)
});
/** @constructor */
function $c_sc_IndexedSeqView$IndexedSeqViewIterator(self) {
  this.self$2 = null;
  this.current$2 = 0;
  this.self$2 = self;
  this.current$2 = 0
}
$c_sc_IndexedSeqView$IndexedSeqViewIterator.prototype = new $h_sc_AbstractIterator();
$c_sc_IndexedSeqView$IndexedSeqViewIterator.prototype.constructor = $c_sc_IndexedSeqView$IndexedSeqViewIterator;
/** @constructor */
function $h_sc_IndexedSeqView$IndexedSeqViewIterator() {
  /*<skip>*/
}
$h_sc_IndexedSeqView$IndexedSeqViewIterator.prototype = $c_sc_IndexedSeqView$IndexedSeqViewIterator.prototype;
$c_sc_IndexedSeqView$IndexedSeqViewIterator.prototype.next__O = (function() {
  if (this.hasNext__Z()) {
    var r = this.self$2.apply__I__O(this.current$2);
    this.current$2 = ((1 + this.current$2) | 0);
    return r
  } else {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  }
});
$c_sc_IndexedSeqView$IndexedSeqViewIterator.prototype.hasNext__Z = (function() {
  var jsx$1 = this.current$2;
  var this$1 = this.self$2;
  return (jsx$1 < this$1.length__I())
});
$c_sc_IndexedSeqView$IndexedSeqViewIterator.prototype.knownSize__I = (function() {
  var this$1 = this.self$2;
  return ((this$1.length__I() - this.current$2) | 0)
});
var $d_sc_IndexedSeqView$IndexedSeqViewIterator = new $TypeData().initClass({
  sc_IndexedSeqView$IndexedSeqViewIterator: 0
}, false, "scala.collection.IndexedSeqView$IndexedSeqViewIterator", {
  sc_IndexedSeqView$IndexedSeqViewIterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sc_IndexedSeqView$IndexedSeqViewIterator.prototype.$classData = $d_sc_IndexedSeqView$IndexedSeqViewIterator;
function $f_sc_StrictOptimizedLinearSeqOps__loop$2__psc_StrictOptimizedLinearSeqOps__I__sc_LinearSeq__sc_LinearSeq($thiz, n, s) {
  while (true) {
    if (((n <= 0) || s.isEmpty__Z())) {
      return s
    } else {
      var temp$n = (((-1) + n) | 0);
      var temp$s = $as_sc_LinearSeq(s.tail__O());
      n = temp$n;
      s = temp$s
    }
  }
}
/** @constructor */
function $c_sci_RangeIterator(start, step, lastElement, initiallyEmpty) {
  this.step$2 = 0;
  this.lastElement$2 = 0;
  this.$$undhasNext$2 = false;
  this.$$undnext$2 = 0;
  this.step$2 = step;
  this.lastElement$2 = lastElement;
  this.$$undhasNext$2 = (!initiallyEmpty);
  this.$$undnext$2 = start
}
$c_sci_RangeIterator.prototype = new $h_sc_AbstractIterator();
$c_sci_RangeIterator.prototype.constructor = $c_sci_RangeIterator;
/** @constructor */
function $h_sci_RangeIterator() {
  /*<skip>*/
}
$h_sci_RangeIterator.prototype = $c_sci_RangeIterator.prototype;
$c_sci_RangeIterator.prototype.next__O = (function() {
  return this.next__I()
});
$c_sci_RangeIterator.prototype.next__I = (function() {
  if ((!this.$$undhasNext$2)) {
    $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f.next__O()
  };
  var value = this.$$undnext$2;
  this.$$undhasNext$2 = (value !== this.lastElement$2);
  this.$$undnext$2 = ((value + this.step$2) | 0);
  return value
});
$c_sci_RangeIterator.prototype.hasNext__Z = (function() {
  return this.$$undhasNext$2
});
$c_sci_RangeIterator.prototype.knownSize__I = (function() {
  return (this.$$undhasNext$2 ? ((1 + ((((this.lastElement$2 - this.$$undnext$2) | 0) / this.step$2) | 0)) | 0) : 0)
});
var $d_sci_RangeIterator = new $TypeData().initClass({
  sci_RangeIterator: 0
}, false, "scala.collection.immutable.RangeIterator", {
  sci_RangeIterator: 1,
  sc_AbstractIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_sci_RangeIterator.prototype.$classData = $d_sci_RangeIterator;
/** @constructor */
function $c_jl_JSConsoleBasedPrintStream(isErr) {
  this.out$2 = null;
  this.encoder$3 = null;
  this.autoFlush$3 = false;
  this.charset$3 = null;
  this.closing$3 = false;
  this.java$io$PrintStream$$closed$3 = false;
  this.errorFlag$3 = false;
  this.bitmap$0$3 = false;
  this.isErr$4 = null;
  this.flushed$4 = false;
  this.buffer$4 = null;
  this.isErr$4 = isErr;
  var out = new $c_jl_JSConsoleBasedPrintStream$DummyOutputStream();
  $c_Ljava_io_PrintStream.prototype.init___Ljava_io_OutputStream__Z__Ljava_nio_charset_Charset.call(this, out, false, null);
  this.flushed$4 = true;
  this.buffer$4 = ""
}
$c_jl_JSConsoleBasedPrintStream.prototype = new $h_Ljava_io_PrintStream();
$c_jl_JSConsoleBasedPrintStream.prototype.constructor = $c_jl_JSConsoleBasedPrintStream;
/** @constructor */
function $h_jl_JSConsoleBasedPrintStream() {
  /*<skip>*/
}
$h_jl_JSConsoleBasedPrintStream.prototype = $c_jl_JSConsoleBasedPrintStream.prototype;
var $d_jl_JSConsoleBasedPrintStream = new $TypeData().initClass({
  jl_JSConsoleBasedPrintStream: 0
}, false, "java.lang.JSConsoleBasedPrintStream", {
  jl_JSConsoleBasedPrintStream: 1,
  Ljava_io_PrintStream: 1,
  Ljava_io_FilterOutputStream: 1,
  Ljava_io_OutputStream: 1,
  O: 1,
  Ljava_io_Closeable: 1,
  jl_AutoCloseable: 1,
  Ljava_io_Flushable: 1,
  jl_Appendable: 1
});
$c_jl_JSConsoleBasedPrintStream.prototype.$classData = $d_jl_JSConsoleBasedPrintStream;
function $f_s_math_Numeric$IntIsIntegral__plus__I__I__I($thiz, x, y) {
  return ((x + y) | 0)
}
/** @constructor */
function $c_s_math_Ordering$DeprecatedDoubleOrdering$() {
  /*<skip>*/
}
$c_s_math_Ordering$DeprecatedDoubleOrdering$.prototype = new $h_O();
$c_s_math_Ordering$DeprecatedDoubleOrdering$.prototype.constructor = $c_s_math_Ordering$DeprecatedDoubleOrdering$;
/** @constructor */
function $h_s_math_Ordering$DeprecatedDoubleOrdering$() {
  /*<skip>*/
}
$h_s_math_Ordering$DeprecatedDoubleOrdering$.prototype = $c_s_math_Ordering$DeprecatedDoubleOrdering$.prototype;
$c_s_math_Ordering$DeprecatedDoubleOrdering$.prototype.compare__O__O__I = (function(x, y) {
  var x$1 = $uD(x);
  var y$1 = $uD(y);
  return $m_jl_Double$().compare__D__D__I(x$1, y$1)
});
var $d_s_math_Ordering$DeprecatedDoubleOrdering$ = new $TypeData().initClass({
  s_math_Ordering$DeprecatedDoubleOrdering$: 0
}, false, "scala.math.Ordering$DeprecatedDoubleOrdering$", {
  s_math_Ordering$DeprecatedDoubleOrdering$: 1,
  O: 1,
  s_math_Ordering$Double$TotalOrdering: 1,
  s_math_Ordering: 1,
  ju_Comparator: 1,
  s_math_PartialOrdering: 1,
  s_math_Equiv: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1
});
$c_s_math_Ordering$DeprecatedDoubleOrdering$.prototype.$classData = $d_s_math_Ordering$DeprecatedDoubleOrdering$;
var $n_s_math_Ordering$DeprecatedDoubleOrdering$ = (void 0);
function $m_s_math_Ordering$DeprecatedDoubleOrdering$() {
  if ((!$n_s_math_Ordering$DeprecatedDoubleOrdering$)) {
    $n_s_math_Ordering$DeprecatedDoubleOrdering$ = new $c_s_math_Ordering$DeprecatedDoubleOrdering$()
  };
  return $n_s_math_Ordering$DeprecatedDoubleOrdering$
}
/** @constructor */
function $c_s_reflect_AnyValManifest() {
  this.toString$1 = null;
  this.hashCode$1 = 0
}
$c_s_reflect_AnyValManifest.prototype = new $h_O();
$c_s_reflect_AnyValManifest.prototype.constructor = $c_s_reflect_AnyValManifest;
/** @constructor */
function $h_s_reflect_AnyValManifest() {
  /*<skip>*/
}
$h_s_reflect_AnyValManifest.prototype = $c_s_reflect_AnyValManifest.prototype;
$c_s_reflect_AnyValManifest.prototype.equals__O__Z = (function(that) {
  return (this === that)
});
$c_s_reflect_AnyValManifest.prototype.toString__T = (function() {
  return this.toString$1
});
$c_s_reflect_AnyValManifest.prototype.hashCode__I = (function() {
  return this.hashCode$1
});
/** @constructor */
function $c_s_reflect_ManifestFactory$ClassTypeManifest() {
  this.prefix$1 = null;
  this.runtimeClass1$1 = null;
  this.typeArguments$1 = null
}
$c_s_reflect_ManifestFactory$ClassTypeManifest.prototype = new $h_O();
$c_s_reflect_ManifestFactory$ClassTypeManifest.prototype.constructor = $c_s_reflect_ManifestFactory$ClassTypeManifest;
/** @constructor */
function $h_s_reflect_ManifestFactory$ClassTypeManifest() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$ClassTypeManifest.prototype = $c_s_reflect_ManifestFactory$ClassTypeManifest.prototype;
/** @constructor */
function $c_sci_MapKeyValueTupleHashIterator(rootNode) {
  this.currentValueCursor$1 = 0;
  this.currentValueNode$1 = null;
  this.currentStackLevel$1 = 0;
  this.nodeIndex$1 = null;
  this.nodeStack$1 = null;
  this.scala$collection$immutable$MapKeyValueTupleHashIterator$$hash$f = 0;
  this.value$2 = null;
  this.key$2 = null;
  $c_sci_ChampBaseReverseIterator.prototype.init___sci_Node.call(this, rootNode);
  this.scala$collection$immutable$MapKeyValueTupleHashIterator$$hash$f = 0;
  this.key$2 = new $c_sci_MapKeyValueTupleHashIterator$$anon$1(this)
}
$c_sci_MapKeyValueTupleHashIterator.prototype = new $h_sci_ChampBaseReverseIterator();
$c_sci_MapKeyValueTupleHashIterator.prototype.constructor = $c_sci_MapKeyValueTupleHashIterator;
/** @constructor */
function $h_sci_MapKeyValueTupleHashIterator() {
  /*<skip>*/
}
$h_sci_MapKeyValueTupleHashIterator.prototype = $c_sci_MapKeyValueTupleHashIterator.prototype;
$c_sci_MapKeyValueTupleHashIterator.prototype.next__O = (function() {
  return this.next__sci_MapKeyValueTupleHashIterator()
});
$c_sci_MapKeyValueTupleHashIterator.prototype.productPrefix__T = (function() {
  return "Tuple2"
});
$c_sci_MapKeyValueTupleHashIterator.prototype.concat__F0__sc_Iterator = (function(xs) {
  return $f_sc_Iterator__concat__F0__sc_Iterator(this, xs)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.productArity__I = (function() {
  return 2
});
$c_sci_MapKeyValueTupleHashIterator.prototype.isEmpty__Z = (function() {
  return (!this.hasNext__Z())
});
$c_sci_MapKeyValueTupleHashIterator.prototype.productElement__I__O = (function(n) {
  return $f_s_Product2__productElement__I__O(this, n)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.toString__T = (function() {
  return "<iterator>"
});
$c_sci_MapKeyValueTupleHashIterator.prototype.sliceIterator__I__I__sc_Iterator = (function(from, until) {
  return $f_sc_Iterator__sliceIterator__I__I__sc_Iterator(this, from, until)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.foreach__F1__V = (function(f) {
  $f_sc_IterableOnceOps__foreach__F1__V(this, f)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_IterableOnceOps__foldLeft__O__F2__O(this, z, op)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.$$und2__O = (function() {
  return this.value$2
});
$c_sci_MapKeyValueTupleHashIterator.prototype.copyToArray__O__I__I = (function(xs, start) {
  return $f_sc_IterableOnceOps__copyToArray__O__I__I(this, xs, start)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.iterator__sc_Iterator = (function() {
  return this
});
$c_sci_MapKeyValueTupleHashIterator.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(b, start, sep, end) {
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, b, start, sep, end)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.hashCode__I = (function() {
  var this$1 = $m_s_util_hashing_MurmurHash3$();
  return this$1.productHash__s_Product__I__I(this, (-889275714))
});
$c_sci_MapKeyValueTupleHashIterator.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return $m_sci_Map$().from__sc_IterableOnce__sci_Map(this)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.sum__s_math_Numeric__O = (function(num) {
  return $f_sc_IterableOnceOps__sum__s_math_Numeric__O(this, num)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.$$und1__O = (function() {
  return this.key$2
});
$c_sci_MapKeyValueTupleHashIterator.prototype.next__sci_MapKeyValueTupleHashIterator = (function() {
  if ((!this.hasNext__Z())) {
    throw new $c_ju_NoSuchElementException().init___()
  };
  this.scala$collection$immutable$MapKeyValueTupleHashIterator$$hash$f = this.currentValueNode$1.getHash__I__I(this.currentValueCursor$1);
  this.value$2 = $as_sci_MapNode(this.currentValueNode$1).getValue__I__O(this.currentValueCursor$1);
  this.currentValueCursor$1 = (((-1) + this.currentValueCursor$1) | 0);
  return this
});
$c_sci_MapKeyValueTupleHashIterator.prototype.productIterator__sc_Iterator = (function() {
  return new $c_s_Product$$anon$1(this)
});
$c_sci_MapKeyValueTupleHashIterator.prototype.knownSize__I = (function() {
  return (-1)
});
var $d_sci_MapKeyValueTupleHashIterator = new $TypeData().initClass({
  sci_MapKeyValueTupleHashIterator: 0
}, false, "scala.collection.immutable.MapKeyValueTupleHashIterator", {
  sci_MapKeyValueTupleHashIterator: 1,
  sci_ChampBaseReverseIterator: 1,
  O: 1,
  sc_Iterator: 1,
  sc_IterableOnce: 1,
  sc_IterableOnceOps: 1,
  s_Product2: 1,
  s_Product: 1,
  s_Equals: 1
});
$c_sci_MapKeyValueTupleHashIterator.prototype.$classData = $d_sci_MapKeyValueTupleHashIterator;
/** @constructor */
function $c_sjs_js_JavaScriptException(exception) {
  this.s$1 = null;
  this.e$1 = null;
  this.enableSuppression$1 = false;
  this.writableStackTrace$1 = false;
  this.stackTraceStateInternal$1 = null;
  this.stackTrace$1 = null;
  this.suppressed$1 = null;
  this.exception$4 = null;
  this.exception$4 = exception;
  $c_jl_Throwable.prototype.init___T__jl_Throwable__Z__Z.call(this, null, null, true, true)
}
$c_sjs_js_JavaScriptException.prototype = new $h_jl_RuntimeException();
$c_sjs_js_JavaScriptException.prototype.constructor = $c_sjs_js_JavaScriptException;
/** @constructor */
function $h_sjs_js_JavaScriptException() {
  /*<skip>*/
}
$h_sjs_js_JavaScriptException.prototype = $c_sjs_js_JavaScriptException.prototype;
$c_sjs_js_JavaScriptException.prototype.productPrefix__T = (function() {
  return "JavaScriptException"
});
$c_sjs_js_JavaScriptException.prototype.productArity__I = (function() {
  return 1
});
$c_sjs_js_JavaScriptException.prototype.fillInStackTrace__jl_Throwable = (function() {
  this.setStackTraceStateInternal__O__(this.exception$4);
  return this
});
$c_sjs_js_JavaScriptException.prototype.equals__O__Z = (function(x$1) {
  if ((this === x$1)) {
    return true
  } else if ($is_sjs_js_JavaScriptException(x$1)) {
    var JavaScriptException$1 = $as_sjs_js_JavaScriptException(x$1);
    return $m_sr_BoxesRunTime$().equals__O__O__Z(this.exception$4, JavaScriptException$1.exception$4)
  } else {
    return false
  }
});
$c_sjs_js_JavaScriptException.prototype.productElement__I__O = (function(x$1) {
  if ((x$1 === 0)) {
    return this.exception$4
  } else {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
  }
});
$c_sjs_js_JavaScriptException.prototype.getMessage__T = (function() {
  return $dp_toString__T(this.exception$4)
});
$c_sjs_js_JavaScriptException.prototype.hashCode__I = (function() {
  var this$2 = $m_s_util_hashing_MurmurHash3$();
  return this$2.productHash__s_Product__I__I(this, (-889275714))
});
$c_sjs_js_JavaScriptException.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
$c_sjs_js_JavaScriptException.prototype.setStackTraceStateInternal__O__ = (function(e) {
  this.stackTraceStateInternal$1 = e
});
function $is_sjs_js_JavaScriptException(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sjs_js_JavaScriptException)))
}
function $as_sjs_js_JavaScriptException(obj) {
  return (($is_sjs_js_JavaScriptException(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.scalajs.js.JavaScriptException"))
}
function $isArrayOf_sjs_js_JavaScriptException(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sjs_js_JavaScriptException)))
}
function $asArrayOf_sjs_js_JavaScriptException(obj, depth) {
  return (($isArrayOf_sjs_js_JavaScriptException(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.scalajs.js.JavaScriptException;", depth))
}
var $d_sjs_js_JavaScriptException = new $TypeData().initClass({
  sjs_js_JavaScriptException: 0
}, false, "scala.scalajs.js.JavaScriptException", {
  sjs_js_JavaScriptException: 1,
  jl_RuntimeException: 1,
  jl_Exception: 1,
  jl_Throwable: 1,
  O: 1,
  Ljava_io_Serializable: 1,
  s_Product: 1,
  s_Equals: 1,
  s_Serializable: 1
});
$c_sjs_js_JavaScriptException.prototype.$classData = $d_sjs_js_JavaScriptException;
/** @constructor */
function $c_s_reflect_ManifestFactory$BooleanManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Boolean";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$BooleanManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$BooleanManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$BooleanManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$BooleanManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$BooleanManifest$.prototype = $c_s_reflect_ManifestFactory$BooleanManifest$.prototype;
$c_s_reflect_ManifestFactory$BooleanManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_Z.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$BooleanManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_Z.getClassOf()
});
var $d_s_reflect_ManifestFactory$BooleanManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$BooleanManifest$: 0
}, false, "scala.reflect.ManifestFactory$BooleanManifest$", {
  s_reflect_ManifestFactory$BooleanManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$BooleanManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$BooleanManifest$;
var $n_s_reflect_ManifestFactory$BooleanManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$BooleanManifest$() {
  if ((!$n_s_reflect_ManifestFactory$BooleanManifest$)) {
    $n_s_reflect_ManifestFactory$BooleanManifest$ = new $c_s_reflect_ManifestFactory$BooleanManifest$()
  };
  return $n_s_reflect_ManifestFactory$BooleanManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$ByteManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Byte";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$ByteManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$ByteManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$ByteManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$ByteManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$ByteManifest$.prototype = $c_s_reflect_ManifestFactory$ByteManifest$.prototype;
$c_s_reflect_ManifestFactory$ByteManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_B.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$ByteManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_B.getClassOf()
});
var $d_s_reflect_ManifestFactory$ByteManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$ByteManifest$: 0
}, false, "scala.reflect.ManifestFactory$ByteManifest$", {
  s_reflect_ManifestFactory$ByteManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$ByteManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$ByteManifest$;
var $n_s_reflect_ManifestFactory$ByteManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$ByteManifest$() {
  if ((!$n_s_reflect_ManifestFactory$ByteManifest$)) {
    $n_s_reflect_ManifestFactory$ByteManifest$ = new $c_s_reflect_ManifestFactory$ByteManifest$()
  };
  return $n_s_reflect_ManifestFactory$ByteManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$CharManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Char";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$CharManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$CharManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$CharManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$CharManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$CharManifest$.prototype = $c_s_reflect_ManifestFactory$CharManifest$.prototype;
$c_s_reflect_ManifestFactory$CharManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_C.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$CharManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_C.getClassOf()
});
var $d_s_reflect_ManifestFactory$CharManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$CharManifest$: 0
}, false, "scala.reflect.ManifestFactory$CharManifest$", {
  s_reflect_ManifestFactory$CharManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$CharManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$CharManifest$;
var $n_s_reflect_ManifestFactory$CharManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$CharManifest$() {
  if ((!$n_s_reflect_ManifestFactory$CharManifest$)) {
    $n_s_reflect_ManifestFactory$CharManifest$ = new $c_s_reflect_ManifestFactory$CharManifest$()
  };
  return $n_s_reflect_ManifestFactory$CharManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$DoubleManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Double";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$DoubleManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$DoubleManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$DoubleManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$DoubleManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$DoubleManifest$.prototype = $c_s_reflect_ManifestFactory$DoubleManifest$.prototype;
$c_s_reflect_ManifestFactory$DoubleManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_D.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$DoubleManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_D.getClassOf()
});
var $d_s_reflect_ManifestFactory$DoubleManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$DoubleManifest$: 0
}, false, "scala.reflect.ManifestFactory$DoubleManifest$", {
  s_reflect_ManifestFactory$DoubleManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$DoubleManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$DoubleManifest$;
var $n_s_reflect_ManifestFactory$DoubleManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$DoubleManifest$() {
  if ((!$n_s_reflect_ManifestFactory$DoubleManifest$)) {
    $n_s_reflect_ManifestFactory$DoubleManifest$ = new $c_s_reflect_ManifestFactory$DoubleManifest$()
  };
  return $n_s_reflect_ManifestFactory$DoubleManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$FloatManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Float";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$FloatManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$FloatManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$FloatManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$FloatManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$FloatManifest$.prototype = $c_s_reflect_ManifestFactory$FloatManifest$.prototype;
$c_s_reflect_ManifestFactory$FloatManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_F.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$FloatManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_F.getClassOf()
});
var $d_s_reflect_ManifestFactory$FloatManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$FloatManifest$: 0
}, false, "scala.reflect.ManifestFactory$FloatManifest$", {
  s_reflect_ManifestFactory$FloatManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$FloatManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$FloatManifest$;
var $n_s_reflect_ManifestFactory$FloatManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$FloatManifest$() {
  if ((!$n_s_reflect_ManifestFactory$FloatManifest$)) {
    $n_s_reflect_ManifestFactory$FloatManifest$ = new $c_s_reflect_ManifestFactory$FloatManifest$()
  };
  return $n_s_reflect_ManifestFactory$FloatManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$IntManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Int";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$IntManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$IntManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$IntManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$IntManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$IntManifest$.prototype = $c_s_reflect_ManifestFactory$IntManifest$.prototype;
$c_s_reflect_ManifestFactory$IntManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_I.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$IntManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_I.getClassOf()
});
var $d_s_reflect_ManifestFactory$IntManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$IntManifest$: 0
}, false, "scala.reflect.ManifestFactory$IntManifest$", {
  s_reflect_ManifestFactory$IntManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$IntManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$IntManifest$;
var $n_s_reflect_ManifestFactory$IntManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$IntManifest$() {
  if ((!$n_s_reflect_ManifestFactory$IntManifest$)) {
    $n_s_reflect_ManifestFactory$IntManifest$ = new $c_s_reflect_ManifestFactory$IntManifest$()
  };
  return $n_s_reflect_ManifestFactory$IntManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$LongManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Long";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$LongManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$LongManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$LongManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$LongManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$LongManifest$.prototype = $c_s_reflect_ManifestFactory$LongManifest$.prototype;
$c_s_reflect_ManifestFactory$LongManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_J.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$LongManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_J.getClassOf()
});
var $d_s_reflect_ManifestFactory$LongManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$LongManifest$: 0
}, false, "scala.reflect.ManifestFactory$LongManifest$", {
  s_reflect_ManifestFactory$LongManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$LongManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$LongManifest$;
var $n_s_reflect_ManifestFactory$LongManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$LongManifest$() {
  if ((!$n_s_reflect_ManifestFactory$LongManifest$)) {
    $n_s_reflect_ManifestFactory$LongManifest$ = new $c_s_reflect_ManifestFactory$LongManifest$()
  };
  return $n_s_reflect_ManifestFactory$LongManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$PhantomManifest() {
  this.prefix$1 = null;
  this.runtimeClass1$1 = null;
  this.typeArguments$1 = null;
  this.toString$2 = null;
  this.hashCode$2 = 0
}
$c_s_reflect_ManifestFactory$PhantomManifest.prototype = new $h_s_reflect_ManifestFactory$ClassTypeManifest();
$c_s_reflect_ManifestFactory$PhantomManifest.prototype.constructor = $c_s_reflect_ManifestFactory$PhantomManifest;
/** @constructor */
function $h_s_reflect_ManifestFactory$PhantomManifest() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$PhantomManifest.prototype = $c_s_reflect_ManifestFactory$PhantomManifest.prototype;
$c_s_reflect_ManifestFactory$PhantomManifest.prototype.equals__O__Z = (function(that) {
  return (this === that)
});
$c_s_reflect_ManifestFactory$PhantomManifest.prototype.toString__T = (function() {
  return this.toString$2
});
$c_s_reflect_ManifestFactory$PhantomManifest.prototype.hashCode__I = (function() {
  return this.hashCode$2
});
/** @constructor */
function $c_s_reflect_ManifestFactory$ShortManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Short";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$ShortManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$ShortManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$ShortManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$ShortManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$ShortManifest$.prototype = $c_s_reflect_ManifestFactory$ShortManifest$.prototype;
$c_s_reflect_ManifestFactory$ShortManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_S.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$ShortManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_S.getClassOf()
});
var $d_s_reflect_ManifestFactory$ShortManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$ShortManifest$: 0
}, false, "scala.reflect.ManifestFactory$ShortManifest$", {
  s_reflect_ManifestFactory$ShortManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$ShortManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$ShortManifest$;
var $n_s_reflect_ManifestFactory$ShortManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$ShortManifest$() {
  if ((!$n_s_reflect_ManifestFactory$ShortManifest$)) {
    $n_s_reflect_ManifestFactory$ShortManifest$ = new $c_s_reflect_ManifestFactory$ShortManifest$()
  };
  return $n_s_reflect_ManifestFactory$ShortManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$UnitManifest$() {
  this.toString$1 = null;
  this.hashCode$1 = 0;
  this.toString$1 = "Unit";
  this.hashCode$1 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$UnitManifest$.prototype = new $h_s_reflect_AnyValManifest();
$c_s_reflect_ManifestFactory$UnitManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$UnitManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$UnitManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$UnitManifest$.prototype = $c_s_reflect_ManifestFactory$UnitManifest$.prototype;
$c_s_reflect_ManifestFactory$UnitManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_sr_BoxedUnit.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$UnitManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_V.getClassOf()
});
var $d_s_reflect_ManifestFactory$UnitManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$UnitManifest$: 0
}, false, "scala.reflect.ManifestFactory$UnitManifest$", {
  s_reflect_ManifestFactory$UnitManifest$: 1,
  s_reflect_AnyValManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$UnitManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$UnitManifest$;
var $n_s_reflect_ManifestFactory$UnitManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$UnitManifest$() {
  if ((!$n_s_reflect_ManifestFactory$UnitManifest$)) {
    $n_s_reflect_ManifestFactory$UnitManifest$ = new $c_s_reflect_ManifestFactory$UnitManifest$()
  };
  return $n_s_reflect_ManifestFactory$UnitManifest$
}
/** @constructor */
function $c_sc_AbstractView() {
  /*<skip>*/
}
$c_sc_AbstractView.prototype = new $h_sc_AbstractIterable();
$c_sc_AbstractView.prototype.constructor = $c_sc_AbstractView;
/** @constructor */
function $h_sc_AbstractView() {
  /*<skip>*/
}
$h_sc_AbstractView.prototype = $c_sc_AbstractView.prototype;
$c_sc_AbstractView.prototype.toString__T = (function() {
  return $f_sc_View__toString__T(this)
});
$c_sc_AbstractView.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sc_View$()
});
$c_sc_AbstractView.prototype.stringPrefix__T = (function() {
  return "View"
});
function $f_sc_Set__equals__O__Z($thiz, that) {
  if ($is_sc_Set(that)) {
    var x2 = $as_sc_Set(that);
    return (($thiz === x2) || (($thiz.size__I() === x2.size__I()) && $thiz.subsetOf__sc_Set__Z(x2)))
  } else {
    return false
  }
}
function $is_sc_Set(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_Set)))
}
function $as_sc_Set(obj) {
  return (($is_sc_Set(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.Set"))
}
function $isArrayOf_sc_Set(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_Set)))
}
function $asArrayOf_sc_Set(obj, depth) {
  return (($isArrayOf_sc_Set(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.Set;", depth))
}
/** @constructor */
function $c_s_reflect_ManifestFactory$AnyManifest$() {
  this.prefix$1 = null;
  this.runtimeClass1$1 = null;
  this.typeArguments$1 = null;
  this.toString$2 = null;
  this.hashCode$2 = 0;
  this.toString$2 = "Any";
  var prefix = $m_s_None$();
  var typeArguments = $m_sci_Nil$();
  this.prefix$1 = prefix;
  this.runtimeClass1$1 = $d_O.getClassOf();
  this.typeArguments$1 = typeArguments;
  this.hashCode$2 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$AnyManifest$.prototype = new $h_s_reflect_ManifestFactory$PhantomManifest();
$c_s_reflect_ManifestFactory$AnyManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$AnyManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$AnyManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$AnyManifest$.prototype = $c_s_reflect_ManifestFactory$AnyManifest$.prototype;
$c_s_reflect_ManifestFactory$AnyManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_O.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$AnyManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_O.getClassOf()
});
var $d_s_reflect_ManifestFactory$AnyManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$AnyManifest$: 0
}, false, "scala.reflect.ManifestFactory$AnyManifest$", {
  s_reflect_ManifestFactory$AnyManifest$: 1,
  s_reflect_ManifestFactory$PhantomManifest: 1,
  s_reflect_ManifestFactory$ClassTypeManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$AnyManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$AnyManifest$;
var $n_s_reflect_ManifestFactory$AnyManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$AnyManifest$() {
  if ((!$n_s_reflect_ManifestFactory$AnyManifest$)) {
    $n_s_reflect_ManifestFactory$AnyManifest$ = new $c_s_reflect_ManifestFactory$AnyManifest$()
  };
  return $n_s_reflect_ManifestFactory$AnyManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$AnyValManifest$() {
  this.prefix$1 = null;
  this.runtimeClass1$1 = null;
  this.typeArguments$1 = null;
  this.toString$2 = null;
  this.hashCode$2 = 0;
  this.toString$2 = "AnyVal";
  var prefix = $m_s_None$();
  var typeArguments = $m_sci_Nil$();
  this.prefix$1 = prefix;
  this.runtimeClass1$1 = $d_O.getClassOf();
  this.typeArguments$1 = typeArguments;
  this.hashCode$2 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$AnyValManifest$.prototype = new $h_s_reflect_ManifestFactory$PhantomManifest();
$c_s_reflect_ManifestFactory$AnyValManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$AnyValManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$AnyValManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$AnyValManifest$.prototype = $c_s_reflect_ManifestFactory$AnyValManifest$.prototype;
$c_s_reflect_ManifestFactory$AnyValManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_O.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$AnyValManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_O.getClassOf()
});
var $d_s_reflect_ManifestFactory$AnyValManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$AnyValManifest$: 0
}, false, "scala.reflect.ManifestFactory$AnyValManifest$", {
  s_reflect_ManifestFactory$AnyValManifest$: 1,
  s_reflect_ManifestFactory$PhantomManifest: 1,
  s_reflect_ManifestFactory$ClassTypeManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$AnyValManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$AnyValManifest$;
var $n_s_reflect_ManifestFactory$AnyValManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$AnyValManifest$() {
  if ((!$n_s_reflect_ManifestFactory$AnyValManifest$)) {
    $n_s_reflect_ManifestFactory$AnyValManifest$ = new $c_s_reflect_ManifestFactory$AnyValManifest$()
  };
  return $n_s_reflect_ManifestFactory$AnyValManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$NothingManifest$() {
  this.prefix$1 = null;
  this.runtimeClass1$1 = null;
  this.typeArguments$1 = null;
  this.toString$2 = null;
  this.hashCode$2 = 0;
  this.toString$2 = "Nothing";
  var prefix = $m_s_None$();
  var typeArguments = $m_sci_Nil$();
  this.prefix$1 = prefix;
  this.runtimeClass1$1 = $d_sr_Nothing$.getClassOf();
  this.typeArguments$1 = typeArguments;
  this.hashCode$2 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$NothingManifest$.prototype = new $h_s_reflect_ManifestFactory$PhantomManifest();
$c_s_reflect_ManifestFactory$NothingManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$NothingManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$NothingManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$NothingManifest$.prototype = $c_s_reflect_ManifestFactory$NothingManifest$.prototype;
$c_s_reflect_ManifestFactory$NothingManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_O.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$NothingManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_sr_Nothing$.getClassOf()
});
var $d_s_reflect_ManifestFactory$NothingManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$NothingManifest$: 0
}, false, "scala.reflect.ManifestFactory$NothingManifest$", {
  s_reflect_ManifestFactory$NothingManifest$: 1,
  s_reflect_ManifestFactory$PhantomManifest: 1,
  s_reflect_ManifestFactory$ClassTypeManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$NothingManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$NothingManifest$;
var $n_s_reflect_ManifestFactory$NothingManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$NothingManifest$() {
  if ((!$n_s_reflect_ManifestFactory$NothingManifest$)) {
    $n_s_reflect_ManifestFactory$NothingManifest$ = new $c_s_reflect_ManifestFactory$NothingManifest$()
  };
  return $n_s_reflect_ManifestFactory$NothingManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$NullManifest$() {
  this.prefix$1 = null;
  this.runtimeClass1$1 = null;
  this.typeArguments$1 = null;
  this.toString$2 = null;
  this.hashCode$2 = 0;
  this.toString$2 = "Null";
  var prefix = $m_s_None$();
  var typeArguments = $m_sci_Nil$();
  this.prefix$1 = prefix;
  this.runtimeClass1$1 = $d_sr_Null$.getClassOf();
  this.typeArguments$1 = typeArguments;
  this.hashCode$2 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$NullManifest$.prototype = new $h_s_reflect_ManifestFactory$PhantomManifest();
$c_s_reflect_ManifestFactory$NullManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$NullManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$NullManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$NullManifest$.prototype = $c_s_reflect_ManifestFactory$NullManifest$.prototype;
$c_s_reflect_ManifestFactory$NullManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_O.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$NullManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_sr_Null$.getClassOf()
});
var $d_s_reflect_ManifestFactory$NullManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$NullManifest$: 0
}, false, "scala.reflect.ManifestFactory$NullManifest$", {
  s_reflect_ManifestFactory$NullManifest$: 1,
  s_reflect_ManifestFactory$PhantomManifest: 1,
  s_reflect_ManifestFactory$ClassTypeManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$NullManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$NullManifest$;
var $n_s_reflect_ManifestFactory$NullManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$NullManifest$() {
  if ((!$n_s_reflect_ManifestFactory$NullManifest$)) {
    $n_s_reflect_ManifestFactory$NullManifest$ = new $c_s_reflect_ManifestFactory$NullManifest$()
  };
  return $n_s_reflect_ManifestFactory$NullManifest$
}
/** @constructor */
function $c_s_reflect_ManifestFactory$ObjectManifest$() {
  this.prefix$1 = null;
  this.runtimeClass1$1 = null;
  this.typeArguments$1 = null;
  this.toString$2 = null;
  this.hashCode$2 = 0;
  this.toString$2 = "Object";
  var prefix = $m_s_None$();
  var typeArguments = $m_sci_Nil$();
  this.prefix$1 = prefix;
  this.runtimeClass1$1 = $d_O.getClassOf();
  this.typeArguments$1 = typeArguments;
  this.hashCode$2 = $systemIdentityHashCode(this)
}
$c_s_reflect_ManifestFactory$ObjectManifest$.prototype = new $h_s_reflect_ManifestFactory$PhantomManifest();
$c_s_reflect_ManifestFactory$ObjectManifest$.prototype.constructor = $c_s_reflect_ManifestFactory$ObjectManifest$;
/** @constructor */
function $h_s_reflect_ManifestFactory$ObjectManifest$() {
  /*<skip>*/
}
$h_s_reflect_ManifestFactory$ObjectManifest$.prototype = $c_s_reflect_ManifestFactory$ObjectManifest$.prototype;
$c_s_reflect_ManifestFactory$ObjectManifest$.prototype.newArray__I__O = (function(len) {
  return $newArrayObject($d_O.getArrayOf(), [len])
});
$c_s_reflect_ManifestFactory$ObjectManifest$.prototype.runtimeClass__jl_Class = (function() {
  return $d_O.getClassOf()
});
var $d_s_reflect_ManifestFactory$ObjectManifest$ = new $TypeData().initClass({
  s_reflect_ManifestFactory$ObjectManifest$: 0
}, false, "scala.reflect.ManifestFactory$ObjectManifest$", {
  s_reflect_ManifestFactory$ObjectManifest$: 1,
  s_reflect_ManifestFactory$PhantomManifest: 1,
  s_reflect_ManifestFactory$ClassTypeManifest: 1,
  O: 1,
  s_reflect_Manifest: 1,
  s_reflect_ClassTag: 1,
  s_reflect_ClassManifestDeprecatedApis: 1,
  s_reflect_OptManifest: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_Equals: 1
});
$c_s_reflect_ManifestFactory$ObjectManifest$.prototype.$classData = $d_s_reflect_ManifestFactory$ObjectManifest$;
var $n_s_reflect_ManifestFactory$ObjectManifest$ = (void 0);
function $m_s_reflect_ManifestFactory$ObjectManifest$() {
  if ((!$n_s_reflect_ManifestFactory$ObjectManifest$)) {
    $n_s_reflect_ManifestFactory$ObjectManifest$ = new $c_s_reflect_ManifestFactory$ObjectManifest$()
  };
  return $n_s_reflect_ManifestFactory$ObjectManifest$
}
function $f_sc_Map__equals__O__Z($thiz, o) {
  if ($is_sc_Map(o)) {
    var x2 = $as_sc_Map(o);
    return (($thiz === x2) || (($thiz.size__I() === x2.size__I()) && $f_sc_Map__liftedTree1$1__psc_Map__sc_Map__Z($thiz, x2)))
  } else {
    return false
  }
}
function $f_sc_Map__liftedTree1$1__psc_Map__sc_Map__Z($thiz, x2$1) {
  try {
    var res = true;
    var it = $thiz.iterator__sc_Iterator();
    while ((res && it.hasNext__Z())) {
      var arg1 = it.next__O();
      var x0$1 = $as_T2(arg1);
      if ((x0$1 === null)) {
        throw new $c_s_MatchError(x0$1)
      };
      var k = x0$1.$$und1$f;
      var v = x0$1.$$und2$f;
      res = $m_sr_BoxesRunTime$().equals__O__O__Z(x2$1.getOrElse__O__F0__O(k, new $c_sjsr_AnonFunction0((function($this) {
        return (function() {
          return $m_sc_Map$().scala$collection$Map$$DefaultSentinel$2
        })
      })($thiz))), v)
    };
    return res
  } catch (e) {
    if ($is_jl_ClassCastException(e)) {
      return false
    } else {
      throw e
    }
  }
}
function $is_sc_Map(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_Map)))
}
function $as_sc_Map(obj) {
  return (($is_sc_Map(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.Map"))
}
function $isArrayOf_sc_Map(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_Map)))
}
function $asArrayOf_sc_Map(obj, depth) {
  return (($isArrayOf_sc_Map(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.Map;", depth))
}
function $f_sc_Seq__equals__O__Z($thiz, o) {
  if (($thiz === o)) {
    return true
  } else if ($is_sc_Seq(o)) {
    var x2 = $as_sc_Seq(o);
    return $thiz.sameElements__sc_IterableOnce__Z(x2)
  } else {
    return false
  }
}
function $is_sc_Seq(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_Seq)))
}
function $as_sc_Seq(obj) {
  return (($is_sc_Seq(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.Seq"))
}
function $isArrayOf_sc_Seq(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_Seq)))
}
function $asArrayOf_sc_Seq(obj, depth) {
  return (($isArrayOf_sc_Seq(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.Seq;", depth))
}
/** @constructor */
function $c_sc_View$$anon$1(it$1) {
  this.it$1$3 = null;
  this.it$1$3 = it$1
}
$c_sc_View$$anon$1.prototype = new $h_sc_AbstractView();
$c_sc_View$$anon$1.prototype.constructor = $c_sc_View$$anon$1;
/** @constructor */
function $h_sc_View$$anon$1() {
  /*<skip>*/
}
$h_sc_View$$anon$1.prototype = $c_sc_View$$anon$1.prototype;
$c_sc_View$$anon$1.prototype.iterator__sc_Iterator = (function() {
  return $as_sc_Iterator(this.it$1$3.apply__O())
});
var $d_sc_View$$anon$1 = new $TypeData().initClass({
  sc_View$$anon$1: 0
}, false, "scala.collection.View$$anon$1", {
  sc_View$$anon$1: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1
});
$c_sc_View$$anon$1.prototype.$classData = $d_sc_View$$anon$1;
/** @constructor */
function $c_sc_View$Drop() {
  this.underlying$3 = null;
  this.n$3 = 0;
  this.normN$3 = 0
}
$c_sc_View$Drop.prototype = new $h_sc_AbstractView();
$c_sc_View$Drop.prototype.constructor = $c_sc_View$Drop;
/** @constructor */
function $h_sc_View$Drop() {
  /*<skip>*/
}
$h_sc_View$Drop.prototype = $c_sc_View$Drop.prototype;
$c_sc_View$Drop.prototype.isEmpty__Z = (function() {
  var this$1 = this.iterator__sc_Iterator();
  return (!this$1.hasNext__Z())
});
$c_sc_View$Drop.prototype.iterator__sc_Iterator = (function() {
  var this$1 = this.underlying$3.iterator__sc_Iterator();
  var n = this.n$3;
  return $f_sc_Iterator__drop__I__sc_Iterator(this$1, n)
});
$c_sc_View$Drop.prototype.init___sc_IterableOps__I = (function(underlying, n) {
  this.underlying$3 = underlying;
  this.n$3 = n;
  this.normN$3 = ((n > 0) ? n : 0);
  return this
});
$c_sc_View$Drop.prototype.knownSize__I = (function() {
  var size = this.underlying$3.knownSize__I();
  if ((size >= 0)) {
    var x = ((size - this.normN$3) | 0);
    return ((x > 0) ? x : 0)
  } else {
    return (-1)
  }
});
var $d_sc_View$Drop = new $TypeData().initClass({
  sc_View$Drop: 0
}, false, "scala.collection.View$Drop", {
  sc_View$Drop: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1
});
$c_sc_View$Drop.prototype.$classData = $d_sc_View$Drop;
/** @constructor */
function $c_sc_View$Fill(n, elem) {
  this.n$3 = 0;
  this.elem$3 = null;
  this.n$3 = n;
  this.elem$3 = elem
}
$c_sc_View$Fill.prototype = new $h_sc_AbstractView();
$c_sc_View$Fill.prototype.constructor = $c_sc_View$Fill;
/** @constructor */
function $h_sc_View$Fill() {
  /*<skip>*/
}
$h_sc_View$Fill.prototype = $c_sc_View$Fill.prototype;
$c_sc_View$Fill.prototype.isEmpty__Z = (function() {
  return (this.n$3 <= 0)
});
$c_sc_View$Fill.prototype.iterator__sc_Iterator = (function() {
  $m_sc_Iterator$();
  var len = this.n$3;
  var elem = this.elem$3;
  return new $c_sc_Iterator$$anon$21(len, elem)
});
$c_sc_View$Fill.prototype.knownSize__I = (function() {
  var that = this.n$3;
  return ((that < 0) ? 0 : that)
});
var $d_sc_View$Fill = new $TypeData().initClass({
  sc_View$Fill: 0
}, false, "scala.collection.View$Fill", {
  sc_View$Fill: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1
});
$c_sc_View$Fill.prototype.$classData = $d_sc_View$Fill;
/** @constructor */
function $c_sc_View$Filter(underlying, p, isFlipped) {
  this.underlying$3 = null;
  this.p$3 = null;
  this.isFlipped$3 = false;
  this.underlying$3 = underlying;
  this.p$3 = p;
  this.isFlipped$3 = isFlipped
}
$c_sc_View$Filter.prototype = new $h_sc_AbstractView();
$c_sc_View$Filter.prototype.constructor = $c_sc_View$Filter;
/** @constructor */
function $h_sc_View$Filter() {
  /*<skip>*/
}
$h_sc_View$Filter.prototype = $c_sc_View$Filter.prototype;
$c_sc_View$Filter.prototype.isEmpty__Z = (function() {
  var this$1 = this.iterator__sc_Iterator();
  return (!this$1.hasNext__Z())
});
$c_sc_View$Filter.prototype.iterator__sc_Iterator = (function() {
  var this$1 = this.underlying$3.iterator__sc_Iterator();
  var p = this.p$3;
  var isFlipped = this.isFlipped$3;
  return new $c_sc_Iterator$$anon$6(this$1, p, isFlipped)
});
$c_sc_View$Filter.prototype.knownSize__I = (function() {
  return ((this.underlying$3.knownSize__I() === 0) ? 0 : (-1))
});
var $d_sc_View$Filter = new $TypeData().initClass({
  sc_View$Filter: 0
}, false, "scala.collection.View$Filter", {
  sc_View$Filter: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1
});
$c_sc_View$Filter.prototype.$classData = $d_sc_View$Filter;
/** @constructor */
function $c_sc_View$FlatMap(underlying, f) {
  this.underlying$3 = null;
  this.f$3 = null;
  this.underlying$3 = underlying;
  this.f$3 = f
}
$c_sc_View$FlatMap.prototype = new $h_sc_AbstractView();
$c_sc_View$FlatMap.prototype.constructor = $c_sc_View$FlatMap;
/** @constructor */
function $h_sc_View$FlatMap() {
  /*<skip>*/
}
$h_sc_View$FlatMap.prototype = $c_sc_View$FlatMap.prototype;
$c_sc_View$FlatMap.prototype.isEmpty__Z = (function() {
  var this$1 = this.iterator__sc_Iterator();
  return (!this$1.hasNext__Z())
});
$c_sc_View$FlatMap.prototype.iterator__sc_Iterator = (function() {
  var this$1 = this.underlying$3.iterator__sc_Iterator();
  var f = this.f$3;
  return new $c_sc_Iterator$$anon$10(this$1, f)
});
$c_sc_View$FlatMap.prototype.knownSize__I = (function() {
  return ((this.underlying$3.knownSize__I() === 0) ? 0 : (-1))
});
var $d_sc_View$FlatMap = new $TypeData().initClass({
  sc_View$FlatMap: 0
}, false, "scala.collection.View$FlatMap", {
  sc_View$FlatMap: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1
});
$c_sc_View$FlatMap.prototype.$classData = $d_sc_View$FlatMap;
/** @constructor */
function $c_sc_View$Map() {
  this.underlying$3 = null;
  this.f$3 = null
}
$c_sc_View$Map.prototype = new $h_sc_AbstractView();
$c_sc_View$Map.prototype.constructor = $c_sc_View$Map;
/** @constructor */
function $h_sc_View$Map() {
  /*<skip>*/
}
$h_sc_View$Map.prototype = $c_sc_View$Map.prototype;
$c_sc_View$Map.prototype.isEmpty__Z = (function() {
  return this.underlying$3.isEmpty__Z()
});
$c_sc_View$Map.prototype.init___sc_IterableOps__F1 = (function(underlying, f) {
  this.underlying$3 = underlying;
  this.f$3 = f;
  return this
});
$c_sc_View$Map.prototype.iterator__sc_Iterator = (function() {
  var this$1 = this.underlying$3.iterator__sc_Iterator();
  var f = this.f$3;
  return new $c_sc_Iterator$$anon$9(this$1, f)
});
$c_sc_View$Map.prototype.knownSize__I = (function() {
  return this.underlying$3.knownSize__I()
});
var $d_sc_View$Map = new $TypeData().initClass({
  sc_View$Map: 0
}, false, "scala.collection.View$Map", {
  sc_View$Map: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1
});
$c_sc_View$Map.prototype.$classData = $d_sc_View$Map;
/** @constructor */
function $c_sc_View$Take() {
  this.underlying$3 = null;
  this.n$3 = 0;
  this.normN$3 = 0
}
$c_sc_View$Take.prototype = new $h_sc_AbstractView();
$c_sc_View$Take.prototype.constructor = $c_sc_View$Take;
/** @constructor */
function $h_sc_View$Take() {
  /*<skip>*/
}
$h_sc_View$Take.prototype = $c_sc_View$Take.prototype;
$c_sc_View$Take.prototype.isEmpty__Z = (function() {
  var this$1 = this.iterator__sc_Iterator();
  return (!this$1.hasNext__Z())
});
$c_sc_View$Take.prototype.iterator__sc_Iterator = (function() {
  var this$1 = this.underlying$3.iterator__sc_Iterator();
  var n = this.n$3;
  return $f_sc_Iterator__take__I__sc_Iterator(this$1, n)
});
$c_sc_View$Take.prototype.init___sc_IterableOps__I = (function(underlying, n) {
  this.underlying$3 = underlying;
  this.n$3 = n;
  this.normN$3 = ((n > 0) ? n : 0);
  return this
});
$c_sc_View$Take.prototype.knownSize__I = (function() {
  var size = this.underlying$3.knownSize__I();
  if ((size >= 0)) {
    var that = this.normN$3;
    return ((size < that) ? size : that)
  } else {
    return (-1)
  }
});
var $d_sc_View$Take = new $TypeData().initClass({
  sc_View$Take: 0
}, false, "scala.collection.View$Take", {
  sc_View$Take: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1
});
$c_sc_View$Take.prototype.$classData = $d_sc_View$Take;
/** @constructor */
function $c_s_math_Numeric$IntIsIntegral$() {
  /*<skip>*/
}
$c_s_math_Numeric$IntIsIntegral$.prototype = new $h_O();
$c_s_math_Numeric$IntIsIntegral$.prototype.constructor = $c_s_math_Numeric$IntIsIntegral$;
/** @constructor */
function $h_s_math_Numeric$IntIsIntegral$() {
  /*<skip>*/
}
$h_s_math_Numeric$IntIsIntegral$.prototype = $c_s_math_Numeric$IntIsIntegral$.prototype;
$c_s_math_Numeric$IntIsIntegral$.prototype.compare__O__O__I = (function(x, y) {
  var x$1 = $uI(x);
  var y$1 = $uI(y);
  return ((x$1 === y$1) ? 0 : ((x$1 < y$1) ? (-1) : 1))
});
var $d_s_math_Numeric$IntIsIntegral$ = new $TypeData().initClass({
  s_math_Numeric$IntIsIntegral$: 0
}, false, "scala.math.Numeric$IntIsIntegral$", {
  s_math_Numeric$IntIsIntegral$: 1,
  O: 1,
  s_math_Numeric$IntIsIntegral: 1,
  s_math_Integral: 1,
  s_math_Numeric: 1,
  s_math_Ordering: 1,
  ju_Comparator: 1,
  s_math_PartialOrdering: 1,
  s_math_Equiv: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  s_math_Ordering$IntOrdering: 1
});
$c_s_math_Numeric$IntIsIntegral$.prototype.$classData = $d_s_math_Numeric$IntIsIntegral$;
var $n_s_math_Numeric$IntIsIntegral$ = (void 0);
function $m_s_math_Numeric$IntIsIntegral$() {
  if ((!$n_s_math_Numeric$IntIsIntegral$)) {
    $n_s_math_Numeric$IntIsIntegral$ = new $c_s_math_Numeric$IntIsIntegral$()
  };
  return $n_s_math_Numeric$IntIsIntegral$
}
/** @constructor */
function $c_sc_AbstractSeqView() {
  /*<skip>*/
}
$c_sc_AbstractSeqView.prototype = new $h_sc_AbstractView();
$c_sc_AbstractSeqView.prototype.constructor = $c_sc_AbstractSeqView;
/** @constructor */
function $h_sc_AbstractSeqView() {
  /*<skip>*/
}
$h_sc_AbstractSeqView.prototype = $c_sc_AbstractSeqView.prototype;
$c_sc_AbstractSeqView.prototype.lengthCompare__I__I = (function(len) {
  return $f_sc_IterableOps__sizeCompare__I__I(this, len)
});
$c_sc_AbstractSeqView.prototype.isEmpty__Z = (function() {
  return $f_sc_SeqOps__isEmpty__Z(this)
});
$c_sc_AbstractSeqView.prototype.map__F1__sc_SeqView = (function(f) {
  return new $c_sc_SeqView$Map().init___sc_SeqOps__F1(this, f)
});
$c_sc_AbstractSeqView.prototype.take__I__sc_SeqView = (function(n) {
  return new $c_sc_SeqView$Take().init___sc_SeqOps__I(this, n)
});
$c_sc_AbstractSeqView.prototype.size__I = (function() {
  return this.length__I()
});
$c_sc_AbstractSeqView.prototype.take__I__O = (function(n) {
  return this.take__I__sc_SeqView(n)
});
$c_sc_AbstractSeqView.prototype.map__F1__O = (function(f) {
  return this.map__F1__sc_SeqView(f)
});
/** @constructor */
function $c_sc_AbstractSet() {
  /*<skip>*/
}
$c_sc_AbstractSet.prototype = new $h_sc_AbstractIterable();
$c_sc_AbstractSet.prototype.constructor = $c_sc_AbstractSet;
/** @constructor */
function $h_sc_AbstractSet() {
  /*<skip>*/
}
$h_sc_AbstractSet.prototype = $c_sc_AbstractSet.prototype;
$c_sc_AbstractSet.prototype.apply__O__O = (function(v1) {
  return this.contains__O__Z(v1)
});
$c_sc_AbstractSet.prototype.equals__O__Z = (function(that) {
  return $f_sc_Set__equals__O__Z(this, that)
});
$c_sc_AbstractSet.prototype.toString__T = (function() {
  return $f_sc_Iterable__toString__T(this)
});
$c_sc_AbstractSet.prototype.subsetOf__sc_Set__Z = (function(that) {
  return this.forall__F1__Z(that)
});
$c_sc_AbstractSet.prototype.hashCode__I = (function() {
  var this$1 = $m_s_util_hashing_MurmurHash3$();
  return this$1.unorderedHash__sc_IterableOnce__I__I(this, this$1.setSeed$2)
});
$c_sc_AbstractSet.prototype.stringPrefix__T = (function() {
  return "Set"
});
function $is_sc_LinearSeq(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_LinearSeq)))
}
function $as_sc_LinearSeq(obj) {
  return (($is_sc_LinearSeq(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.LinearSeq"))
}
function $isArrayOf_sc_LinearSeq(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_LinearSeq)))
}
function $asArrayOf_sc_LinearSeq(obj, depth) {
  return (($isArrayOf_sc_LinearSeq(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.LinearSeq;", depth))
}
function $is_sci_Set(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_Set)))
}
function $as_sci_Set(obj) {
  return (($is_sci_Set(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.Set"))
}
function $isArrayOf_sci_Set(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_Set)))
}
function $asArrayOf_sci_Set(obj, depth) {
  return (($isArrayOf_sci_Set(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.Set;", depth))
}
/** @constructor */
function $c_sc_AbstractMap() {
  /*<skip>*/
}
$c_sc_AbstractMap.prototype = new $h_sc_AbstractIterable();
$c_sc_AbstractMap.prototype.constructor = $c_sc_AbstractMap;
/** @constructor */
function $h_sc_AbstractMap() {
  /*<skip>*/
}
$h_sc_AbstractMap.prototype = $c_sc_AbstractMap.prototype;
$c_sc_AbstractMap.prototype.apply__O__O = (function(key) {
  return $f_sc_MapOps__apply__O__O(this, key)
});
$c_sc_AbstractMap.prototype.equals__O__Z = (function(o) {
  return $f_sc_Map__equals__O__Z(this, o)
});
$c_sc_AbstractMap.prototype.fromSpecific__sc_IterableOnce__O = (function(coll) {
  return $as_sc_Map(this.mapFactory__sc_MapFactory().from__sc_IterableOnce__O(coll))
});
$c_sc_AbstractMap.prototype.getOrElse__O__F0__O = (function(key, $default) {
  return $f_sc_MapOps__getOrElse__O__F0__O(this, key, $default)
});
$c_sc_AbstractMap.prototype.toString__T = (function() {
  return $f_sc_Iterable__toString__T(this)
});
$c_sc_AbstractMap.prototype.newSpecificBuilder__scm_Builder = (function() {
  return this.mapFactory__sc_MapFactory().newBuilder__scm_Builder()
});
$c_sc_AbstractMap.prototype.fromSpecific__sc_IterableOnce__sc_Iterable = (function(coll) {
  return $as_sc_Map(this.mapFactory__sc_MapFactory().from__sc_IterableOnce__O(coll))
});
$c_sc_AbstractMap.prototype.contains__O__Z = (function(key) {
  return $f_sc_MapOps__contains__O__Z(this, key)
});
$c_sc_AbstractMap.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(sb, start, sep, end) {
  return $f_sc_MapOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, sb, start, sep, end)
});
$c_sc_AbstractMap.prototype.hashCode__I = (function() {
  var this$1 = $m_s_util_hashing_MurmurHash3$();
  return this$1.unorderedHash__sc_IterableOnce__I__I(this, this$1.mapSeed$2)
});
$c_sc_AbstractMap.prototype.withFilter__F1__sc_WithFilter = (function(p) {
  return new $c_sc_MapOps$WithFilter(this, p)
});
$c_sc_AbstractMap.prototype.stringPrefix__T = (function() {
  return "Map"
});
/** @constructor */
function $c_sc_AbstractSeq() {
  /*<skip>*/
}
$c_sc_AbstractSeq.prototype = new $h_sc_AbstractIterable();
$c_sc_AbstractSeq.prototype.constructor = $c_sc_AbstractSeq;
/** @constructor */
function $h_sc_AbstractSeq() {
  /*<skip>*/
}
$h_sc_AbstractSeq.prototype = $c_sc_AbstractSeq.prototype;
$c_sc_AbstractSeq.prototype.lengthCompare__I__I = (function(len) {
  return $f_sc_IterableOps__sizeCompare__I__I(this, len)
});
$c_sc_AbstractSeq.prototype.isEmpty__Z = (function() {
  return $f_sc_SeqOps__isEmpty__Z(this)
});
$c_sc_AbstractSeq.prototype.sameElements__sc_IterableOnce__Z = (function(that) {
  return $f_sc_SeqOps__sameElements__sc_IterableOnce__Z(this, that)
});
$c_sc_AbstractSeq.prototype.equals__O__Z = (function(o) {
  return $f_sc_Seq__equals__O__Z(this, o)
});
$c_sc_AbstractSeq.prototype.toString__T = (function() {
  return $f_sc_Iterable__toString__T(this)
});
$c_sc_AbstractSeq.prototype.size__I = (function() {
  return this.length__I()
});
$c_sc_AbstractSeq.prototype.hashCode__I = (function() {
  return $m_s_util_hashing_MurmurHash3$().seqHash__sc_Seq__I(this)
});
/** @constructor */
function $c_sc_SeqView$Id() {
  this.underlying$4 = null
}
$c_sc_SeqView$Id.prototype = new $h_sc_AbstractSeqView();
$c_sc_SeqView$Id.prototype.constructor = $c_sc_SeqView$Id;
/** @constructor */
function $h_sc_SeqView$Id() {
  /*<skip>*/
}
$h_sc_SeqView$Id.prototype = $c_sc_SeqView$Id.prototype;
$c_sc_SeqView$Id.prototype.init___sc_SeqOps = (function(underlying) {
  this.underlying$4 = underlying;
  return this
});
$c_sc_SeqView$Id.prototype.apply__I__O = (function(idx) {
  return this.underlying$4.apply__I__O(idx)
});
$c_sc_SeqView$Id.prototype.iterator__sc_Iterator = (function() {
  return this.underlying$4.iterator__sc_Iterator()
});
$c_sc_SeqView$Id.prototype.length__I = (function() {
  return this.underlying$4.length__I()
});
$c_sc_SeqView$Id.prototype.knownSize__I = (function() {
  return this.underlying$4.knownSize__I()
});
var $d_sc_SeqView$Id = new $TypeData().initClass({
  sc_SeqView$Id: 0
}, false, "scala.collection.SeqView$Id", {
  sc_SeqView$Id: 1,
  sc_AbstractSeqView: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_SeqView: 1,
  sc_SeqOps: 1
});
$c_sc_SeqView$Id.prototype.$classData = $d_sc_SeqView$Id;
/** @constructor */
function $c_sc_SeqView$Map() {
  this.underlying$3 = null;
  this.f$3 = null;
  this.underlying$4 = null;
  this.f$4 = null
}
$c_sc_SeqView$Map.prototype = new $h_sc_View$Map();
$c_sc_SeqView$Map.prototype.constructor = $c_sc_SeqView$Map;
/** @constructor */
function $h_sc_SeqView$Map() {
  /*<skip>*/
}
$h_sc_SeqView$Map.prototype = $c_sc_SeqView$Map.prototype;
$c_sc_SeqView$Map.prototype.lengthCompare__I__I = (function(len) {
  return $f_sc_IterableOps__sizeCompare__I__I(this, len)
});
$c_sc_SeqView$Map.prototype.apply__I__O = (function(idx) {
  return this.f$4.apply__O__O(this.underlying$4.apply__I__O(idx))
});
$c_sc_SeqView$Map.prototype.isEmpty__Z = (function() {
  return $f_sc_SeqOps__isEmpty__Z(this)
});
$c_sc_SeqView$Map.prototype.map__F1__sc_SeqView = (function(f) {
  return new $c_sc_SeqView$Map().init___sc_SeqOps__F1(this, f)
});
$c_sc_SeqView$Map.prototype.take__I__sc_SeqView = (function(n) {
  return new $c_sc_SeqView$Take().init___sc_SeqOps__I(this, n)
});
$c_sc_SeqView$Map.prototype.size__I = (function() {
  return this.length__I()
});
$c_sc_SeqView$Map.prototype.length__I = (function() {
  return this.underlying$4.length__I()
});
$c_sc_SeqView$Map.prototype.take__I__O = (function(n) {
  return this.take__I__sc_SeqView(n)
});
$c_sc_SeqView$Map.prototype.init___sc_SeqOps__F1 = (function(underlying, f) {
  this.underlying$4 = underlying;
  this.f$4 = f;
  $c_sc_View$Map.prototype.init___sc_IterableOps__F1.call(this, underlying, f);
  return this
});
$c_sc_SeqView$Map.prototype.map__F1__O = (function(f) {
  return this.map__F1__sc_SeqView(f)
});
var $d_sc_SeqView$Map = new $TypeData().initClass({
  sc_SeqView$Map: 0
}, false, "scala.collection.SeqView$Map", {
  sc_SeqView$Map: 1,
  sc_View$Map: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_SeqView: 1,
  sc_SeqOps: 1
});
$c_sc_SeqView$Map.prototype.$classData = $d_sc_SeqView$Map;
/** @constructor */
function $c_sc_SeqView$Take() {
  this.underlying$3 = null;
  this.n$3 = 0;
  this.normN$3 = 0;
  this.underlying$4 = null;
  this.n$4 = 0
}
$c_sc_SeqView$Take.prototype = new $h_sc_View$Take();
$c_sc_SeqView$Take.prototype.constructor = $c_sc_SeqView$Take;
/** @constructor */
function $h_sc_SeqView$Take() {
  /*<skip>*/
}
$h_sc_SeqView$Take.prototype = $c_sc_SeqView$Take.prototype;
$c_sc_SeqView$Take.prototype.lengthCompare__I__I = (function(len) {
  return $f_sc_IterableOps__sizeCompare__I__I(this, len)
});
$c_sc_SeqView$Take.prototype.apply__I__O = (function(idx) {
  if ((idx < this.n$4)) {
    return this.underlying$4.apply__I__O(idx)
  } else {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + idx))
  }
});
$c_sc_SeqView$Take.prototype.init___sc_SeqOps__I = (function(underlying, n) {
  this.underlying$4 = underlying;
  this.n$4 = n;
  $c_sc_View$Take.prototype.init___sc_IterableOps__I.call(this, underlying, n);
  return this
});
$c_sc_SeqView$Take.prototype.isEmpty__Z = (function() {
  return $f_sc_SeqOps__isEmpty__Z(this)
});
$c_sc_SeqView$Take.prototype.map__F1__sc_SeqView = (function(f) {
  return new $c_sc_SeqView$Map().init___sc_SeqOps__F1(this, f)
});
$c_sc_SeqView$Take.prototype.take__I__sc_SeqView = (function(n) {
  return new $c_sc_SeqView$Take().init___sc_SeqOps__I(this, n)
});
$c_sc_SeqView$Take.prototype.size__I = (function() {
  return this.length__I()
});
$c_sc_SeqView$Take.prototype.length__I = (function() {
  var x = this.underlying$4.length__I();
  var that = this.normN$3;
  return ((x < that) ? x : that)
});
$c_sc_SeqView$Take.prototype.take__I__O = (function(n) {
  return this.take__I__sc_SeqView(n)
});
$c_sc_SeqView$Take.prototype.map__F1__O = (function(f) {
  return this.map__F1__sc_SeqView(f)
});
var $d_sc_SeqView$Take = new $TypeData().initClass({
  sc_SeqView$Take: 0
}, false, "scala.collection.SeqView$Take", {
  sc_SeqView$Take: 1,
  sc_View$Take: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_SeqView: 1,
  sc_SeqOps: 1
});
$c_sc_SeqView$Take.prototype.$classData = $d_sc_SeqView$Take;
function $is_sci_Map(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_Map)))
}
function $as_sci_Map(obj) {
  return (($is_sci_Map(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.Map"))
}
function $isArrayOf_sci_Map(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_Map)))
}
function $asArrayOf_sci_Map(obj, depth) {
  return (($isArrayOf_sci_Map(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.Map;", depth))
}
function $is_sci_Seq(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_Seq)))
}
function $as_sci_Seq(obj) {
  return (($is_sci_Seq(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.Seq"))
}
function $isArrayOf_sci_Seq(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_Seq)))
}
function $asArrayOf_sci_Seq(obj, depth) {
  return (($isArrayOf_sci_Seq(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.Seq;", depth))
}
/** @constructor */
function $c_sc_AbstractIndexedSeqView() {
  /*<skip>*/
}
$c_sc_AbstractIndexedSeqView.prototype = new $h_sc_AbstractSeqView();
$c_sc_AbstractIndexedSeqView.prototype.constructor = $c_sc_AbstractIndexedSeqView;
/** @constructor */
function $h_sc_AbstractIndexedSeqView() {
  /*<skip>*/
}
$h_sc_AbstractIndexedSeqView.prototype = $c_sc_AbstractIndexedSeqView.prototype;
$c_sc_AbstractIndexedSeqView.prototype.lengthCompare__I__I = (function(len) {
  var x = this.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sc_AbstractIndexedSeqView.prototype.map__F1__sc_SeqView = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_AbstractIndexedSeqView.prototype.take__I__sc_SeqView = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_AbstractIndexedSeqView.prototype.iterator__sc_Iterator = (function() {
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this)
});
$c_sc_AbstractIndexedSeqView.prototype.take__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_AbstractIndexedSeqView.prototype.drop__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Drop(this, n)
});
$c_sc_AbstractIndexedSeqView.prototype.map__F1__O = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_AbstractIndexedSeqView.prototype.knownSize__I = (function() {
  return this.length__I()
});
/** @constructor */
function $c_sc_IndexedSeqView$Drop(underlying, n) {
  this.underlying$3 = null;
  this.n$3 = 0;
  this.normN$3 = 0;
  this.underlying$4 = null;
  this.underlying$4 = underlying;
  $c_sc_View$Drop.prototype.init___sc_IterableOps__I.call(this, underlying, n)
}
$c_sc_IndexedSeqView$Drop.prototype = new $h_sc_View$Drop();
$c_sc_IndexedSeqView$Drop.prototype.constructor = $c_sc_IndexedSeqView$Drop;
/** @constructor */
function $h_sc_IndexedSeqView$Drop() {
  /*<skip>*/
}
$h_sc_IndexedSeqView$Drop.prototype = $c_sc_IndexedSeqView$Drop.prototype;
$c_sc_IndexedSeqView$Drop.prototype.apply__I__O = (function(i) {
  return this.underlying$4.apply__I__O(((i + this.normN$3) | 0))
});
$c_sc_IndexedSeqView$Drop.prototype.lengthCompare__I__I = (function(len) {
  var x = this.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sc_IndexedSeqView$Drop.prototype.isEmpty__Z = (function() {
  return $f_sc_SeqOps__isEmpty__Z(this)
});
$c_sc_IndexedSeqView$Drop.prototype.size__I = (function() {
  return this.length__I()
});
$c_sc_IndexedSeqView$Drop.prototype.iterator__sc_Iterator = (function() {
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this)
});
$c_sc_IndexedSeqView$Drop.prototype.length__I = (function() {
  var this$1 = this.underlying$4;
  var x = ((this$1.length__I() - this.normN$3) | 0);
  return ((x > 0) ? x : 0)
});
$c_sc_IndexedSeqView$Drop.prototype.take__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_IndexedSeqView$Drop.prototype.drop__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Drop(this, n)
});
$c_sc_IndexedSeqView$Drop.prototype.map__F1__O = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_IndexedSeqView$Drop.prototype.knownSize__I = (function() {
  return this.length__I()
});
var $d_sc_IndexedSeqView$Drop = new $TypeData().initClass({
  sc_IndexedSeqView$Drop: 0
}, false, "scala.collection.IndexedSeqView$Drop", {
  sc_IndexedSeqView$Drop: 1,
  sc_View$Drop: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_IndexedSeqView: 1,
  sc_IndexedSeqOps: 1,
  sc_SeqOps: 1,
  sc_SeqView: 1
});
$c_sc_IndexedSeqView$Drop.prototype.$classData = $d_sc_IndexedSeqView$Drop;
/** @constructor */
function $c_sc_IndexedSeqView$Id(underlying) {
  this.underlying$4 = null;
  $c_sc_SeqView$Id.prototype.init___sc_SeqOps.call(this, underlying)
}
$c_sc_IndexedSeqView$Id.prototype = new $h_sc_SeqView$Id();
$c_sc_IndexedSeqView$Id.prototype.constructor = $c_sc_IndexedSeqView$Id;
/** @constructor */
function $h_sc_IndexedSeqView$Id() {
  /*<skip>*/
}
$h_sc_IndexedSeqView$Id.prototype = $c_sc_IndexedSeqView$Id.prototype;
$c_sc_IndexedSeqView$Id.prototype.lengthCompare__I__I = (function(len) {
  var x = this.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sc_IndexedSeqView$Id.prototype.map__F1__sc_SeqView = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_IndexedSeqView$Id.prototype.take__I__sc_SeqView = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_IndexedSeqView$Id.prototype.iterator__sc_Iterator = (function() {
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this)
});
$c_sc_IndexedSeqView$Id.prototype.take__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_IndexedSeqView$Id.prototype.drop__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Drop(this, n)
});
$c_sc_IndexedSeqView$Id.prototype.map__F1__O = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_IndexedSeqView$Id.prototype.knownSize__I = (function() {
  return this.length__I()
});
var $d_sc_IndexedSeqView$Id = new $TypeData().initClass({
  sc_IndexedSeqView$Id: 0
}, false, "scala.collection.IndexedSeqView$Id", {
  sc_IndexedSeqView$Id: 1,
  sc_SeqView$Id: 1,
  sc_AbstractSeqView: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_SeqView: 1,
  sc_SeqOps: 1,
  sc_IndexedSeqView: 1,
  sc_IndexedSeqOps: 1
});
$c_sc_IndexedSeqView$Id.prototype.$classData = $d_sc_IndexedSeqView$Id;
/** @constructor */
function $c_sc_IndexedSeqView$Map(underlying, f) {
  this.underlying$3 = null;
  this.f$3 = null;
  this.underlying$4 = null;
  this.f$4 = null;
  $c_sc_SeqView$Map.prototype.init___sc_SeqOps__F1.call(this, underlying, f)
}
$c_sc_IndexedSeqView$Map.prototype = new $h_sc_SeqView$Map();
$c_sc_IndexedSeqView$Map.prototype.constructor = $c_sc_IndexedSeqView$Map;
/** @constructor */
function $h_sc_IndexedSeqView$Map() {
  /*<skip>*/
}
$h_sc_IndexedSeqView$Map.prototype = $c_sc_IndexedSeqView$Map.prototype;
$c_sc_IndexedSeqView$Map.prototype.lengthCompare__I__I = (function(len) {
  var x = this.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sc_IndexedSeqView$Map.prototype.map__F1__sc_SeqView = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_IndexedSeqView$Map.prototype.take__I__sc_SeqView = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_IndexedSeqView$Map.prototype.iterator__sc_Iterator = (function() {
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this)
});
$c_sc_IndexedSeqView$Map.prototype.take__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_IndexedSeqView$Map.prototype.drop__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Drop(this, n)
});
$c_sc_IndexedSeqView$Map.prototype.map__F1__O = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_IndexedSeqView$Map.prototype.knownSize__I = (function() {
  return this.length__I()
});
var $d_sc_IndexedSeqView$Map = new $TypeData().initClass({
  sc_IndexedSeqView$Map: 0
}, false, "scala.collection.IndexedSeqView$Map", {
  sc_IndexedSeqView$Map: 1,
  sc_SeqView$Map: 1,
  sc_View$Map: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_SeqView: 1,
  sc_SeqOps: 1,
  sc_IndexedSeqView: 1,
  sc_IndexedSeqOps: 1
});
$c_sc_IndexedSeqView$Map.prototype.$classData = $d_sc_IndexedSeqView$Map;
/** @constructor */
function $c_sc_IndexedSeqView$Take(underlying, n) {
  this.underlying$3 = null;
  this.n$3 = 0;
  this.normN$3 = 0;
  this.underlying$4 = null;
  this.n$4 = 0;
  $c_sc_SeqView$Take.prototype.init___sc_SeqOps__I.call(this, underlying, n)
}
$c_sc_IndexedSeqView$Take.prototype = new $h_sc_SeqView$Take();
$c_sc_IndexedSeqView$Take.prototype.constructor = $c_sc_IndexedSeqView$Take;
/** @constructor */
function $h_sc_IndexedSeqView$Take() {
  /*<skip>*/
}
$h_sc_IndexedSeqView$Take.prototype = $c_sc_IndexedSeqView$Take.prototype;
$c_sc_IndexedSeqView$Take.prototype.lengthCompare__I__I = (function(len) {
  var x = this.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sc_IndexedSeqView$Take.prototype.map__F1__sc_SeqView = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_IndexedSeqView$Take.prototype.take__I__sc_SeqView = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_IndexedSeqView$Take.prototype.iterator__sc_Iterator = (function() {
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this)
});
$c_sc_IndexedSeqView$Take.prototype.take__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Take(this, n)
});
$c_sc_IndexedSeqView$Take.prototype.drop__I__O = (function(n) {
  return new $c_sc_IndexedSeqView$Drop(this, n)
});
$c_sc_IndexedSeqView$Take.prototype.map__F1__O = (function(f) {
  return new $c_sc_IndexedSeqView$Map(this, f)
});
$c_sc_IndexedSeqView$Take.prototype.knownSize__I = (function() {
  return this.length__I()
});
var $d_sc_IndexedSeqView$Take = new $TypeData().initClass({
  sc_IndexedSeqView$Take: 0
}, false, "scala.collection.IndexedSeqView$Take", {
  sc_IndexedSeqView$Take: 1,
  sc_SeqView$Take: 1,
  sc_View$Take: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_SeqView: 1,
  sc_SeqOps: 1,
  sc_IndexedSeqView: 1,
  sc_IndexedSeqOps: 1
});
$c_sc_IndexedSeqView$Take.prototype.$classData = $d_sc_IndexedSeqView$Take;
/** @constructor */
function $c_sci_AbstractSet() {
  /*<skip>*/
}
$c_sci_AbstractSet.prototype = new $h_sc_AbstractSet();
$c_sci_AbstractSet.prototype.constructor = $c_sci_AbstractSet;
/** @constructor */
function $h_sci_AbstractSet() {
  /*<skip>*/
}
$h_sci_AbstractSet.prototype = $c_sci_AbstractSet.prototype;
$c_sci_AbstractSet.prototype.concat__sc_IterableOnce__sc_SetOps = (function(that) {
  return this.concat__sc_IterableOnce__sci_SetOps(that)
});
$c_sci_AbstractSet.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_Set$()
});
$c_sci_AbstractSet.prototype.concat__sc_IterableOnce__sci_SetOps = (function(that) {
  return $f_sci_SetOps__concat__sc_IterableOnce__sci_SetOps(this, that)
});
/** @constructor */
function $c_scm_ArrayBufferView(array, length) {
  this.array$5 = null;
  this.length$5 = 0;
  this.array$5 = array;
  this.length$5 = length
}
$c_scm_ArrayBufferView.prototype = new $h_sc_AbstractIndexedSeqView();
$c_scm_ArrayBufferView.prototype.constructor = $c_scm_ArrayBufferView;
/** @constructor */
function $h_scm_ArrayBufferView() {
  /*<skip>*/
}
$h_scm_ArrayBufferView.prototype = $c_scm_ArrayBufferView.prototype;
$c_scm_ArrayBufferView.prototype.apply__I__O = (function(n) {
  if ((n < this.length$5)) {
    return this.array$5.get(n)
  } else {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + n))
  }
});
$c_scm_ArrayBufferView.prototype.length__I = (function() {
  return this.length$5
});
$c_scm_ArrayBufferView.prototype.className__T = (function() {
  return "ArrayBufferView"
});
var $d_scm_ArrayBufferView = new $TypeData().initClass({
  scm_ArrayBufferView: 0
}, false, "scala.collection.mutable.ArrayBufferView", {
  scm_ArrayBufferView: 1,
  sc_AbstractIndexedSeqView: 1,
  sc_AbstractSeqView: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_SeqView: 1,
  sc_SeqOps: 1,
  sc_IndexedSeqView: 1,
  sc_IndexedSeqOps: 1
});
$c_scm_ArrayBufferView.prototype.$classData = $d_scm_ArrayBufferView;
/** @constructor */
function $c_sci_AbstractMap() {
  /*<skip>*/
}
$c_sci_AbstractMap.prototype = new $h_sc_AbstractMap();
$c_sci_AbstractMap.prototype.constructor = $c_sci_AbstractMap;
/** @constructor */
function $h_sci_AbstractMap() {
  /*<skip>*/
}
$h_sci_AbstractMap.prototype = $c_sci_AbstractMap.prototype;
$c_sci_AbstractMap.prototype.$$plus__T2__sci_MapOps = (function(kv) {
  return this.updated__O__O__sci_MapOps(kv.$$und1$f, kv.$$und2$f)
});
$c_sci_AbstractMap.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_Iterable$()
});
$c_sci_AbstractMap.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return this
});
$c_sci_AbstractMap.prototype.mapFactory__sc_MapFactory = (function() {
  return $m_sci_Map$()
});
/** @constructor */
function $c_sci_AbstractSeq() {
  /*<skip>*/
}
$c_sci_AbstractSeq.prototype = new $h_sc_AbstractSeq();
$c_sci_AbstractSeq.prototype.constructor = $c_sci_AbstractSeq;
/** @constructor */
function $h_sci_AbstractSeq() {
  /*<skip>*/
}
$h_sci_AbstractSeq.prototype = $c_sci_AbstractSeq.prototype;
function $is_sci_IndexedSeq(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_IndexedSeq)))
}
function $as_sci_IndexedSeq(obj) {
  return (($is_sci_IndexedSeq(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.IndexedSeq"))
}
function $isArrayOf_sci_IndexedSeq(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_IndexedSeq)))
}
function $asArrayOf_sci_IndexedSeq(obj, depth) {
  return (($isArrayOf_sci_IndexedSeq(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.IndexedSeq;", depth))
}
/** @constructor */
function $c_sci_Set$EmptySet$() {
  /*<skip>*/
}
$c_sci_Set$EmptySet$.prototype = new $h_sci_AbstractSet();
$c_sci_Set$EmptySet$.prototype.constructor = $c_sci_Set$EmptySet$;
/** @constructor */
function $h_sci_Set$EmptySet$() {
  /*<skip>*/
}
$h_sci_Set$EmptySet$.prototype = $c_sci_Set$EmptySet$.prototype;
$c_sci_Set$EmptySet$.prototype.isEmpty__Z = (function() {
  return true
});
$c_sci_Set$EmptySet$.prototype.foreach__F1__V = (function(f) {
  /*<skip>*/
});
$c_sci_Set$EmptySet$.prototype.size__I = (function() {
  return 0
});
$c_sci_Set$EmptySet$.prototype.iterator__sc_Iterator = (function() {
  return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
});
$c_sci_Set$EmptySet$.prototype.contains__O__Z = (function(elem) {
  return false
});
$c_sci_Set$EmptySet$.prototype.incl__O__sci_SetOps = (function(elem) {
  return new $c_sci_Set$Set1(elem)
});
$c_sci_Set$EmptySet$.prototype.excl__O__sci_SetOps = (function(elem) {
  return this
});
$c_sci_Set$EmptySet$.prototype.knownSize__I = (function() {
  return 0
});
var $d_sci_Set$EmptySet$ = new $TypeData().initClass({
  sci_Set$EmptySet$: 0
}, false, "scala.collection.immutable.Set$EmptySet$", {
  sci_Set$EmptySet$: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1
});
$c_sci_Set$EmptySet$.prototype.$classData = $d_sci_Set$EmptySet$;
var $n_sci_Set$EmptySet$ = (void 0);
function $m_sci_Set$EmptySet$() {
  if ((!$n_sci_Set$EmptySet$)) {
    $n_sci_Set$EmptySet$ = new $c_sci_Set$EmptySet$()
  };
  return $n_sci_Set$EmptySet$
}
function $is_sci_SortedSet(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_SortedSet)))
}
function $as_sci_SortedSet(obj) {
  return (($is_sci_SortedSet(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.SortedSet"))
}
function $isArrayOf_sci_SortedSet(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_SortedSet)))
}
function $asArrayOf_sci_SortedSet(obj, depth) {
  return (($isArrayOf_sci_SortedSet(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.SortedSet;", depth))
}
/** @constructor */
function $c_sc_StringView(s) {
  this.s$5 = null;
  this.s$5 = s
}
$c_sc_StringView.prototype = new $h_sc_AbstractIndexedSeqView();
$c_sc_StringView.prototype.constructor = $c_sc_StringView;
/** @constructor */
function $h_sc_StringView() {
  /*<skip>*/
}
$h_sc_StringView.prototype = $c_sc_StringView.prototype;
$c_sc_StringView.prototype.productPrefix__T = (function() {
  return "StringView"
});
$c_sc_StringView.prototype.apply__I__O = (function(i) {
  var this$1 = this.s$5;
  return $bC((65535 & $uI(this$1.charCodeAt(i))))
});
$c_sc_StringView.prototype.productArity__I = (function() {
  return 1
});
$c_sc_StringView.prototype.equals__O__Z = (function(x$1) {
  if ((this === x$1)) {
    return true
  } else if ($is_sc_StringView(x$1)) {
    var StringView$1 = $as_sc_StringView(x$1);
    return (this.s$5 === StringView$1.s$5)
  } else {
    return false
  }
});
$c_sc_StringView.prototype.productElement__I__O = (function(x$1) {
  if ((x$1 === 0)) {
    return this.s$5
  } else {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
  }
});
$c_sc_StringView.prototype.length__I = (function() {
  var this$1 = this.s$5;
  return $uI(this$1.length)
});
$c_sc_StringView.prototype.hashCode__I = (function() {
  var this$2 = $m_s_util_hashing_MurmurHash3$();
  return this$2.productHash__s_Product__I__I(this, (-889275714))
});
$c_sc_StringView.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
$c_sc_StringView.prototype.className__T = (function() {
  return "StringView"
});
function $is_sc_StringView(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sc_StringView)))
}
function $as_sc_StringView(obj) {
  return (($is_sc_StringView(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.StringView"))
}
function $isArrayOf_sc_StringView(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sc_StringView)))
}
function $asArrayOf_sc_StringView(obj, depth) {
  return (($isArrayOf_sc_StringView(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.StringView;", depth))
}
var $d_sc_StringView = new $TypeData().initClass({
  sc_StringView: 0
}, false, "scala.collection.StringView", {
  sc_StringView: 1,
  sc_AbstractIndexedSeqView: 1,
  sc_AbstractSeqView: 1,
  sc_AbstractView: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_View: 1,
  sc_SeqView: 1,
  sc_SeqOps: 1,
  sc_IndexedSeqView: 1,
  sc_IndexedSeqOps: 1,
  s_Product: 1,
  s_Equals: 1
});
$c_sc_StringView.prototype.$classData = $d_sc_StringView;
/** @constructor */
function $c_sci_HashSet(rootNode, cachedJavaHashCode) {
  this.rootNode$4 = null;
  this.cachedJavaHashCode$4 = 0;
  this.rootNode$4 = rootNode;
  this.cachedJavaHashCode$4 = cachedJavaHashCode
}
$c_sci_HashSet.prototype = new $h_sci_AbstractSet();
$c_sci_HashSet.prototype.constructor = $c_sci_HashSet;
/** @constructor */
function $h_sci_HashSet() {
  /*<skip>*/
}
$h_sci_HashSet.prototype = $c_sci_HashSet.prototype;
$c_sci_HashSet.prototype.head__O = (function() {
  return this.iterator__sc_Iterator().next__O()
});
$c_sci_HashSet.prototype.incl__O__sci_HashSet = (function(element) {
  var elementUnimprovedHash = $m_sr_Statics$().anyHash__O__I(element);
  var elementHash = $m_sc_Hashing$().improve__I__I(elementUnimprovedHash);
  var newRootNode = this.rootNode$4.updated__O__I__I__I__sci_SetNode(element, elementUnimprovedHash, elementHash, 0);
  if ((newRootNode !== this.rootNode$4)) {
    var newCachedJavaHashCode = ((this.cachedJavaHashCode$4 + ((newRootNode.size__I() === this.rootNode$4.size__I()) ? 0 : elementHash)) | 0);
    $m_sci_HashSet$();
    return new $c_sci_HashSet(newRootNode, newCachedJavaHashCode)
  } else {
    return this
  }
});
$c_sci_HashSet.prototype.isEmpty__Z = (function() {
  return (this.rootNode$4.size__I() === 0)
});
$c_sci_HashSet.prototype.equals__O__Z = (function(that) {
  if ($is_sci_HashSet(that)) {
    var x2 = $as_sci_HashSet(that);
    if ((this === x2)) {
      return true
    } else if (((this.rootNode$4.size__I() === x2.rootNode$4.size__I()) && (this.cachedJavaHashCode$4 === x2.cachedJavaHashCode$4))) {
      var x = this.rootNode$4;
      var x$2 = x2.rootNode$4;
      return ((x === null) ? (x$2 === null) : x.equals__O__Z(x$2))
    } else {
      return false
    }
  } else {
    return $f_sc_Set__equals__O__Z(this, that)
  }
});
$c_sci_HashSet.prototype.foreach__F1__V = (function(f) {
  this.rootNode$4.foreach__F1__V(f)
});
$c_sci_HashSet.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sci_HashSet.prototype.size__I = (function() {
  return this.rootNode$4.size__I()
});
$c_sci_HashSet.prototype.iterator__sc_Iterator = (function() {
  return (this.isEmpty__Z() ? $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f : new $c_sci_SetIterator(this.rootNode$4))
});
$c_sci_HashSet.prototype.excl__O__sci_HashSet = (function(element) {
  var elementUnimprovedHash = $m_sr_Statics$().anyHash__O__I(element);
  var elementHash = $m_sc_Hashing$().improve__I__I(elementUnimprovedHash);
  var newRootNode = this.rootNode$4.removed__O__I__I__I__sci_SetNode(element, elementUnimprovedHash, elementHash, 0);
  if ((this.rootNode$4 !== newRootNode)) {
    $m_sci_HashSet$();
    var cachedJavaHashCode = ((this.cachedJavaHashCode$4 - elementHash) | 0);
    return new $c_sci_HashSet(newRootNode, cachedJavaHashCode)
  } else {
    return this
  }
});
$c_sci_HashSet.prototype.filterNot__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, true)
});
$c_sci_HashSet.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_HashSet$()
});
$c_sci_HashSet.prototype.contains__O__Z = (function(element) {
  var elementUnimprovedHash = $m_sr_Statics$().anyHash__O__I(element);
  var elementHash = $m_sc_Hashing$().improve__I__I(elementUnimprovedHash);
  return this.rootNode$4.contains__O__I__I__I__Z(element, elementUnimprovedHash, elementHash, 0)
});
$c_sci_HashSet.prototype.tail__O = (function() {
  var elem = this.iterator__sc_Iterator().next__O();
  return this.excl__O__sci_HashSet(elem)
});
$c_sci_HashSet.prototype.incl__O__sci_SetOps = (function(elem) {
  return this.incl__O__sci_HashSet(elem)
});
$c_sci_HashSet.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_HashSet.prototype.hashCode__I = (function() {
  var it = new $c_sci_SetHashIterator(this.rootNode$4);
  var hash = $m_s_util_hashing_MurmurHash3$().unorderedHash__sc_IterableOnce__I__I(it, $m_s_util_hashing_MurmurHash3$().setSeed$2);
  return hash
});
$c_sci_HashSet.prototype.excl__O__sci_SetOps = (function(elem) {
  return this.excl__O__sci_HashSet(elem)
});
$c_sci_HashSet.prototype.className__T = (function() {
  return "HashSet"
});
$c_sci_HashSet.prototype.knownSize__I = (function() {
  return this.rootNode$4.size__I()
});
function $is_sci_HashSet(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_HashSet)))
}
function $as_sci_HashSet(obj) {
  return (($is_sci_HashSet(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.HashSet"))
}
function $isArrayOf_sci_HashSet(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_HashSet)))
}
function $asArrayOf_sci_HashSet(obj, depth) {
  return (($isArrayOf_sci_HashSet(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.HashSet;", depth))
}
var $d_sci_HashSet = new $TypeData().initClass({
  sci_HashSet: 0
}, false, "scala.collection.immutable.HashSet", {
  sci_HashSet: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_HashSet.prototype.$classData = $d_sci_HashSet;
/** @constructor */
function $c_sci_ListSet() {
  /*<skip>*/
}
$c_sci_ListSet.prototype = new $h_sci_AbstractSet();
$c_sci_ListSet.prototype.constructor = $c_sci_ListSet;
/** @constructor */
function $h_sci_ListSet() {
  /*<skip>*/
}
$h_sci_ListSet.prototype = $c_sci_ListSet.prototype;
$c_sci_ListSet.prototype.next__sci_ListSet = (function() {
  throw new $c_ju_NoSuchElementException().init___T("next of empty set")
});
$c_sci_ListSet.prototype.isEmpty__Z = (function() {
  return true
});
$c_sci_ListSet.prototype.incl__O__sci_ListSet = (function(elem) {
  return new $c_sci_ListSet$Node(this, elem)
});
$c_sci_ListSet.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sci_ListSet.prototype.size__I = (function() {
  return 0
});
$c_sci_ListSet.prototype.iterator__sc_Iterator = (function() {
  var curr = this;
  var res = $m_sci_Nil$();
  while ((!curr.isEmpty__Z())) {
    var rassoc$1 = curr.elem__O();
    var this$1 = res;
    res = new $c_sci_$colon$colon(rassoc$1, this$1);
    curr = curr.next__sci_ListSet()
  };
  return res.iterator__sc_Iterator()
});
$c_sci_ListSet.prototype.filterNot__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, true)
});
$c_sci_ListSet.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_ListSet$()
});
$c_sci_ListSet.prototype.excl__O__sci_ListSet = (function(elem) {
  return this
});
$c_sci_ListSet.prototype.elem__O = (function() {
  throw new $c_ju_NoSuchElementException().init___T("elem of empty set")
});
$c_sci_ListSet.prototype.contains__O__Z = (function(elem) {
  return false
});
$c_sci_ListSet.prototype.incl__O__sci_SetOps = (function(elem) {
  return this.incl__O__sci_ListSet(elem)
});
$c_sci_ListSet.prototype.excl__O__sci_SetOps = (function(elem) {
  return this.excl__O__sci_ListSet(elem)
});
$c_sci_ListSet.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_ListSet.prototype.className__T = (function() {
  return "ListSet"
});
function $is_sci_ListSet(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_ListSet)))
}
function $as_sci_ListSet(obj) {
  return (($is_sci_ListSet(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.ListSet"))
}
function $isArrayOf_sci_ListSet(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_ListSet)))
}
function $asArrayOf_sci_ListSet(obj, depth) {
  return (($isArrayOf_sci_ListSet(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.ListSet;", depth))
}
/** @constructor */
function $c_sci_Map$EmptyMap$() {
  /*<skip>*/
}
$c_sci_Map$EmptyMap$.prototype = new $h_sci_AbstractMap();
$c_sci_Map$EmptyMap$.prototype.constructor = $c_sci_Map$EmptyMap$;
/** @constructor */
function $h_sci_Map$EmptyMap$() {
  /*<skip>*/
}
$h_sci_Map$EmptyMap$.prototype = $c_sci_Map$EmptyMap$.prototype;
$c_sci_Map$EmptyMap$.prototype.apply__O__O = (function(key) {
  this.apply__O__E(key)
});
$c_sci_Map$EmptyMap$.prototype.isEmpty__Z = (function() {
  return true
});
$c_sci_Map$EmptyMap$.prototype.getOrElse__O__F0__O = (function(key, $default) {
  return $default.apply__O()
});
$c_sci_Map$EmptyMap$.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return new $c_sci_Map$Map1(key, value)
});
$c_sci_Map$EmptyMap$.prototype.size__I = (function() {
  return 0
});
$c_sci_Map$EmptyMap$.prototype.apply__O__E = (function(key) {
  throw new $c_ju_NoSuchElementException().init___T(("key not found: " + key))
});
$c_sci_Map$EmptyMap$.prototype.iterator__sc_Iterator = (function() {
  return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
});
$c_sci_Map$EmptyMap$.prototype.get__O__s_Option = (function(key) {
  return $m_s_None$()
});
$c_sci_Map$EmptyMap$.prototype.knownSize__I = (function() {
  return 0
});
var $d_sci_Map$EmptyMap$ = new $TypeData().initClass({
  sci_Map$EmptyMap$: 0
}, false, "scala.collection.immutable.Map$EmptyMap$", {
  sci_Map$EmptyMap$: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1
});
$c_sci_Map$EmptyMap$.prototype.$classData = $d_sci_Map$EmptyMap$;
var $n_sci_Map$EmptyMap$ = (void 0);
function $m_sci_Map$EmptyMap$() {
  if ((!$n_sci_Map$EmptyMap$)) {
    $n_sci_Map$EmptyMap$ = new $c_sci_Map$EmptyMap$()
  };
  return $n_sci_Map$EmptyMap$
}
/** @constructor */
function $c_sci_OldHashSet() {
  /*<skip>*/
}
$c_sci_OldHashSet.prototype = new $h_sci_AbstractSet();
$c_sci_OldHashSet.prototype.constructor = $c_sci_OldHashSet;
/** @constructor */
function $h_sci_OldHashSet() {
  /*<skip>*/
}
$h_sci_OldHashSet.prototype = $c_sci_OldHashSet.prototype;
$c_sci_OldHashSet.prototype.filter__F1__sci_OldHashSet = (function(p) {
  var size = this.size__I();
  var x = ((6 + size) | 0);
  var buffer = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [((x < 224) ? x : 224)]);
  var s = this.filter0__F1__Z__I__Asci_OldHashSet__I__sci_OldHashSet(p, false, 0, buffer, 0);
  return ((s === null) ? $m_sci_OldHashSet$EmptyOldHashSet$() : s)
});
$c_sci_OldHashSet.prototype.concat__sc_IterableOnce__sc_SetOps = (function(that) {
  return this.concat__sc_IterableOnce__sci_OldHashSet(that)
});
$c_sci_OldHashSet.prototype.subsetOf__sc_Set__Z = (function(that) {
  if ($is_sci_OldHashSet(that)) {
    var x2 = $as_sci_OldHashSet(that);
    return this.subsetOf0__sci_OldHashSet__I__Z(x2, 0)
  } else {
    return $f_sc_IterableOnceOps__forall__F1__Z(this, that)
  }
});
$c_sci_OldHashSet.prototype.tail__sci_OldHashSet = (function() {
  var elem = this.head__O();
  return this.excl__O__sci_OldHashSet(elem)
});
$c_sci_OldHashSet.prototype.filter__F1__O = (function(pred) {
  return this.filter__F1__sci_OldHashSet(pred)
});
$c_sci_OldHashSet.prototype.filterNot__F1__sci_OldHashSet = (function(p) {
  var size = this.size__I();
  var x = ((6 + size) | 0);
  var buffer = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [((x < 224) ? x : 224)]);
  var s = this.filter0__F1__Z__I__Asci_OldHashSet__I__sci_OldHashSet(p, true, 0, buffer, 0);
  return ((s === null) ? $m_sci_OldHashSet$EmptyOldHashSet$() : s)
});
$c_sci_OldHashSet.prototype.concat__sc_IterableOnce__sci_OldHashSet = (function(that) {
  if ($is_sci_OldHashSet(that)) {
    var x2 = $as_sci_OldHashSet(that);
    var size = ((this.size__I() + x2.size__I()) | 0);
    var x = ((6 + size) | 0);
    var buffer = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [((x < 224) ? x : 224)]);
    var s = this.union0__sci_OldHashSet__I__Asci_OldHashSet__I__sci_OldHashSet(x2, 0, buffer, 0);
    return ((s === null) ? $m_sci_OldHashSet$EmptyOldHashSet$() : s)
  } else {
    return $as_sci_OldHashSet($f_sci_SetOps__concat__sc_IterableOnce__sci_SetOps(this, that))
  }
});
$c_sci_OldHashSet.prototype.filterNot__F1__O = (function(pred) {
  return this.filterNot__F1__sci_OldHashSet(pred)
});
$c_sci_OldHashSet.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_OldHashSet$()
});
$c_sci_OldHashSet.prototype.tail__O = (function() {
  return this.tail__sci_OldHashSet()
});
$c_sci_OldHashSet.prototype.contains__O__Z = (function(elem) {
  return this.get0__O__I__I__Z(elem, $m_sc_Hashing$().computeHash__O__I(elem), 0)
});
$c_sci_OldHashSet.prototype.incl__O__sci_OldHashSet = (function(elem) {
  return this.updated0__O__I__I__sci_OldHashSet(elem, $m_sc_Hashing$().computeHash__O__I(elem), 0)
});
$c_sci_OldHashSet.prototype.incl__O__sci_SetOps = (function(elem) {
  return this.incl__O__sci_OldHashSet(elem)
});
$c_sci_OldHashSet.prototype.excl__O__sci_SetOps = (function(elem) {
  return this.excl__O__sci_OldHashSet(elem)
});
$c_sci_OldHashSet.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_OldHashSet.prototype.excl__O__sci_OldHashSet = (function(elem) {
  var s = this.removed0__O__I__I__sci_OldHashSet(elem, $m_sc_Hashing$().computeHash__O__I(elem), 0);
  return ((s === null) ? $m_sci_OldHashSet$EmptyOldHashSet$() : s)
});
$c_sci_OldHashSet.prototype.className__T = (function() {
  return "OldHashSet"
});
$c_sci_OldHashSet.prototype.concat__sc_IterableOnce__sci_SetOps = (function(that) {
  return this.concat__sc_IterableOnce__sci_OldHashSet(that)
});
function $is_sci_OldHashSet(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_OldHashSet)))
}
function $as_sci_OldHashSet(obj) {
  return (($is_sci_OldHashSet(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.OldHashSet"))
}
function $isArrayOf_sci_OldHashSet(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_OldHashSet)))
}
function $asArrayOf_sci_OldHashSet(obj, depth) {
  return (($isArrayOf_sci_OldHashSet(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.OldHashSet;", depth))
}
var $d_sci_OldHashSet = new $TypeData().initClass({
  sci_OldHashSet: 0
}, false, "scala.collection.immutable.OldHashSet", {
  sci_OldHashSet: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_OldHashSet.prototype.$classData = $d_sci_OldHashSet;
/** @constructor */
function $c_sci_Set$Set1(elem1) {
  this.elem1$4 = null;
  this.elem1$4 = elem1
}
$c_sci_Set$Set1.prototype = new $h_sci_AbstractSet();
$c_sci_Set$Set1.prototype.constructor = $c_sci_Set$Set1;
/** @constructor */
function $h_sci_Set$Set1() {
  /*<skip>*/
}
$h_sci_Set$Set1.prototype = $c_sci_Set$Set1.prototype;
$c_sci_Set$Set1.prototype.head__O = (function() {
  return this.elem1$4
});
$c_sci_Set$Set1.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Set$Set1.prototype.forall__F1__Z = (function(p) {
  return $uZ(p.apply__O__O(this.elem1$4))
});
$c_sci_Set$Set1.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(this.elem1$4)
});
$c_sci_Set$Set1.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sci_Set$Set1.prototype.size__I = (function() {
  return 1
});
$c_sci_Set$Set1.prototype.excl__O__sci_Set = (function(elem) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem1$4) ? ($m_sci_Set$(), $m_sci_Set$EmptySet$()) : this)
});
$c_sci_Set$Set1.prototype.iterator__sc_Iterator = (function() {
  $m_sc_Iterator$();
  var a = this.elem1$4;
  return new $c_sc_Iterator$$anon$19(a)
});
$c_sci_Set$Set1.prototype.filterNot__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, true)
});
$c_sci_Set$Set1.prototype.incl__O__sci_Set = (function(elem) {
  return (this.contains__O__Z(elem) ? this : new $c_sci_Set$Set2(this.elem1$4, elem))
});
$c_sci_Set$Set1.prototype.tail__O = (function() {
  $m_sci_Set$();
  return $m_sci_Set$EmptySet$()
});
$c_sci_Set$Set1.prototype.contains__O__Z = (function(elem) {
  return $m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem1$4)
});
$c_sci_Set$Set1.prototype.incl__O__sci_SetOps = (function(elem) {
  return this.incl__O__sci_Set(elem)
});
$c_sci_Set$Set1.prototype.excl__O__sci_SetOps = (function(elem) {
  return this.excl__O__sci_Set(elem)
});
$c_sci_Set$Set1.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_Set$Set1.prototype.knownSize__I = (function() {
  return 1
});
var $d_sci_Set$Set1 = new $TypeData().initClass({
  sci_Set$Set1: 0
}, false, "scala.collection.immutable.Set$Set1", {
  sci_Set$Set1: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Set$Set1.prototype.$classData = $d_sci_Set$Set1;
/** @constructor */
function $c_sci_Set$Set2(elem1, elem2) {
  this.elem1$4 = null;
  this.elem2$4 = null;
  this.elem1$4 = elem1;
  this.elem2$4 = elem2
}
$c_sci_Set$Set2.prototype = new $h_sci_AbstractSet();
$c_sci_Set$Set2.prototype.constructor = $c_sci_Set$Set2;
/** @constructor */
function $h_sci_Set$Set2() {
  /*<skip>*/
}
$h_sci_Set$Set2.prototype = $c_sci_Set$Set2.prototype;
$c_sci_Set$Set2.prototype.head__O = (function() {
  return this.elem1$4
});
$c_sci_Set$Set2.prototype.tail__sci_Set = (function() {
  return new $c_sci_Set$Set1(this.elem2$4)
});
$c_sci_Set$Set2.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Set$Set2.prototype.forall__F1__Z = (function(p) {
  return ($uZ(p.apply__O__O(this.elem1$4)) && $uZ(p.apply__O__O(this.elem2$4)))
});
$c_sci_Set$Set2.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(this.elem1$4);
  f.apply__O__O(this.elem2$4)
});
$c_sci_Set$Set2.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sci_Set$Set2.prototype.size__I = (function() {
  return 2
});
$c_sci_Set$Set2.prototype.excl__O__sci_Set = (function(elem) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem1$4) ? new $c_sci_Set$Set1(this.elem2$4) : ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem2$4) ? new $c_sci_Set$Set1(this.elem1$4) : this))
});
$c_sci_Set$Set2.prototype.iterator__sc_Iterator = (function() {
  var rassoc$2 = this.elem1$4;
  var rassoc$1 = this.elem2$4;
  var this$1 = $m_sci_Nil$();
  var this$2 = new $c_sci_$colon$colon(rassoc$1, this$1);
  var this$3 = new $c_sci_$colon$colon(rassoc$2, this$2);
  return new $c_sc_StrictOptimizedLinearSeqOps$$anon$1(this$3)
});
$c_sci_Set$Set2.prototype.filterNot__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, true)
});
$c_sci_Set$Set2.prototype.incl__O__sci_Set = (function(elem) {
  return (this.contains__O__Z(elem) ? this : new $c_sci_Set$Set3(this.elem1$4, this.elem2$4, elem))
});
$c_sci_Set$Set2.prototype.tail__O = (function() {
  return this.tail__sci_Set()
});
$c_sci_Set$Set2.prototype.contains__O__Z = (function(elem) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem1$4) || $m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem2$4))
});
$c_sci_Set$Set2.prototype.incl__O__sci_SetOps = (function(elem) {
  return this.incl__O__sci_Set(elem)
});
$c_sci_Set$Set2.prototype.excl__O__sci_SetOps = (function(elem) {
  return this.excl__O__sci_Set(elem)
});
$c_sci_Set$Set2.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_Set$Set2.prototype.knownSize__I = (function() {
  return 2
});
var $d_sci_Set$Set2 = new $TypeData().initClass({
  sci_Set$Set2: 0
}, false, "scala.collection.immutable.Set$Set2", {
  sci_Set$Set2: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Set$Set2.prototype.$classData = $d_sci_Set$Set2;
/** @constructor */
function $c_sci_Set$Set3(elem1, elem2, elem3) {
  this.elem1$4 = null;
  this.elem2$4 = null;
  this.elem3$4 = null;
  this.elem1$4 = elem1;
  this.elem2$4 = elem2;
  this.elem3$4 = elem3
}
$c_sci_Set$Set3.prototype = new $h_sci_AbstractSet();
$c_sci_Set$Set3.prototype.constructor = $c_sci_Set$Set3;
/** @constructor */
function $h_sci_Set$Set3() {
  /*<skip>*/
}
$h_sci_Set$Set3.prototype = $c_sci_Set$Set3.prototype;
$c_sci_Set$Set3.prototype.head__O = (function() {
  return this.elem1$4
});
$c_sci_Set$Set3.prototype.tail__sci_Set = (function() {
  return new $c_sci_Set$Set2(this.elem2$4, this.elem3$4)
});
$c_sci_Set$Set3.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Set$Set3.prototype.forall__F1__Z = (function(p) {
  return (($uZ(p.apply__O__O(this.elem1$4)) && $uZ(p.apply__O__O(this.elem2$4))) && $uZ(p.apply__O__O(this.elem3$4)))
});
$c_sci_Set$Set3.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(this.elem1$4);
  f.apply__O__O(this.elem2$4);
  f.apply__O__O(this.elem3$4)
});
$c_sci_Set$Set3.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sci_Set$Set3.prototype.size__I = (function() {
  return 3
});
$c_sci_Set$Set3.prototype.excl__O__sci_Set = (function(elem) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem1$4) ? new $c_sci_Set$Set2(this.elem2$4, this.elem3$4) : ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem2$4) ? new $c_sci_Set$Set2(this.elem1$4, this.elem3$4) : ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem3$4) ? new $c_sci_Set$Set2(this.elem1$4, this.elem2$4) : this)))
});
$c_sci_Set$Set3.prototype.iterator__sc_Iterator = (function() {
  var rassoc$5 = this.elem1$4;
  var rassoc$4 = this.elem2$4;
  var rassoc$3 = this.elem3$4;
  var this$1 = $m_sci_Nil$();
  var this$2 = new $c_sci_$colon$colon(rassoc$3, this$1);
  var this$3 = new $c_sci_$colon$colon(rassoc$4, this$2);
  var this$4 = new $c_sci_$colon$colon(rassoc$5, this$3);
  return new $c_sc_StrictOptimizedLinearSeqOps$$anon$1(this$4)
});
$c_sci_Set$Set3.prototype.filterNot__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, true)
});
$c_sci_Set$Set3.prototype.incl__O__sci_Set = (function(elem) {
  return (this.contains__O__Z(elem) ? this : new $c_sci_Set$Set4(this.elem1$4, this.elem2$4, this.elem3$4, elem))
});
$c_sci_Set$Set3.prototype.tail__O = (function() {
  return this.tail__sci_Set()
});
$c_sci_Set$Set3.prototype.contains__O__Z = (function(elem) {
  return (($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem1$4) || $m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem2$4)) || $m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem3$4))
});
$c_sci_Set$Set3.prototype.incl__O__sci_SetOps = (function(elem) {
  return this.incl__O__sci_Set(elem)
});
$c_sci_Set$Set3.prototype.excl__O__sci_SetOps = (function(elem) {
  return this.excl__O__sci_Set(elem)
});
$c_sci_Set$Set3.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_Set$Set3.prototype.knownSize__I = (function() {
  return 3
});
var $d_sci_Set$Set3 = new $TypeData().initClass({
  sci_Set$Set3: 0
}, false, "scala.collection.immutable.Set$Set3", {
  sci_Set$Set3: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Set$Set3.prototype.$classData = $d_sci_Set$Set3;
/** @constructor */
function $c_sci_Set$Set4(elem1, elem2, elem3, elem4) {
  this.elem1$4 = null;
  this.elem2$4 = null;
  this.elem3$4 = null;
  this.elem4$4 = null;
  this.elem1$4 = elem1;
  this.elem2$4 = elem2;
  this.elem3$4 = elem3;
  this.elem4$4 = elem4
}
$c_sci_Set$Set4.prototype = new $h_sci_AbstractSet();
$c_sci_Set$Set4.prototype.constructor = $c_sci_Set$Set4;
/** @constructor */
function $h_sci_Set$Set4() {
  /*<skip>*/
}
$h_sci_Set$Set4.prototype = $c_sci_Set$Set4.prototype;
$c_sci_Set$Set4.prototype.head__O = (function() {
  return this.elem1$4
});
$c_sci_Set$Set4.prototype.tail__sci_Set = (function() {
  return new $c_sci_Set$Set3(this.elem2$4, this.elem3$4, this.elem4$4)
});
$c_sci_Set$Set4.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Set$Set4.prototype.forall__F1__Z = (function(p) {
  return ((($uZ(p.apply__O__O(this.elem1$4)) && $uZ(p.apply__O__O(this.elem2$4))) && $uZ(p.apply__O__O(this.elem3$4))) && $uZ(p.apply__O__O(this.elem4$4)))
});
$c_sci_Set$Set4.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(this.elem1$4);
  f.apply__O__O(this.elem2$4);
  f.apply__O__O(this.elem3$4);
  f.apply__O__O(this.elem4$4)
});
$c_sci_Set$Set4.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sci_Set$Set4.prototype.size__I = (function() {
  return 4
});
$c_sci_Set$Set4.prototype.excl__O__sci_Set = (function(elem) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem1$4) ? new $c_sci_Set$Set3(this.elem2$4, this.elem3$4, this.elem4$4) : ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem2$4) ? new $c_sci_Set$Set3(this.elem1$4, this.elem3$4, this.elem4$4) : ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem3$4) ? new $c_sci_Set$Set3(this.elem1$4, this.elem2$4, this.elem4$4) : ($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem4$4) ? new $c_sci_Set$Set3(this.elem1$4, this.elem2$4, this.elem3$4) : this))))
});
$c_sci_Set$Set4.prototype.iterator__sc_Iterator = (function() {
  var rassoc$9 = this.elem1$4;
  var rassoc$8 = this.elem2$4;
  var rassoc$7 = this.elem3$4;
  var rassoc$6 = this.elem4$4;
  var this$1 = $m_sci_Nil$();
  var this$2 = new $c_sci_$colon$colon(rassoc$6, this$1);
  var this$3 = new $c_sci_$colon$colon(rassoc$7, this$2);
  var this$4 = new $c_sci_$colon$colon(rassoc$8, this$3);
  var this$5 = new $c_sci_$colon$colon(rassoc$9, this$4);
  return new $c_sc_StrictOptimizedLinearSeqOps$$anon$1(this$5)
});
$c_sci_Set$Set4.prototype.filterNot__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, true)
});
$c_sci_Set$Set4.prototype.incl__O__sci_Set = (function(elem) {
  if (this.contains__O__Z(elem)) {
    return this
  } else {
    if ($m_sci_Set$().scala$collection$immutable$Set$$useBaseline$1) {
      var this$3 = $m_sci_OldHashSet$EmptyOldHashSet$()
    } else {
      var this$2 = $m_sci_HashSet$();
      var this$3 = this$2.EmptySet$1
    };
    var elem$1 = this.elem1$4;
    var this$4 = this$3.incl__O__sci_SetOps(elem$1);
    var elem$2 = this.elem2$4;
    var this$5 = this$4.incl__O__sci_SetOps(elem$2);
    var elem$3 = this.elem3$4;
    var this$6 = this$5.incl__O__sci_SetOps(elem$3);
    var elem$4 = this.elem4$4;
    var this$7 = this$6.incl__O__sci_SetOps(elem$4);
    return $as_sci_Set(this$7.incl__O__sci_SetOps(elem))
  }
});
$c_sci_Set$Set4.prototype.tail__O = (function() {
  return this.tail__sci_Set()
});
$c_sci_Set$Set4.prototype.contains__O__Z = (function(elem) {
  return ((($m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem1$4) || $m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem2$4)) || $m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem3$4)) || $m_sr_BoxesRunTime$().equals__O__O__Z(elem, this.elem4$4))
});
$c_sci_Set$Set4.prototype.incl__O__sci_SetOps = (function(elem) {
  return this.incl__O__sci_Set(elem)
});
$c_sci_Set$Set4.prototype.excl__O__sci_SetOps = (function(elem) {
  return this.excl__O__sci_Set(elem)
});
$c_sci_Set$Set4.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_Set$Set4.prototype.knownSize__I = (function() {
  return 4
});
var $d_sci_Set$Set4 = new $TypeData().initClass({
  sci_Set$Set4: 0
}, false, "scala.collection.immutable.Set$Set4", {
  sci_Set$Set4: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Set$Set4.prototype.$classData = $d_sci_Set$Set4;
/** @constructor */
function $c_sci_ListSet$EmptyListSet$() {
  /*<skip>*/
}
$c_sci_ListSet$EmptyListSet$.prototype = new $h_sci_ListSet();
$c_sci_ListSet$EmptyListSet$.prototype.constructor = $c_sci_ListSet$EmptyListSet$;
/** @constructor */
function $h_sci_ListSet$EmptyListSet$() {
  /*<skip>*/
}
$h_sci_ListSet$EmptyListSet$.prototype = $c_sci_ListSet$EmptyListSet$.prototype;
$c_sci_ListSet$EmptyListSet$.prototype.knownSize__I = (function() {
  return 0
});
var $d_sci_ListSet$EmptyListSet$ = new $TypeData().initClass({
  sci_ListSet$EmptyListSet$: 0
}, false, "scala.collection.immutable.ListSet$EmptyListSet$", {
  sci_ListSet$EmptyListSet$: 1,
  sci_ListSet: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_ListSet$EmptyListSet$.prototype.$classData = $d_sci_ListSet$EmptyListSet$;
var $n_sci_ListSet$EmptyListSet$ = (void 0);
function $m_sci_ListSet$EmptyListSet$() {
  if ((!$n_sci_ListSet$EmptyListSet$)) {
    $n_sci_ListSet$EmptyListSet$ = new $c_sci_ListSet$EmptyListSet$()
  };
  return $n_sci_ListSet$EmptyListSet$
}
/** @constructor */
function $c_sci_ListSet$Node($$outer, elem) {
  this.elem$5 = null;
  this.$$outer$5 = null;
  this.elem$5 = elem;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$5 = $$outer
  }
}
$c_sci_ListSet$Node.prototype = new $h_sci_ListSet();
$c_sci_ListSet$Node.prototype.constructor = $c_sci_ListSet$Node;
/** @constructor */
function $h_sci_ListSet$Node() {
  /*<skip>*/
}
$h_sci_ListSet$Node.prototype = $c_sci_ListSet$Node.prototype;
$c_sci_ListSet$Node.prototype.next__sci_ListSet = (function() {
  return this.$$outer$5
});
$c_sci_ListSet$Node.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_ListSet$Node.prototype.incl__O__sci_ListSet = (function(e) {
  return (this.containsInternal__p5__sci_ListSet__O__Z(this, e) ? this : new $c_sci_ListSet$Node(this, e))
});
$c_sci_ListSet$Node.prototype.sizeInternal__p5__sci_ListSet__I__I = (function(n, acc) {
  while (true) {
    if (n.isEmpty__Z()) {
      return acc
    } else {
      var temp$n = n.next__sci_ListSet();
      var temp$acc = ((1 + acc) | 0);
      n = temp$n;
      acc = temp$acc
    }
  }
});
$c_sci_ListSet$Node.prototype.size__I = (function() {
  return this.sizeInternal__p5__sci_ListSet__I__I(this, 0)
});
$c_sci_ListSet$Node.prototype.removeInternal__p5__O__sci_ListSet__sci_List__sci_ListSet = (function(k, cur, acc) {
  while (true) {
    if (cur.isEmpty__Z()) {
      return $as_sci_ListSet(acc.last__O())
    } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(k, cur.elem__O())) {
      var this$1 = acc;
      var z = cur.next__sci_ListSet();
      var acc$1 = z;
      var these = this$1;
      while ((!these.isEmpty__Z())) {
        var arg1 = acc$1;
        var arg2 = these.head__O();
        var t = $as_sci_ListSet(arg1);
        var h = $as_sci_ListSet(arg2);
        acc$1 = new $c_sci_ListSet$Node(t, h.elem__O());
        these = $as_sc_LinearSeq(these.tail__O())
      };
      return $as_sci_ListSet(acc$1)
    } else {
      var temp$cur = cur.next__sci_ListSet();
      var rassoc$2 = cur;
      var this$2 = acc;
      var temp$acc = new $c_sci_$colon$colon(rassoc$2, this$2);
      cur = temp$cur;
      acc = temp$acc
    }
  }
});
$c_sci_ListSet$Node.prototype.excl__O__sci_ListSet = (function(e) {
  return this.removeInternal__p5__O__sci_ListSet__sci_List__sci_ListSet(e, this, $m_sci_Nil$())
});
$c_sci_ListSet$Node.prototype.elem__O = (function() {
  return this.elem$5
});
$c_sci_ListSet$Node.prototype.contains__O__Z = (function(e) {
  return this.containsInternal__p5__sci_ListSet__O__Z(this, e)
});
$c_sci_ListSet$Node.prototype.incl__O__sci_SetOps = (function(elem) {
  return this.incl__O__sci_ListSet(elem)
});
$c_sci_ListSet$Node.prototype.excl__O__sci_SetOps = (function(elem) {
  return this.removeInternal__p5__O__sci_ListSet__sci_List__sci_ListSet(elem, this, $m_sci_Nil$())
});
$c_sci_ListSet$Node.prototype.containsInternal__p5__sci_ListSet__O__Z = (function(n, e) {
  while (true) {
    if ((!n.isEmpty__Z())) {
      if ($m_sr_BoxesRunTime$().equals__O__O__Z(n.elem__O(), e)) {
        return true
      } else {
        n = n.next__sci_ListSet()
      }
    } else {
      return false
    }
  }
});
$c_sci_ListSet$Node.prototype.knownSize__I = (function() {
  return (-1)
});
var $d_sci_ListSet$Node = new $TypeData().initClass({
  sci_ListSet$Node: 0
}, false, "scala.collection.immutable.ListSet$Node", {
  sci_ListSet$Node: 1,
  sci_ListSet: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_ListSet$Node.prototype.$classData = $d_sci_ListSet$Node;
/** @constructor */
function $c_sci_Map$Map1(key1, value1) {
  this.key1$4 = null;
  this.value1$4 = null;
  this.key1$4 = key1;
  this.value1$4 = value1
}
$c_sci_Map$Map1.prototype = new $h_sci_AbstractMap();
$c_sci_Map$Map1.prototype.constructor = $c_sci_Map$Map1;
/** @constructor */
function $h_sci_Map$Map1() {
  /*<skip>*/
}
$h_sci_Map$Map1.prototype = $c_sci_Map$Map1.prototype;
$c_sci_Map$Map1.prototype.apply__O__O = (function(key) {
  if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key1$4)) {
    return this.value1$4
  } else {
    throw new $c_ju_NoSuchElementException().init___T(("key not found: " + key))
  }
});
$c_sci_Map$Map1.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Map$Map1.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return this.updated__O__O__sci_Map(key, value)
});
$c_sci_Map$Map1.prototype.getOrElse__O__F0__O = (function(key, $default) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key1$4) ? this.value1$4 : $default.apply__O())
});
$c_sci_Map$Map1.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(new $c_T2(this.key1$4, this.value1$4))
});
$c_sci_Map$Map1.prototype.size__I = (function() {
  return 1
});
$c_sci_Map$Map1.prototype.iterator__sc_Iterator = (function() {
  $m_sc_Iterator$();
  var a = new $c_T2(this.key1$4, this.value1$4);
  return new $c_sc_Iterator$$anon$19(a)
});
$c_sci_Map$Map1.prototype.updated__O__O__sci_Map = (function(key, value) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key1$4) ? new $c_sci_Map$Map1(this.key1$4, value) : new $c_sci_Map$Map2(this.key1$4, this.value1$4, key, value))
});
$c_sci_Map$Map1.prototype.get__O__s_Option = (function(key) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key1$4) ? new $c_s_Some(this.value1$4) : $m_s_None$())
});
$c_sci_Map$Map1.prototype.knownSize__I = (function() {
  return 1
});
var $d_sci_Map$Map1 = new $TypeData().initClass({
  sci_Map$Map1: 0
}, false, "scala.collection.immutable.Map$Map1", {
  sci_Map$Map1: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Map$Map1.prototype.$classData = $d_sci_Map$Map1;
/** @constructor */
function $c_sci_Map$Map2(key1, value1, key2, value2) {
  this.scala$collection$immutable$Map$Map2$$key1$f = null;
  this.scala$collection$immutable$Map$Map2$$value1$f = null;
  this.scala$collection$immutable$Map$Map2$$key2$f = null;
  this.scala$collection$immutable$Map$Map2$$value2$f = null;
  this.scala$collection$immutable$Map$Map2$$key1$f = key1;
  this.scala$collection$immutable$Map$Map2$$value1$f = value1;
  this.scala$collection$immutable$Map$Map2$$key2$f = key2;
  this.scala$collection$immutable$Map$Map2$$value2$f = value2
}
$c_sci_Map$Map2.prototype = new $h_sci_AbstractMap();
$c_sci_Map$Map2.prototype.constructor = $c_sci_Map$Map2;
/** @constructor */
function $h_sci_Map$Map2() {
  /*<skip>*/
}
$h_sci_Map$Map2.prototype = $c_sci_Map$Map2.prototype;
$c_sci_Map$Map2.prototype.apply__O__O = (function(key) {
  if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map2$$key1$f)) {
    return this.scala$collection$immutable$Map$Map2$$value1$f
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map2$$key2$f)) {
    return this.scala$collection$immutable$Map$Map2$$value2$f
  } else {
    throw new $c_ju_NoSuchElementException().init___T(("key not found: " + key))
  }
});
$c_sci_Map$Map2.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Map$Map2.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return this.updated__O__O__sci_Map(key, value)
});
$c_sci_Map$Map2.prototype.getOrElse__O__F0__O = (function(key, $default) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map2$$key1$f) ? this.scala$collection$immutable$Map$Map2$$value1$f : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map2$$key2$f) ? this.scala$collection$immutable$Map$Map2$$value2$f : $default.apply__O()))
});
$c_sci_Map$Map2.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map2$$key1$f, this.scala$collection$immutable$Map$Map2$$value1$f));
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map2$$key2$f, this.scala$collection$immutable$Map$Map2$$value2$f))
});
$c_sci_Map$Map2.prototype.size__I = (function() {
  return 2
});
$c_sci_Map$Map2.prototype.iterator__sc_Iterator = (function() {
  return new $c_sci_Map$Map2$$anon$2(this)
});
$c_sci_Map$Map2.prototype.updated__O__O__sci_Map = (function(key, value) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map2$$key1$f) ? new $c_sci_Map$Map2(this.scala$collection$immutable$Map$Map2$$key1$f, value, this.scala$collection$immutable$Map$Map2$$key2$f, this.scala$collection$immutable$Map$Map2$$value2$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map2$$key2$f) ? new $c_sci_Map$Map2(this.scala$collection$immutable$Map$Map2$$key1$f, this.scala$collection$immutable$Map$Map2$$value1$f, this.scala$collection$immutable$Map$Map2$$key2$f, value) : new $c_sci_Map$Map3(this.scala$collection$immutable$Map$Map2$$key1$f, this.scala$collection$immutable$Map$Map2$$value1$f, this.scala$collection$immutable$Map$Map2$$key2$f, this.scala$collection$immutable$Map$Map2$$value2$f, key, value)))
});
$c_sci_Map$Map2.prototype.get__O__s_Option = (function(key) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map2$$key1$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map2$$value1$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map2$$key2$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map2$$value2$f) : $m_s_None$()))
});
$c_sci_Map$Map2.prototype.knownSize__I = (function() {
  return 2
});
var $d_sci_Map$Map2 = new $TypeData().initClass({
  sci_Map$Map2: 0
}, false, "scala.collection.immutable.Map$Map2", {
  sci_Map$Map2: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Map$Map2.prototype.$classData = $d_sci_Map$Map2;
/** @constructor */
function $c_sci_Map$Map3(key1, value1, key2, value2, key3, value3) {
  this.scala$collection$immutable$Map$Map3$$key1$f = null;
  this.scala$collection$immutable$Map$Map3$$value1$f = null;
  this.scala$collection$immutable$Map$Map3$$key2$f = null;
  this.scala$collection$immutable$Map$Map3$$value2$f = null;
  this.scala$collection$immutable$Map$Map3$$key3$f = null;
  this.scala$collection$immutable$Map$Map3$$value3$f = null;
  this.scala$collection$immutable$Map$Map3$$key1$f = key1;
  this.scala$collection$immutable$Map$Map3$$value1$f = value1;
  this.scala$collection$immutable$Map$Map3$$key2$f = key2;
  this.scala$collection$immutable$Map$Map3$$value2$f = value2;
  this.scala$collection$immutable$Map$Map3$$key3$f = key3;
  this.scala$collection$immutable$Map$Map3$$value3$f = value3
}
$c_sci_Map$Map3.prototype = new $h_sci_AbstractMap();
$c_sci_Map$Map3.prototype.constructor = $c_sci_Map$Map3;
/** @constructor */
function $h_sci_Map$Map3() {
  /*<skip>*/
}
$h_sci_Map$Map3.prototype = $c_sci_Map$Map3.prototype;
$c_sci_Map$Map3.prototype.apply__O__O = (function(key) {
  if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key1$f)) {
    return this.scala$collection$immutable$Map$Map3$$value1$f
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key2$f)) {
    return this.scala$collection$immutable$Map$Map3$$value2$f
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key3$f)) {
    return this.scala$collection$immutable$Map$Map3$$value3$f
  } else {
    throw new $c_ju_NoSuchElementException().init___T(("key not found: " + key))
  }
});
$c_sci_Map$Map3.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Map$Map3.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return this.updated__O__O__sci_Map(key, value)
});
$c_sci_Map$Map3.prototype.getOrElse__O__F0__O = (function(key, $default) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key1$f) ? this.scala$collection$immutable$Map$Map3$$value1$f : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key2$f) ? this.scala$collection$immutable$Map$Map3$$value2$f : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key3$f) ? this.scala$collection$immutable$Map$Map3$$value3$f : $default.apply__O())))
});
$c_sci_Map$Map3.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map3$$key1$f, this.scala$collection$immutable$Map$Map3$$value1$f));
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map3$$key2$f, this.scala$collection$immutable$Map$Map3$$value2$f));
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map3$$key3$f, this.scala$collection$immutable$Map$Map3$$value3$f))
});
$c_sci_Map$Map3.prototype.size__I = (function() {
  return 3
});
$c_sci_Map$Map3.prototype.iterator__sc_Iterator = (function() {
  return new $c_sci_Map$Map3$$anon$5(this)
});
$c_sci_Map$Map3.prototype.updated__O__O__sci_Map = (function(key, value) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key1$f) ? new $c_sci_Map$Map3(this.scala$collection$immutable$Map$Map3$$key1$f, value, this.scala$collection$immutable$Map$Map3$$key2$f, this.scala$collection$immutable$Map$Map3$$value2$f, this.scala$collection$immutable$Map$Map3$$key3$f, this.scala$collection$immutable$Map$Map3$$value3$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key2$f) ? new $c_sci_Map$Map3(this.scala$collection$immutable$Map$Map3$$key1$f, this.scala$collection$immutable$Map$Map3$$value1$f, this.scala$collection$immutable$Map$Map3$$key2$f, value, this.scala$collection$immutable$Map$Map3$$key3$f, this.scala$collection$immutable$Map$Map3$$value3$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key3$f) ? new $c_sci_Map$Map3(this.scala$collection$immutable$Map$Map3$$key1$f, this.scala$collection$immutable$Map$Map3$$value1$f, this.scala$collection$immutable$Map$Map3$$key2$f, this.scala$collection$immutable$Map$Map3$$value2$f, this.scala$collection$immutable$Map$Map3$$key3$f, value) : new $c_sci_Map$Map4(this.scala$collection$immutable$Map$Map3$$key1$f, this.scala$collection$immutable$Map$Map3$$value1$f, this.scala$collection$immutable$Map$Map3$$key2$f, this.scala$collection$immutable$Map$Map3$$value2$f, this.scala$collection$immutable$Map$Map3$$key3$f, this.scala$collection$immutable$Map$Map3$$value3$f, key, value))))
});
$c_sci_Map$Map3.prototype.get__O__s_Option = (function(key) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key1$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map3$$value1$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key2$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map3$$value2$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map3$$key3$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map3$$value3$f) : $m_s_None$())))
});
$c_sci_Map$Map3.prototype.knownSize__I = (function() {
  return 3
});
var $d_sci_Map$Map3 = new $TypeData().initClass({
  sci_Map$Map3: 0
}, false, "scala.collection.immutable.Map$Map3", {
  sci_Map$Map3: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Map$Map3.prototype.$classData = $d_sci_Map$Map3;
/** @constructor */
function $c_sci_Map$Map4(key1, value1, key2, value2, key3, value3, key4, value4) {
  this.scala$collection$immutable$Map$Map4$$key1$f = null;
  this.scala$collection$immutable$Map$Map4$$value1$f = null;
  this.scala$collection$immutable$Map$Map4$$key2$f = null;
  this.scala$collection$immutable$Map$Map4$$value2$f = null;
  this.scala$collection$immutable$Map$Map4$$key3$f = null;
  this.scala$collection$immutable$Map$Map4$$value3$f = null;
  this.scala$collection$immutable$Map$Map4$$key4$f = null;
  this.scala$collection$immutable$Map$Map4$$value4$f = null;
  this.scala$collection$immutable$Map$Map4$$key1$f = key1;
  this.scala$collection$immutable$Map$Map4$$value1$f = value1;
  this.scala$collection$immutable$Map$Map4$$key2$f = key2;
  this.scala$collection$immutable$Map$Map4$$value2$f = value2;
  this.scala$collection$immutable$Map$Map4$$key3$f = key3;
  this.scala$collection$immutable$Map$Map4$$value3$f = value3;
  this.scala$collection$immutable$Map$Map4$$key4$f = key4;
  this.scala$collection$immutable$Map$Map4$$value4$f = value4
}
$c_sci_Map$Map4.prototype = new $h_sci_AbstractMap();
$c_sci_Map$Map4.prototype.constructor = $c_sci_Map$Map4;
/** @constructor */
function $h_sci_Map$Map4() {
  /*<skip>*/
}
$h_sci_Map$Map4.prototype = $c_sci_Map$Map4.prototype;
$c_sci_Map$Map4.prototype.apply__O__O = (function(key) {
  if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key1$f)) {
    return this.scala$collection$immutable$Map$Map4$$value1$f
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key2$f)) {
    return this.scala$collection$immutable$Map$Map4$$value2$f
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key3$f)) {
    return this.scala$collection$immutable$Map$Map4$$value3$f
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key4$f)) {
    return this.scala$collection$immutable$Map$Map4$$value4$f
  } else {
    throw new $c_ju_NoSuchElementException().init___T(("key not found: " + key))
  }
});
$c_sci_Map$Map4.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Map$Map4.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return this.updated__O__O__sci_Map(key, value)
});
$c_sci_Map$Map4.prototype.getOrElse__O__F0__O = (function(key, $default) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key1$f) ? this.scala$collection$immutable$Map$Map4$$value1$f : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key2$f) ? this.scala$collection$immutable$Map$Map4$$value2$f : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key3$f) ? this.scala$collection$immutable$Map$Map4$$value3$f : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key4$f) ? this.scala$collection$immutable$Map$Map4$$value4$f : $default.apply__O()))))
});
$c_sci_Map$Map4.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map4$$key1$f, this.scala$collection$immutable$Map$Map4$$value1$f));
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map4$$key2$f, this.scala$collection$immutable$Map$Map4$$value2$f));
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map4$$key3$f, this.scala$collection$immutable$Map$Map4$$value3$f));
  f.apply__O__O(new $c_T2(this.scala$collection$immutable$Map$Map4$$key4$f, this.scala$collection$immutable$Map$Map4$$value4$f))
});
$c_sci_Map$Map4.prototype.size__I = (function() {
  return 4
});
$c_sci_Map$Map4.prototype.iterator__sc_Iterator = (function() {
  return new $c_sci_Map$Map4$$anon$8(this)
});
$c_sci_Map$Map4.prototype.updated__O__O__sci_Map = (function(key, value) {
  if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key1$f)) {
    return new $c_sci_Map$Map4(this.scala$collection$immutable$Map$Map4$$key1$f, value, this.scala$collection$immutable$Map$Map4$$key2$f, this.scala$collection$immutable$Map$Map4$$value2$f, this.scala$collection$immutable$Map$Map4$$key3$f, this.scala$collection$immutable$Map$Map4$$value3$f, this.scala$collection$immutable$Map$Map4$$key4$f, this.scala$collection$immutable$Map$Map4$$value4$f)
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key2$f)) {
    return new $c_sci_Map$Map4(this.scala$collection$immutable$Map$Map4$$key1$f, this.scala$collection$immutable$Map$Map4$$value1$f, this.scala$collection$immutable$Map$Map4$$key2$f, value, this.scala$collection$immutable$Map$Map4$$key3$f, this.scala$collection$immutable$Map$Map4$$value3$f, this.scala$collection$immutable$Map$Map4$$key4$f, this.scala$collection$immutable$Map$Map4$$value4$f)
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key3$f)) {
    return new $c_sci_Map$Map4(this.scala$collection$immutable$Map$Map4$$key1$f, this.scala$collection$immutable$Map$Map4$$value1$f, this.scala$collection$immutable$Map$Map4$$key2$f, this.scala$collection$immutable$Map$Map4$$value2$f, this.scala$collection$immutable$Map$Map4$$key3$f, value, this.scala$collection$immutable$Map$Map4$$key4$f, this.scala$collection$immutable$Map$Map4$$value4$f)
  } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key4$f)) {
    return new $c_sci_Map$Map4(this.scala$collection$immutable$Map$Map4$$key1$f, this.scala$collection$immutable$Map$Map4$$value1$f, this.scala$collection$immutable$Map$Map4$$key2$f, this.scala$collection$immutable$Map$Map4$$value2$f, this.scala$collection$immutable$Map$Map4$$key3$f, this.scala$collection$immutable$Map$Map4$$value3$f, this.scala$collection$immutable$Map$Map4$$key4$f, value)
  } else {
    if ($m_sci_Map$().scala$collection$immutable$Map$$useBaseline$1) {
      $m_sci_OldHashMap$();
      var jsx$1 = $m_sci_OldHashMap$EmptyOldHashMap$()
    } else {
      var this$2 = $m_sci_HashMap$();
      var jsx$1 = this$2.EmptyMap$1
    };
    return $as_sci_Map(jsx$1.updated__O__O__sci_MapOps(this.scala$collection$immutable$Map$Map4$$key1$f, this.scala$collection$immutable$Map$Map4$$value1$f).updated__O__O__sci_MapOps(this.scala$collection$immutable$Map$Map4$$key2$f, this.scala$collection$immutable$Map$Map4$$value2$f).updated__O__O__sci_MapOps(this.scala$collection$immutable$Map$Map4$$key3$f, this.scala$collection$immutable$Map$Map4$$value3$f).updated__O__O__sci_MapOps(this.scala$collection$immutable$Map$Map4$$key4$f, this.scala$collection$immutable$Map$Map4$$value4$f).updated__O__O__sci_MapOps(key, value))
  }
});
$c_sci_Map$Map4.prototype.get__O__s_Option = (function(key) {
  return ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key1$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map4$$value1$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key2$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map4$$value2$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key3$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map4$$value3$f) : ($m_sr_BoxesRunTime$().equals__O__O__Z(key, this.scala$collection$immutable$Map$Map4$$key4$f) ? new $c_s_Some(this.scala$collection$immutable$Map$Map4$$value4$f) : $m_s_None$()))))
});
$c_sci_Map$Map4.prototype.knownSize__I = (function() {
  return 4
});
var $d_sci_Map$Map4 = new $TypeData().initClass({
  sci_Map$Map4: 0
}, false, "scala.collection.immutable.Map$Map4", {
  sci_Map$Map4: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Map$Map4.prototype.$classData = $d_sci_Map$Map4;
/** @constructor */
function $c_sci_OldHashSet$EmptyOldHashSet$() {
  /*<skip>*/
}
$c_sci_OldHashSet$EmptyOldHashSet$.prototype = new $h_sci_OldHashSet();
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.constructor = $c_sci_OldHashSet$EmptyOldHashSet$;
/** @constructor */
function $h_sci_OldHashSet$EmptyOldHashSet$() {
  /*<skip>*/
}
$h_sci_OldHashSet$EmptyOldHashSet$.prototype = $c_sci_OldHashSet$EmptyOldHashSet$.prototype;
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.head__O = (function() {
  throw new $c_ju_NoSuchElementException().init___T("Empty Set")
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.subsetOf0__sci_OldHashSet__I__Z = (function(that, level) {
  return true
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.isEmpty__Z = (function() {
  return true
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.foreach__F1__V = (function(f) {
  /*<skip>*/
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.tail__sci_OldHashSet = (function() {
  throw new $c_ju_NoSuchElementException().init___T("Empty Set")
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.size__I = (function() {
  return 0
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.iterator__sc_Iterator = (function() {
  return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet = (function(that, level) {
  return that
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.updated0__O__I__I__sci_OldHashSet = (function(key, hash, level) {
  return new $c_sci_OldHashSet$OldHashSet1(key, hash)
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.tail__O = (function() {
  return this.tail__sci_OldHashSet()
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.removed0__O__I__I__sci_OldHashSet = (function(key, hash, level) {
  return this
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.filter0__F1__Z__I__Asci_OldHashSet__I__sci_OldHashSet = (function(p, negate, level, buffer, offset0) {
  return null
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.get0__O__I__I__Z = (function(elem, hash, level) {
  return false
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.union0__sci_OldHashSet__I__Asci_OldHashSet__I__sci_OldHashSet = (function(that, level, buffer, offset0) {
  return that
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.knownSize__I = (function() {
  return 0
});
var $d_sci_OldHashSet$EmptyOldHashSet$ = new $TypeData().initClass({
  sci_OldHashSet$EmptyOldHashSet$: 0
}, false, "scala.collection.immutable.OldHashSet$EmptyOldHashSet$", {
  sci_OldHashSet$EmptyOldHashSet$: 1,
  sci_OldHashSet: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_OldHashSet$EmptyOldHashSet$.prototype.$classData = $d_sci_OldHashSet$EmptyOldHashSet$;
var $n_sci_OldHashSet$EmptyOldHashSet$ = (void 0);
function $m_sci_OldHashSet$EmptyOldHashSet$() {
  if ((!$n_sci_OldHashSet$EmptyOldHashSet$)) {
    $n_sci_OldHashSet$EmptyOldHashSet$ = new $c_sci_OldHashSet$EmptyOldHashSet$()
  };
  return $n_sci_OldHashSet$EmptyOldHashSet$
}
/** @constructor */
function $c_sci_OldHashSet$HashTrieSet(bitmap, elems, size0) {
  this.bitmap$5 = 0;
  this.elems$5 = null;
  this.size0$5 = 0;
  this.bitmap$5 = bitmap;
  this.elems$5 = elems;
  this.size0$5 = size0;
  $m_s_Predef$().assert__Z__V(($m_jl_Integer$().bitCount__I__I(bitmap) === elems.u.length))
}
$c_sci_OldHashSet$HashTrieSet.prototype = new $h_sci_OldHashSet();
$c_sci_OldHashSet$HashTrieSet.prototype.constructor = $c_sci_OldHashSet$HashTrieSet;
/** @constructor */
function $h_sci_OldHashSet$HashTrieSet() {
  /*<skip>*/
}
$h_sci_OldHashSet$HashTrieSet.prototype = $c_sci_OldHashSet$HashTrieSet.prototype;
$c_sci_OldHashSet$HashTrieSet.prototype.subsetOf0__sci_OldHashSet__I__Z = (function(that, level) {
  if ((that === this)) {
    return true
  } else {
    if ($is_sci_OldHashSet$HashTrieSet(that)) {
      var x2 = $as_sci_OldHashSet$HashTrieSet(that);
      if ((this.size0$5 <= x2.size0$5)) {
        var abm = this.bitmap$5;
        var a = this.elems$5;
        var ai = 0;
        var b = x2.elems$5;
        var bbm = x2.bitmap$5;
        var bi = 0;
        if (((abm & bbm) === abm)) {
          while ((abm !== 0)) {
            var alsb = (abm ^ (abm & (((-1) + abm) | 0)));
            var blsb = (bbm ^ (bbm & (((-1) + bbm) | 0)));
            if ((alsb === blsb)) {
              if ((!a.get(ai).subsetOf0__sci_OldHashSet__I__Z(b.get(bi), ((5 + level) | 0)))) {
                return false
              };
              abm = (abm & (~alsb));
              ai = ((1 + ai) | 0)
            };
            bbm = (bbm & (~blsb));
            bi = ((1 + bi) | 0)
          };
          return true
        } else {
          return false
        }
      }
    };
    return false
  }
});
$c_sci_OldHashSet$HashTrieSet.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_OldHashSet$HashTrieSet.prototype.foreach__F1__V = (function(f) {
  var i = 0;
  while ((i < this.elems$5.u.length)) {
    this.elems$5.get(i).foreach__F1__V(f);
    i = ((1 + i) | 0)
  }
});
$c_sci_OldHashSet$HashTrieSet.prototype.size__I = (function() {
  return this.size0$5
});
$c_sci_OldHashSet$HashTrieSet.prototype.iterator__sc_Iterator = (function() {
  return new $c_sci_OldHashSet$HashTrieSet$$anon$2(this)
});
$c_sci_OldHashSet$HashTrieSet.prototype.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet = (function(that, level) {
  var index = (31 & ((that.hash__I() >>> level) | 0));
  var mask = (1 << index);
  var offset = $m_jl_Integer$().bitCount__I__I((this.bitmap$5 & (((-1) + mask) | 0)));
  if (((this.bitmap$5 & mask) !== 0)) {
    var sub = this.elems$5.get(offset);
    var sub1 = sub.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet(that, ((5 + level) | 0));
    if ((sub === sub1)) {
      return this
    } else {
      var elems1 = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [this.elems$5.u.length]);
      $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, 0, elems1, 0, this.elems$5.u.length);
      elems1.set(offset, sub1);
      return new $c_sci_OldHashSet$HashTrieSet(this.bitmap$5, elems1, ((this.size0$5 + ((sub1.size__I() - sub.size__I()) | 0)) | 0))
    }
  } else {
    var elems1$2 = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [((1 + this.elems$5.u.length) | 0)]);
    $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, 0, elems1$2, 0, offset);
    elems1$2.set(offset, that);
    $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, offset, elems1$2, ((1 + offset) | 0), ((this.elems$5.u.length - offset) | 0));
    var bitmap1 = (this.bitmap$5 | mask);
    return new $c_sci_OldHashSet$HashTrieSet(bitmap1, elems1$2, ((this.size0$5 + that.size__I()) | 0))
  }
});
$c_sci_OldHashSet$HashTrieSet.prototype.updated0__O__I__I__sci_OldHashSet = (function(key, hash, level) {
  var index = (31 & ((hash >>> level) | 0));
  var mask = (1 << index);
  var offset = $m_jl_Integer$().bitCount__I__I((this.bitmap$5 & (((-1) + mask) | 0)));
  if (((this.bitmap$5 & mask) !== 0)) {
    var sub = this.elems$5.get(offset);
    var subNew = sub.updated0__O__I__I__sci_OldHashSet(key, hash, ((5 + level) | 0));
    if ((sub === subNew)) {
      return this
    } else {
      var elemsNew = $asArrayOf_sci_OldHashSet($m_ju_Arrays$().copyOf__AO__I__AO(this.elems$5, this.elems$5.u.length), 1);
      elemsNew.set(offset, subNew);
      return new $c_sci_OldHashSet$HashTrieSet(this.bitmap$5, elemsNew, ((this.size0$5 + ((subNew.size__I() - sub.size__I()) | 0)) | 0))
    }
  } else {
    var elemsNew$2 = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [((1 + this.elems$5.u.length) | 0)]);
    $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, 0, elemsNew$2, 0, offset);
    elemsNew$2.set(offset, new $c_sci_OldHashSet$OldHashSet1(key, hash));
    $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, offset, elemsNew$2, ((1 + offset) | 0), ((this.elems$5.u.length - offset) | 0));
    var bitmapNew = (this.bitmap$5 | mask);
    return new $c_sci_OldHashSet$HashTrieSet(bitmapNew, elemsNew$2, ((1 + this.size0$5) | 0))
  }
});
$c_sci_OldHashSet$HashTrieSet.prototype.filter0__F1__Z__I__Asci_OldHashSet__I__sci_OldHashSet = (function(p, negate, level, buffer, offset0) {
  var offset = offset0;
  var rs = 0;
  var kept = 0;
  var i = 0;
  while ((i < this.elems$5.u.length)) {
    var result = this.elems$5.get(i).filter0__F1__Z__I__Asci_OldHashSet__I__sci_OldHashSet(p, negate, ((5 + level) | 0), buffer, offset);
    if ((result !== null)) {
      buffer.set(offset, result);
      offset = ((1 + offset) | 0);
      rs = ((rs + result.size__I()) | 0);
      kept = (kept | (1 << i))
    };
    i = ((1 + i) | 0)
  };
  if ((offset === offset0)) {
    return null
  } else if ((rs === this.size0$5)) {
    return this
  } else if (((offset === ((1 + offset0) | 0)) && (!$is_sci_OldHashSet$HashTrieSet(buffer.get(offset0))))) {
    return buffer.get(offset0)
  } else {
    var length = ((offset - offset0) | 0);
    var elems1 = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [length]);
    $systemArraycopy(buffer, offset0, elems1, 0, length);
    var bitmap1 = ((length === this.elems$5.u.length) ? this.bitmap$5 : $m_sc_Hashing$().keepBits__I__I__I(this.bitmap$5, kept));
    return new $c_sci_OldHashSet$HashTrieSet(bitmap1, elems1, rs)
  }
});
$c_sci_OldHashSet$HashTrieSet.prototype.get0__O__I__I__Z = (function(key, hash, level) {
  var index = (31 & ((hash >>> level) | 0));
  var mask = (1 << index);
  if ((this.bitmap$5 === (-1))) {
    return this.elems$5.get((31 & index)).get0__O__I__I__Z(key, hash, ((5 + level) | 0))
  } else if (((this.bitmap$5 & mask) !== 0)) {
    var offset = $m_jl_Integer$().bitCount__I__I((this.bitmap$5 & (((-1) + mask) | 0)));
    return this.elems$5.get(offset).get0__O__I__I__Z(key, hash, ((5 + level) | 0))
  } else {
    return false
  }
});
$c_sci_OldHashSet$HashTrieSet.prototype.removed0__O__I__I__sci_OldHashSet = (function(key, hash, level) {
  var index = (31 & ((hash >>> level) | 0));
  var mask = (1 << index);
  var offset = $m_jl_Integer$().bitCount__I__I((this.bitmap$5 & (((-1) + mask) | 0)));
  if (((this.bitmap$5 & mask) !== 0)) {
    var sub = this.elems$5.get(offset);
    var subNew = sub.removed0__O__I__I__sci_OldHashSet(key, hash, ((5 + level) | 0));
    if ((sub === subNew)) {
      return this
    } else if ((subNew === null)) {
      var bitmapNew = (this.bitmap$5 ^ mask);
      if ((bitmapNew !== 0)) {
        var elemsNew = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [(((-1) + this.elems$5.u.length) | 0)]);
        $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, 0, elemsNew, 0, offset);
        $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, ((1 + offset) | 0), elemsNew, offset, (((-1) + ((this.elems$5.u.length - offset) | 0)) | 0));
        var sizeNew = ((this.size0$5 - sub.size__I()) | 0);
        return (((elemsNew.u.length === 1) && (!$is_sci_OldHashSet$HashTrieSet(elemsNew.get(0)))) ? elemsNew.get(0) : new $c_sci_OldHashSet$HashTrieSet(bitmapNew, elemsNew, sizeNew))
      } else {
        return null
      }
    } else if (((this.elems$5.u.length === 1) && (!$is_sci_OldHashSet$HashTrieSet(subNew)))) {
      return subNew
    } else {
      var elemsNew$2 = $asArrayOf_sci_OldHashSet($m_ju_Arrays$().copyOf__AO__I__AO(this.elems$5, this.elems$5.u.length), 1);
      elemsNew$2.set(offset, subNew);
      var sizeNew$2 = ((this.size0$5 + ((subNew.size__I() - sub.size__I()) | 0)) | 0);
      return new $c_sci_OldHashSet$HashTrieSet(this.bitmap$5, elemsNew$2, sizeNew$2)
    }
  } else {
    return this
  }
});
$c_sci_OldHashSet$HashTrieSet.prototype.union0__sci_OldHashSet__I__Asci_OldHashSet__I__sci_OldHashSet = (function(that, level, buffer, offset0) {
  if ((that === this)) {
    return this
  } else if ($is_sci_OldHashSet$LeafOldHashSet(that)) {
    var x2 = $as_sci_OldHashSet$LeafOldHashSet(that);
    return this.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet(x2, level)
  } else if ($is_sci_OldHashSet$HashTrieSet(that)) {
    var x3 = $as_sci_OldHashSet$HashTrieSet(that);
    var a = this.elems$5;
    var abm = this.bitmap$5;
    var ai = 0;
    var b = x3.elems$5;
    var bbm = x3.bitmap$5;
    var bi = 0;
    var offset = offset0;
    var rs = 0;
    while (((abm | bbm) !== 0)) {
      var alsb = (abm ^ (abm & (((-1) + abm) | 0)));
      var blsb = (bbm ^ (bbm & (((-1) + bbm) | 0)));
      if ((alsb === blsb)) {
        var sub1 = a.get(ai).union0__sci_OldHashSet__I__Asci_OldHashSet__I__sci_OldHashSet(b.get(bi), ((5 + level) | 0), buffer, offset);
        rs = ((rs + sub1.size__I()) | 0);
        buffer.set(offset, sub1);
        offset = ((1 + offset) | 0);
        abm = (abm & (~alsb));
        ai = ((1 + ai) | 0);
        bbm = (bbm & (~blsb));
        bi = ((1 + bi) | 0)
      } else {
        var this$1 = $m_scg_BitOperations$Int$();
        var i = (((-1) + alsb) | 0);
        var j = (((-1) + blsb) | 0);
        if ($f_scg_BitOperations$Int__unsignedCompare__I__I__Z(this$1, i, j)) {
          var sub1$2 = a.get(ai);
          rs = ((rs + sub1$2.size__I()) | 0);
          buffer.set(offset, sub1$2);
          offset = ((1 + offset) | 0);
          abm = (abm & (~alsb));
          ai = ((1 + ai) | 0)
        } else {
          var sub1$3 = b.get(bi);
          rs = ((rs + sub1$3.size__I()) | 0);
          buffer.set(offset, sub1$3);
          offset = ((1 + offset) | 0);
          bbm = (bbm & (~blsb));
          bi = ((1 + bi) | 0)
        }
      }
    };
    if ((rs === this.size0$5)) {
      return this
    } else if ((rs === x3.size0$5)) {
      return x3
    } else {
      var length = ((offset - offset0) | 0);
      var elems = $newArrayObject($d_sci_OldHashSet.getArrayOf(), [length]);
      $systemArraycopy(buffer, offset0, elems, 0, length);
      return new $c_sci_OldHashSet$HashTrieSet((this.bitmap$5 | x3.bitmap$5), elems, rs)
    }
  } else {
    return this
  }
});
$c_sci_OldHashSet$HashTrieSet.prototype.knownSize__I = (function() {
  return this.size0$5
});
function $is_sci_OldHashSet$HashTrieSet(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_OldHashSet$HashTrieSet)))
}
function $as_sci_OldHashSet$HashTrieSet(obj) {
  return (($is_sci_OldHashSet$HashTrieSet(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.OldHashSet$HashTrieSet"))
}
function $isArrayOf_sci_OldHashSet$HashTrieSet(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_OldHashSet$HashTrieSet)))
}
function $asArrayOf_sci_OldHashSet$HashTrieSet(obj, depth) {
  return (($isArrayOf_sci_OldHashSet$HashTrieSet(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.OldHashSet$HashTrieSet;", depth))
}
var $d_sci_OldHashSet$HashTrieSet = new $TypeData().initClass({
  sci_OldHashSet$HashTrieSet: 0
}, false, "scala.collection.immutable.OldHashSet$HashTrieSet", {
  sci_OldHashSet$HashTrieSet: 1,
  sci_OldHashSet: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_OldHashSet$HashTrieSet.prototype.$classData = $d_sci_OldHashSet$HashTrieSet;
/** @constructor */
function $c_sci_OldHashSet$LeafOldHashSet() {
  /*<skip>*/
}
$c_sci_OldHashSet$LeafOldHashSet.prototype = new $h_sci_OldHashSet();
$c_sci_OldHashSet$LeafOldHashSet.prototype.constructor = $c_sci_OldHashSet$LeafOldHashSet;
/** @constructor */
function $h_sci_OldHashSet$LeafOldHashSet() {
  /*<skip>*/
}
$h_sci_OldHashSet$LeafOldHashSet.prototype = $c_sci_OldHashSet$LeafOldHashSet.prototype;
function $is_sci_OldHashSet$LeafOldHashSet(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_OldHashSet$LeafOldHashSet)))
}
function $as_sci_OldHashSet$LeafOldHashSet(obj) {
  return (($is_sci_OldHashSet$LeafOldHashSet(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.OldHashSet$LeafOldHashSet"))
}
function $isArrayOf_sci_OldHashSet$LeafOldHashSet(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_OldHashSet$LeafOldHashSet)))
}
function $asArrayOf_sci_OldHashSet$LeafOldHashSet(obj, depth) {
  return (($isArrayOf_sci_OldHashSet$LeafOldHashSet(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.OldHashSet$LeafOldHashSet;", depth))
}
function $is_scm_Set(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.scm_Set)))
}
function $as_scm_Set(obj) {
  return (($is_scm_Set(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.mutable.Set"))
}
function $isArrayOf_scm_Set(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.scm_Set)))
}
function $asArrayOf_scm_Set(obj, depth) {
  return (($isArrayOf_scm_Set(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.mutable.Set;", depth))
}
/** @constructor */
function $c_sci_HashMap(rootNode, cachedJavaKeySetHashCode) {
  this.rootNode$4 = null;
  this.cachedJavaKeySetHashCode$4 = 0;
  this.rootNode$4 = rootNode;
  this.cachedJavaKeySetHashCode$4 = cachedJavaKeySetHashCode
}
$c_sci_HashMap.prototype = new $h_sci_AbstractMap();
$c_sci_HashMap.prototype.constructor = $c_sci_HashMap;
/** @constructor */
function $h_sci_HashMap() {
  /*<skip>*/
}
$h_sci_HashMap.prototype = $c_sci_HashMap.prototype;
$c_sci_HashMap.prototype.head__O = (function() {
  return $as_T2(this.iterator__sc_Iterator().next__O())
});
$c_sci_HashMap.prototype.isEmpty__Z = (function() {
  return (this.rootNode$4.size__I() === 0)
});
$c_sci_HashMap.prototype.equals__O__Z = (function(that) {
  if ($is_sci_HashMap(that)) {
    var x2 = $as_sci_HashMap(that);
    if ((this === x2)) {
      return true
    } else if (((this.rootNode$4.size__I() === x2.rootNode$4.size__I()) && (this.cachedJavaKeySetHashCode$4 === x2.cachedJavaKeySetHashCode$4))) {
      var x = this.rootNode$4;
      var x$2 = x2.rootNode$4;
      return ((x === null) ? (x$2 === null) : x.equals__O__Z(x$2))
    } else {
      return false
    }
  } else {
    return $f_sc_Map__equals__O__Z(this, that)
  }
});
$c_sci_HashMap.prototype.getOrElse__O__F0__O = (function(key, $default) {
  var keyUnimprovedHash = $m_sr_Statics$().anyHash__O__I(key);
  var keyHash = $m_sc_Hashing$().improve__I__I(keyUnimprovedHash);
  return this.rootNode$4.getOrElse__O__I__I__I__F0__O(key, keyUnimprovedHash, keyHash, 0, $default)
});
$c_sci_HashMap.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return this.updated__O__O__sci_HashMap(key, value)
});
$c_sci_HashMap.prototype.foreach__F1__V = (function(f) {
  this.rootNode$4.foreach__F1__V(f)
});
$c_sci_HashMap.prototype.updated__O__O__sci_HashMap = (function(key, value) {
  var keyUnimprovedHash = $m_sr_Statics$().anyHash__O__I(key);
  var keyHash = $m_sc_Hashing$().improve__I__I(keyUnimprovedHash);
  var newRootNode = this.rootNode$4.updated__O__O__I__I__I__sci_MapNode(key, value, keyUnimprovedHash, keyHash, 0);
  if ((newRootNode !== this.rootNode$4)) {
    var replaced = (this.rootNode$4.size__I() === newRootNode.size__I());
    var newCachedJavaKeySetHashCode = ((this.cachedJavaKeySetHashCode$4 + (replaced ? 0 : keyHash)) | 0);
    $m_sci_HashMap$();
    return new $c_sci_HashMap(newRootNode, newCachedJavaKeySetHashCode)
  } else {
    return this
  }
});
$c_sci_HashMap.prototype.size__I = (function() {
  return this.rootNode$4.size__I()
});
$c_sci_HashMap.prototype.iterator__sc_Iterator = (function() {
  return (this.isEmpty__Z() ? $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f : new $c_sci_MapKeyValueTupleIterator(this.rootNode$4))
});
$c_sci_HashMap.prototype.tail__sci_HashMap = (function() {
  var key = $as_T2(this.iterator__sc_Iterator().next__O()).$$und1$f;
  return this.remove__O__sci_HashMap(key)
});
$c_sci_HashMap.prototype.get__O__s_Option = (function(key) {
  var keyUnimprovedHash = $m_sr_Statics$().anyHash__O__I(key);
  var keyHash = $m_sc_Hashing$().improve__I__I(keyUnimprovedHash);
  return this.rootNode$4.get__O__I__I__I__s_Option(key, keyUnimprovedHash, keyHash, 0)
});
$c_sci_HashMap.prototype.remove__O__sci_HashMap = (function(key) {
  var keyUnimprovedHash = $m_sr_Statics$().anyHash__O__I(key);
  var keyHash = $m_sc_Hashing$().improve__I__I(keyUnimprovedHash);
  var newRootNode = this.rootNode$4.removed__O__I__I__I__sci_MapNode(key, keyUnimprovedHash, keyHash, 0);
  if ((newRootNode !== this.rootNode$4)) {
    $m_sci_HashMap$();
    var cachedJavaHashCode = ((this.cachedJavaKeySetHashCode$4 - keyHash) | 0);
    return new $c_sci_HashMap(newRootNode, cachedJavaHashCode)
  } else {
    return this
  }
});
$c_sci_HashMap.prototype.tail__O = (function() {
  return this.tail__sci_HashMap()
});
$c_sci_HashMap.prototype.hashCode__I = (function() {
  var hashIterator = new $c_sci_MapKeyValueTupleHashIterator(this.rootNode$4);
  var hash = $m_s_util_hashing_MurmurHash3$().unorderedHash__sc_IterableOnce__I__I(hashIterator, $m_s_util_hashing_MurmurHash3$().mapSeed$2);
  return hash
});
$c_sci_HashMap.prototype.className__T = (function() {
  return "HashMap"
});
$c_sci_HashMap.prototype.knownSize__I = (function() {
  return this.rootNode$4.size__I()
});
$c_sci_HashMap.prototype.mapFactory__sc_MapFactory = (function() {
  return $m_sci_HashMap$()
});
function $is_sci_HashMap(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_HashMap)))
}
function $as_sci_HashMap(obj) {
  return (($is_sci_HashMap(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.HashMap"))
}
function $isArrayOf_sci_HashMap(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_HashMap)))
}
function $asArrayOf_sci_HashMap(obj, depth) {
  return (($isArrayOf_sci_HashMap(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.HashMap;", depth))
}
var $d_sci_HashMap = new $TypeData().initClass({
  sci_HashMap: 0
}, false, "scala.collection.immutable.HashMap", {
  sci_HashMap: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sc_StrictOptimizedMapOps: 1
});
$c_sci_HashMap.prototype.$classData = $d_sci_HashMap;
/** @constructor */
function $c_sci_OldHashMap() {
  /*<skip>*/
}
$c_sci_OldHashMap.prototype = new $h_sci_AbstractMap();
$c_sci_OldHashMap.prototype.constructor = $c_sci_OldHashMap;
/** @constructor */
function $h_sci_OldHashMap() {
  /*<skip>*/
}
$h_sci_OldHashMap.prototype = $c_sci_OldHashMap.prototype;
$c_sci_OldHashMap.prototype.$$plus__T2__sci_MapOps = (function(kv) {
  return this.updated__O__O__sci_OldHashMap(kv.$$und1$f, kv.$$und2$f)
});
$c_sci_OldHashMap.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return this.updated__O__O__sci_OldHashMap(key, value)
});
$c_sci_OldHashMap.prototype.tail__sci_OldHashMap = (function() {
  var key = $as_T2(this.head__O()).$$und1$f;
  return this.remove__O__sci_OldHashMap(key)
});
$c_sci_OldHashMap.prototype.updated__O__O__sci_OldHashMap = (function(key, value) {
  return this.updated0__O__I__I__O__T2__sci_OldHashMap$Merger__sci_OldHashMap(key, $m_sc_Hashing$().computeHash__O__I(key), 0, value, null, null)
});
$c_sci_OldHashMap.prototype.remove__O__sci_OldHashMap = (function(key) {
  return this.removed0__O__I__I__sci_OldHashMap(key, $m_sc_Hashing$().computeHash__O__I(key), 0)
});
$c_sci_OldHashMap.prototype.get__O__s_Option = (function(key) {
  return this.get0__O__I__I__s_Option(key, $m_sc_Hashing$().computeHash__O__I(key), 0)
});
$c_sci_OldHashMap.prototype.tail__O = (function() {
  return this.tail__sci_OldHashMap()
});
$c_sci_OldHashMap.prototype.className__T = (function() {
  return "OldHashMap"
});
$c_sci_OldHashMap.prototype.mapFactory__sc_MapFactory = (function() {
  return $m_sci_OldHashMap$()
});
function $is_sci_OldHashMap(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_OldHashMap)))
}
function $as_sci_OldHashMap(obj) {
  return (($is_sci_OldHashMap(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.OldHashMap"))
}
function $isArrayOf_sci_OldHashMap(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_OldHashMap)))
}
function $asArrayOf_sci_OldHashMap(obj, depth) {
  return (($isArrayOf_sci_OldHashMap(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.OldHashMap;", depth))
}
var $d_sci_OldHashMap = new $TypeData().initClass({
  sci_OldHashMap: 0
}, false, "scala.collection.immutable.OldHashMap", {
  sci_OldHashMap: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sc_StrictOptimizedMapOps: 1
});
$c_sci_OldHashMap.prototype.$classData = $d_sci_OldHashMap;
/** @constructor */
function $c_sci_OldHashSet$OldHashSet1(key, hash) {
  this.key$6 = null;
  this.hash$6 = 0;
  this.key$6 = key;
  this.hash$6 = hash
}
$c_sci_OldHashSet$OldHashSet1.prototype = new $h_sci_OldHashSet$LeafOldHashSet();
$c_sci_OldHashSet$OldHashSet1.prototype.constructor = $c_sci_OldHashSet$OldHashSet1;
/** @constructor */
function $h_sci_OldHashSet$OldHashSet1() {
  /*<skip>*/
}
$h_sci_OldHashSet$OldHashSet1.prototype = $c_sci_OldHashSet$OldHashSet1.prototype;
$c_sci_OldHashSet$OldHashSet1.prototype.head__O = (function() {
  return this.key$6
});
$c_sci_OldHashSet$OldHashSet1.prototype.subsetOf0__sci_OldHashSet__I__Z = (function(that, level) {
  return that.get0__O__I__I__Z(this.key$6, this.hash$6, level)
});
$c_sci_OldHashSet$OldHashSet1.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_OldHashSet$OldHashSet1.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(this.key$6)
});
$c_sci_OldHashSet$OldHashSet1.prototype.tail__sci_OldHashSet = (function() {
  return $m_sci_OldHashSet$EmptyOldHashSet$()
});
$c_sci_OldHashSet$OldHashSet1.prototype.size__I = (function() {
  return 1
});
$c_sci_OldHashSet$OldHashSet1.prototype.iterator__sc_Iterator = (function() {
  $m_sc_Iterator$();
  var a = this.key$6;
  return new $c_sc_Iterator$$anon$19(a)
});
$c_sci_OldHashSet$OldHashSet1.prototype.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet = (function(that, level) {
  if ((that.hash__I() !== this.hash$6)) {
    return $m_sci_OldHashSet$().scala$collection$immutable$OldHashSet$$makeHashTrieSet__I__sci_OldHashSet__I__sci_OldHashSet__I__sci_OldHashSet$HashTrieSet(this.hash$6, this, that.hash__I(), that, level)
  } else if ($is_sci_OldHashSet$OldHashSet1(that)) {
    var x2 = $as_sci_OldHashSet$OldHashSet1(that);
    if ($m_sr_BoxesRunTime$().equals__O__O__Z(this.key$6, x2.key$6)) {
      return this
    } else {
      var jsx$1 = this.hash$6;
      var this$2 = $m_sci_ListSet$EmptyListSet$();
      var elem = this.key$6;
      var this$3 = new $c_sci_ListSet$Node(this$2, elem);
      var elem$1 = x2.key$6;
      return new $c_sci_OldHashSet$OldHashSetCollision1(jsx$1, this$3.incl__O__sci_ListSet(elem$1))
    }
  } else if ($is_sci_OldHashSet$OldHashSetCollision1(that)) {
    var x3 = $as_sci_OldHashSet$OldHashSetCollision1(that);
    var this$4 = x3.ks$6;
    var elem$2 = this.key$6;
    var ks1 = this$4.incl__O__sci_ListSet(elem$2);
    return ((ks1.size__I() === x3.ks$6.size__I()) ? x3 : new $c_sci_OldHashSet$OldHashSetCollision1(this.hash$6, ks1))
  } else {
    throw new $c_s_MatchError(that)
  }
});
$c_sci_OldHashSet$OldHashSet1.prototype.updated0__O__I__I__sci_OldHashSet = (function(key, hash, level) {
  if (((hash === this.hash$6) && $m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key$6))) {
    return this
  } else if ((hash !== this.hash$6)) {
    return $m_sci_OldHashSet$().scala$collection$immutable$OldHashSet$$makeHashTrieSet__I__sci_OldHashSet__I__sci_OldHashSet__I__sci_OldHashSet$HashTrieSet(this.hash$6, this, hash, new $c_sci_OldHashSet$OldHashSet1(key, hash), level)
  } else {
    var this$2 = $m_sci_ListSet$EmptyListSet$();
    var elem = this.key$6;
    var this$3 = new $c_sci_ListSet$Node(this$2, elem);
    return new $c_sci_OldHashSet$OldHashSetCollision1(hash, this$3.incl__O__sci_ListSet(key))
  }
});
$c_sci_OldHashSet$OldHashSet1.prototype.tail__O = (function() {
  return $m_sci_OldHashSet$EmptyOldHashSet$()
});
$c_sci_OldHashSet$OldHashSet1.prototype.hash__I = (function() {
  return this.hash$6
});
$c_sci_OldHashSet$OldHashSet1.prototype.filter0__F1__Z__I__Asci_OldHashSet__I__sci_OldHashSet = (function(p, negate, level, buffer, offset0) {
  return ((negate !== $uZ(p.apply__O__O(this.key$6))) ? this : null)
});
$c_sci_OldHashSet$OldHashSet1.prototype.union0__sci_OldHashSet__I__Asci_OldHashSet__I__sci_OldHashSet = (function(that, level, buffer, offset0) {
  return that.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet(this, level)
});
$c_sci_OldHashSet$OldHashSet1.prototype.get0__O__I__I__Z = (function(key, hash, level) {
  return ((hash === this.hash$6) && $m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key$6))
});
$c_sci_OldHashSet$OldHashSet1.prototype.removed0__O__I__I__sci_OldHashSet = (function(key, hash, level) {
  return (((hash === this.hash$6) && $m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key$6)) ? null : this)
});
$c_sci_OldHashSet$OldHashSet1.prototype.knownSize__I = (function() {
  return 1
});
function $is_sci_OldHashSet$OldHashSet1(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_OldHashSet$OldHashSet1)))
}
function $as_sci_OldHashSet$OldHashSet1(obj) {
  return (($is_sci_OldHashSet$OldHashSet1(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.OldHashSet$OldHashSet1"))
}
function $isArrayOf_sci_OldHashSet$OldHashSet1(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_OldHashSet$OldHashSet1)))
}
function $asArrayOf_sci_OldHashSet$OldHashSet1(obj, depth) {
  return (($isArrayOf_sci_OldHashSet$OldHashSet1(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.OldHashSet$OldHashSet1;", depth))
}
var $d_sci_OldHashSet$OldHashSet1 = new $TypeData().initClass({
  sci_OldHashSet$OldHashSet1: 0
}, false, "scala.collection.immutable.OldHashSet$OldHashSet1", {
  sci_OldHashSet$OldHashSet1: 1,
  sci_OldHashSet$LeafOldHashSet: 1,
  sci_OldHashSet: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_OldHashSet$OldHashSet1.prototype.$classData = $d_sci_OldHashSet$OldHashSet1;
/** @constructor */
function $c_sci_OldHashSet$OldHashSetCollision1(hash, ks) {
  this.hash$6 = 0;
  this.ks$6 = null;
  this.hash$6 = hash;
  this.ks$6 = ks
}
$c_sci_OldHashSet$OldHashSetCollision1.prototype = new $h_sci_OldHashSet$LeafOldHashSet();
$c_sci_OldHashSet$OldHashSetCollision1.prototype.constructor = $c_sci_OldHashSet$OldHashSetCollision1;
/** @constructor */
function $h_sci_OldHashSet$OldHashSetCollision1() {
  /*<skip>*/
}
$h_sci_OldHashSet$OldHashSetCollision1.prototype = $c_sci_OldHashSet$OldHashSetCollision1.prototype;
$c_sci_OldHashSet$OldHashSetCollision1.prototype.subsetOf0__sci_OldHashSet__I__Z = (function(that, level) {
  var this$1 = this.ks$6;
  var res = true;
  var it = this$1.iterator__sc_Iterator();
  while ((res && it.hasNext__Z())) {
    var arg1 = it.next__O();
    res = that.get0__O__I__I__Z(arg1, this.hash$6, level)
  };
  return res
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.foreach__F1__V = (function(f) {
  var this$1 = this.ks$6;
  $f_sc_IterableOnceOps__foreach__F1__V(this$1, f)
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.size__I = (function() {
  return this.ks$6.size__I()
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.iterator__sc_Iterator = (function() {
  return this.ks$6.iterator__sc_Iterator()
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet = (function(that, level) {
  if ((that.hash__I() !== this.hash$6)) {
    return $m_sci_OldHashSet$().scala$collection$immutable$OldHashSet$$makeHashTrieSet__I__sci_OldHashSet__I__sci_OldHashSet__I__sci_OldHashSet$HashTrieSet(this.hash$6, this, that.hash__I(), that, level)
  } else if ($is_sci_OldHashSet$OldHashSet1(that)) {
    var x2 = $as_sci_OldHashSet$OldHashSet1(that);
    var this$1 = this.ks$6;
    var elem = x2.key$6;
    var ks1 = this$1.incl__O__sci_ListSet(elem);
    return ((ks1.size__I() === this.ks$6.size__I()) ? this : new $c_sci_OldHashSet$OldHashSetCollision1(this.hash$6, ks1))
  } else if ($is_sci_OldHashSet$OldHashSetCollision1(that)) {
    var x3 = $as_sci_OldHashSet$OldHashSetCollision1(that);
    var this$2 = this.ks$6;
    var that$1 = x3.ks$6;
    var ks1$2 = $as_sci_ListSet($f_sci_SetOps__concat__sc_IterableOnce__sci_SetOps(this$2, that$1));
    var x1$2 = ks1$2.size__I();
    return ((x1$2 === this.ks$6.size__I()) ? this : ((x1$2 === x3.ks$6.size__I()) ? x3 : new $c_sci_OldHashSet$OldHashSetCollision1(this.hash$6, ks1$2)))
  } else {
    throw new $c_s_MatchError(that)
  }
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.updated0__O__I__I__sci_OldHashSet = (function(key, hash, level) {
  if ((hash === this.hash$6)) {
    var this$1 = this.ks$6;
    return new $c_sci_OldHashSet$OldHashSetCollision1(hash, this$1.incl__O__sci_ListSet(key))
  } else {
    return $m_sci_OldHashSet$().scala$collection$immutable$OldHashSet$$makeHashTrieSet__I__sci_OldHashSet__I__sci_OldHashSet__I__sci_OldHashSet$HashTrieSet(this.hash$6, this, hash, new $c_sci_OldHashSet$OldHashSet1(key, hash), level)
  }
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.hash__I = (function() {
  return this.hash$6
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.get0__O__I__I__Z = (function(key, hash, level) {
  return ((hash === this.hash$6) && this.ks$6.contains__O__Z(key))
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.removed0__O__I__I__sci_OldHashSet = (function(key, hash, level) {
  if ((hash === this.hash$6)) {
    var this$1 = this.ks$6;
    var ks1 = this$1.excl__O__sci_ListSet(key);
    var x1 = ks1.size__I();
    switch (x1) {
      case 0: {
        return null;
        break
      }
      case 1: {
        return new $c_sci_OldHashSet$OldHashSet1(ks1.iterator__sc_Iterator().next__O(), hash);
        break
      }
      default: {
        return ((x1 === this.ks$6.size__I()) ? this : new $c_sci_OldHashSet$OldHashSetCollision1(hash, ks1))
      }
    }
  } else {
    return this
  }
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.filter0__F1__Z__I__Asci_OldHashSet__I__sci_OldHashSet = (function(p, negate, level, buffer, offset0) {
  if (negate) {
    var this$1 = this.ks$6;
    var ks1 = $as_sci_ListSet($f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this$1, p, true))
  } else {
    var this$2 = this.ks$6;
    var ks1 = $as_sci_ListSet($f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this$2, p, false))
  };
  var x1 = ks1.size__I();
  switch (x1) {
    case 0: {
      return null;
      break
    }
    case 1: {
      return new $c_sci_OldHashSet$OldHashSet1(ks1.iterator__sc_Iterator().next__O(), this.hash$6);
      break
    }
    default: {
      return ((x1 === this.ks$6.size__I()) ? this : new $c_sci_OldHashSet$OldHashSetCollision1(this.hash$6, ks1))
    }
  }
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.union0__sci_OldHashSet__I__Asci_OldHashSet__I__sci_OldHashSet = (function(that, level, buffer, offset0) {
  if ($is_sci_OldHashSet$LeafOldHashSet(that)) {
    var x2 = $as_sci_OldHashSet$LeafOldHashSet(that);
    return this.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet(x2, level)
  } else if ($is_sci_OldHashSet$HashTrieSet(that)) {
    var x3 = $as_sci_OldHashSet$HashTrieSet(that);
    return x3.union0__sci_OldHashSet$LeafOldHashSet__I__sci_OldHashSet(this, level)
  } else {
    return this
  }
});
function $is_sci_OldHashSet$OldHashSetCollision1(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_OldHashSet$OldHashSetCollision1)))
}
function $as_sci_OldHashSet$OldHashSetCollision1(obj) {
  return (($is_sci_OldHashSet$OldHashSetCollision1(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.OldHashSet$OldHashSetCollision1"))
}
function $isArrayOf_sci_OldHashSet$OldHashSetCollision1(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_OldHashSet$OldHashSetCollision1)))
}
function $asArrayOf_sci_OldHashSet$OldHashSetCollision1(obj, depth) {
  return (($isArrayOf_sci_OldHashSet$OldHashSetCollision1(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.OldHashSet$OldHashSetCollision1;", depth))
}
var $d_sci_OldHashSet$OldHashSetCollision1 = new $TypeData().initClass({
  sci_OldHashSet$OldHashSetCollision1: 0
}, false, "scala.collection.immutable.OldHashSet$OldHashSetCollision1", {
  sci_OldHashSet$OldHashSetCollision1: 1,
  sci_OldHashSet$LeafOldHashSet: 1,
  sci_OldHashSet: 1,
  sci_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  sci_Set: 1,
  sci_Iterable: 1,
  sci_SetOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_OldHashSet$OldHashSetCollision1.prototype.$classData = $d_sci_OldHashSet$OldHashSetCollision1;
/** @constructor */
function $c_scm_AbstractSeq() {
  /*<skip>*/
}
$c_scm_AbstractSeq.prototype = new $h_sc_AbstractSeq();
$c_scm_AbstractSeq.prototype.constructor = $c_scm_AbstractSeq;
/** @constructor */
function $h_scm_AbstractSeq() {
  /*<skip>*/
}
$h_scm_AbstractSeq.prototype = $c_scm_AbstractSeq.prototype;
/** @constructor */
function $c_sci_ListMap() {
  /*<skip>*/
}
$c_sci_ListMap.prototype = new $h_sci_AbstractMap();
$c_sci_ListMap.prototype.constructor = $c_sci_ListMap;
/** @constructor */
function $h_sci_ListMap() {
  /*<skip>*/
}
$h_sci_ListMap.prototype = $c_sci_ListMap.prototype;
$c_sci_ListMap.prototype.value__O = (function() {
  throw new $c_ju_NoSuchElementException().init___T("value of empty map")
});
$c_sci_ListMap.prototype.isEmpty__Z = (function() {
  return true
});
$c_sci_ListMap.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return this.updated__O__O__sci_ListMap(key, value)
});
$c_sci_ListMap.prototype.size__I = (function() {
  return 0
});
$c_sci_ListMap.prototype.iterator__sc_Iterator = (function() {
  var curr = this;
  var res = $m_sci_Nil$();
  while ((!curr.isEmpty__Z())) {
    var rassoc$1 = new $c_T2(curr.key__O(), curr.value__O());
    var this$1 = res;
    res = new $c_sci_$colon$colon(rassoc$1, this$1);
    curr = curr.next__sci_ListMap()
  };
  return res.iterator__sc_Iterator()
});
$c_sci_ListMap.prototype.key__O = (function() {
  throw new $c_ju_NoSuchElementException().init___T("key of empty map")
});
$c_sci_ListMap.prototype.updated__O__O__sci_ListMap = (function(key, value) {
  return new $c_sci_ListMap$Node(this, key, value)
});
$c_sci_ListMap.prototype.get__O__s_Option = (function(key) {
  return $m_s_None$()
});
$c_sci_ListMap.prototype.remove__O__sci_ListMap = (function(key) {
  return this
});
$c_sci_ListMap.prototype.className__T = (function() {
  return "ListMap"
});
$c_sci_ListMap.prototype.next__sci_ListMap = (function() {
  throw new $c_ju_NoSuchElementException().init___T("next of empty map")
});
$c_sci_ListMap.prototype.mapFactory__sc_MapFactory = (function() {
  return $m_sci_ListMap$()
});
$c_sci_ListMap.prototype.knownSize__I = (function() {
  return 0
});
function $is_sci_ListMap(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_ListMap)))
}
function $as_sci_ListMap(obj) {
  return (($is_sci_ListMap(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.ListMap"))
}
function $isArrayOf_sci_ListMap(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_ListMap)))
}
function $asArrayOf_sci_ListMap(obj, depth) {
  return (($isArrayOf_sci_ListMap(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.ListMap;", depth))
}
/** @constructor */
function $c_sci_OldHashMap$EmptyOldHashMap$() {
  /*<skip>*/
}
$c_sci_OldHashMap$EmptyOldHashMap$.prototype = new $h_sci_OldHashMap();
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.constructor = $c_sci_OldHashMap$EmptyOldHashMap$;
/** @constructor */
function $h_sci_OldHashMap$EmptyOldHashMap$() {
  /*<skip>*/
}
$h_sci_OldHashMap$EmptyOldHashMap$.prototype = $c_sci_OldHashMap$EmptyOldHashMap$.prototype;
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.updated0__O__I__I__O__T2__sci_OldHashMap$Merger__sci_OldHashMap = (function(key, hash, level, value, kv, merger) {
  return new $c_sci_OldHashMap$OldHashMap1(key, hash, value, kv)
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.head__O = (function() {
  return this.head__T2()
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.isEmpty__Z = (function() {
  return true
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.get0__O__I__I__s_Option = (function(key, hash, level) {
  return $m_s_None$()
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.tail__sci_OldHashMap = (function() {
  throw new $c_ju_NoSuchElementException().init___T("Empty Map")
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.foreach__F1__V = (function(f) {
  /*<skip>*/
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.iterator__sc_Iterator = (function() {
  return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.head__T2 = (function() {
  throw new $c_ju_NoSuchElementException().init___T("Empty Map")
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.tail__O = (function() {
  return this.tail__sci_OldHashMap()
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.removed0__O__I__I__sci_OldHashMap = (function(key, hash, level) {
  return this
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.knownSize__I = (function() {
  return 0
});
var $d_sci_OldHashMap$EmptyOldHashMap$ = new $TypeData().initClass({
  sci_OldHashMap$EmptyOldHashMap$: 0
}, false, "scala.collection.immutable.OldHashMap$EmptyOldHashMap$", {
  sci_OldHashMap$EmptyOldHashMap$: 1,
  sci_OldHashMap: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sc_StrictOptimizedMapOps: 1
});
$c_sci_OldHashMap$EmptyOldHashMap$.prototype.$classData = $d_sci_OldHashMap$EmptyOldHashMap$;
var $n_sci_OldHashMap$EmptyOldHashMap$ = (void 0);
function $m_sci_OldHashMap$EmptyOldHashMap$() {
  if ((!$n_sci_OldHashMap$EmptyOldHashMap$)) {
    $n_sci_OldHashMap$EmptyOldHashMap$ = new $c_sci_OldHashMap$EmptyOldHashMap$()
  };
  return $n_sci_OldHashMap$EmptyOldHashMap$
}
/** @constructor */
function $c_sci_OldHashMap$HashTrieMap(bitmap, elems, size0) {
  this.bitmap$5 = 0;
  this.elems$5 = null;
  this.size0$5 = 0;
  this.bitmap$5 = bitmap;
  this.elems$5 = elems;
  this.size0$5 = size0
}
$c_sci_OldHashMap$HashTrieMap.prototype = new $h_sci_OldHashMap();
$c_sci_OldHashMap$HashTrieMap.prototype.constructor = $c_sci_OldHashMap$HashTrieMap;
/** @constructor */
function $h_sci_OldHashMap$HashTrieMap() {
  /*<skip>*/
}
$h_sci_OldHashMap$HashTrieMap.prototype = $c_sci_OldHashMap$HashTrieMap.prototype;
$c_sci_OldHashMap$HashTrieMap.prototype.updated0__O__I__I__O__T2__sci_OldHashMap$Merger__sci_OldHashMap = (function(key, hash, level, value, kv, merger) {
  var index = (31 & ((hash >>> level) | 0));
  var mask = (1 << index);
  var offset = $m_jl_Integer$().bitCount__I__I((this.bitmap$5 & (((-1) + mask) | 0)));
  if (((this.bitmap$5 & mask) !== 0)) {
    var sub = this.elems$5.get(offset);
    var subNew = sub.updated0__O__I__I__O__T2__sci_OldHashMap$Merger__sci_OldHashMap(key, hash, ((5 + level) | 0), value, kv, merger);
    if ((subNew === sub)) {
      return this
    } else {
      var elemsNew = $newArrayObject($d_sci_OldHashMap.getArrayOf(), [this.elems$5.u.length]);
      $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, 0, elemsNew, 0, this.elems$5.u.length);
      elemsNew.set(offset, subNew);
      return new $c_sci_OldHashMap$HashTrieMap(this.bitmap$5, elemsNew, ((this.size0$5 + ((subNew.size__I() - sub.size__I()) | 0)) | 0))
    }
  } else {
    var elemsNew$2 = $newArrayObject($d_sci_OldHashMap.getArrayOf(), [((1 + this.elems$5.u.length) | 0)]);
    $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, 0, elemsNew$2, 0, offset);
    elemsNew$2.set(offset, new $c_sci_OldHashMap$OldHashMap1(key, hash, value, kv));
    $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, offset, elemsNew$2, ((1 + offset) | 0), ((this.elems$5.u.length - offset) | 0));
    return new $c_sci_OldHashMap$HashTrieMap((this.bitmap$5 | mask), elemsNew$2, ((1 + this.size0$5) | 0))
  }
});
$c_sci_OldHashMap$HashTrieMap.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_OldHashMap$HashTrieMap.prototype.get0__O__I__I__s_Option = (function(key, hash, level) {
  var index = (31 & ((hash >>> level) | 0));
  if ((this.bitmap$5 === (-1))) {
    return this.elems$5.get(index).get0__O__I__I__s_Option(key, hash, ((5 + level) | 0))
  } else {
    var mask = (1 << index);
    if (((this.bitmap$5 & mask) !== 0)) {
      var offset = $m_jl_Integer$().bitCount__I__I((this.bitmap$5 & (((-1) + mask) | 0)));
      return this.elems$5.get(offset).get0__O__I__I__s_Option(key, hash, ((5 + level) | 0))
    } else {
      return $m_s_None$()
    }
  }
});
$c_sci_OldHashMap$HashTrieMap.prototype.foreach__F1__V = (function(f) {
  var i = 0;
  while ((i < this.elems$5.u.length)) {
    this.elems$5.get(i).foreach__F1__V(f);
    i = ((1 + i) | 0)
  }
});
$c_sci_OldHashMap$HashTrieMap.prototype.size__I = (function() {
  return this.size0$5
});
$c_sci_OldHashMap$HashTrieMap.prototype.iterator__sc_Iterator = (function() {
  return new $c_sci_OldHashMap$HashTrieMap$$anon$4(this)
});
$c_sci_OldHashMap$HashTrieMap.prototype.removed0__O__I__I__sci_OldHashMap = (function(key, hash, level) {
  var index = (31 & ((hash >>> level) | 0));
  var mask = (1 << index);
  var offset = $m_jl_Integer$().bitCount__I__I((this.bitmap$5 & (((-1) + mask) | 0)));
  if (((this.bitmap$5 & mask) !== 0)) {
    var sub = this.elems$5.get(offset);
    var subNew = sub.removed0__O__I__I__sci_OldHashMap(key, hash, ((5 + level) | 0));
    if ((subNew === sub)) {
      return this
    } else if (subNew.isEmpty__Z()) {
      var bitmapNew = (this.bitmap$5 ^ mask);
      if ((bitmapNew !== 0)) {
        var elemsNew = $newArrayObject($d_sci_OldHashMap.getArrayOf(), [(((-1) + this.elems$5.u.length) | 0)]);
        $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, 0, elemsNew, 0, offset);
        $m_s_Array$().copy__O__I__O__I__I__V(this.elems$5, ((1 + offset) | 0), elemsNew, offset, (((-1) + ((this.elems$5.u.length - offset) | 0)) | 0));
        var sizeNew = ((this.size0$5 - sub.size__I()) | 0);
        return (((elemsNew.u.length === 1) && (!$is_sci_OldHashMap$HashTrieMap(elemsNew.get(0)))) ? elemsNew.get(0) : new $c_sci_OldHashMap$HashTrieMap(bitmapNew, elemsNew, sizeNew))
      } else {
        $m_sci_OldHashMap$();
        return $m_sci_OldHashMap$EmptyOldHashMap$()
      }
    } else if (((this.elems$5.u.length === 1) && (!$is_sci_OldHashMap$HashTrieMap(subNew)))) {
      return subNew
    } else {
      var elemsNew$2 = $asArrayOf_sci_OldHashMap($m_ju_Arrays$().copyOf__AO__I__AO(this.elems$5, this.elems$5.u.length), 1);
      elemsNew$2.set(offset, subNew);
      var sizeNew$2 = ((this.size0$5 + ((subNew.size__I() - sub.size__I()) | 0)) | 0);
      return new $c_sci_OldHashMap$HashTrieMap(this.bitmap$5, elemsNew$2, sizeNew$2)
    }
  } else {
    return this
  }
});
$c_sci_OldHashMap$HashTrieMap.prototype.knownSize__I = (function() {
  return this.size0$5
});
function $is_sci_OldHashMap$HashTrieMap(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_OldHashMap$HashTrieMap)))
}
function $as_sci_OldHashMap$HashTrieMap(obj) {
  return (($is_sci_OldHashMap$HashTrieMap(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.OldHashMap$HashTrieMap"))
}
function $isArrayOf_sci_OldHashMap$HashTrieMap(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_OldHashMap$HashTrieMap)))
}
function $asArrayOf_sci_OldHashMap$HashTrieMap(obj, depth) {
  return (($isArrayOf_sci_OldHashMap$HashTrieMap(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.OldHashMap$HashTrieMap;", depth))
}
var $d_sci_OldHashMap$HashTrieMap = new $TypeData().initClass({
  sci_OldHashMap$HashTrieMap: 0
}, false, "scala.collection.immutable.OldHashMap$HashTrieMap", {
  sci_OldHashMap$HashTrieMap: 1,
  sci_OldHashMap: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sc_StrictOptimizedMapOps: 1
});
$c_sci_OldHashMap$HashTrieMap.prototype.$classData = $d_sci_OldHashMap$HashTrieMap;
/** @constructor */
function $c_sci_OldHashMap$OldHashMap1(key, hash, value, kv) {
  this.key$5 = null;
  this.hash$5 = 0;
  this.value$5 = null;
  this.kv$5 = null;
  this.key$5 = key;
  this.hash$5 = hash;
  this.value$5 = value;
  this.kv$5 = kv
}
$c_sci_OldHashMap$OldHashMap1.prototype = new $h_sci_OldHashMap();
$c_sci_OldHashMap$OldHashMap1.prototype.constructor = $c_sci_OldHashMap$OldHashMap1;
/** @constructor */
function $h_sci_OldHashMap$OldHashMap1() {
  /*<skip>*/
}
$h_sci_OldHashMap$OldHashMap1.prototype = $c_sci_OldHashMap$OldHashMap1.prototype;
$c_sci_OldHashMap$OldHashMap1.prototype.updated0__O__I__I__O__T2__sci_OldHashMap$Merger__sci_OldHashMap = (function(key, hash, level, value, kv, merger) {
  if (((hash === this.hash$5) && $m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key$5))) {
    if ((merger === null)) {
      return ((this.value$5 === value) ? this : new $c_sci_OldHashMap$OldHashMap1(key, hash, value, kv))
    } else {
      var nkv = merger.apply__T2__T2__T2(this.ensurePair__T2(), ((kv !== null) ? kv : new $c_T2(key, value)));
      return new $c_sci_OldHashMap$OldHashMap1(nkv.$$und1$f, hash, nkv.$$und2$f, nkv)
    }
  } else if ((hash !== this.hash$5)) {
    var that = new $c_sci_OldHashMap$OldHashMap1(key, hash, value, kv);
    return $m_sci_OldHashMap$().scala$collection$immutable$OldHashMap$$makeHashTrieMap__I__sci_OldHashMap__I__sci_OldHashMap__I__I__sci_OldHashMap$HashTrieMap(this.hash$5, this, hash, that, level, 2)
  } else {
    var this$2 = $m_sci_ListMap$EmptyListMap$();
    var key$1 = this.key$5;
    var value$1 = this.value$5;
    return new $c_sci_OldHashMap$OldHashMapCollision1(hash, new $c_sci_ListMap$Node(this$2, key$1, value$1).updated__O__O__sci_ListMap(key, value))
  }
});
$c_sci_OldHashMap$OldHashMap1.prototype.ensurePair__T2 = (function() {
  if ((this.kv$5 !== null)) {
    return this.kv$5
  } else {
    this.kv$5 = new $c_T2(this.key$5, this.value$5);
    return this.kv$5
  }
});
$c_sci_OldHashMap$OldHashMap1.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_OldHashMap$OldHashMap1.prototype.get0__O__I__I__s_Option = (function(key, hash, level) {
  return (((hash === this.hash$5) && $m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key$5)) ? new $c_s_Some(this.value$5) : $m_s_None$())
});
$c_sci_OldHashMap$OldHashMap1.prototype.foreach__F1__V = (function(f) {
  f.apply__O__O(this.ensurePair__T2())
});
$c_sci_OldHashMap$OldHashMap1.prototype.size__I = (function() {
  return 1
});
$c_sci_OldHashMap$OldHashMap1.prototype.iterator__sc_Iterator = (function() {
  $m_sc_Iterator$();
  var a = this.ensurePair__T2();
  return new $c_sc_Iterator$$anon$19(a)
});
$c_sci_OldHashMap$OldHashMap1.prototype.removed0__O__I__I__sci_OldHashMap = (function(key, hash, level) {
  return (((hash === this.hash$5) && $m_sr_BoxesRunTime$().equals__O__O__Z(key, this.key$5)) ? ($m_sci_OldHashMap$(), $m_sci_OldHashMap$EmptyOldHashMap$()) : this)
});
$c_sci_OldHashMap$OldHashMap1.prototype.knownSize__I = (function() {
  return 1
});
function $is_sci_OldHashMap$OldHashMap1(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_OldHashMap$OldHashMap1)))
}
function $as_sci_OldHashMap$OldHashMap1(obj) {
  return (($is_sci_OldHashMap$OldHashMap1(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.OldHashMap$OldHashMap1"))
}
function $isArrayOf_sci_OldHashMap$OldHashMap1(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_OldHashMap$OldHashMap1)))
}
function $asArrayOf_sci_OldHashMap$OldHashMap1(obj, depth) {
  return (($isArrayOf_sci_OldHashMap$OldHashMap1(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.OldHashMap$OldHashMap1;", depth))
}
var $d_sci_OldHashMap$OldHashMap1 = new $TypeData().initClass({
  sci_OldHashMap$OldHashMap1: 0
}, false, "scala.collection.immutable.OldHashMap$OldHashMap1", {
  sci_OldHashMap$OldHashMap1: 1,
  sci_OldHashMap: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sc_StrictOptimizedMapOps: 1
});
$c_sci_OldHashMap$OldHashMap1.prototype.$classData = $d_sci_OldHashMap$OldHashMap1;
/** @constructor */
function $c_sci_OldHashMap$OldHashMapCollision1(hash, kvs) {
  this.hash$5 = 0;
  this.kvs$5 = null;
  this.hash$5 = hash;
  this.kvs$5 = kvs
}
$c_sci_OldHashMap$OldHashMapCollision1.prototype = new $h_sci_OldHashMap();
$c_sci_OldHashMap$OldHashMapCollision1.prototype.constructor = $c_sci_OldHashMap$OldHashMapCollision1;
/** @constructor */
function $h_sci_OldHashMap$OldHashMapCollision1() {
  /*<skip>*/
}
$h_sci_OldHashMap$OldHashMapCollision1.prototype = $c_sci_OldHashMap$OldHashMapCollision1.prototype;
$c_sci_OldHashMap$OldHashMapCollision1.prototype.updated0__O__I__I__O__T2__sci_OldHashMap$Merger__sci_OldHashMap = (function(key, hash, level, value, kv, merger) {
  if ((hash === this.hash$5)) {
    if (((merger === null) || (!this.kvs$5.contains__O__Z(key)))) {
      return new $c_sci_OldHashMap$OldHashMapCollision1(hash, this.kvs$5.updated__O__O__sci_ListMap(key, value))
    } else {
      var this$1 = this.kvs$5;
      var kv$1 = merger.apply__T2__T2__T2(new $c_T2(key, this.kvs$5.apply__O__O(key)), kv);
      var key$1 = kv$1.$$und1$f;
      var value$1 = kv$1.$$und2$f;
      return new $c_sci_OldHashMap$OldHashMapCollision1(hash, this$1.updated__O__O__sci_ListMap(key$1, value$1))
    }
  } else {
    var that = new $c_sci_OldHashMap$OldHashMap1(key, hash, value, kv);
    return $m_sci_OldHashMap$().scala$collection$immutable$OldHashMap$$makeHashTrieMap__I__sci_OldHashMap__I__sci_OldHashMap__I__I__sci_OldHashMap$HashTrieMap(this.hash$5, this, hash, that, level, ((1 + this.kvs$5.size__I()) | 0))
  }
});
$c_sci_OldHashMap$OldHashMapCollision1.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_OldHashMap$OldHashMapCollision1.prototype.get0__O__I__I__s_Option = (function(key, hash, level) {
  return ((hash === this.hash$5) ? this.kvs$5.get__O__s_Option(key) : $m_s_None$())
});
$c_sci_OldHashMap$OldHashMapCollision1.prototype.foreach__F1__V = (function(f) {
  var this$1 = this.kvs$5;
  $f_sc_IterableOnceOps__foreach__F1__V(this$1, f)
});
$c_sci_OldHashMap$OldHashMapCollision1.prototype.size__I = (function() {
  return this.kvs$5.size__I()
});
$c_sci_OldHashMap$OldHashMapCollision1.prototype.iterator__sc_Iterator = (function() {
  return this.kvs$5.iterator__sc_Iterator()
});
$c_sci_OldHashMap$OldHashMapCollision1.prototype.removed0__O__I__I__sci_OldHashMap = (function(key, hash, level) {
  if ((hash === this.hash$5)) {
    var this$1 = this.kvs$5;
    var kvs1 = this$1.remove__O__sci_ListMap(key);
    var x1 = kvs1.size__I();
    switch (x1) {
      case 0: {
        $m_sci_OldHashMap$();
        return $m_sci_OldHashMap$EmptyOldHashMap$();
        break
      }
      case 1: {
        var kv = $as_T2(kvs1.iterator__sc_Iterator().next__O());
        return new $c_sci_OldHashMap$OldHashMap1(kv.$$und1$f, hash, kv.$$und2$f, kv);
        break
      }
      default: {
        return ((x1 === this.kvs$5.size__I()) ? this : new $c_sci_OldHashMap$OldHashMapCollision1(hash, kvs1))
      }
    }
  } else {
    return this
  }
});
var $d_sci_OldHashMap$OldHashMapCollision1 = new $TypeData().initClass({
  sci_OldHashMap$OldHashMapCollision1: 0
}, false, "scala.collection.immutable.OldHashMap$OldHashMapCollision1", {
  sci_OldHashMap$OldHashMapCollision1: 1,
  sci_OldHashMap: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sc_StrictOptimizedMapOps: 1
});
$c_sci_OldHashMap$OldHashMapCollision1.prototype.$classData = $d_sci_OldHashMap$OldHashMapCollision1;
/** @constructor */
function $c_sci_LazyList(lazyState) {
  this.state$4 = null;
  this.lazyState$4 = null;
  this.scala$collection$immutable$LazyList$$stateEvaluated$f = false;
  this.bitmap$0$4 = false;
  this.lazyState$4 = lazyState;
  this.scala$collection$immutable$LazyList$$stateEvaluated$f = false
}
$c_sci_LazyList.prototype = new $h_sci_AbstractSeq();
$c_sci_LazyList.prototype.constructor = $c_sci_LazyList;
/** @constructor */
function $h_sci_LazyList() {
  /*<skip>*/
}
$h_sci_LazyList.prototype = $c_sci_LazyList.prototype;
$c_sci_LazyList.prototype.head__O = (function() {
  return this.state__p4__sci_LazyList$State().head__O()
});
$c_sci_LazyList.prototype.apply__I__O = (function(n) {
  return $f_sc_LinearSeqOps__apply__I__O(this, n)
});
$c_sci_LazyList.prototype.lengthCompare__I__I = (function(len) {
  return $f_sc_LinearSeqOps__lengthCompare__I__I(this, len)
});
$c_sci_LazyList.prototype.apply__O__O = (function(v1) {
  var n = $uI(v1);
  return $f_sc_LinearSeqOps__apply__I__O(this, n)
});
$c_sci_LazyList.prototype.exists__F1__Z = (function(p) {
  return $f_sc_LinearSeqOps__exists__F1__Z(this, p)
});
$c_sci_LazyList.prototype.isEmpty__Z = (function() {
  return (this.state__p4__sci_LazyList$State() === $m_sci_LazyList$State$Empty$())
});
$c_sci_LazyList.prototype.sameElements__sc_IterableOnce__Z = (function(that) {
  return $f_sc_LinearSeqOps__sameElements__sc_IterableOnce__Z(this, that)
});
$c_sci_LazyList.prototype.equals__O__Z = (function(that) {
  return ((this === that) || $f_sc_Seq__equals__O__Z(this, that))
});
$c_sci_LazyList.prototype.state__p4__sci_LazyList$State = (function() {
  return ((!this.bitmap$0$4) ? this.state$lzycompute__p4__sci_LazyList$State() : this.state$4)
});
$c_sci_LazyList.prototype.state$lzycompute__p4__sci_LazyList$State = (function() {
  if ((!this.bitmap$0$4)) {
    this.scala$collection$immutable$LazyList$$stateEvaluated$f = true;
    var res = $as_sci_LazyList$State(this.lazyState$4.apply__O());
    this.lazyState$4 = null;
    this.state$4 = res;
    this.bitmap$0$4 = true
  };
  return this.state$4
});
$c_sci_LazyList.prototype.toString__T = (function() {
  return this.addStringNoForce__p4__jl_StringBuilder__T__T__T__jl_StringBuilder(new $c_jl_StringBuilder().init___T("LazyList"), "(", ", ", ")").java$lang$StringBuilder$$content$f
});
$c_sci_LazyList.prototype.flatMap__F1__sci_LazyList = (function(f) {
  $m_sci_LazyList$();
  var state = new $c_sjsr_AnonFunction0((function($this, f$1) {
    return (function() {
      return $this.scala$collection$immutable$LazyList$$flatMapState__F1__sci_LazyList$State(f$1)
    })
  })(this, f));
  return new $c_sci_LazyList(state)
});
$c_sci_LazyList.prototype.foreach__F1__V = (function(f) {
  var _$this = this;
  while (true) {
    var this$1 = _$this;
    if ((!this$1.isEmpty__Z())) {
      var this$2 = _$this;
      f.apply__O__O(this$2.state__p4__sci_LazyList$State().head__O());
      var this$3 = _$this;
      _$this = this$3.state__p4__sci_LazyList$State().tail__sci_LazyList();
      continue
    };
    break
  }
});
$c_sci_LazyList.prototype.foldLeft__O__F2__O = (function(z, op) {
  var _$this = this;
  while (true) {
    if (_$this.isEmpty__Z()) {
      return z
    } else {
      var this$1 = _$this;
      var temp$_$this = this$1.state__p4__sci_LazyList$State().tail__sci_LazyList();
      var jsx$1 = z;
      var this$2 = _$this;
      var temp$z = op.apply__O__O__O(jsx$1, this$2.state__p4__sci_LazyList$State().head__O());
      _$this = temp$_$this;
      z = temp$z
    }
  }
});
$c_sci_LazyList.prototype.flatMap__F1__O = (function(f) {
  return this.flatMap__F1__sci_LazyList(f)
});
$c_sci_LazyList.prototype.dropState__p4__I__sci_LazyList$State = (function(n) {
  var _$this = this;
  while (true) {
    if ((n <= 0)) {
      return _$this.state__p4__sci_LazyList$State()
    } else if (_$this.isEmpty__Z()) {
      return $m_sci_LazyList$State$Empty$()
    } else {
      var this$1 = _$this;
      var temp$_$this = this$1.state__p4__sci_LazyList$State().tail__sci_LazyList();
      var temp$n = (((-1) + n) | 0);
      _$this = temp$_$this;
      n = temp$n
    }
  }
});
$c_sci_LazyList.prototype.filter__F1__O = (function(pred) {
  return this.filter__F1__sci_LazyList(pred)
});
$c_sci_LazyList.prototype.iterator__sc_Iterator = (function() {
  return new $c_sci_LazyList$LazyIterator(this)
});
$c_sci_LazyList.prototype.filter__F1__sci_LazyList = (function(pred) {
  $m_sci_LazyList$();
  var state = new $c_sjsr_AnonFunction0((function($this, p, isFlipped) {
    return (function() {
      return $this.scala$collection$immutable$LazyList$$filterState__F1__Z__sci_LazyList$State(p, isFlipped)
    })
  })(this, pred, false));
  return new $c_sci_LazyList(state)
});
$c_sci_LazyList.prototype.length__I = (function() {
  return $f_sc_LinearSeqOps__length__I(this)
});
$c_sci_LazyList.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_LazyList$()
});
$c_sci_LazyList.prototype.drop__I__O = (function(n) {
  return this.drop__I__sci_LazyList(n)
});
$c_sci_LazyList.prototype.scala$collection$immutable$LazyList$$flatMapState__F1__sci_LazyList$State = (function(f) {
  var _$this = this;
  while (true) {
    if (_$this.isEmpty__Z()) {
      return $m_sci_LazyList$State$Empty$()
    } else {
      var this$1 = _$this;
      var it = $as_sc_IterableOnce(f.apply__O__O(this$1.state__p4__sci_LazyList$State().head__O())).iterator__sc_Iterator();
      if ((!it.hasNext__Z())) {
        var this$2 = _$this;
        _$this = this$2.state__p4__sci_LazyList$State().tail__sci_LazyList()
      } else {
        var this$4 = $m_sci_LazyList$();
        var suffix = new $c_sjsr_AnonFunction0((function($this, f$1) {
          return (function() {
            var this$3 = $this.state__p4__sci_LazyList$State().tail__sci_LazyList();
            return this$3.scala$collection$immutable$LazyList$$flatMapState__F1__sci_LazyList$State(f$1)
          })
        })(_$this, f));
        return this$4.nextState$1__p1__sc_Iterator__F0__sci_LazyList$State(it, suffix)
      }
    }
  }
});
$c_sci_LazyList.prototype.scala$collection$immutable$LazyList$$headDefined__Z = (function() {
  return (this.scala$collection$immutable$LazyList$$stateEvaluated$f && this.state__p4__sci_LazyList$State().headDefined__Z())
});
$c_sci_LazyList.prototype.tail__O = (function() {
  return this.state__p4__sci_LazyList$State().tail__sci_LazyList()
});
$c_sci_LazyList.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(sb, start, sep, end) {
  this.force__sci_LazyList();
  this.addStringNoForce__p4__jl_StringBuilder__T__T__T__jl_StringBuilder(sb.underlying$4, start, sep, end);
  return sb
});
$c_sci_LazyList.prototype.addStringNoForce__p4__jl_StringBuilder__T__T__T__jl_StringBuilder = (function(b, start, sep, end) {
  b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + start);
  if ((!this.scala$collection$immutable$LazyList$$stateEvaluated$f)) {
    var str = $as_T(String.fromCharCode(63));
    b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str)
  } else if ((!this.isEmpty__Z())) {
    if (this.scala$collection$immutable$LazyList$$headDefined__Z()) {
      var obj = this.state__p4__sci_LazyList$State().head__O();
      b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj)
    } else {
      var str$1 = $as_T(String.fromCharCode(95));
      b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$1)
    };
    var elem$1 = null;
    elem$1 = this;
    var elem = this.state__p4__sci_LazyList$State().tail__sci_LazyList();
    var elem$1$1 = null;
    elem$1$1 = elem;
    if (($as_sci_LazyList(elem$1) !== $as_sci_LazyList(elem$1$1))) {
      elem$1 = $as_sci_LazyList(elem$1$1);
      if ($as_sci_LazyList(elem$1$1).scala$collection$immutable$LazyList$$stateEvaluated$f) {
        var this$5 = $as_sci_LazyList(elem$1$1);
        var jsx$1 = (!this$5.isEmpty__Z())
      } else {
        var jsx$1 = false
      };
      if (jsx$1) {
        var this$6 = $as_sci_LazyList(elem$1$1);
        elem$1$1 = this$6.state__p4__sci_LazyList$State().tail__sci_LazyList();
        while (true) {
          if (($as_sci_LazyList(elem$1) !== $as_sci_LazyList(elem$1$1))) {
            if ($as_sci_LazyList(elem$1$1).scala$collection$immutable$LazyList$$stateEvaluated$f) {
              var this$7 = $as_sci_LazyList(elem$1$1);
              var jsx$3 = (!this$7.isEmpty__Z())
            } else {
              var jsx$3 = false
            }
          } else {
            var jsx$3 = false
          };
          if (jsx$3) {
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
            if ($as_sci_LazyList(elem$1).scala$collection$immutable$LazyList$$headDefined__Z()) {
              var this$8 = $as_sci_LazyList(elem$1);
              var obj$1 = this$8.state__p4__sci_LazyList$State().head__O();
              b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$1)
            } else {
              var str$2 = $as_T(String.fromCharCode(95));
              b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$2)
            };
            var this$10 = $as_sci_LazyList(elem$1);
            elem$1 = this$10.state__p4__sci_LazyList$State().tail__sci_LazyList();
            var this$11 = $as_sci_LazyList(elem$1$1);
            elem$1$1 = this$11.state__p4__sci_LazyList$State().tail__sci_LazyList();
            if ($as_sci_LazyList(elem$1$1).scala$collection$immutable$LazyList$$stateEvaluated$f) {
              var this$12 = $as_sci_LazyList(elem$1$1);
              var jsx$2 = (!this$12.isEmpty__Z())
            } else {
              var jsx$2 = false
            };
            if (jsx$2) {
              var this$13 = $as_sci_LazyList(elem$1$1);
              elem$1$1 = this$13.state__p4__sci_LazyList$State().tail__sci_LazyList()
            }
          } else {
            break
          }
        }
      }
    };
    if ($as_sci_LazyList(elem$1$1).scala$collection$immutable$LazyList$$stateEvaluated$f) {
      var this$14 = $as_sci_LazyList(elem$1$1);
      var jsx$4 = (!this$14.isEmpty__Z())
    } else {
      var jsx$4 = false
    };
    if ((!jsx$4)) {
      while (($as_sci_LazyList(elem$1) !== $as_sci_LazyList(elem$1$1))) {
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
        if ($as_sci_LazyList(elem$1).scala$collection$immutable$LazyList$$headDefined__Z()) {
          var this$15 = $as_sci_LazyList(elem$1);
          var obj$2 = this$15.state__p4__sci_LazyList$State().head__O();
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$2)
        } else {
          var str$3 = $as_T(String.fromCharCode(95));
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$3)
        };
        var this$17 = $as_sci_LazyList(elem$1);
        elem$1 = this$17.state__p4__sci_LazyList$State().tail__sci_LazyList()
      };
      if ((!$as_sci_LazyList(elem$1).scala$collection$immutable$LazyList$$stateEvaluated$f)) {
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
        var str$4 = $as_T(String.fromCharCode(63));
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$4)
      }
    } else {
      var runner = this;
      var k = 0;
      while ((runner !== $as_sci_LazyList(elem$1$1))) {
        var this$19 = runner;
        runner = this$19.state__p4__sci_LazyList$State().tail__sci_LazyList();
        var this$20 = $as_sci_LazyList(elem$1$1);
        elem$1$1 = this$20.state__p4__sci_LazyList$State().tail__sci_LazyList();
        k = ((1 + k) | 0)
      };
      if ((($as_sci_LazyList(elem$1) === $as_sci_LazyList(elem$1$1)) && (k > 0))) {
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
        if ($as_sci_LazyList(elem$1).scala$collection$immutable$LazyList$$headDefined__Z()) {
          var this$21 = $as_sci_LazyList(elem$1);
          var obj$3 = this$21.state__p4__sci_LazyList$State().head__O();
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$3)
        } else {
          var str$5 = $as_T(String.fromCharCode(95));
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$5)
        };
        var this$23 = $as_sci_LazyList(elem$1);
        elem$1 = this$23.state__p4__sci_LazyList$State().tail__sci_LazyList()
      };
      while (($as_sci_LazyList(elem$1) !== $as_sci_LazyList(elem$1$1))) {
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
        if ($as_sci_LazyList(elem$1).scala$collection$immutable$LazyList$$headDefined__Z()) {
          var this$24 = $as_sci_LazyList(elem$1);
          var obj$4 = this$24.state__p4__sci_LazyList$State().head__O();
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$4)
        } else {
          var str$6 = $as_T(String.fromCharCode(95));
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$6)
        };
        var this$26 = $as_sci_LazyList(elem$1);
        elem$1 = this$26.state__p4__sci_LazyList$State().tail__sci_LazyList()
      };
      b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
      b.java$lang$StringBuilder$$content$f = (b.java$lang$StringBuilder$$content$f + "...")
    }
  };
  b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + end);
  return b
});
$c_sci_LazyList.prototype.map__F1__sci_LazyList = (function(f) {
  $m_sci_LazyList$();
  var state = new $c_sjsr_AnonFunction0((function($this, f$1) {
    return (function() {
      if ($this.isEmpty__Z()) {
        return $m_sci_LazyList$State$Empty$()
      } else {
        $m_sci_LazyList$();
        var hd = new $c_sjsr_AnonFunction0((function($this$1, f$1$1) {
          return (function() {
            return f$1$1.apply__O__O($this$1.state__p4__sci_LazyList$State().head__O())
          })
        })($this, f$1));
        var tl = $this.state__p4__sci_LazyList$State().tail__sci_LazyList().map__F1__sci_LazyList(f$1);
        return new $c_sci_LazyList$State$Cons(hd, tl)
      }
    })
  })(this, f));
  return new $c_sci_LazyList(state)
});
$c_sci_LazyList.prototype.map__F1__O = (function(f) {
  return this.map__F1__sci_LazyList(f)
});
$c_sci_LazyList.prototype.force__sci_LazyList = (function() {
  var these = this;
  var those = this;
  var this$1 = these;
  if ((!this$1.isEmpty__Z())) {
    var this$2 = these;
    this$2.state__p4__sci_LazyList$State().head__O();
    var this$3 = these;
    these = this$3.state__p4__sci_LazyList$State().tail__sci_LazyList()
  };
  while ((those !== these)) {
    if (these.isEmpty__Z()) {
      return this
    };
    var this$4 = these;
    this$4.state__p4__sci_LazyList$State().head__O();
    var this$5 = these;
    these = this$5.state__p4__sci_LazyList$State().tail__sci_LazyList();
    if (these.isEmpty__Z()) {
      return this
    };
    var this$6 = these;
    this$6.state__p4__sci_LazyList$State().head__O();
    var this$7 = these;
    these = this$7.state__p4__sci_LazyList$State().tail__sci_LazyList();
    if ((these === those)) {
      return this
    };
    var this$8 = those;
    those = this$8.state__p4__sci_LazyList$State().tail__sci_LazyList()
  };
  return this
});
$c_sci_LazyList.prototype.withFilter__F1__sc_WithFilter = (function(p) {
  return new $c_sci_LazyList$WithFilter(this, p)
});
$c_sci_LazyList.prototype.drop__I__sci_LazyList = (function(n) {
  if ((n <= 0)) {
    return this
  } else {
    $m_sci_LazyList$();
    var state = new $c_sjsr_AnonFunction0((function($this, n$1) {
      return (function() {
        return $this.dropState__p4__I__sci_LazyList$State(n$1)
      })
    })(this, n));
    return new $c_sci_LazyList(state)
  }
});
$c_sci_LazyList.prototype.className__T = (function() {
  return "LazyList"
});
$c_sci_LazyList.prototype.knownSize__I = (function() {
  return ((this.scala$collection$immutable$LazyList$$stateEvaluated$f && this.isEmpty__Z()) ? 0 : (-1))
});
$c_sci_LazyList.prototype.stringPrefix__T = (function() {
  return "LinearSeq"
});
$c_sci_LazyList.prototype.scala$collection$immutable$LazyList$$filterState__F1__Z__sci_LazyList$State = (function(p, isFlipped) {
  var _$this = this;
  while (true) {
    if (_$this.isEmpty__Z()) {
      return $m_sci_LazyList$State$Empty$()
    } else {
      var this$1 = _$this;
      var elem = this$1.state__p4__sci_LazyList$State().head__O();
      if (($uZ(p.apply__O__O(elem)) === isFlipped)) {
        var this$2 = _$this;
        _$this = this$2.state__p4__sci_LazyList$State().tail__sci_LazyList()
      } else {
        $m_sci_LazyList$();
        var hd = new $c_sjsr_AnonFunction0((function($this, elem$1) {
          return (function() {
            return elem$1
          })
        })(_$this, elem));
        var this$3 = _$this;
        var this$4 = this$3.state__p4__sci_LazyList$State().tail__sci_LazyList();
        $m_sci_LazyList$();
        var state = new $c_sjsr_AnonFunction0((function($this$1, p$1, isFlipped$1) {
          return (function() {
            return $this$1.scala$collection$immutable$LazyList$$filterState__F1__Z__sci_LazyList$State(p$1, isFlipped$1)
          })
        })(this$4, p, isFlipped));
        var tl = new $c_sci_LazyList(state);
        return new $c_sci_LazyList$State$Cons(hd, tl)
      }
    }
  }
});
function $is_sci_LazyList(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_LazyList)))
}
function $as_sci_LazyList(obj) {
  return (($is_sci_LazyList(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.LazyList"))
}
function $isArrayOf_sci_LazyList(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_LazyList)))
}
function $asArrayOf_sci_LazyList(obj, depth) {
  return (($isArrayOf_sci_LazyList(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.LazyList;", depth))
}
var $d_sci_LazyList = new $TypeData().initClass({
  sci_LazyList: 0
}, false, "scala.collection.immutable.LazyList", {
  sci_LazyList: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_LinearSeq: 1,
  sc_LinearSeq: 1,
  sc_LinearSeqOps: 1,
  sci_LinearSeqOps: 1
});
$c_sci_LazyList.prototype.$classData = $d_sci_LazyList;
/** @constructor */
function $c_sci_ListMap$EmptyListMap$() {
  /*<skip>*/
}
$c_sci_ListMap$EmptyListMap$.prototype = new $h_sci_ListMap();
$c_sci_ListMap$EmptyListMap$.prototype.constructor = $c_sci_ListMap$EmptyListMap$;
/** @constructor */
function $h_sci_ListMap$EmptyListMap$() {
  /*<skip>*/
}
$h_sci_ListMap$EmptyListMap$.prototype = $c_sci_ListMap$EmptyListMap$.prototype;
var $d_sci_ListMap$EmptyListMap$ = new $TypeData().initClass({
  sci_ListMap$EmptyListMap$: 0
}, false, "scala.collection.immutable.ListMap$EmptyListMap$", {
  sci_ListMap$EmptyListMap$: 1,
  sci_ListMap: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sci_SeqMap: 1,
  sc_StrictOptimizedIterableOps: 1,
  sc_StrictOptimizedMapOps: 1
});
$c_sci_ListMap$EmptyListMap$.prototype.$classData = $d_sci_ListMap$EmptyListMap$;
var $n_sci_ListMap$EmptyListMap$ = (void 0);
function $m_sci_ListMap$EmptyListMap$() {
  if ((!$n_sci_ListMap$EmptyListMap$)) {
    $n_sci_ListMap$EmptyListMap$ = new $c_sci_ListMap$EmptyListMap$()
  };
  return $n_sci_ListMap$EmptyListMap$
}
/** @constructor */
function $c_sci_ListMap$Node($$outer, key, value) {
  this.key$5 = null;
  this.value$5 = null;
  this.$$outer$5 = null;
  this.key$5 = key;
  this.value$5 = value;
  if (($$outer === null)) {
    throw $m_sjsr_package$().unwrapJavaScriptException__jl_Throwable__O(null)
  } else {
    this.$$outer$5 = $$outer
  }
}
$c_sci_ListMap$Node.prototype = new $h_sci_ListMap();
$c_sci_ListMap$Node.prototype.constructor = $c_sci_ListMap$Node;
/** @constructor */
function $h_sci_ListMap$Node() {
  /*<skip>*/
}
$h_sci_ListMap$Node.prototype = $c_sci_ListMap$Node.prototype;
$c_sci_ListMap$Node.prototype.apply__O__O = (function(k) {
  return this.applyInternal__p5__sci_ListMap__O__O(this, k)
});
$c_sci_ListMap$Node.prototype.value__O = (function() {
  return this.value$5
});
$c_sci_ListMap$Node.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_ListMap$Node.prototype.containsInternal__p5__sci_ListMap__O__Z = (function(cur, k) {
  while (true) {
    if ((!cur.isEmpty__Z())) {
      if ($m_sr_BoxesRunTime$().equals__O__O__Z(k, cur.key__O())) {
        return true
      } else {
        cur = cur.next__sci_ListMap()
      }
    } else {
      return false
    }
  }
});
$c_sci_ListMap$Node.prototype.updated__O__O__sci_MapOps = (function(key, value) {
  return this.updated__O__O__sci_ListMap(key, value)
});
$c_sci_ListMap$Node.prototype.removeInternal__p5__O__sci_ListMap__sci_List__sci_ListMap = (function(k, cur, acc) {
  while (true) {
    if (cur.isEmpty__Z()) {
      return $as_sci_ListMap(acc.last__O())
    } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(k, cur.key__O())) {
      var this$1 = acc;
      var z = cur.next__sci_ListMap();
      var acc$1 = z;
      var these = this$1;
      while ((!these.isEmpty__Z())) {
        var arg1 = acc$1;
        var arg2 = these.head__O();
        var t = $as_sci_ListMap(arg1);
        var h = $as_sci_ListMap(arg2);
        acc$1 = new $c_sci_ListMap$Node(t, h.key__O(), h.value__O());
        these = $as_sc_LinearSeq(these.tail__O())
      };
      return $as_sci_ListMap(acc$1)
    } else {
      var temp$cur = cur.next__sci_ListMap();
      var rassoc$2 = cur;
      var this$2 = acc;
      var temp$acc = new $c_sci_$colon$colon(rassoc$2, this$2);
      cur = temp$cur;
      acc = temp$acc
    }
  }
});
$c_sci_ListMap$Node.prototype.getInternal__p5__sci_ListMap__O__s_Option = (function(cur, k) {
  while (true) {
    if (cur.isEmpty__Z()) {
      return $m_s_None$()
    } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(k, cur.key__O())) {
      return new $c_s_Some(cur.value__O())
    } else {
      cur = cur.next__sci_ListMap()
    }
  }
});
$c_sci_ListMap$Node.prototype.applyInternal__p5__sci_ListMap__O__O = (function(cur, k) {
  while (true) {
    if (cur.isEmpty__Z()) {
      throw new $c_ju_NoSuchElementException().init___T(("key not found: " + k))
    } else if ($m_sr_BoxesRunTime$().equals__O__O__Z(k, cur.key__O())) {
      return cur.value__O()
    } else {
      cur = cur.next__sci_ListMap()
    }
  }
});
$c_sci_ListMap$Node.prototype.size__I = (function() {
  return this.sizeInternal__p5__sci_ListMap__I__I(this, 0)
});
$c_sci_ListMap$Node.prototype.sizeInternal__p5__sci_ListMap__I__I = (function(cur, acc) {
  while (true) {
    if (cur.isEmpty__Z()) {
      return acc
    } else {
      var temp$cur = cur.next__sci_ListMap();
      var temp$acc = ((1 + acc) | 0);
      cur = temp$cur;
      acc = temp$acc
    }
  }
});
$c_sci_ListMap$Node.prototype.key__O = (function() {
  return this.key$5
});
$c_sci_ListMap$Node.prototype.updated__O__O__sci_ListMap = (function(k, v) {
  var m = this.removeInternal__p5__O__sci_ListMap__sci_List__sci_ListMap(k, this, $m_sci_Nil$());
  return new $c_sci_ListMap$Node(m, k, v)
});
$c_sci_ListMap$Node.prototype.get__O__s_Option = (function(k) {
  return this.getInternal__p5__sci_ListMap__O__s_Option(this, k)
});
$c_sci_ListMap$Node.prototype.contains__O__Z = (function(k) {
  return this.containsInternal__p5__sci_ListMap__O__Z(this, k)
});
$c_sci_ListMap$Node.prototype.remove__O__sci_ListMap = (function(k) {
  return this.removeInternal__p5__O__sci_ListMap__sci_List__sci_ListMap(k, this, $m_sci_Nil$())
});
$c_sci_ListMap$Node.prototype.knownSize__I = (function() {
  return (-1)
});
$c_sci_ListMap$Node.prototype.next__sci_ListMap = (function() {
  return this.$$outer$5
});
var $d_sci_ListMap$Node = new $TypeData().initClass({
  sci_ListMap$Node: 0
}, false, "scala.collection.immutable.ListMap$Node", {
  sci_ListMap$Node: 1,
  sci_ListMap: 1,
  sci_AbstractMap: 1,
  sc_AbstractMap: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Map: 1,
  sc_MapOps: 1,
  s_PartialFunction: 1,
  F1: 1,
  s_Equals: 1,
  sci_Map: 1,
  sci_Iterable: 1,
  sci_MapOps: 1,
  sci_SeqMap: 1,
  sc_StrictOptimizedIterableOps: 1,
  sc_StrictOptimizedMapOps: 1
});
$c_sci_ListMap$Node.prototype.$classData = $d_sci_ListMap$Node;
/** @constructor */
function $c_sci_Stream() {
  /*<skip>*/
}
$c_sci_Stream.prototype = new $h_sci_AbstractSeq();
$c_sci_Stream.prototype.constructor = $c_sci_Stream;
/** @constructor */
function $h_sci_Stream() {
  /*<skip>*/
}
$h_sci_Stream.prototype = $c_sci_Stream.prototype;
$c_sci_Stream.prototype.apply__I__O = (function(n) {
  return $f_sc_LinearSeqOps__apply__I__O(this, n)
});
$c_sci_Stream.prototype.lengthCompare__I__I = (function(len) {
  return $f_sc_LinearSeqOps__lengthCompare__I__I(this, len)
});
$c_sci_Stream.prototype.apply__O__O = (function(v1) {
  var n = $uI(v1);
  return $f_sc_LinearSeqOps__apply__I__O(this, n)
});
$c_sci_Stream.prototype.exists__F1__Z = (function(p) {
  return $f_sc_LinearSeqOps__exists__F1__Z(this, p)
});
$c_sci_Stream.prototype.sameElements__sc_IterableOnce__Z = (function(that) {
  return $f_sc_LinearSeqOps__sameElements__sc_IterableOnce__Z(this, that)
});
$c_sci_Stream.prototype.lazyAppendedAll__F0__sci_Stream = (function(suffix) {
  if (this.isEmpty__Z()) {
    var this$1 = $m_sci_Stream$();
    var source = $as_sc_IterableOnce(suffix.apply__O());
    return this$1.from__sc_IterableOnce__sci_Stream(source)
  } else {
    var tl = new $c_sjsr_AnonFunction0((function(this$2, suffix$1) {
      return (function() {
        return $as_sci_Stream(this$2.tail__O()).lazyAppendedAll__F0__sci_Stream(suffix$1)
      })
    })(this, suffix));
    return new $c_sci_Stream$Cons(this.head__O(), tl)
  }
});
$c_sci_Stream.prototype.equals__O__Z = (function(that) {
  return ((this === that) || $f_sc_Seq__equals__O__Z(this, that))
});
$c_sci_Stream.prototype.filterImpl__F1__Z__sci_Stream = (function(p, isFlipped) {
  var rest = this;
  while (true) {
    var this$1 = rest;
    if (((!this$1.isEmpty__Z()) && ($uZ(p.apply__O__O(rest.head__O())) === isFlipped))) {
      rest = $as_sci_Stream(rest.tail__O())
    } else {
      break
    }
  };
  var this$2 = rest;
  if ((!this$2.isEmpty__Z())) {
    return $m_sci_Stream$().filteredTail__sci_Stream__F1__Z__sci_Stream(rest, p, isFlipped)
  } else {
    return $m_sci_Stream$Empty$()
  }
});
$c_sci_Stream.prototype.flatMap__F1__sci_Stream = (function(f) {
  if (this.isEmpty__Z()) {
    return $m_sci_Stream$Empty$()
  } else {
    var nonEmptyPrefix = new $c_sr_ObjectRef(this);
    var this$3 = $m_sci_Stream$();
    var source = $as_sc_IterableOnce(f.apply__O__O($as_sci_Stream(nonEmptyPrefix.elem$1).head__O()));
    var prefix = this$3.from__sc_IterableOnce__sci_Stream(source);
    while (((!$as_sci_Stream(nonEmptyPrefix.elem$1).isEmpty__Z()) && prefix.isEmpty__Z())) {
      nonEmptyPrefix.elem$1 = $as_sci_Stream($as_sci_Stream(nonEmptyPrefix.elem$1).tail__O());
      if ((!$as_sci_Stream(nonEmptyPrefix.elem$1).isEmpty__Z())) {
        var this$4 = $m_sci_Stream$();
        var source$1 = $as_sc_IterableOnce(f.apply__O__O($as_sci_Stream(nonEmptyPrefix.elem$1).head__O()));
        prefix = this$4.from__sc_IterableOnce__sci_Stream(source$1)
      }
    };
    return ($as_sci_Stream(nonEmptyPrefix.elem$1).isEmpty__Z() ? $m_sci_Stream$Empty$() : prefix.lazyAppendedAll__F0__sci_Stream(new $c_sjsr_AnonFunction0((function($this, nonEmptyPrefix$1, f$1) {
      return (function() {
        return $as_sci_Stream($as_sci_Stream(nonEmptyPrefix$1.elem$1).tail__O()).flatMap__F1__sci_Stream(f$1)
      })
    })(this, nonEmptyPrefix, f))))
  }
});
$c_sci_Stream.prototype.toString__T = (function() {
  return this.addStringNoForce__p4__jl_StringBuilder__T__T__T__jl_StringBuilder(new $c_jl_StringBuilder().init___T("Stream"), "(", ", ", ")").java$lang$StringBuilder$$content$f
});
$c_sci_Stream.prototype.foreach__F1__V = (function(f) {
  var _$this = this;
  while (true) {
    if ((!_$this.isEmpty__Z())) {
      f.apply__O__O(_$this.head__O());
      _$this = $as_sci_Stream(_$this.tail__O());
      continue
    };
    break
  }
});
$c_sci_Stream.prototype.flatMap__F1__O = (function(f) {
  return this.flatMap__F1__sci_Stream(f)
});
$c_sci_Stream.prototype.foldLeft__O__F2__O = (function(z, op) {
  var _$this = this;
  while (true) {
    if (_$this.isEmpty__Z()) {
      return z
    } else {
      var temp$_$this = $as_sci_Stream(_$this.tail__O());
      var temp$z = op.apply__O__O__O(z, _$this.head__O());
      _$this = temp$_$this;
      z = temp$z
    }
  }
});
$c_sci_Stream.prototype.filter__F1__O = (function(pred) {
  return this.filterImpl__F1__Z__sci_Stream(pred, false)
});
$c_sci_Stream.prototype.iterator__sc_Iterator = (function() {
  return new $c_sc_LinearSeqIterator(this)
});
$c_sci_Stream.prototype.length__I = (function() {
  return $f_sc_LinearSeqOps__length__I(this)
});
$c_sci_Stream.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_Stream$()
});
$c_sci_Stream.prototype.take__I__O = (function(n) {
  return this.take__I__sci_Stream(n)
});
$c_sci_Stream.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(sb, start, sep, end) {
  this.force__sci_Stream();
  this.addStringNoForce__p4__jl_StringBuilder__T__T__T__jl_StringBuilder(sb.underlying$4, start, sep, end);
  return sb
});
$c_sci_Stream.prototype.addStringNoForce__p4__jl_StringBuilder__T__T__T__jl_StringBuilder = (function(b, start, sep, end) {
  b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + start);
  if ((!this.isEmpty__Z())) {
    if (this.headDefined__Z()) {
      var obj = this.head__O();
      b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj)
    } else {
      var str = $as_T(String.fromCharCode(95));
      b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str)
    };
    var elem$1 = null;
    elem$1 = this;
    if (this.tailDefined__Z()) {
      var scout = $as_sci_Stream(this.tail__O());
      if (($as_sci_Stream(elem$1) !== scout)) {
        elem$1 = scout;
        if (scout.tailDefined__Z()) {
          scout = $as_sci_Stream(scout.tail__O());
          while ((($as_sci_Stream(elem$1) !== scout) && scout.tailDefined__Z())) {
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
            if ($as_sci_Stream(elem$1).headDefined__Z()) {
              var obj$1 = $as_sci_Stream(elem$1).head__O();
              b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$1)
            } else {
              var str$1 = $as_T(String.fromCharCode(95));
              b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$1)
            };
            elem$1 = $as_sci_Stream($as_sci_Stream(elem$1).tail__O());
            scout = $as_sci_Stream(scout.tail__O());
            if (scout.tailDefined__Z()) {
              scout = $as_sci_Stream(scout.tail__O())
            }
          }
        }
      };
      if ((!scout.tailDefined__Z())) {
        while (($as_sci_Stream(elem$1) !== scout)) {
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
          if ($as_sci_Stream(elem$1).headDefined__Z()) {
            var obj$2 = $as_sci_Stream(elem$1).head__O();
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$2)
          } else {
            var str$2 = $as_T(String.fromCharCode(95));
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$2)
          };
          elem$1 = $as_sci_Stream($as_sci_Stream(elem$1).tail__O())
        };
        var this$5 = $as_sci_Stream(elem$1);
        if ((!this$5.isEmpty__Z())) {
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
          if ($as_sci_Stream(elem$1).headDefined__Z()) {
            var obj$3 = $as_sci_Stream(elem$1).head__O();
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$3)
          } else {
            var str$3 = $as_T(String.fromCharCode(95));
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$3)
          }
        }
      } else {
        var runner = this;
        var k = 0;
        while ((runner !== scout)) {
          runner = $as_sci_Stream(runner.tail__O());
          scout = $as_sci_Stream(scout.tail__O());
          k = ((1 + k) | 0)
        };
        if ((($as_sci_Stream(elem$1) === scout) && (k > 0))) {
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
          if ($as_sci_Stream(elem$1).headDefined__Z()) {
            var obj$4 = $as_sci_Stream(elem$1).head__O();
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$4)
          } else {
            var str$4 = $as_T(String.fromCharCode(95));
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$4)
          };
          elem$1 = $as_sci_Stream($as_sci_Stream(elem$1).tail__O())
        };
        while (($as_sci_Stream(elem$1) !== scout)) {
          b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
          if ($as_sci_Stream(elem$1).headDefined__Z()) {
            var obj$5 = $as_sci_Stream(elem$1).head__O();
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + obj$5)
          } else {
            var str$5 = $as_T(String.fromCharCode(95));
            b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$5)
          };
          elem$1 = $as_sci_Stream($as_sci_Stream(elem$1).tail__O())
        }
      }
    };
    var this$9 = $as_sci_Stream(elem$1);
    if ((!this$9.isEmpty__Z())) {
      if ((!$as_sci_Stream(elem$1).tailDefined__Z())) {
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
        var str$6 = $as_T(String.fromCharCode(63));
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$6)
      } else {
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + sep);
        b.java$lang$StringBuilder$$content$f = (b.java$lang$StringBuilder$$content$f + "...")
      }
    }
  };
  b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + end);
  return b
});
$c_sci_Stream.prototype.map__F1__O = (function(f) {
  return this.map__F1__sci_Stream(f)
});
$c_sci_Stream.prototype.map__F1__sci_Stream = (function(f) {
  if (this.isEmpty__Z()) {
    return $m_sci_Stream$Empty$()
  } else {
    var tl = new $c_sjsr_AnonFunction0((function(this$2, f$1) {
      return (function() {
        return $as_sci_Stream(this$2.tail__O()).map__F1__sci_Stream(f$1)
      })
    })(this, f));
    return new $c_sci_Stream$Cons(f.apply__O__O(this.head__O()), tl)
  }
});
$c_sci_Stream.prototype.take__I__sci_Stream = (function(n) {
  return (((n <= 0) || this.isEmpty__Z()) ? $m_sci_Stream$Empty$() : ((n === 1) ? new $c_sci_Stream$Cons(this.head__O(), new $c_sjsr_AnonFunction0((function($this) {
    return (function() {
      return $m_sci_Stream$Empty$()
    })
  })(this))) : new $c_sci_Stream$Cons(this.head__O(), new $c_sjsr_AnonFunction0((function(this$2$1, n$1) {
    return (function() {
      return $as_sci_Stream(this$2$1.tail__O()).take__I__sci_Stream((((-1) + n$1) | 0))
    })
  })(this, n)))))
});
$c_sci_Stream.prototype.withFilter__F1__sc_WithFilter = (function(p) {
  return new $c_sci_Stream$WithFilter(this, p)
});
$c_sci_Stream.prototype.className__T = (function() {
  return "Stream"
});
$c_sci_Stream.prototype.stringPrefix__T = (function() {
  return "LinearSeq"
});
function $is_sci_Stream(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_Stream)))
}
function $as_sci_Stream(obj) {
  return (($is_sci_Stream(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.Stream"))
}
function $isArrayOf_sci_Stream(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_Stream)))
}
function $asArrayOf_sci_Stream(obj, depth) {
  return (($isArrayOf_sci_Stream(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.Stream;", depth))
}
/** @constructor */
function $c_sci_WrappedString(self) {
  this.scala$collection$immutable$WrappedString$$self$4 = null;
  this.scala$collection$immutable$WrappedString$$self$4 = self
}
$c_sci_WrappedString.prototype = new $h_sci_AbstractSeq();
$c_sci_WrappedString.prototype.constructor = $c_sci_WrappedString;
/** @constructor */
function $h_sci_WrappedString() {
  /*<skip>*/
}
$h_sci_WrappedString.prototype = $c_sci_WrappedString.prototype;
$c_sci_WrappedString.prototype.apply__I__O = (function(i) {
  var this$1 = this.scala$collection$immutable$WrappedString$$self$4;
  return $bC((65535 & $uI(this$1.charCodeAt(i))))
});
$c_sci_WrappedString.prototype.lengthCompare__I__I = (function(len) {
  var this$1 = this.scala$collection$immutable$WrappedString$$self$4;
  var x = $uI(this$1.length);
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sci_WrappedString.prototype.apply__O__O = (function(v1) {
  var i = $uI(v1);
  var this$1 = this.scala$collection$immutable$WrappedString$$self$4;
  return $bC((65535 & $uI(this$1.charCodeAt(i))))
});
$c_sci_WrappedString.prototype.equals__O__Z = (function(other) {
  if ($is_sci_WrappedString(other)) {
    var x2 = $as_sci_WrappedString(other);
    return (this.scala$collection$immutable$WrappedString$$self$4 === x2.scala$collection$immutable$WrappedString$$self$4)
  } else {
    return $f_sc_Seq__equals__O__Z(this, other)
  }
});
$c_sci_WrappedString.prototype.fromSpecific__sc_IterableOnce__O = (function(coll) {
  return $m_sci_WrappedString$().fromSpecific__sc_IterableOnce__sci_WrappedString(coll)
});
$c_sci_WrappedString.prototype.toString__T = (function() {
  return this.scala$collection$immutable$WrappedString$$self$4
});
$c_sci_WrappedString.prototype.newSpecificBuilder__scm_Builder = (function() {
  return $m_sci_WrappedString$().newBuilder__scm_Builder()
});
$c_sci_WrappedString.prototype.fromSpecific__sc_IterableOnce__sc_Iterable = (function(coll) {
  return $m_sci_WrappedString$().fromSpecific__sc_IterableOnce__sci_WrappedString(coll)
});
$c_sci_WrappedString.prototype.iterator__sc_Iterator = (function() {
  var this$1 = new $c_sc_StringView(this.scala$collection$immutable$WrappedString$$self$4);
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$1)
});
$c_sci_WrappedString.prototype.length__I = (function() {
  var this$1 = this.scala$collection$immutable$WrappedString$$self$4;
  return $uI(this$1.length)
});
$c_sci_WrappedString.prototype.take__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__take__I__O(this, n)
});
$c_sci_WrappedString.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_IndexedSeq$()
});
$c_sci_WrappedString.prototype.drop__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__drop__I__O(this, n)
});
$c_sci_WrappedString.prototype.map__F1__O = (function(f) {
  return $f_sc_IndexedSeqOps__map__F1__O(this, f)
});
$c_sci_WrappedString.prototype.className__T = (function() {
  return "WrappedString"
});
$c_sci_WrappedString.prototype.knownSize__I = (function() {
  var this$1 = this.scala$collection$immutable$WrappedString$$self$4;
  return $uI(this$1.length)
});
$c_sci_WrappedString.prototype.stringPrefix__T = (function() {
  return "IndexedSeq"
});
function $is_sci_WrappedString(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_WrappedString)))
}
function $as_sci_WrappedString(obj) {
  return (($is_sci_WrappedString(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.WrappedString"))
}
function $isArrayOf_sci_WrappedString(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_WrappedString)))
}
function $asArrayOf_sci_WrappedString(obj, depth) {
  return (($isArrayOf_sci_WrappedString(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.WrappedString;", depth))
}
var $d_sci_WrappedString = new $TypeData().initClass({
  sci_WrappedString: 0
}, false, "scala.collection.immutable.WrappedString", {
  sci_WrappedString: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_IndexedSeq: 1,
  sc_IndexedSeq: 1,
  sc_IndexedSeqOps: 1,
  sci_IndexedSeqOps: 1
});
$c_sci_WrappedString.prototype.$classData = $d_sci_WrappedString;
/** @constructor */
function $c_sjsr_WrappedVarArgs(array) {
  this.scala$scalajs$runtime$WrappedVarArgs$$array$f = null;
  this.scala$scalajs$runtime$WrappedVarArgs$$array$f = array
}
$c_sjsr_WrappedVarArgs.prototype = new $h_O();
$c_sjsr_WrappedVarArgs.prototype.constructor = $c_sjsr_WrappedVarArgs;
/** @constructor */
function $h_sjsr_WrappedVarArgs() {
  /*<skip>*/
}
$h_sjsr_WrappedVarArgs.prototype = $c_sjsr_WrappedVarArgs.prototype;
$c_sjsr_WrappedVarArgs.prototype.head__O = (function() {
  var this$1 = new $c_sc_IndexedSeqView$Id(this);
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$1).next__O()
});
$c_sjsr_WrappedVarArgs.prototype.apply__I__O = (function(idx) {
  return this.scala$scalajs$runtime$WrappedVarArgs$$array$f[idx]
});
$c_sjsr_WrappedVarArgs.prototype.lengthCompare__I__I = (function(len) {
  var x = this.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sjsr_WrappedVarArgs.prototype.apply__O__O = (function(v1) {
  return this.apply__I__O($uI(v1))
});
$c_sjsr_WrappedVarArgs.prototype.exists__F1__Z = (function(p) {
  return $f_sc_IterableOnceOps__exists__F1__Z(this, p)
});
$c_sjsr_WrappedVarArgs.prototype.isEmpty__Z = (function() {
  return $f_sc_SeqOps__isEmpty__Z(this)
});
$c_sjsr_WrappedVarArgs.prototype.sameElements__sc_IterableOnce__Z = (function(that) {
  return $f_sc_SeqOps__sameElements__sc_IterableOnce__Z(this, that)
});
$c_sjsr_WrappedVarArgs.prototype.equals__O__Z = (function(o) {
  return $f_sc_Seq__equals__O__Z(this, o)
});
$c_sjsr_WrappedVarArgs.prototype.fromSpecific__sc_IterableOnce__O = (function(coll) {
  var this$1 = $m_sjsr_WrappedVarArgs$();
  return this$1.from__sc_IterableOnce__sjsr_WrappedVarArgs(coll)
});
$c_sjsr_WrappedVarArgs.prototype.toString__T = (function() {
  return $f_sc_Iterable__toString__T(this)
});
$c_sjsr_WrappedVarArgs.prototype.foreach__F1__V = (function(f) {
  $f_sc_IterableOnceOps__foreach__F1__V(this, f)
});
$c_sjsr_WrappedVarArgs.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_IterableOnceOps__foldLeft__O__F2__O(this, z, op)
});
$c_sjsr_WrappedVarArgs.prototype.flatMap__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__flatMap__F1__O(this, f)
});
$c_sjsr_WrappedVarArgs.prototype.copyToArray__O__I__I = (function(xs, start) {
  return $f_sc_IterableOnceOps__copyToArray__O__I__I(this, xs, start)
});
$c_sjsr_WrappedVarArgs.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sjsr_WrappedVarArgs.prototype.newSpecificBuilder__scm_Builder = (function() {
  return $m_sjsr_WrappedVarArgs$().newBuilder__scm_Builder()
});
$c_sjsr_WrappedVarArgs.prototype.size__I = (function() {
  return this.length__I()
});
$c_sjsr_WrappedVarArgs.prototype.iterator__sc_Iterator = (function() {
  var this$1 = new $c_sc_IndexedSeqView$Id(this);
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$1)
});
$c_sjsr_WrappedVarArgs.prototype.length__I = (function() {
  return $uI(this.scala$scalajs$runtime$WrappedVarArgs$$array$f.length)
});
$c_sjsr_WrappedVarArgs.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sjsr_WrappedVarArgs$()
});
$c_sjsr_WrappedVarArgs.prototype.take__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__take__I__O(this, n)
});
$c_sjsr_WrappedVarArgs.prototype.drop__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__drop__I__O(this, n)
});
$c_sjsr_WrappedVarArgs.prototype.tail__O = (function() {
  return $f_sc_IterableOps__tail__O(this)
});
$c_sjsr_WrappedVarArgs.prototype.addString__scm_StringBuilder__T__T__T__scm_StringBuilder = (function(b, start, sep, end) {
  return $f_sc_IterableOnceOps__addString__scm_StringBuilder__T__T__T__scm_StringBuilder(this, b, start, sep, end)
});
$c_sjsr_WrappedVarArgs.prototype.hashCode__I = (function() {
  return $m_s_util_hashing_MurmurHash3$().seqHash__sc_Seq__I(this)
});
$c_sjsr_WrappedVarArgs.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sjsr_WrappedVarArgs.prototype.toMap__s_Predef$$less$colon$less__sci_Map = (function(ev) {
  return $m_sci_Map$().from__sc_IterableOnce__sci_Map(this)
});
$c_sjsr_WrappedVarArgs.prototype.sum__s_math_Numeric__O = (function(num) {
  return $f_sc_IterableOnceOps__sum__s_math_Numeric__O(this, num)
});
$c_sjsr_WrappedVarArgs.prototype.withFilter__F1__sc_WithFilter = (function(p) {
  return new $c_sc_IterableOps$WithFilter().init___sc_IterableOps__F1(this, p)
});
$c_sjsr_WrappedVarArgs.prototype.className__T = (function() {
  return "WrappedVarArgs"
});
$c_sjsr_WrappedVarArgs.prototype.knownSize__I = (function() {
  return this.length__I()
});
$c_sjsr_WrappedVarArgs.prototype.iterableFactory__sc_SeqFactory = (function() {
  return $m_sjsr_WrappedVarArgs$()
});
function $is_sjsr_WrappedVarArgs(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sjsr_WrappedVarArgs)))
}
function $as_sjsr_WrappedVarArgs(obj) {
  return (($is_sjsr_WrappedVarArgs(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.scalajs.runtime.WrappedVarArgs"))
}
function $isArrayOf_sjsr_WrappedVarArgs(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sjsr_WrappedVarArgs)))
}
function $asArrayOf_sjsr_WrappedVarArgs(obj, depth) {
  return (($isArrayOf_sjsr_WrappedVarArgs(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.scalajs.runtime.WrappedVarArgs;", depth))
}
var $d_sjsr_WrappedVarArgs = new $TypeData().initClass({
  sjsr_WrappedVarArgs: 0
}, false, "scala.scalajs.runtime.WrappedVarArgs", {
  sjsr_WrappedVarArgs: 1,
  O: 1,
  sci_IndexedSeq: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_SeqOps: 1,
  sc_IndexedSeq: 1,
  sc_IndexedSeqOps: 1,
  sci_IndexedSeqOps: 1,
  sci_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sjsr_WrappedVarArgs.prototype.$classData = $d_sjsr_WrappedVarArgs;
/** @constructor */
function $c_sci_Stream$Cons(head, tl) {
  this.tail$5 = null;
  this.head$5 = null;
  this.tl$5 = null;
  this.tlEvaluated$5 = false;
  this.bitmap$0$5 = false;
  this.head$5 = head;
  this.tl$5 = tl;
  this.tlEvaluated$5 = false
}
$c_sci_Stream$Cons.prototype = new $h_sci_Stream();
$c_sci_Stream$Cons.prototype.constructor = $c_sci_Stream$Cons;
/** @constructor */
function $h_sci_Stream$Cons() {
  /*<skip>*/
}
$h_sci_Stream$Cons.prototype = $c_sci_Stream$Cons.prototype;
$c_sci_Stream$Cons.prototype.head__O = (function() {
  return this.head$5
});
$c_sci_Stream$Cons.prototype.tail__sci_Stream = (function() {
  return ((!this.bitmap$0$5) ? this.tail$lzycompute__p5__sci_Stream() : this.tail$5)
});
$c_sci_Stream$Cons.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_Stream$Cons.prototype.tailDefined__Z = (function() {
  return this.tlEvaluated$5
});
$c_sci_Stream$Cons.prototype.tail__O = (function() {
  return this.tail__sci_Stream()
});
$c_sci_Stream$Cons.prototype.headDefined__Z = (function() {
  return true
});
$c_sci_Stream$Cons.prototype.force__sci_Stream = (function() {
  return this.force__sci_Stream$Cons()
});
$c_sci_Stream$Cons.prototype.tail$lzycompute__p5__sci_Stream = (function() {
  if ((!this.bitmap$0$5)) {
    this.tlEvaluated$5 = true;
    this.tail$5 = $as_sci_Stream(this.tl$5.apply__O());
    this.bitmap$0$5 = true
  };
  this.tl$5 = null;
  return this.tail$5
});
$c_sci_Stream$Cons.prototype.force__sci_Stream$Cons = (function() {
  var these = this;
  var those = this;
  if ((!these.isEmpty__Z())) {
    these = $as_sci_Stream(these.tail__O())
  };
  while ((those !== these)) {
    if (these.isEmpty__Z()) {
      return this
    };
    these = $as_sci_Stream(these.tail__O());
    if (these.isEmpty__Z()) {
      return this
    };
    these = $as_sci_Stream(these.tail__O());
    if ((these === those)) {
      return this
    };
    those = $as_sci_Stream(those.tail__O())
  };
  return this
});
var $d_sci_Stream$Cons = new $TypeData().initClass({
  sci_Stream$Cons: 0
}, false, "scala.collection.immutable.Stream$Cons", {
  sci_Stream$Cons: 1,
  sci_Stream: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_LinearSeq: 1,
  sc_LinearSeq: 1,
  sc_LinearSeqOps: 1,
  sci_LinearSeqOps: 1
});
$c_sci_Stream$Cons.prototype.$classData = $d_sci_Stream$Cons;
/** @constructor */
function $c_sci_Stream$Empty$() {
  /*<skip>*/
}
$c_sci_Stream$Empty$.prototype = new $h_sci_Stream();
$c_sci_Stream$Empty$.prototype.constructor = $c_sci_Stream$Empty$;
/** @constructor */
function $h_sci_Stream$Empty$() {
  /*<skip>*/
}
$h_sci_Stream$Empty$.prototype = $c_sci_Stream$Empty$.prototype;
$c_sci_Stream$Empty$.prototype.head__O = (function() {
  this.head__E()
});
$c_sci_Stream$Empty$.prototype.tail__sci_Stream = (function() {
  throw new $c_jl_UnsupportedOperationException().init___T("tail of empty stream")
});
$c_sci_Stream$Empty$.prototype.isEmpty__Z = (function() {
  return true
});
$c_sci_Stream$Empty$.prototype.tailDefined__Z = (function() {
  return false
});
$c_sci_Stream$Empty$.prototype.head__E = (function() {
  throw new $c_ju_NoSuchElementException().init___T("head of empty stream")
});
$c_sci_Stream$Empty$.prototype.tail__O = (function() {
  return this.tail__sci_Stream()
});
$c_sci_Stream$Empty$.prototype.headDefined__Z = (function() {
  return false
});
$c_sci_Stream$Empty$.prototype.force__sci_Stream = (function() {
  return this
});
$c_sci_Stream$Empty$.prototype.knownSize__I = (function() {
  return 0
});
var $d_sci_Stream$Empty$ = new $TypeData().initClass({
  sci_Stream$Empty$: 0
}, false, "scala.collection.immutable.Stream$Empty$", {
  sci_Stream$Empty$: 1,
  sci_Stream: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_LinearSeq: 1,
  sc_LinearSeq: 1,
  sc_LinearSeqOps: 1,
  sci_LinearSeqOps: 1
});
$c_sci_Stream$Empty$.prototype.$classData = $d_sci_Stream$Empty$;
var $n_sci_Stream$Empty$ = (void 0);
function $m_sci_Stream$Empty$() {
  if ((!$n_sci_Stream$Empty$)) {
    $n_sci_Stream$Empty$ = new $c_sci_Stream$Empty$()
  };
  return $n_sci_Stream$Empty$
}
/** @constructor */
function $c_scm_AbstractSet() {
  /*<skip>*/
}
$c_scm_AbstractSet.prototype = new $h_sc_AbstractSet();
$c_scm_AbstractSet.prototype.constructor = $c_scm_AbstractSet;
/** @constructor */
function $h_scm_AbstractSet() {
  /*<skip>*/
}
$h_scm_AbstractSet.prototype = $c_scm_AbstractSet.prototype;
$c_scm_AbstractSet.prototype.result__O = (function() {
  return this
});
$c_scm_AbstractSet.prototype.addAll__sc_IterableOnce__scm_Growable = (function(xs) {
  return $f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this, xs)
});
$c_scm_AbstractSet.prototype.sizeHint__I__V = (function(size) {
  /*<skip>*/
});
/** @constructor */
function $c_sci_Range() {
  this.start$4 = 0;
  this.end$4 = 0;
  this.step$4 = 0;
  this.isEmpty$4 = false;
  this.scala$collection$immutable$Range$$numRangeElements$f = 0;
  this.scala$collection$immutable$Range$$lastElement$f = 0
}
$c_sci_Range.prototype = new $h_sci_AbstractSeq();
$c_sci_Range.prototype.constructor = $c_sci_Range;
/** @constructor */
function $h_sci_Range() {
  /*<skip>*/
}
$h_sci_Range.prototype = $c_sci_Range.prototype;
$c_sci_Range.prototype.copy__I__I__I__Z__sci_Range = (function(start, end, step, isInclusive) {
  return (isInclusive ? new $c_sci_Range$Inclusive(start, end, step) : new $c_sci_Range$Exclusive(start, end, step))
});
$c_sci_Range.prototype.head__O = (function() {
  return this.head__I()
});
$c_sci_Range.prototype.apply__I__O = (function(i) {
  return this.apply$mcII$sp__I__I(i)
});
$c_sci_Range.prototype.lengthCompare__I__I = (function(len) {
  var x = this.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sci_Range.prototype.apply__O__O = (function(v1) {
  var idx = $uI(v1);
  return this.apply$mcII$sp__I__I(idx)
});
$c_sci_Range.prototype.isEmpty__Z = (function() {
  return this.isEmpty$4
});
$c_sci_Range.prototype.longLength__p4__J = (function() {
  var t = this.gap__p4__J();
  var lo = t.lo$2;
  var hi$1 = t.hi$2;
  var value = this.step$4;
  var hi = (value >> 31);
  var this$2 = $m_sjsr_RuntimeLong$();
  var lo$1 = this$2.divideImpl__I__I__I__I__I(lo, hi$1, value, hi);
  var hi$2 = this$2.scala$scalajs$runtime$RuntimeLong$$hiReturn$f;
  var value$1 = (this.hasStub__p4__Z() ? 1 : 0);
  var hi$3 = (value$1 >> 31);
  var lo$2 = ((lo$1 + value$1) | 0);
  var hi$4 = ((((-2147483648) ^ lo$2) < ((-2147483648) ^ lo$1)) ? ((1 + ((hi$2 + hi$3) | 0)) | 0) : ((hi$2 + hi$3) | 0));
  return new $c_sjsr_RuntimeLong(lo$2, hi$4)
});
$c_sci_Range.prototype.locationAfterN__p4__I__I = (function(n) {
  return ((this.start$4 + $imul(this.step$4, n)) | 0)
});
$c_sci_Range.prototype.equals__O__Z = (function(other) {
  if ($is_sci_Range(other)) {
    var x2 = $as_sci_Range(other);
    if (this.isEmpty$4) {
      return x2.isEmpty$4
    } else if (((!x2.isEmpty$4) && (this.start$4 === x2.start$4))) {
      var l0 = this.last__I();
      return ((l0 === x2.last__I()) && ((this.start$4 === l0) || (this.step$4 === x2.step$4)))
    } else {
      return false
    }
  } else {
    return $f_sc_Seq__equals__O__Z(this, other)
  }
});
$c_sci_Range.prototype.apply$mcII$sp__I__I = (function(idx) {
  this.scala$collection$immutable$Range$$validateMaxLength__V();
  if (((idx < 0) || (idx >= this.scala$collection$immutable$Range$$numRangeElements$f))) {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + idx))
  } else {
    return ((this.start$4 + $imul(this.step$4, idx)) | 0)
  }
});
$c_sci_Range.prototype.init___I__I__I = (function(start, end, step) {
  this.start$4 = start;
  this.end$4 = end;
  this.step$4 = step;
  this.isEmpty$4 = ((((start > end) && (step > 0)) || ((start < end) && (step < 0))) || ((start === end) && (!this.isInclusive__Z())));
  if ((step === 0)) {
    var jsx$1;
    throw new $c_jl_IllegalArgumentException().init___T("step cannot be 0.")
  } else if (this.isEmpty$4) {
    var jsx$1 = 0
  } else {
    var t = this.longLength__p4__J();
    var lo = t.lo$2;
    var hi = t.hi$2;
    var jsx$1 = (((hi === 0) ? (((-2147483648) ^ lo) > (-1)) : (hi > 0)) ? (-1) : lo)
  };
  this.scala$collection$immutable$Range$$numRangeElements$f = jsx$1;
  switch (step) {
    case 1: {
      var jsx$2 = (this.isInclusive__Z() ? end : (((-1) + end) | 0));
      break
    }
    case (-1): {
      var jsx$2 = (this.isInclusive__Z() ? end : ((1 + end) | 0));
      break
    }
    default: {
      var t$1 = this.gap__p4__J();
      var lo$1 = t$1.lo$2;
      var hi$2 = t$1.hi$2;
      var hi$1 = (step >> 31);
      var this$2 = $m_sjsr_RuntimeLong$();
      var lo$2 = this$2.remainderImpl__I__I__I__I__I(lo$1, hi$2, step, hi$1);
      var jsx$2 = ((lo$2 !== 0) ? ((end - lo$2) | 0) : (this.isInclusive__Z() ? end : ((end - step) | 0)))
    }
  };
  this.scala$collection$immutable$Range$$lastElement$f = jsx$2;
  return this
});
$c_sci_Range.prototype.toString__T = (function() {
  var preposition = (this.isInclusive__Z() ? "to" : "until");
  var stepped = ((this.step$4 === 1) ? "" : (" by " + this.step$4));
  var prefix = (this.isEmpty$4 ? "empty " : ((!this.isExact__p4__Z()) ? "inexact " : ""));
  return (((((((prefix + "Range ") + this.start$4) + " ") + preposition) + " ") + this.end$4) + stepped)
});
$c_sci_Range.prototype.foreach__F1__V = (function(f) {
  if ((!this.isEmpty$4)) {
    var i = this.start$4;
    while (true) {
      f.apply__O__O(i);
      if ((i === this.scala$collection$immutable$Range$$lastElement$f)) {
        break
      };
      i = ((i + this.step$4) | 0)
    }
  }
});
$c_sci_Range.prototype.hasStub__p4__Z = (function() {
  return (this.isInclusive__Z() || (!this.isExact__p4__Z()))
});
$c_sci_Range.prototype.flatMap__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__flatMap__F1__O(this, f)
});
$c_sci_Range.prototype.tail__sci_Range = (function() {
  if (this.isEmpty$4) {
    $m_sci_Nil$().tail__E()
  };
  if ((this.scala$collection$immutable$Range$$numRangeElements$f === 1)) {
    var value = this.end$4;
    return new $c_sci_Range$Exclusive(value, value, this.step$4)
  } else {
    return (this.isInclusive__Z() ? new $c_sci_Range$Inclusive(((this.start$4 + this.step$4) | 0), this.end$4, this.step$4) : new $c_sci_Range$Exclusive(((this.start$4 + this.step$4) | 0), this.end$4, this.step$4))
  }
});
$c_sci_Range.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sci_Range.prototype.iterator__sc_Iterator = (function() {
  return new $c_sci_RangeIterator(this.start$4, this.step$4, this.scala$collection$immutable$Range$$lastElement$f, this.isEmpty$4)
});
$c_sci_Range.prototype.scala$collection$immutable$Range$$validateMaxLength__V = (function() {
  if ((this.scala$collection$immutable$Range$$numRangeElements$f < 0)) {
    $m_sci_Range$().scala$collection$immutable$Range$$fail__I__I__I__Z__E(this.start$4, this.end$4, this.step$4, this.isInclusive__Z())
  }
});
$c_sci_Range.prototype.length__I = (function() {
  return ((this.scala$collection$immutable$Range$$numRangeElements$f < 0) ? $m_sci_Range$().scala$collection$immutable$Range$$fail__I__I__I__Z__E(this.start$4, this.end$4, this.step$4, this.isInclusive__Z()) : this.scala$collection$immutable$Range$$numRangeElements$f)
});
$c_sci_Range.prototype.drop__I__sci_Range = (function(n) {
  if (((n <= 0) || this.isEmpty$4)) {
    return this
  } else if (((n >= this.scala$collection$immutable$Range$$numRangeElements$f) && (this.scala$collection$immutable$Range$$numRangeElements$f >= 0))) {
    var value = this.end$4;
    return new $c_sci_Range$Exclusive(value, value, this.step$4)
  } else {
    return this.copy__I__I__I__Z__sci_Range(this.locationAfterN__p4__I__I(n), this.end$4, this.step$4, this.isInclusive__Z())
  }
});
$c_sci_Range.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_IndexedSeq$()
});
$c_sci_Range.prototype.take__I__O = (function(n) {
  return this.take__I__sci_Range(n)
});
$c_sci_Range.prototype.isExact__p4__Z = (function() {
  var t = this.gap__p4__J();
  var lo = t.lo$2;
  var hi$1 = t.hi$2;
  var value = this.step$4;
  var hi = (value >> 31);
  var this$2 = $m_sjsr_RuntimeLong$();
  var lo$1 = this$2.remainderImpl__I__I__I__I__I(lo, hi$1, value, hi);
  var hi$2 = this$2.scala$scalajs$runtime$RuntimeLong$$hiReturn$f;
  return ((lo$1 === 0) && (hi$2 === 0))
});
$c_sci_Range.prototype.drop__I__O = (function(n) {
  return this.drop__I__sci_Range(n)
});
$c_sci_Range.prototype.tail__O = (function() {
  return this.tail__sci_Range()
});
$c_sci_Range.prototype.take__I__sci_Range = (function(n) {
  if (((n <= 0) || this.isEmpty$4)) {
    var value = this.start$4;
    return new $c_sci_Range$Exclusive(value, value, this.step$4)
  } else {
    return (((n >= this.scala$collection$immutable$Range$$numRangeElements$f) && (this.scala$collection$immutable$Range$$numRangeElements$f >= 0)) ? this : new $c_sci_Range$Inclusive(this.start$4, this.locationAfterN__p4__I__I((((-1) + n) | 0)), this.step$4))
  }
});
$c_sci_Range.prototype.last__I = (function() {
  return (this.isEmpty$4 ? $m_sci_Nil$().head__E() : this.scala$collection$immutable$Range$$lastElement$f)
});
$c_sci_Range.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_Range.prototype.sum__s_math_Numeric__O = (function(num) {
  return this.sum__s_math_Numeric__I(num)
});
$c_sci_Range.prototype.sum__s_math_Numeric__I = (function(num) {
  if ((num === $m_s_math_Numeric$IntIsIntegral$())) {
    if (this.isEmpty$4) {
      return 0
    } else if ((this.length__I() === 1)) {
      return this.head__I()
    } else {
      var value = this.length__I();
      var hi = (value >> 31);
      var value$1 = this.head__I();
      var hi$1 = (value$1 >> 31);
      var value$2 = this.last__I();
      var hi$2 = (value$2 >> 31);
      var lo = ((value$1 + value$2) | 0);
      var hi$3 = ((((-2147483648) ^ lo) < ((-2147483648) ^ value$1)) ? ((1 + ((hi$1 + hi$2) | 0)) | 0) : ((hi$1 + hi$2) | 0));
      var a0 = (65535 & value);
      var a1 = ((value >>> 16) | 0);
      var b0 = (65535 & lo);
      var b1 = ((lo >>> 16) | 0);
      var a0b0 = $imul(a0, b0);
      var a1b0 = $imul(a1, b0);
      var a0b1 = $imul(a0, b1);
      var lo$1 = ((a0b0 + (((a1b0 + a0b1) | 0) << 16)) | 0);
      var c1part = ((((a0b0 >>> 16) | 0) + a0b1) | 0);
      var hi$4 = (((((((($imul(value, hi$3) + $imul(hi, lo)) | 0) + $imul(a1, b1)) | 0) + ((c1part >>> 16) | 0)) | 0) + (((((65535 & c1part) + a1b0) | 0) >>> 16) | 0)) | 0);
      var this$5 = $m_sjsr_RuntimeLong$();
      var lo$2 = this$5.divideImpl__I__I__I__I__I(lo$1, hi$4, 2, 0);
      return lo$2
    }
  } else if (this.isEmpty$4) {
    return 0
  } else {
    var acc = 0;
    var i = this.head__I();
    while (true) {
      var x = acc;
      var y = i;
      var x$1 = $uI(x);
      acc = $f_s_math_Numeric$IntIsIntegral__plus__I__I__I(num, x$1, y);
      if ((i === this.scala$collection$immutable$Range$$lastElement$f)) {
        var x$2 = acc;
        var x$3 = $uI(x$2);
        return x$3
      };
      i = ((i + this.step$4) | 0)
    }
  }
});
$c_sci_Range.prototype.head__I = (function() {
  return (this.isEmpty$4 ? $m_sci_Nil$().head__E() : this.start$4)
});
$c_sci_Range.prototype.className__T = (function() {
  return "Range"
});
$c_sci_Range.prototype.knownSize__I = (function() {
  return this.length__I()
});
$c_sci_Range.prototype.iterableFactory__sc_SeqFactory = (function() {
  return $m_sci_IndexedSeq$()
});
$c_sci_Range.prototype.stringPrefix__T = (function() {
  return "IndexedSeq"
});
$c_sci_Range.prototype.gap__p4__J = (function() {
  var value = this.end$4;
  var hi = (value >> 31);
  var value$1 = this.start$4;
  var hi$1 = (value$1 >> 31);
  var lo = ((value - value$1) | 0);
  var hi$2 = ((((-2147483648) ^ lo) > ((-2147483648) ^ value)) ? (((-1) + ((hi - hi$1) | 0)) | 0) : ((hi - hi$1) | 0));
  return new $c_sjsr_RuntimeLong(lo, hi$2)
});
function $is_sci_Range(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_Range)))
}
function $as_sci_Range(obj) {
  return (($is_sci_Range(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.Range"))
}
function $isArrayOf_sci_Range(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_Range)))
}
function $asArrayOf_sci_Range(obj, depth) {
  return (($isArrayOf_sci_Range(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.Range;", depth))
}
/** @constructor */
function $c_scm_AbstractBuffer() {
  /*<skip>*/
}
$c_scm_AbstractBuffer.prototype = new $h_scm_AbstractSeq();
$c_scm_AbstractBuffer.prototype.constructor = $c_scm_AbstractBuffer;
/** @constructor */
function $h_scm_AbstractBuffer() {
  /*<skip>*/
}
$h_scm_AbstractBuffer.prototype = $c_scm_AbstractBuffer.prototype;
$c_scm_AbstractBuffer.prototype.addAll__sc_IterableOnce__scm_Growable = (function(xs) {
  return $f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this, xs)
});
/** @constructor */
function $c_scm_HashSet() {
  this.table$4 = null;
  this.table$4 = new $c_scm_FlatHashTable()
}
$c_scm_HashSet.prototype = new $h_scm_AbstractSet();
$c_scm_HashSet.prototype.constructor = $c_scm_HashSet;
/** @constructor */
function $h_scm_HashSet() {
  /*<skip>*/
}
$h_scm_HashSet.prototype = $c_scm_HashSet.prototype;
$c_scm_HashSet.prototype.isEmpty__Z = (function() {
  return (this.size__I() === 0)
});
$c_scm_HashSet.prototype.subtractOne__O__scm_HashSet = (function(elem) {
  this.table$4.removeElem__O__Z(elem);
  return this
});
$c_scm_HashSet.prototype.foreach__F1__V = (function(f) {
  var i = 0;
  var entries = this.table$4.table$1;
  var len = entries.u.length;
  while ((i < len)) {
    var curEntry = entries.get(i);
    if ((curEntry !== null)) {
      var this$1 = this.table$4;
      f.apply__O__O($f_scm_FlatHashTable$HashUtils__entryToElem__O__O(this$1, curEntry))
    };
    i = ((1 + i) | 0)
  }
});
$c_scm_HashSet.prototype.addOne__O__scm_HashSet = (function(elem) {
  this.table$4.addElem__O__Z(elem);
  return this
});
$c_scm_HashSet.prototype.size__I = (function() {
  var this$1 = this.table$4;
  return this$1.tableSize$1
});
$c_scm_HashSet.prototype.iterator__sc_Iterator = (function() {
  var this$1 = this.table$4;
  return new $c_scm_FlatHashTable$$anon$1(this$1)
});
$c_scm_HashSet.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_scm_HashSet$()
});
$c_scm_HashSet.prototype.contains__O__Z = (function(elem) {
  return this.table$4.containsElem__O__Z(elem)
});
$c_scm_HashSet.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__scm_HashSet(elem)
});
$c_scm_HashSet.prototype.knownSize__I = (function() {
  var this$1 = this.table$4;
  return this$1.tableSize$1
});
$c_scm_HashSet.prototype.stringPrefix__T = (function() {
  return "HashSet"
});
function $is_scm_HashSet(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.scm_HashSet)))
}
function $as_scm_HashSet(obj) {
  return (($is_scm_HashSet(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.mutable.HashSet"))
}
function $isArrayOf_scm_HashSet(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.scm_HashSet)))
}
function $asArrayOf_scm_HashSet(obj, depth) {
  return (($isArrayOf_scm_HashSet(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.mutable.HashSet;", depth))
}
var $d_scm_HashSet = new $TypeData().initClass({
  scm_HashSet: 0
}, false, "scala.collection.mutable.HashSet", {
  scm_HashSet: 1,
  scm_AbstractSet: 1,
  sc_AbstractSet: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Set: 1,
  sc_SetOps: 1,
  F1: 1,
  s_Equals: 1,
  scm_Set: 1,
  scm_Iterable: 1,
  scm_SetOps: 1,
  scm_Cloneable: 1,
  s_Cloneable: 1,
  jl_Cloneable: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1,
  scm_Shrinkable: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_scm_HashSet.prototype.$classData = $d_scm_HashSet;
/** @constructor */
function $c_sci_List() {
  /*<skip>*/
}
$c_sci_List.prototype = new $h_sci_AbstractSeq();
$c_sci_List.prototype.constructor = $c_sci_List;
/** @constructor */
function $h_sci_List() {
  /*<skip>*/
}
$h_sci_List.prototype = $c_sci_List.prototype;
$c_sci_List.prototype.flatMap__F1__sci_List = (function(f) {
  if ((this === $m_sci_Nil$())) {
    return $m_sci_Nil$()
  } else {
    var rest = this;
    var elem$1 = false;
    elem$1 = false;
    var elem$1$1 = null;
    elem$1$1 = null;
    var elem$1$2 = null;
    elem$1$2 = null;
    while ((rest !== $m_sci_Nil$())) {
      var this$4 = $as_sc_IterableOnce(f.apply__O__O(rest.head__O())).iterator__sc_Iterator();
      while (this$4.hasNext__Z()) {
        var arg1 = this$4.next__O();
        if ((!elem$1)) {
          elem$1$1 = new $c_sci_$colon$colon(arg1, $m_sci_Nil$());
          elem$1$2 = $as_sci_$colon$colon(elem$1$1);
          elem$1 = true
        } else {
          var nx = new $c_sci_$colon$colon(arg1, $m_sci_Nil$());
          $as_sci_$colon$colon(elem$1$2).next$5 = nx;
          elem$1$2 = nx
        }
      };
      rest = $as_sci_List(rest.tail__O())
    };
    return ((!elem$1) ? $m_sci_Nil$() : $as_sci_$colon$colon(elem$1$1))
  }
});
$c_sci_List.prototype.apply__I__O = (function(n) {
  return $f_sc_LinearSeqOps__apply__I__O(this, n)
});
$c_sci_List.prototype.map__F1__sci_List = (function(f) {
  if ((this === $m_sci_Nil$())) {
    return $m_sci_Nil$()
  } else {
    var h = new $c_sci_$colon$colon(f.apply__O__O(this.head__O()), $m_sci_Nil$());
    var t = h;
    var rest = $as_sci_List(this.tail__O());
    while ((rest !== $m_sci_Nil$())) {
      var nx = new $c_sci_$colon$colon(f.apply__O__O(rest.head__O()), $m_sci_Nil$());
      t.next$5 = nx;
      t = nx;
      rest = $as_sci_List(rest.tail__O())
    };
    return h
  }
});
$c_sci_List.prototype.lengthCompare__I__I = (function(len) {
  return ((len < 0) ? 1 : this.loop$2__p4__I__sci_List__I__I(0, this, len))
});
$c_sci_List.prototype.apply__O__O = (function(v1) {
  var n = $uI(v1);
  return $f_sc_LinearSeqOps__apply__I__O(this, n)
});
$c_sci_List.prototype.exists__F1__Z = (function(p) {
  var these = this;
  while ((!these.isEmpty__Z())) {
    if ($uZ(p.apply__O__O(these.head__O()))) {
      return true
    };
    these = $as_sci_List(these.tail__O())
  };
  return false
});
$c_sci_List.prototype.sameElements__sc_IterableOnce__Z = (function(that) {
  return $f_sc_LinearSeqOps__sameElements__sc_IterableOnce__Z(this, that)
});
$c_sci_List.prototype.equals__O__Z = (function(o) {
  if ($is_sci_List(o)) {
    var x2 = $as_sci_List(o);
    return this.listEq$1__p4__sci_List__sci_List__Z(this, x2)
  } else {
    return $f_sc_Seq__equals__O__Z(this, o)
  }
});
$c_sci_List.prototype.take__I__sci_List = (function(n) {
  if ((this.isEmpty__Z() || (n <= 0))) {
    return $m_sci_Nil$()
  } else {
    var h = new $c_sci_$colon$colon(this.head__O(), $m_sci_Nil$());
    var t = h;
    var rest = $as_sci_List(this.tail__O());
    var i = 1;
    while (true) {
      if (rest.isEmpty__Z()) {
        return this
      };
      if ((i < n)) {
        i = ((1 + i) | 0);
        var nx = new $c_sci_$colon$colon(rest.head__O(), $m_sci_Nil$());
        t.next$5 = nx;
        t = nx;
        rest = $as_sci_List(rest.tail__O())
      } else {
        break
      }
    };
    return h
  }
});
$c_sci_List.prototype.loop$2__p4__I__sci_List__I__I = (function(i, xs, len$1) {
  while (true) {
    if ((i === len$1)) {
      return (xs.isEmpty__Z() ? 0 : 1)
    } else if (xs.isEmpty__Z()) {
      return (-1)
    } else {
      var temp$i = ((1 + i) | 0);
      var temp$xs = $as_sci_List(xs.tail__O());
      i = temp$i;
      xs = temp$xs
    }
  }
});
$c_sci_List.prototype.foreach__F1__V = (function(f) {
  var these = this;
  while ((!these.isEmpty__Z())) {
    f.apply__O__O(these.head__O());
    these = $as_sci_List(these.tail__O())
  }
});
$c_sci_List.prototype.flatMap__F1__O = (function(f) {
  return this.flatMap__F1__sci_List(f)
});
$c_sci_List.prototype.foldLeft__O__F2__O = (function(z, op) {
  return $f_sc_LinearSeqOps__foldLeft__O__F2__O(this, z, op)
});
$c_sci_List.prototype.listEq$1__p4__sci_List__sci_List__Z = (function(a, b) {
  while (true) {
    if ((a === b)) {
      return true
    } else {
      var aEmpty = a.isEmpty__Z();
      var bEmpty = b.isEmpty__Z();
      if (((!(aEmpty || bEmpty)) && $m_sr_BoxesRunTime$().equals__O__O__Z(a.head__O(), b.head__O()))) {
        var temp$a = $as_sci_List(a.tail__O());
        var temp$b = $as_sci_List(b.tail__O());
        a = temp$a;
        b = temp$b
      } else {
        return (aEmpty && bEmpty)
      }
    }
  }
});
$c_sci_List.prototype.filter__F1__O = (function(pred) {
  return this.filterImpl__p4__F1__Z__sci_List(pred, false)
});
$c_sci_List.prototype.iterator__sc_Iterator = (function() {
  return new $c_sc_StrictOptimizedLinearSeqOps$$anon$1(this)
});
$c_sci_List.prototype.partialFill$1__p4__sci_List__sci_List__F1__Z__sci_List = (function(origStart, firstMiss, p$1, isFlipped$1) {
  var newHead = new $c_sci_$colon$colon(origStart.head__O(), $m_sci_Nil$());
  var toProcess = $as_sci_List(origStart.tail__O());
  var currentLast = newHead;
  while ((toProcess !== firstMiss)) {
    var newElem = new $c_sci_$colon$colon(toProcess.head__O(), $m_sci_Nil$());
    currentLast.next$5 = newElem;
    currentLast = newElem;
    toProcess = $as_sci_List(toProcess.tail__O())
  };
  var next = $as_sci_List(firstMiss.tail__O());
  var nextToCopy = next;
  while ((!next.isEmpty__Z())) {
    var head = next.head__O();
    if (($uZ(p$1.apply__O__O(head)) !== isFlipped$1)) {
      next = $as_sci_List(next.tail__O())
    } else {
      while ((nextToCopy !== next)) {
        var newElem$2 = new $c_sci_$colon$colon(nextToCopy.head__O(), $m_sci_Nil$());
        currentLast.next$5 = newElem$2;
        currentLast = newElem$2;
        nextToCopy = $as_sci_List(nextToCopy.tail__O())
      };
      nextToCopy = $as_sci_List(next.tail__O());
      next = $as_sci_List(next.tail__O())
    }
  };
  if ((!nextToCopy.isEmpty__Z())) {
    currentLast.next$5 = nextToCopy
  };
  return newHead
});
$c_sci_List.prototype.length__I = (function() {
  var these = this;
  var len = 0;
  while ((!these.isEmpty__Z())) {
    len = ((1 + len) | 0);
    these = $as_sci_List(these.tail__O())
  };
  return len
});
$c_sci_List.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_List$()
});
$c_sci_List.prototype.take__I__O = (function(n) {
  return this.take__I__sci_List(n)
});
$c_sci_List.prototype.drop__I__O = (function(n) {
  var n$1 = n;
  var s = this;
  return $f_sc_StrictOptimizedLinearSeqOps__loop$2__psc_StrictOptimizedLinearSeqOps__I__sc_LinearSeq__sc_LinearSeq(this, n$1, s)
});
$c_sci_List.prototype.noneIn$1__p4__sci_List__F1__Z__sci_List = (function(l, p$1, isFlipped$1) {
  while (true) {
    if (l.isEmpty__Z()) {
      return $m_sci_Nil$()
    } else {
      var h = l.head__O();
      var t = $as_sci_List(l.tail__O());
      if (($uZ(p$1.apply__O__O(h)) !== isFlipped$1)) {
        return this.allIn$1__p4__sci_List__sci_List__F1__Z__sci_List(l, t, p$1, isFlipped$1)
      } else {
        l = t
      }
    }
  }
});
$c_sci_List.prototype.allIn$1__p4__sci_List__sci_List__F1__Z__sci_List = (function(start, remaining, p$1, isFlipped$1) {
  while (true) {
    if (remaining.isEmpty__Z()) {
      return start
    } else {
      var x$2 = remaining.head__O();
      if (($uZ(p$1.apply__O__O(x$2)) !== isFlipped$1)) {
        remaining = $as_sci_List(remaining.tail__O())
      } else {
        return this.partialFill$1__p4__sci_List__sci_List__F1__Z__sci_List(start, remaining, p$1, isFlipped$1)
      }
    }
  }
});
$c_sci_List.prototype.filterImpl__p4__F1__Z__sci_List = (function(p, isFlipped) {
  var result = this.noneIn$1__p4__sci_List__F1__Z__sci_List(this, p, isFlipped);
  return result
});
$c_sci_List.prototype.map__F1__O = (function(f) {
  return this.map__F1__sci_List(f)
});
$c_sci_List.prototype.className__T = (function() {
  return "List"
});
$c_sci_List.prototype.iterableFactory__sc_SeqFactory = (function() {
  return $m_sci_List$()
});
$c_sci_List.prototype.stringPrefix__T = (function() {
  return "LinearSeq"
});
function $is_sci_List(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_List)))
}
function $as_sci_List(obj) {
  return (($is_sci_List(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.List"))
}
function $isArrayOf_sci_List(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_List)))
}
function $asArrayOf_sci_List(obj, depth) {
  return (($isArrayOf_sci_List(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.List;", depth))
}
/** @constructor */
function $c_sci_Range$Exclusive(start, end, step) {
  this.start$4 = 0;
  this.end$4 = 0;
  this.step$4 = 0;
  this.isEmpty$4 = false;
  this.scala$collection$immutable$Range$$numRangeElements$f = 0;
  this.scala$collection$immutable$Range$$lastElement$f = 0;
  $c_sci_Range.prototype.init___I__I__I.call(this, start, end, step)
}
$c_sci_Range$Exclusive.prototype = new $h_sci_Range();
$c_sci_Range$Exclusive.prototype.constructor = $c_sci_Range$Exclusive;
/** @constructor */
function $h_sci_Range$Exclusive() {
  /*<skip>*/
}
$h_sci_Range$Exclusive.prototype = $c_sci_Range$Exclusive.prototype;
$c_sci_Range$Exclusive.prototype.isInclusive__Z = (function() {
  return false
});
var $d_sci_Range$Exclusive = new $TypeData().initClass({
  sci_Range$Exclusive: 0
}, false, "scala.collection.immutable.Range$Exclusive", {
  sci_Range$Exclusive: 1,
  sci_Range: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_IndexedSeq: 1,
  sc_IndexedSeq: 1,
  sc_IndexedSeqOps: 1,
  sci_IndexedSeqOps: 1,
  sci_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Range$Exclusive.prototype.$classData = $d_sci_Range$Exclusive;
/** @constructor */
function $c_sci_Range$Inclusive(start, end, step) {
  this.start$4 = 0;
  this.end$4 = 0;
  this.step$4 = 0;
  this.isEmpty$4 = false;
  this.scala$collection$immutable$Range$$numRangeElements$f = 0;
  this.scala$collection$immutable$Range$$lastElement$f = 0;
  $c_sci_Range.prototype.init___I__I__I.call(this, start, end, step)
}
$c_sci_Range$Inclusive.prototype = new $h_sci_Range();
$c_sci_Range$Inclusive.prototype.constructor = $c_sci_Range$Inclusive;
/** @constructor */
function $h_sci_Range$Inclusive() {
  /*<skip>*/
}
$h_sci_Range$Inclusive.prototype = $c_sci_Range$Inclusive.prototype;
$c_sci_Range$Inclusive.prototype.isInclusive__Z = (function() {
  return true
});
var $d_sci_Range$Inclusive = new $TypeData().initClass({
  sci_Range$Inclusive: 0
}, false, "scala.collection.immutable.Range$Inclusive", {
  sci_Range$Inclusive: 1,
  sci_Range: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_IndexedSeq: 1,
  sc_IndexedSeq: 1,
  sc_IndexedSeqOps: 1,
  sci_IndexedSeqOps: 1,
  sci_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_sci_Range$Inclusive.prototype.$classData = $d_sci_Range$Inclusive;
/** @constructor */
function $c_sci_Vector(startIndex, endIndex, focus) {
  this.startIndex$4 = 0;
  this.endIndex$4 = 0;
  this.focus$4 = 0;
  this.dirty$4 = false;
  this.depth$4 = 0;
  this.display0$4 = null;
  this.display1$4 = null;
  this.display2$4 = null;
  this.display3$4 = null;
  this.display4$4 = null;
  this.display5$4 = null;
  this.startIndex$4 = startIndex;
  this.endIndex$4 = endIndex;
  this.focus$4 = focus;
  this.dirty$4 = false
}
$c_sci_Vector.prototype = new $h_sci_AbstractSeq();
$c_sci_Vector.prototype.constructor = $c_sci_Vector;
/** @constructor */
function $h_sci_Vector() {
  /*<skip>*/
}
$h_sci_Vector.prototype = $c_sci_Vector.prototype;
$c_sci_Vector.prototype.checkRangeConvert__p4__I__I = (function(index) {
  var idx = ((index + this.startIndex$4) | 0);
  if (((index >= 0) && (idx < this.endIndex$4))) {
    return idx
  } else {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + index))
  }
});
$c_sci_Vector.prototype.display3__AO = (function() {
  return this.display3$4
});
$c_sci_Vector.prototype.gotoPosWritable__p4__I__I__I__V = (function(oldIndex, newIndex, xor) {
  if (this.dirty$4) {
    $f_sci_VectorPointer__gotoPosWritable1__I__I__I__V(this, oldIndex, newIndex, xor)
  } else {
    $f_sci_VectorPointer__gotoPosWritable0__I__I__V(this, newIndex, xor);
    this.dirty$4 = true
  }
});
$c_sci_Vector.prototype.head__O = (function() {
  if ($f_sc_SeqOps__isEmpty__Z(this)) {
    throw new $c_ju_NoSuchElementException().init___T("empty.head")
  };
  return this.apply__I__O(0)
});
$c_sci_Vector.prototype.apply__I__O = (function(index) {
  var idx = this.checkRangeConvert__p4__I__I(index);
  var xor = (idx ^ this.focus$4);
  return $f_sci_VectorPointer__getElem__I__I__O(this, idx, xor)
});
$c_sci_Vector.prototype.lengthCompare__I__I = (function(len) {
  var x = this.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sci_Vector.prototype.depth__I = (function() {
  return this.depth$4
});
$c_sci_Vector.prototype.apply__O__O = (function(v1) {
  return this.apply__I__O($uI(v1))
});
$c_sci_Vector.prototype.take__I__sci_Vector = (function(n) {
  if ((n <= 0)) {
    var this$1 = $m_sci_Vector$();
    return this$1.NIL$1
  } else {
    return ((this.startIndex$4 < ((this.endIndex$4 - n) | 0)) ? this.dropBack0__p4__I__sci_Vector(((this.startIndex$4 + n) | 0)) : this)
  }
});
$c_sci_Vector.prototype.initIterator__sci_VectorIterator__V = (function(s) {
  var depth = this.depth$4;
  $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s, this, depth);
  if (this.dirty$4) {
    var index = this.focus$4;
    $f_sci_VectorPointer__stabilize__I__V(s, index)
  };
  if ((s.depth$2 > 1)) {
    var index$1 = this.startIndex$4;
    var xor = (this.startIndex$4 ^ this.focus$4);
    $f_sci_VectorPointer__gotoPos__I__I__V(s, index$1, xor)
  }
});
$c_sci_Vector.prototype.display5$und$eq__AO__V = (function(x$1) {
  this.display5$4 = x$1
});
$c_sci_Vector.prototype.cleanLeftEdge__p4__I__V = (function(cutIndex) {
  if ((cutIndex < 32)) {
    this.zeroLeft__p4__AO__I__V(this.display0$4, cutIndex)
  } else if ((cutIndex < 1024)) {
    this.zeroLeft__p4__AO__I__V(this.display0$4, (31 & cutIndex));
    this.display1$4 = this.copyRight__p4__AO__I__AO(this.display1$4, ((cutIndex >>> 5) | 0))
  } else if ((cutIndex < 32768)) {
    this.zeroLeft__p4__AO__I__V(this.display0$4, (31 & cutIndex));
    this.display1$4 = this.copyRight__p4__AO__I__AO(this.display1$4, (31 & ((cutIndex >>> 5) | 0)));
    this.display2$4 = this.copyRight__p4__AO__I__AO(this.display2$4, ((cutIndex >>> 10) | 0))
  } else if ((cutIndex < 1048576)) {
    this.zeroLeft__p4__AO__I__V(this.display0$4, (31 & cutIndex));
    this.display1$4 = this.copyRight__p4__AO__I__AO(this.display1$4, (31 & ((cutIndex >>> 5) | 0)));
    this.display2$4 = this.copyRight__p4__AO__I__AO(this.display2$4, (31 & ((cutIndex >>> 10) | 0)));
    this.display3$4 = this.copyRight__p4__AO__I__AO(this.display3$4, ((cutIndex >>> 15) | 0))
  } else if ((cutIndex < 33554432)) {
    this.zeroLeft__p4__AO__I__V(this.display0$4, (31 & cutIndex));
    this.display1$4 = this.copyRight__p4__AO__I__AO(this.display1$4, (31 & ((cutIndex >>> 5) | 0)));
    this.display2$4 = this.copyRight__p4__AO__I__AO(this.display2$4, (31 & ((cutIndex >>> 10) | 0)));
    this.display3$4 = this.copyRight__p4__AO__I__AO(this.display3$4, (31 & ((cutIndex >>> 15) | 0)));
    this.display4$4 = this.copyRight__p4__AO__I__AO(this.display4$4, ((cutIndex >>> 20) | 0))
  } else if ((cutIndex < 1073741824)) {
    this.zeroLeft__p4__AO__I__V(this.display0$4, (31 & cutIndex));
    this.display1$4 = this.copyRight__p4__AO__I__AO(this.display1$4, (31 & ((cutIndex >>> 5) | 0)));
    this.display2$4 = this.copyRight__p4__AO__I__AO(this.display2$4, (31 & ((cutIndex >>> 10) | 0)));
    this.display3$4 = this.copyRight__p4__AO__I__AO(this.display3$4, (31 & ((cutIndex >>> 15) | 0)));
    this.display4$4 = this.copyRight__p4__AO__I__AO(this.display4$4, (31 & ((cutIndex >>> 20) | 0)));
    this.display5$4 = this.copyRight__p4__AO__I__AO(this.display5$4, ((cutIndex >>> 25) | 0))
  } else {
    throw new $c_jl_IllegalArgumentException().init___()
  }
});
$c_sci_Vector.prototype.display0__AO = (function() {
  return this.display0$4
});
$c_sci_Vector.prototype.flatMap__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__flatMap__F1__O(this, f)
});
$c_sci_Vector.prototype.display2$und$eq__AO__V = (function(x$1) {
  this.display2$4 = x$1
});
$c_sci_Vector.prototype.display4__AO = (function() {
  return this.display4$4
});
$c_sci_Vector.prototype.shiftTopLevel__p4__I__I__V = (function(oldLeft, newLeft) {
  var x1 = (((-1) + this.depth$4) | 0);
  switch (x1) {
    case 0: {
      var array = this.display0$4;
      this.display0$4 = $f_sci_VectorPointer__copyRange__AO__I__I__AO(this, array, oldLeft, newLeft);
      break
    }
    case 1: {
      var array$1 = this.display1$4;
      this.display1$4 = $f_sci_VectorPointer__copyRange__AO__I__I__AO(this, array$1, oldLeft, newLeft);
      break
    }
    case 2: {
      var array$2 = this.display2$4;
      this.display2$4 = $f_sci_VectorPointer__copyRange__AO__I__I__AO(this, array$2, oldLeft, newLeft);
      break
    }
    case 3: {
      var array$3 = this.display3$4;
      this.display3$4 = $f_sci_VectorPointer__copyRange__AO__I__I__AO(this, array$3, oldLeft, newLeft);
      break
    }
    case 4: {
      var array$4 = this.display4$4;
      this.display4$4 = $f_sci_VectorPointer__copyRange__AO__I__I__AO(this, array$4, oldLeft, newLeft);
      break
    }
    case 5: {
      var array$5 = this.display5$4;
      this.display5$4 = $f_sci_VectorPointer__copyRange__AO__I__I__AO(this, array$5, oldLeft, newLeft);
      break
    }
    default: {
      throw new $c_s_MatchError(x1)
    }
  }
});
$c_sci_Vector.prototype.tail__sci_Vector = (function() {
  if ($f_sc_SeqOps__isEmpty__Z(this)) {
    throw new $c_jl_UnsupportedOperationException().init___T("empty.tail")
  };
  return this.drop__I__sci_Vector(1)
});
$c_sci_Vector.prototype.filter__F1__O = (function(pred) {
  return $f_sc_StrictOptimizedIterableOps__filterImpl__F1__Z__O(this, pred, false)
});
$c_sci_Vector.prototype.cleanRightEdge__p4__I__V = (function(cutIndex) {
  if ((cutIndex <= 32)) {
    this.zeroRight__p4__AO__I__V(this.display0$4, cutIndex)
  } else if ((cutIndex <= 1024)) {
    this.zeroRight__p4__AO__I__V(this.display0$4, ((1 + (31 & (((-1) + cutIndex) | 0))) | 0));
    this.display1$4 = this.copyLeft__p4__AO__I__AO(this.display1$4, ((cutIndex >>> 5) | 0))
  } else if ((cutIndex <= 32768)) {
    this.zeroRight__p4__AO__I__V(this.display0$4, ((1 + (31 & (((-1) + cutIndex) | 0))) | 0));
    this.display1$4 = this.copyLeft__p4__AO__I__AO(this.display1$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 5) | 0))) | 0));
    this.display2$4 = this.copyLeft__p4__AO__I__AO(this.display2$4, ((cutIndex >>> 10) | 0))
  } else if ((cutIndex <= 1048576)) {
    this.zeroRight__p4__AO__I__V(this.display0$4, ((1 + (31 & (((-1) + cutIndex) | 0))) | 0));
    this.display1$4 = this.copyLeft__p4__AO__I__AO(this.display1$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 5) | 0))) | 0));
    this.display2$4 = this.copyLeft__p4__AO__I__AO(this.display2$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 10) | 0))) | 0));
    this.display3$4 = this.copyLeft__p4__AO__I__AO(this.display3$4, ((cutIndex >>> 15) | 0))
  } else if ((cutIndex <= 33554432)) {
    this.zeroRight__p4__AO__I__V(this.display0$4, ((1 + (31 & (((-1) + cutIndex) | 0))) | 0));
    this.display1$4 = this.copyLeft__p4__AO__I__AO(this.display1$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 5) | 0))) | 0));
    this.display2$4 = this.copyLeft__p4__AO__I__AO(this.display2$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 10) | 0))) | 0));
    this.display3$4 = this.copyLeft__p4__AO__I__AO(this.display3$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 15) | 0))) | 0));
    this.display4$4 = this.copyLeft__p4__AO__I__AO(this.display4$4, ((cutIndex >>> 20) | 0))
  } else if ((cutIndex <= 1073741824)) {
    this.zeroRight__p4__AO__I__V(this.display0$4, ((1 + (31 & (((-1) + cutIndex) | 0))) | 0));
    this.display1$4 = this.copyLeft__p4__AO__I__AO(this.display1$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 5) | 0))) | 0));
    this.display2$4 = this.copyLeft__p4__AO__I__AO(this.display2$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 10) | 0))) | 0));
    this.display3$4 = this.copyLeft__p4__AO__I__AO(this.display3$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 15) | 0))) | 0));
    this.display4$4 = this.copyLeft__p4__AO__I__AO(this.display4$4, ((1 + (31 & (((((-1) + cutIndex) | 0) >>> 20) | 0))) | 0));
    this.display5$4 = this.copyLeft__p4__AO__I__AO(this.display5$4, ((cutIndex >>> 25) | 0))
  } else {
    throw new $c_jl_IllegalArgumentException().init___()
  }
});
$c_sci_Vector.prototype.appendedAll__sc_IterableOnce__sci_Vector = (function(suffix) {
  if ($m_sc_IterableOnceExtensionMethods$().isEmpty$extension__sc_IterableOnce__Z(suffix)) {
    return this
  } else if ($is_sc_Iterable(suffix)) {
    var x2 = $as_sc_Iterable(suffix);
    var x1$2 = x2.size__I();
    if (((x1$2 <= 2) || (x1$2 < ((this.length__I() >>> 5) | 0)))) {
      var v = new $c_sr_ObjectRef(this);
      x2.foreach__F1__V(new $c_sjsr_AnonFunction1((function($this, v$1) {
        return (function(x$2) {
          var this$3 = $as_sci_Vector(v$1.elem$1);
          v$1.elem$1 = this$3.appended__O__sci_Vector(x$2)
        })
      })(this, v)));
      return $as_sci_Vector(v.elem$1)
    } else if (((this.length__I() < ((x1$2 >>> 5) | 0)) && $is_sci_Vector(x2))) {
      var v$2 = $as_sci_Vector(x2);
      var ri = new $c_sc_IndexedSeqOps$$anon$1(this);
      while (ri.hasNext__Z()) {
        var rassoc$1 = ri.next__O();
        var this$4 = v$2;
        v$2 = this$4.prepended__O__sci_Vector(rassoc$1)
      };
      return v$2
    } else {
      return $as_sci_Vector($f_sc_StrictOptimizedSeqOps__appendedAll__sc_IterableOnce__O(this, x2))
    }
  } else {
    return $as_sci_Vector($f_sc_StrictOptimizedSeqOps__appendedAll__sc_IterableOnce__O(this, suffix))
  }
});
$c_sci_Vector.prototype.iterator__sc_Iterator = (function() {
  if ($f_sc_SeqOps__isEmpty__Z(this)) {
    return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
  } else {
    var s = new $c_sci_VectorIterator(this.startIndex$4, this.endIndex$4);
    this.initIterator__sci_VectorIterator__V(s);
    return s
  }
});
$c_sci_Vector.prototype.display1$und$eq__AO__V = (function(x$1) {
  this.display1$4 = x$1
});
$c_sci_Vector.prototype.prepended__O__sci_Vector = (function(value) {
  if ((this.endIndex$4 !== this.startIndex$4)) {
    var blockIndex = ((-32) & (((-1) + this.startIndex$4) | 0));
    var lo = (31 & (((-1) + this.startIndex$4) | 0));
    if ((this.startIndex$4 !== ((32 + blockIndex) | 0))) {
      var s = new $c_sci_Vector((((-1) + this.startIndex$4) | 0), this.endIndex$4, blockIndex);
      var depth = this.depth$4;
      $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s, this, depth);
      s.dirty$4 = this.dirty$4;
      s.gotoPosWritable__p4__I__I__I__V(this.focus$4, blockIndex, (this.focus$4 ^ blockIndex));
      s.display0$4.set(lo, value);
      var result = s
    } else {
      var freeSpace = (((1 << $imul(5, this.depth$4)) - this.endIndex$4) | 0);
      var shift = (freeSpace & (~(((-1) + (1 << $imul(5, (((-1) + this.depth$4) | 0)))) | 0)));
      var shiftBlocks = ((freeSpace >>> $imul(5, (((-1) + this.depth$4) | 0))) | 0);
      if ((shift !== 0)) {
        if ((this.depth$4 > 1)) {
          var newBlockIndex = ((blockIndex + shift) | 0);
          var newFocus = ((this.focus$4 + shift) | 0);
          var s$2 = new $c_sci_Vector((((((-1) + this.startIndex$4) | 0) + shift) | 0), ((this.endIndex$4 + shift) | 0), newBlockIndex);
          var depth$1 = this.depth$4;
          $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s$2, this, depth$1);
          s$2.dirty$4 = this.dirty$4;
          s$2.shiftTopLevel__p4__I__I__V(0, shiftBlocks);
          s$2.gotoFreshPosWritable__p4__I__I__I__V(newFocus, newBlockIndex, (newFocus ^ newBlockIndex));
          s$2.display0$4.set(lo, value);
          var result = s$2
        } else {
          var newBlockIndex$2 = ((32 + blockIndex) | 0);
          var newFocus$2 = this.focus$4;
          var s$3 = new $c_sci_Vector((((((-1) + this.startIndex$4) | 0) + shift) | 0), ((this.endIndex$4 + shift) | 0), newBlockIndex$2);
          var depth$2 = this.depth$4;
          $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s$3, this, depth$2);
          s$3.dirty$4 = this.dirty$4;
          s$3.shiftTopLevel__p4__I__I__V(0, shiftBlocks);
          s$3.gotoPosWritable__p4__I__I__I__V(newFocus$2, newBlockIndex$2, (newFocus$2 ^ newBlockIndex$2));
          s$3.display0$4.set((((-1) + shift) | 0), value);
          var result = s$3
        }
      } else if ((blockIndex < 0)) {
        var move = (((1 << $imul(5, ((1 + this.depth$4) | 0))) - (1 << $imul(5, this.depth$4))) | 0);
        var newBlockIndex$3 = ((blockIndex + move) | 0);
        var newFocus$3 = ((this.focus$4 + move) | 0);
        var s$4 = new $c_sci_Vector((((((-1) + this.startIndex$4) | 0) + move) | 0), ((this.endIndex$4 + move) | 0), newBlockIndex$3);
        var depth$3 = this.depth$4;
        $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s$4, this, depth$3);
        s$4.dirty$4 = this.dirty$4;
        s$4.gotoFreshPosWritable__p4__I__I__I__V(newFocus$3, newBlockIndex$3, (newFocus$3 ^ newBlockIndex$3));
        s$4.display0$4.set(lo, value);
        var result = s$4
      } else {
        var newFocus$4 = this.focus$4;
        var s$5 = new $c_sci_Vector((((-1) + this.startIndex$4) | 0), this.endIndex$4, blockIndex);
        var depth$4 = this.depth$4;
        $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s$5, this, depth$4);
        s$5.dirty$4 = this.dirty$4;
        s$5.gotoFreshPosWritable__p4__I__I__I__V(newFocus$4, blockIndex, (newFocus$4 ^ blockIndex));
        s$5.display0$4.set(lo, value);
        var result = s$5
      }
    }
  } else {
    var elems = $newArrayObject($d_O.getArrayOf(), [32]);
    elems.set(31, value);
    var s$6 = new $c_sci_Vector(31, 32, 0);
    s$6.depth$4 = 1;
    s$6.display0$4 = elems;
    var result = s$6
  };
  return result
});
$c_sci_Vector.prototype.zeroRight__p4__AO__I__V = (function(array, index) {
  var i = index;
  while ((i < array.u.length)) {
    array.set(i, null);
    i = ((1 + i) | 0)
  }
});
$c_sci_Vector.prototype.length__I = (function() {
  return ((this.endIndex$4 - this.startIndex$4) | 0)
});
$c_sci_Vector.prototype.display4$und$eq__AO__V = (function(x$1) {
  this.display4$4 = x$1
});
$c_sci_Vector.prototype.gotoFreshPosWritable__p4__I__I__I__V = (function(oldIndex, newIndex, xor) {
  if (this.dirty$4) {
    $f_sci_VectorPointer__gotoFreshPosWritable1__I__I__I__V(this, oldIndex, newIndex, xor)
  } else {
    $f_sci_VectorPointer__gotoFreshPosWritable0__I__I__I__V(this, oldIndex, newIndex, xor);
    this.dirty$4 = true
  }
});
$c_sci_Vector.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sci_Vector$()
});
$c_sci_Vector.prototype.display1__AO = (function() {
  return this.display1$4
});
$c_sci_Vector.prototype.take__I__O = (function(n) {
  return this.take__I__sci_Vector(n)
});
$c_sci_Vector.prototype.drop__I__O = (function(n) {
  return this.drop__I__sci_Vector(n)
});
$c_sci_Vector.prototype.display5__AO = (function() {
  return this.display5$4
});
$c_sci_Vector.prototype.tail__O = (function() {
  return this.tail__sci_Vector()
});
$c_sci_Vector.prototype.requiredDepth__p4__I__I = (function(xor) {
  if ((xor < 32)) {
    return 1
  } else if ((xor < 1024)) {
    return 2
  } else if ((xor < 32768)) {
    return 3
  } else if ((xor < 1048576)) {
    return 4
  } else if ((xor < 33554432)) {
    return 5
  } else if ((xor < 1073741824)) {
    return 6
  } else {
    throw new $c_jl_IllegalArgumentException().init___()
  }
});
$c_sci_Vector.prototype.dropBack0__p4__I__sci_Vector = (function(cutIndex) {
  var blockIndex = ((-32) & (((-1) + cutIndex) | 0));
  var xor = (this.startIndex$4 ^ (((-1) + cutIndex) | 0));
  var d = this.requiredDepth__p4__I__I(xor);
  var shift = (this.startIndex$4 & (~(((-1) + (1 << $imul(5, d))) | 0)));
  var s = new $c_sci_Vector(((this.startIndex$4 - shift) | 0), ((cutIndex - shift) | 0), ((blockIndex - shift) | 0));
  var depth = this.depth$4;
  $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s, this, depth);
  s.dirty$4 = this.dirty$4;
  s.gotoPosWritable__p4__I__I__I__V(this.focus$4, blockIndex, (this.focus$4 ^ blockIndex));
  $f_sci_VectorPointer__preClean__I__V(s, d);
  s.cleanRightEdge__p4__I__V(((cutIndex - shift) | 0));
  return s
});
$c_sci_Vector.prototype.zeroLeft__p4__AO__I__V = (function(array, index) {
  var i = 0;
  while ((i < index)) {
    array.set(i, null);
    i = ((1 + i) | 0)
  }
});
$c_sci_Vector.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_sci_Vector.prototype.depth$und$eq__I__V = (function(x$1) {
  this.depth$4 = x$1
});
$c_sci_Vector.prototype.display2__AO = (function() {
  return this.display2$4
});
$c_sci_Vector.prototype.dropFront0__p4__I__sci_Vector = (function(cutIndex) {
  var blockIndex = ((-32) & cutIndex);
  var xor = (cutIndex ^ (((-1) + this.endIndex$4) | 0));
  var d = this.requiredDepth__p4__I__I(xor);
  var shift = (cutIndex & (~(((-1) + (1 << $imul(5, d))) | 0)));
  var s = new $c_sci_Vector(((cutIndex - shift) | 0), ((this.endIndex$4 - shift) | 0), ((blockIndex - shift) | 0));
  var depth = this.depth$4;
  $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s, this, depth);
  s.dirty$4 = this.dirty$4;
  s.gotoPosWritable__p4__I__I__I__V(this.focus$4, blockIndex, (this.focus$4 ^ blockIndex));
  $f_sci_VectorPointer__preClean__I__V(s, d);
  s.cleanLeftEdge__p4__I__V(((cutIndex - shift) | 0));
  return s
});
$c_sci_Vector.prototype.display0$und$eq__AO__V = (function(x$1) {
  this.display0$4 = x$1
});
$c_sci_Vector.prototype.className__T = (function() {
  return "Vector"
});
$c_sci_Vector.prototype.drop__I__sci_Vector = (function(n) {
  if ((n <= 0)) {
    return this
  } else if ((this.startIndex$4 < ((this.endIndex$4 - n) | 0))) {
    return this.dropFront0__p4__I__sci_Vector(((this.startIndex$4 + n) | 0))
  } else {
    var this$1 = $m_sci_Vector$();
    return this$1.NIL$1
  }
});
$c_sci_Vector.prototype.appended__O__sci_Vector = (function(value) {
  if ((this.endIndex$4 !== this.startIndex$4)) {
    var blockIndex = ((-32) & this.endIndex$4);
    var lo = (31 & this.endIndex$4);
    if ((this.endIndex$4 !== blockIndex)) {
      var s = new $c_sci_Vector(this.startIndex$4, ((1 + this.endIndex$4) | 0), blockIndex);
      var depth = this.depth$4;
      $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s, this, depth);
      s.dirty$4 = this.dirty$4;
      s.gotoPosWritable__p4__I__I__I__V(this.focus$4, blockIndex, (this.focus$4 ^ blockIndex));
      s.display0$4.set(lo, value);
      var result = s
    } else {
      var shift = (this.startIndex$4 & (~(((-1) + (1 << $imul(5, (((-1) + this.depth$4) | 0)))) | 0)));
      var shiftBlocks = ((this.startIndex$4 >>> $imul(5, (((-1) + this.depth$4) | 0))) | 0);
      if ((shift !== 0)) {
        if ((this.depth$4 > 1)) {
          var newBlockIndex = ((blockIndex - shift) | 0);
          var newFocus = ((this.focus$4 - shift) | 0);
          var s$2 = new $c_sci_Vector(((this.startIndex$4 - shift) | 0), ((((1 + this.endIndex$4) | 0) - shift) | 0), newBlockIndex);
          var depth$1 = this.depth$4;
          $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s$2, this, depth$1);
          s$2.dirty$4 = this.dirty$4;
          s$2.shiftTopLevel__p4__I__I__V(shiftBlocks, 0);
          s$2.gotoFreshPosWritable__p4__I__I__I__V(newFocus, newBlockIndex, (newFocus ^ newBlockIndex));
          s$2.display0$4.set(lo, value);
          var result = s$2
        } else {
          var newBlockIndex$2 = (((-32) + blockIndex) | 0);
          var newFocus$2 = this.focus$4;
          var s$3 = new $c_sci_Vector(((this.startIndex$4 - shift) | 0), ((((1 + this.endIndex$4) | 0) - shift) | 0), newBlockIndex$2);
          var depth$2 = this.depth$4;
          $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s$3, this, depth$2);
          s$3.dirty$4 = this.dirty$4;
          s$3.shiftTopLevel__p4__I__I__V(shiftBlocks, 0);
          s$3.gotoPosWritable__p4__I__I__I__V(newFocus$2, newBlockIndex$2, (newFocus$2 ^ newBlockIndex$2));
          s$3.display0$4.set(((32 - shift) | 0), value);
          var result = s$3
        }
      } else {
        var newFocus$3 = this.focus$4;
        var s$4 = new $c_sci_Vector(this.startIndex$4, ((1 + this.endIndex$4) | 0), blockIndex);
        var depth$3 = this.depth$4;
        $f_sci_VectorPointer__initFrom__sci_VectorPointer__I__V(s$4, this, depth$3);
        s$4.dirty$4 = this.dirty$4;
        s$4.gotoFreshPosWritable__p4__I__I__I__V(newFocus$3, blockIndex, (newFocus$3 ^ blockIndex));
        s$4.display0$4.set(lo, value);
        var result = s$4
      }
    }
  } else {
    var elems = $newArrayObject($d_O.getArrayOf(), [32]);
    elems.set(0, value);
    var s$5 = new $c_sci_Vector(0, 1, 0);
    s$5.depth$4 = 1;
    s$5.display0$4 = elems;
    var result = s$5
  };
  return result
});
$c_sci_Vector.prototype.knownSize__I = (function() {
  return this.length__I()
});
$c_sci_Vector.prototype.copyLeft__p4__AO__I__AO = (function(array, right) {
  var copy = $newArrayObject($d_O.getArrayOf(), [array.u.length]);
  $systemArraycopy(array, 0, copy, 0, right);
  return copy
});
$c_sci_Vector.prototype.iterableFactory__sc_SeqFactory = (function() {
  return $m_sci_Vector$()
});
$c_sci_Vector.prototype.stringPrefix__T = (function() {
  return "IndexedSeq"
});
$c_sci_Vector.prototype.copyRight__p4__AO__I__AO = (function(array, left) {
  var copy = $newArrayObject($d_O.getArrayOf(), [array.u.length]);
  $systemArraycopy(array, left, copy, left, ((copy.u.length - left) | 0));
  return copy
});
$c_sci_Vector.prototype.display3$und$eq__AO__V = (function(x$1) {
  this.display3$4 = x$1
});
function $is_sci_Vector(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_Vector)))
}
function $as_sci_Vector(obj) {
  return (($is_sci_Vector(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.Vector"))
}
function $isArrayOf_sci_Vector(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_Vector)))
}
function $asArrayOf_sci_Vector(obj, depth) {
  return (($isArrayOf_sci_Vector(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.Vector;", depth))
}
var $d_sci_Vector = new $TypeData().initClass({
  sci_Vector: 0
}, false, "scala.collection.immutable.Vector", {
  sci_Vector: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_IndexedSeq: 1,
  sc_IndexedSeq: 1,
  sc_IndexedSeqOps: 1,
  sci_IndexedSeqOps: 1,
  sci_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sci_VectorPointer: 1
});
$c_sci_Vector.prototype.$classData = $d_sci_Vector;
/** @constructor */
function $c_sci_$colon$colon(head, next) {
  this.head$5 = null;
  this.next$5 = null;
  this.head$5 = head;
  this.next$5 = next
}
$c_sci_$colon$colon.prototype = new $h_sci_List();
$c_sci_$colon$colon.prototype.constructor = $c_sci_$colon$colon;
/** @constructor */
function $h_sci_$colon$colon() {
  /*<skip>*/
}
$h_sci_$colon$colon.prototype = $c_sci_$colon$colon.prototype;
$c_sci_$colon$colon.prototype.head__O = (function() {
  return this.head$5
});
$c_sci_$colon$colon.prototype.productPrefix__T = (function() {
  return "::"
});
$c_sci_$colon$colon.prototype.productArity__I = (function() {
  return 2
});
$c_sci_$colon$colon.prototype.isEmpty__Z = (function() {
  return false
});
$c_sci_$colon$colon.prototype.productElement__I__O = (function(x$1) {
  switch (x$1) {
    case 0: {
      return this.head$5;
      break
    }
    case 1: {
      return this.next$5;
      break
    }
    default: {
      throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
    }
  }
});
$c_sci_$colon$colon.prototype.tail__O = (function() {
  return this.next$5
});
$c_sci_$colon$colon.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
function $is_sci_$colon$colon(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sci_$colon$colon)))
}
function $as_sci_$colon$colon(obj) {
  return (($is_sci_$colon$colon(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.immutable.$colon$colon"))
}
function $isArrayOf_sci_$colon$colon(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sci_$colon$colon)))
}
function $asArrayOf_sci_$colon$colon(obj, depth) {
  return (($isArrayOf_sci_$colon$colon(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.immutable.$colon$colon;", depth))
}
var $d_sci_$colon$colon = new $TypeData().initClass({
  sci_$colon$colon: 0
}, false, "scala.collection.immutable.$colon$colon", {
  sci_$colon$colon: 1,
  sci_List: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_LinearSeq: 1,
  sc_LinearSeq: 1,
  sc_LinearSeqOps: 1,
  sci_LinearSeqOps: 1,
  sc_StrictOptimizedLinearSeqOps: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sci_StrictOptimizedSeqOps: 1,
  s_Product: 1
});
$c_sci_$colon$colon.prototype.$classData = $d_sci_$colon$colon;
/** @constructor */
function $c_sci_Nil$() {
  /*<skip>*/
}
$c_sci_Nil$.prototype = new $h_sci_List();
$c_sci_Nil$.prototype.constructor = $c_sci_Nil$;
/** @constructor */
function $h_sci_Nil$() {
  /*<skip>*/
}
$h_sci_Nil$.prototype = $c_sci_Nil$.prototype;
$c_sci_Nil$.prototype.tail__E = (function() {
  throw new $c_jl_UnsupportedOperationException().init___T("tail of empty list")
});
$c_sci_Nil$.prototype.last__E = (function() {
  throw new $c_ju_NoSuchElementException().init___T("last of empty list")
});
$c_sci_Nil$.prototype.productPrefix__T = (function() {
  return "Nil"
});
$c_sci_Nil$.prototype.head__O = (function() {
  this.head__E()
});
$c_sci_Nil$.prototype.productArity__I = (function() {
  return 0
});
$c_sci_Nil$.prototype.isEmpty__Z = (function() {
  return true
});
$c_sci_Nil$.prototype.productElement__I__O = (function(x$1) {
  throw new $c_jl_IndexOutOfBoundsException().init___T(("" + x$1))
});
$c_sci_Nil$.prototype.head__E = (function() {
  throw new $c_ju_NoSuchElementException().init___T("head of empty list")
});
$c_sci_Nil$.prototype.iterator__sc_Iterator = (function() {
  return $m_sc_Iterator$().scala$collection$Iterator$$$undempty$f
});
$c_sci_Nil$.prototype.last__O = (function() {
  this.last__E()
});
$c_sci_Nil$.prototype.tail__O = (function() {
  this.tail__E()
});
$c_sci_Nil$.prototype.productIterator__sc_Iterator = (function() {
  return new $c_sr_ScalaRunTime$$anon$1(this)
});
$c_sci_Nil$.prototype.knownSize__I = (function() {
  return 0
});
var $d_sci_Nil$ = new $TypeData().initClass({
  sci_Nil$: 0
}, false, "scala.collection.immutable.Nil$", {
  sci_Nil$: 1,
  sci_List: 1,
  sci_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  sci_Seq: 1,
  sci_Iterable: 1,
  sci_SeqOps: 1,
  sci_LinearSeq: 1,
  sc_LinearSeq: 1,
  sc_LinearSeqOps: 1,
  sci_LinearSeqOps: 1,
  sc_StrictOptimizedLinearSeqOps: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  sci_StrictOptimizedSeqOps: 1,
  s_Product: 1
});
$c_sci_Nil$.prototype.$classData = $d_sci_Nil$;
var $n_sci_Nil$ = (void 0);
function $m_sci_Nil$() {
  if ((!$n_sci_Nil$)) {
    $n_sci_Nil$ = new $c_sci_Nil$()
  };
  return $n_sci_Nil$
}
function $is_scm_ArraySeq$ofChar(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.scm_ArraySeq$ofChar)))
}
function $as_scm_ArraySeq$ofChar(obj) {
  return (($is_scm_ArraySeq$ofChar(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.mutable.ArraySeq$ofChar"))
}
function $isArrayOf_scm_ArraySeq$ofChar(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.scm_ArraySeq$ofChar)))
}
function $asArrayOf_scm_ArraySeq$ofChar(obj, depth) {
  return (($isArrayOf_scm_ArraySeq$ofChar(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.mutable.ArraySeq$ofChar;", depth))
}
/** @constructor */
function $c_scm_StringBuilder() {
  this.underlying$4 = null
}
$c_scm_StringBuilder.prototype = new $h_scm_AbstractSeq();
$c_scm_StringBuilder.prototype.constructor = $c_scm_StringBuilder;
/** @constructor */
function $h_scm_StringBuilder() {
  /*<skip>*/
}
$h_scm_StringBuilder.prototype = $c_scm_StringBuilder.prototype;
$c_scm_StringBuilder.prototype.init___ = (function() {
  $c_scm_StringBuilder.prototype.init___jl_StringBuilder.call(this, new $c_jl_StringBuilder().init___());
  return this
});
$c_scm_StringBuilder.prototype.apply__I__O = (function(i) {
  return $bC(this.underlying$4.charAt__I__C(i))
});
$c_scm_StringBuilder.prototype.lengthCompare__I__I = (function(len) {
  var x = this.underlying$4.length__I();
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_scm_StringBuilder.prototype.apply__O__O = (function(v1) {
  var i = $uI(v1);
  return $bC(this.underlying$4.charAt__I__C(i))
});
$c_scm_StringBuilder.prototype.appendAll__sc_IterableOnce__scm_StringBuilder = (function(xs) {
  if ($is_sci_WrappedString(xs)) {
    var x2 = $as_sci_WrappedString(xs);
    var this$3 = this.underlying$4;
    $m_sci_WrappedString$();
    var str = x2.scala$collection$immutable$WrappedString$$self$4;
    this$3.java$lang$StringBuilder$$content$f = (("" + this$3.java$lang$StringBuilder$$content$f) + str)
  } else if ($is_scm_ArraySeq$ofChar(xs)) {
    var x3 = $as_scm_ArraySeq$ofChar(xs);
    this.underlying$4.append__AC__jl_StringBuilder(x3.array$5)
  } else if ($is_scm_StringBuilder(xs)) {
    var x4 = $as_scm_StringBuilder(xs);
    var this$4 = this.underlying$4;
    var s = x4.underlying$4;
    this$4.java$lang$StringBuilder$$content$f = (("" + this$4.java$lang$StringBuilder$$content$f) + s)
  } else {
    var ks = xs.knownSize__I();
    if ((ks !== 0)) {
      var b = this.underlying$4;
      if ((ks > 0)) {
        b.length__I()
      };
      var it = xs.iterator__sc_Iterator();
      while (it.hasNext__Z()) {
        var c = $uC(it.next__O());
        var str$1 = $as_T(String.fromCharCode(c));
        b.java$lang$StringBuilder$$content$f = (("" + b.java$lang$StringBuilder$$content$f) + str$1)
      }
    }
  };
  return this
});
$c_scm_StringBuilder.prototype.fromSpecific__sc_IterableOnce__O = (function(coll) {
  return new $c_scm_StringBuilder().init___().appendAll__sc_IterableOnce__scm_StringBuilder(coll)
});
$c_scm_StringBuilder.prototype.toString__T = (function() {
  return this.underlying$4.java$lang$StringBuilder$$content$f
});
$c_scm_StringBuilder.prototype.newSpecificBuilder__scm_Builder = (function() {
  return new $c_scm_GrowableBuilder().init___scm_Growable(new $c_scm_StringBuilder().init___())
});
$c_scm_StringBuilder.prototype.fromSpecific__sc_IterableOnce__sc_Iterable = (function(coll) {
  return new $c_scm_StringBuilder().init___().appendAll__sc_IterableOnce__scm_StringBuilder(coll)
});
$c_scm_StringBuilder.prototype.result__O = (function() {
  return this.underlying$4.java$lang$StringBuilder$$content$f
});
$c_scm_StringBuilder.prototype.iterator__sc_Iterator = (function() {
  var this$1 = new $c_sc_IndexedSeqView$Id(this);
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$1)
});
$c_scm_StringBuilder.prototype.length__I = (function() {
  return this.underlying$4.length__I()
});
$c_scm_StringBuilder.prototype.take__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__take__I__O(this, n)
});
$c_scm_StringBuilder.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_scm_IndexedSeq$()
});
$c_scm_StringBuilder.prototype.drop__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__drop__I__O(this, n)
});
$c_scm_StringBuilder.prototype.addAll__sc_IterableOnce__scm_Growable = (function(xs) {
  return $f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this, xs)
});
$c_scm_StringBuilder.prototype.init___jl_StringBuilder = (function(underlying) {
  this.underlying$4 = underlying;
  return this
});
$c_scm_StringBuilder.prototype.addOne__C__scm_StringBuilder = (function(x) {
  var this$1 = this.underlying$4;
  var str = $as_T(String.fromCharCode(x));
  this$1.java$lang$StringBuilder$$content$f = (("" + this$1.java$lang$StringBuilder$$content$f) + str);
  return this
});
$c_scm_StringBuilder.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__C__scm_StringBuilder($uC(elem))
});
$c_scm_StringBuilder.prototype.sizeHint__I__V = (function(size) {
  /*<skip>*/
});
$c_scm_StringBuilder.prototype.map__F1__O = (function(f) {
  return $f_sc_IndexedSeqOps__map__F1__O(this, f)
});
$c_scm_StringBuilder.prototype.knownSize__I = (function() {
  return this.underlying$4.length__I()
});
$c_scm_StringBuilder.prototype.stringPrefix__T = (function() {
  return "IndexedSeq"
});
function $is_scm_StringBuilder(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.scm_StringBuilder)))
}
function $as_scm_StringBuilder(obj) {
  return (($is_scm_StringBuilder(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.mutable.StringBuilder"))
}
function $isArrayOf_scm_StringBuilder(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.scm_StringBuilder)))
}
function $asArrayOf_scm_StringBuilder(obj, depth) {
  return (($isArrayOf_scm_StringBuilder(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.mutable.StringBuilder;", depth))
}
var $d_scm_StringBuilder = new $TypeData().initClass({
  scm_StringBuilder: 0
}, false, "scala.collection.mutable.StringBuilder", {
  scm_StringBuilder: 1,
  scm_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  scm_Seq: 1,
  scm_Iterable: 1,
  scm_SeqOps: 1,
  scm_Cloneable: 1,
  s_Cloneable: 1,
  jl_Cloneable: 1,
  scm_Builder: 1,
  scm_Growable: 1,
  scm_Clearable: 1,
  scm_IndexedSeq: 1,
  sc_IndexedSeq: 1,
  sc_IndexedSeqOps: 1,
  scm_IndexedSeqOps: 1,
  jl_CharSequence: 1
});
$c_scm_StringBuilder.prototype.$classData = $d_scm_StringBuilder;
/** @constructor */
function $c_scm_ListBuffer() {
  this.first$5 = null;
  this.last0$5 = null;
  this.aliased$5 = false;
  this.len$5 = 0;
  this.first$5 = $m_sci_Nil$();
  this.last0$5 = null;
  this.aliased$5 = false;
  this.len$5 = 0
}
$c_scm_ListBuffer.prototype = new $h_scm_AbstractBuffer();
$c_scm_ListBuffer.prototype.constructor = $c_scm_ListBuffer;
/** @constructor */
function $h_scm_ListBuffer() {
  /*<skip>*/
}
$h_scm_ListBuffer.prototype = $c_scm_ListBuffer.prototype;
$c_scm_ListBuffer.prototype.apply__I__O = (function(i) {
  var this$1 = this.first$5;
  return $f_sc_LinearSeqOps__apply__I__O(this$1, i)
});
$c_scm_ListBuffer.prototype.apply__O__O = (function(v1) {
  var i = $uI(v1);
  var this$1 = this.first$5;
  return $f_sc_LinearSeqOps__apply__I__O(this$1, i)
});
$c_scm_ListBuffer.prototype.isEmpty__Z = (function() {
  return (this.len$5 === 0)
});
$c_scm_ListBuffer.prototype.toList__sci_List = (function() {
  this.aliased$5 = (!this.isEmpty__Z());
  return this.first$5
});
$c_scm_ListBuffer.prototype.addOne__O__scm_ListBuffer = (function(elem) {
  this.ensureUnaliased__p5__V();
  var last1 = new $c_sci_$colon$colon(elem, $m_sci_Nil$());
  if ((this.len$5 === 0)) {
    this.first$5 = last1
  } else {
    this.last0$5.next$5 = last1
  };
  this.last0$5 = last1;
  this.len$5 = ((1 + this.len$5) | 0);
  return this
});
$c_scm_ListBuffer.prototype.ensureUnaliased__p5__V = (function() {
  if (this.aliased$5) {
    this.copyElems__p5__V()
  }
});
$c_scm_ListBuffer.prototype.result__O = (function() {
  return this.toList__sci_List()
});
$c_scm_ListBuffer.prototype.copyElems__p5__V = (function() {
  var this$2 = new $c_scm_ListBuffer();
  var buf = $as_scm_ListBuffer($f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this$2, this));
  this.first$5 = buf.first$5;
  this.last0$5 = buf.last0$5;
  this.aliased$5 = false
});
$c_scm_ListBuffer.prototype.iterator__sc_Iterator = (function() {
  return this.first$5.iterator__sc_Iterator()
});
$c_scm_ListBuffer.prototype.length__I = (function() {
  return this.len$5
});
$c_scm_ListBuffer.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_scm_ListBuffer$()
});
$c_scm_ListBuffer.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__scm_ListBuffer(elem)
});
$c_scm_ListBuffer.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_scm_ListBuffer.prototype.sizeHint__I__V = (function(size) {
  /*<skip>*/
});
$c_scm_ListBuffer.prototype.knownSize__I = (function() {
  return this.len$5
});
$c_scm_ListBuffer.prototype.iterableFactory__sc_SeqFactory = (function() {
  return $m_scm_ListBuffer$()
});
$c_scm_ListBuffer.prototype.stringPrefix__T = (function() {
  return "ListBuffer"
});
function $is_scm_ListBuffer(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.scm_ListBuffer)))
}
function $as_scm_ListBuffer(obj) {
  return (($is_scm_ListBuffer(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.mutable.ListBuffer"))
}
function $isArrayOf_scm_ListBuffer(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.scm_ListBuffer)))
}
function $asArrayOf_scm_ListBuffer(obj, depth) {
  return (($isArrayOf_scm_ListBuffer(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.mutable.ListBuffer;", depth))
}
var $d_scm_ListBuffer = new $TypeData().initClass({
  scm_ListBuffer: 0
}, false, "scala.collection.mutable.ListBuffer", {
  scm_ListBuffer: 1,
  scm_AbstractBuffer: 1,
  scm_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  scm_Seq: 1,
  scm_Iterable: 1,
  scm_SeqOps: 1,
  scm_Cloneable: 1,
  s_Cloneable: 1,
  jl_Cloneable: 1,
  scm_Buffer: 1,
  scm_Growable: 1,
  scm_Clearable: 1,
  scm_Shrinkable: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  scm_ReusableBuilder: 1,
  scm_Builder: 1
});
$c_scm_ListBuffer.prototype.$classData = $d_scm_ListBuffer;
/** @constructor */
function $c_scm_ArrayBuffer() {
  this.array$5 = null;
  this.size0$5 = 0
}
$c_scm_ArrayBuffer.prototype = new $h_scm_AbstractBuffer();
$c_scm_ArrayBuffer.prototype.constructor = $c_scm_ArrayBuffer;
/** @constructor */
function $h_scm_ArrayBuffer() {
  /*<skip>*/
}
$h_scm_ArrayBuffer.prototype = $c_scm_ArrayBuffer.prototype;
$c_scm_ArrayBuffer.prototype.init___ = (function() {
  $c_scm_ArrayBuffer.prototype.init___AO__I.call(this, $newArrayObject($d_O.getArrayOf(), [16]), 0);
  return this
});
$c_scm_ArrayBuffer.prototype.apply__I__O = (function(n) {
  var hi = ((1 + n) | 0);
  if ((n < 0)) {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + n))
  };
  if ((hi > this.size0$5)) {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + hi))
  };
  return this.array$5.get(n)
});
$c_scm_ArrayBuffer.prototype.lengthCompare__I__I = (function(len) {
  var x = this.size0$5;
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_scm_ArrayBuffer.prototype.apply__O__O = (function(v1) {
  return this.apply__I__O($uI(v1))
});
$c_scm_ArrayBuffer.prototype.copyToArray__O__I__I__I = (function(xs, start, len) {
  var srcLen = this.size0$5;
  var destLen = $m_sr_ScalaRunTime$().array$undlength__O__I(xs);
  var x = ((len < srcLen) ? len : srcLen);
  var y = ((destLen - start) | 0);
  var x$1 = ((x < y) ? x : y);
  var copied = ((x$1 > 0) ? x$1 : 0);
  if ((copied > 0)) {
    $m_s_Array$().copy__O__I__O__I__I__V(this.array$5, 0, xs, start, copied)
  };
  return copied
});
$c_scm_ArrayBuffer.prototype.update__I__O__V = (function(index, elem) {
  var hi = ((1 + index) | 0);
  if ((index < 0)) {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + index))
  };
  if ((hi > this.size0$5)) {
    throw new $c_jl_IndexOutOfBoundsException().init___T(("" + hi))
  };
  this.array$5.set(index, elem)
});
$c_scm_ArrayBuffer.prototype.ensureSize__I__V = (function(n) {
  this.array$5 = $m_scm_RefArrayUtils$().ensureSize__AO__I__I__AO(this.array$5, this.size0$5, n)
});
$c_scm_ArrayBuffer.prototype.copyToArray__O__I__I = (function(xs, start) {
  return this.copyToArray__O__I__I__I(xs, start, this.size0$5)
});
$c_scm_ArrayBuffer.prototype.addAll__sc_IterableOnce__scm_ArrayBuffer = (function(elems) {
  if ($is_scm_ArrayBuffer(elems)) {
    var x2 = $as_scm_ArrayBuffer(elems);
    this.ensureSize__I__V(((this.size0$5 + x2.size0$5) | 0));
    $m_s_Array$().copy__O__I__O__I__I__V(x2.array$5, 0, this.array$5, this.size0$5, x2.size0$5);
    this.size0$5 = ((this.size0$5 + x2.size0$5) | 0)
  } else {
    $f_scm_Growable__addAll__sc_IterableOnce__scm_Growable(this, elems)
  };
  return this
});
$c_scm_ArrayBuffer.prototype.iterator__sc_Iterator = (function() {
  var this$1 = new $c_scm_ArrayBufferView(this.array$5, this.size0$5);
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$1)
});
$c_scm_ArrayBuffer.prototype.length__I = (function() {
  return this.size0$5
});
$c_scm_ArrayBuffer.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_scm_ArrayBuffer$()
});
$c_scm_ArrayBuffer.prototype.take__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__take__I__O(this, n)
});
$c_scm_ArrayBuffer.prototype.drop__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__drop__I__O(this, n)
});
$c_scm_ArrayBuffer.prototype.addOne__O__scm_ArrayBuffer = (function(elem) {
  var i = this.size0$5;
  this.ensureSize__I__V(((1 + this.size0$5) | 0));
  this.size0$5 = ((1 + this.size0$5) | 0);
  this.update__I__O__V(i, elem);
  return this
});
$c_scm_ArrayBuffer.prototype.addOne__O__scm_Growable = (function(elem) {
  return this.addOne__O__scm_ArrayBuffer(elem)
});
$c_scm_ArrayBuffer.prototype.map__F1__O = (function(f) {
  return $f_sc_StrictOptimizedIterableOps__map__F1__O(this, f)
});
$c_scm_ArrayBuffer.prototype.knownSize__I = (function() {
  return this.size0$5
});
$c_scm_ArrayBuffer.prototype.iterableFactory__sc_SeqFactory = (function() {
  return $m_scm_ArrayBuffer$()
});
$c_scm_ArrayBuffer.prototype.init___AO__I = (function(initialElements, initialSize) {
  this.array$5 = initialElements;
  this.size0$5 = initialSize;
  return this
});
$c_scm_ArrayBuffer.prototype.stringPrefix__T = (function() {
  return "ArrayBuffer"
});
function $is_scm_ArrayBuffer(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.scm_ArrayBuffer)))
}
function $as_scm_ArrayBuffer(obj) {
  return (($is_scm_ArrayBuffer(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.collection.mutable.ArrayBuffer"))
}
function $isArrayOf_scm_ArrayBuffer(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.scm_ArrayBuffer)))
}
function $asArrayOf_scm_ArrayBuffer(obj, depth) {
  return (($isArrayOf_scm_ArrayBuffer(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.collection.mutable.ArrayBuffer;", depth))
}
var $d_scm_ArrayBuffer = new $TypeData().initClass({
  scm_ArrayBuffer: 0
}, false, "scala.collection.mutable.ArrayBuffer", {
  scm_ArrayBuffer: 1,
  scm_AbstractBuffer: 1,
  scm_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  scm_Seq: 1,
  scm_Iterable: 1,
  scm_SeqOps: 1,
  scm_Cloneable: 1,
  s_Cloneable: 1,
  jl_Cloneable: 1,
  scm_Buffer: 1,
  scm_Growable: 1,
  scm_Clearable: 1,
  scm_Shrinkable: 1,
  scm_IndexedBuffer: 1,
  scm_IndexedSeq: 1,
  sc_IndexedSeq: 1,
  sc_IndexedSeqOps: 1,
  scm_IndexedSeqOps: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1
});
$c_scm_ArrayBuffer.prototype.$classData = $d_scm_ArrayBuffer;
/** @constructor */
function $c_sjs_js_WrappedArray() {
  this.array$5 = null
}
$c_sjs_js_WrappedArray.prototype = new $h_scm_AbstractBuffer();
$c_sjs_js_WrappedArray.prototype.constructor = $c_sjs_js_WrappedArray;
/** @constructor */
function $h_sjs_js_WrappedArray() {
  /*<skip>*/
}
$h_sjs_js_WrappedArray.prototype = $c_sjs_js_WrappedArray.prototype;
$c_sjs_js_WrappedArray.prototype.init___ = (function() {
  $c_sjs_js_WrappedArray.prototype.init___sjs_js_Array.call(this, []);
  return this
});
$c_sjs_js_WrappedArray.prototype.apply__I__O = (function(index) {
  return this.array$5[index]
});
$c_sjs_js_WrappedArray.prototype.lengthCompare__I__I = (function(len) {
  var x = $uI(this.array$5.length);
  return ((x === len) ? 0 : ((x < len) ? (-1) : 1))
});
$c_sjs_js_WrappedArray.prototype.apply__O__O = (function(v1) {
  var index = $uI(v1);
  return this.array$5[index]
});
$c_sjs_js_WrappedArray.prototype.result__O = (function() {
  return this
});
$c_sjs_js_WrappedArray.prototype.iterator__sc_Iterator = (function() {
  var this$1 = new $c_sc_IndexedSeqView$Id(this);
  return new $c_sc_IndexedSeqView$IndexedSeqViewIterator(this$1)
});
$c_sjs_js_WrappedArray.prototype.length__I = (function() {
  return $uI(this.array$5.length)
});
$c_sjs_js_WrappedArray.prototype.iterableFactory__sc_IterableFactory = (function() {
  return $m_sjs_js_WrappedArray$()
});
$c_sjs_js_WrappedArray.prototype.take__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__take__I__O(this, n)
});
$c_sjs_js_WrappedArray.prototype.drop__I__O = (function(n) {
  return $f_sc_IndexedSeqOps__drop__I__O(this, n)
});
$c_sjs_js_WrappedArray.prototype.addOne__O__scm_Growable = (function(elem) {
  this.array$5.push(elem);
  return this
});
$c_sjs_js_WrappedArray.prototype.map__F1__O = (function(f) {
  return $f_sc_IndexedSeqOps__map__F1__O(this, f)
});
$c_sjs_js_WrappedArray.prototype.sizeHint__I__V = (function(size) {
  /*<skip>*/
});
$c_sjs_js_WrappedArray.prototype.className__T = (function() {
  return "WrappedArray"
});
$c_sjs_js_WrappedArray.prototype.init___sjs_js_Array = (function(array) {
  this.array$5 = array;
  return this
});
$c_sjs_js_WrappedArray.prototype.knownSize__I = (function() {
  return $uI(this.array$5.length)
});
$c_sjs_js_WrappedArray.prototype.iterableFactory__sc_SeqFactory = (function() {
  return $m_sjs_js_WrappedArray$()
});
$c_sjs_js_WrappedArray.prototype.stringPrefix__T = (function() {
  return "IndexedSeq"
});
function $is_sjs_js_WrappedArray(obj) {
  return (!(!((obj && obj.$classData) && obj.$classData.ancestors.sjs_js_WrappedArray)))
}
function $as_sjs_js_WrappedArray(obj) {
  return (($is_sjs_js_WrappedArray(obj) || (obj === null)) ? obj : $throwClassCastException(obj, "scala.scalajs.js.WrappedArray"))
}
function $isArrayOf_sjs_js_WrappedArray(obj, depth) {
  return (!(!(((obj && obj.$classData) && (obj.$classData.arrayDepth === depth)) && obj.$classData.arrayBase.ancestors.sjs_js_WrappedArray)))
}
function $asArrayOf_sjs_js_WrappedArray(obj, depth) {
  return (($isArrayOf_sjs_js_WrappedArray(obj, depth) || (obj === null)) ? obj : $throwArrayCastException(obj, "Lscala.scalajs.js.WrappedArray;", depth))
}
var $d_sjs_js_WrappedArray = new $TypeData().initClass({
  sjs_js_WrappedArray: 0
}, false, "scala.scalajs.js.WrappedArray", {
  sjs_js_WrappedArray: 1,
  scm_AbstractBuffer: 1,
  scm_AbstractSeq: 1,
  sc_AbstractSeq: 1,
  sc_AbstractIterable: 1,
  O: 1,
  sc_Iterable: 1,
  sc_IterableOnce: 1,
  sc_IterableOps: 1,
  sc_IterableOnceOps: 1,
  s_Serializable: 1,
  Ljava_io_Serializable: 1,
  sc_Seq: 1,
  s_PartialFunction: 1,
  F1: 1,
  sc_SeqOps: 1,
  s_Equals: 1,
  scm_Seq: 1,
  scm_Iterable: 1,
  scm_SeqOps: 1,
  scm_Cloneable: 1,
  s_Cloneable: 1,
  jl_Cloneable: 1,
  scm_Buffer: 1,
  scm_Growable: 1,
  scm_Clearable: 1,
  scm_Shrinkable: 1,
  sc_StrictOptimizedSeqOps: 1,
  sc_StrictOptimizedIterableOps: 1,
  scm_IndexedSeq: 1,
  sc_IndexedSeq: 1,
  sc_IndexedSeqOps: 1,
  scm_IndexedSeqOps: 1,
  scm_IndexedBuffer: 1,
  scm_Builder: 1
});
$c_sjs_js_WrappedArray.prototype.$classData = $d_sjs_js_WrappedArray;
$L0 = new $c_sjsr_RuntimeLong(0, 0);
$e.GameListener = (function() {
  return new $c_Lcom_kos_wormpad_game_GameListener()
});
$e.WormApp = $m_Lcom_kos_wormpad_WormApp$();
$m_Lcom_kos_wormpad_WormApp$().main__AT__V($makeNativeArrayWrapper($d_T.getArrayOf(), []));
}).call(this);
//# sourceMappingURL=wormpad-fastopt.js.map
