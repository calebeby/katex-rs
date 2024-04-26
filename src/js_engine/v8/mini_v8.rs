use std::any::Any;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::Deref;
use std::rc::Rc;
use std::result::Result as StdResult;
use std::slice;
use std::string::String as StdString;
use std::sync::{Arc, Condvar, Mutex, Once};
use std::thread;
use std::time::Duration;
use std::vec;

#[derive(Clone)]
pub(crate) struct MiniV8 {
    interface: Interface,
}

impl MiniV8 {
    pub(crate) fn new() -> MiniV8 {
        initialize_v8();
        let mut isolate = v8::Isolate::new(Default::default());
        initialize_slots(&mut isolate);
        MiniV8 {
            interface: Interface::new(isolate),
        }
    }

    /// Returns the global JavaScript object.
    pub(crate) fn global(&self) -> Object {
        self.scope(|scope| {
            let global = scope.get_current_context().global(scope);
            Object {
                mv8: self.clone(),
                handle: v8::Global::new(scope, global),
            }
        })
    }

    /// Executes a JavaScript script and returns its result.
    pub(crate) fn eval<S, R>(&self, script: S) -> Result<R>
    where
        S: Into<Script>,
        R: FromValue,
    {
        let script = script.into();
        let isolate_handle = self.interface.isolate_handle();
        match (self.interface.len() == 1, script.timeout) {
            (true, Some(timeout)) => execute_with_timeout(
                timeout,
                || self.eval_inner(script),
                move || {
                    isolate_handle.terminate_execution();
                },
            )?
            .into(self),
            (false, Some(_)) => Err(Error::InvalidTimeout),
            (_, None) => self.eval_inner(script)?.into(self),
        }
    }

    fn eval_inner(&self, script: Script) -> Result<Value> {
        self.try_catch(|scope| {
            let source = create_string(scope, &script.source);
            let origin = script.origin.map(|o| {
                let name = create_string(scope, &o.name).into();
                let source_map_url = create_string(scope, "").into();
                v8::ScriptOrigin::new(
                    scope,
                    name,
                    o.line_offset,
                    o.column_offset,
                    false,
                    0,
                    source_map_url,
                    true,
                    false,
                    false,
                )
            });
            let script = v8::Script::compile(scope, source, origin.as_ref());
            self.exception(scope)?;
            let result = script.unwrap().run(scope);
            self.exception(scope)?;
            Ok(Value::from_v8_value(self, scope, result.unwrap()))
        })
    }

    /// Creates and returns a string managed by V8.
    ///
    /// # Panics
    ///
    /// Panics if source value is longer than `(1 << 28) - 16` bytes.
    fn create_string(&self, value: &str) -> String {
        self.scope(|scope| {
            let string = create_string(scope, value);
            String {
                mv8: self.clone(),
                handle: v8::Global::new(scope, string),
            }
        })
    }

    /// Creates and returns an empty `Array` managed by V8.
    fn create_array(&self) -> Array {
        self.scope(|scope| {
            let array = v8::Array::new(scope, 0);
            Array {
                mv8: self.clone(),
                handle: v8::Global::new(scope, array),
            }
        })
    }

    /// Creates and returns an empty `Object` managed by V8.
    pub(crate) fn create_object(&self) -> Object {
        self.scope(|scope| {
            let object = v8::Object::new(scope);
            Object {
                mv8: self.clone(),
                handle: v8::Global::new(scope, object),
            }
        })
    }

    // Opens a new handle scope in the global context. Nesting calls to this or `MiniV8::try_catch`
    // will cause a panic (unless a callback is entered, see `MiniV8::create_function`).
    fn scope<F, T>(&self, func: F) -> T
    where
        F: FnOnce(&mut v8::ContextScope<v8::HandleScope>) -> T,
    {
        self.interface.scope(func)
    }

    // Opens a new try-catch scope in the global context. Nesting calls to this or `MiniV8::scope`
    // will cause a panic (unless a callback is entered, see `MiniV8::create_function`).
    fn try_catch<F, T>(&self, func: F) -> T
    where
        F: FnOnce(&mut v8::TryCatch<v8::HandleScope>) -> T,
    {
        self.interface.try_catch(func)
    }

    fn exception(&self, scope: &mut v8::TryCatch<v8::HandleScope>) -> Result<()> {
        if scope.has_terminated() {
            Err(Error::Timeout)
        } else if let Some(exception) = scope.exception() {
            Err(Error::Value(Value::from_v8_value(self, scope, exception)))
        } else {
            Ok(())
        }
    }
}

#[derive(Clone)]
struct Interface(Rc<RefCell<Vec<Rc<RefCell<InterfaceEntry>>>>>);

impl Interface {
    fn len(&self) -> usize {
        self.0.borrow().len()
    }

    fn isolate_handle(&self) -> v8::IsolateHandle {
        self.top(|entry| entry.isolate_handle())
    }

    // Opens a new handle scope in the global context.
    fn scope<F, T>(&self, func: F) -> T
    where
        F: FnOnce(&mut v8::ContextScope<v8::HandleScope>) -> T,
    {
        self.top(|entry| entry.scope(func))
    }

    // Opens a new try-catch scope in the global context.
    fn try_catch<F, T>(&self, func: F) -> T
    where
        F: FnOnce(&mut v8::TryCatch<v8::HandleScope>) -> T,
    {
        self.scope(|scope| func(&mut v8::TryCatch::new(scope)))
    }

    fn new(isolate: v8::OwnedIsolate) -> Interface {
        Interface(Rc::new(RefCell::new(vec![Rc::new(RefCell::new(
            InterfaceEntry::Isolate(isolate),
        ))])))
    }

    fn top<F, T>(&self, func: F) -> T
    where
        F: FnOnce(&mut InterfaceEntry) -> T,
    {
        let top = self.0.borrow().last().unwrap().clone();
        let mut top_mut = top.borrow_mut();
        func(&mut top_mut)
    }
}

enum InterfaceEntry {
    Isolate(v8::OwnedIsolate),
}

impl InterfaceEntry {
    fn scope<F, T>(&mut self, func: F) -> T
    where
        F: FnOnce(&mut v8::ContextScope<v8::HandleScope>) -> T,
    {
        match self {
            InterfaceEntry::Isolate(isolate) => {
                let global_context = isolate.get_slot::<Global>().unwrap().context.clone();
                let scope = &mut v8::HandleScope::new(isolate);
                let context = v8::Local::new(scope, global_context);
                let scope = &mut v8::ContextScope::new(scope, context);
                func(scope)
            }
        }
    }

    fn isolate_handle(&self) -> v8::IsolateHandle {
        match self {
            InterfaceEntry::Isolate(isolate) => isolate.thread_safe_handle(),
        }
    }
}

struct Global {
    context: v8::Global<v8::Context>,
}

static INIT: Once = Once::new();

fn initialize_v8() {
    INIT.call_once(|| {
        let platform = v8::new_unprotected_default_platform(0, false).make_shared();
        v8::V8::initialize_platform(platform);
        v8::V8::initialize();
    });
}

fn initialize_slots(isolate: &mut v8::Isolate) {
    let scope = &mut v8::HandleScope::new(isolate);
    let context = v8::Context::new(scope);
    let scope = &mut v8::ContextScope::new(scope, context);
    let global_context = v8::Global::new(scope, context);
    scope.set_slot(Global {
        context: global_context,
    });
    scope.set_slot(AnyMap(Rc::new(RefCell::new(BTreeMap::new()))));
}

fn create_string<'s>(scope: &mut v8::HandleScope<'s>, value: &str) -> v8::Local<'s, v8::String> {
    v8::String::new(scope, value).expect("string exceeds maximum length")
}

struct AnyMap(Rc<RefCell<BTreeMap<StdString, Box<dyn Any>>>>);

// A JavaScript script.
#[derive(Clone, Debug, Default)]
pub(crate) struct Script {
    /// The source of the script.
    source: StdString,
    /// The maximum runtime duration of the script's execution. This cannot be set within a nested
    /// evaluation, i.e. it cannot be set when calling `MiniV8::eval` from within a `Function`
    /// created with `MiniV8::create_function` or `MiniV8::create_function_mut`.
    ///
    /// V8 can only cancel script evaluation while running actual JavaScript code. If Rust code is
    /// being executed when the timeout is triggered, the execution will continue until the
    /// evaluation has returned to running JavaScript code.
    timeout: Option<Duration>,
    /// The script's origin.
    origin: Option<ScriptOrigin>,
}

/// The origin, within a file, of a JavaScript script.
#[derive(Clone, Debug, Default)]
struct ScriptOrigin {
    /// The name of the file this script belongs to.
    name: StdString,
    /// The line at which this script starts.
    line_offset: i32,
    /// The column at which this script starts.
    column_offset: i32,
}

impl From<StdString> for Script {
    fn from(source: StdString) -> Script {
        Script {
            source,
            ..Default::default()
        }
    }
}

impl<'a> From<&'a str> for Script {
    fn from(source: &'a str) -> Script {
        source.to_string().into()
    }
}

fn execute_with_timeout<T>(
    timeout: Duration,
    execute_fn: impl FnOnce() -> T,
    timed_out_fn: impl FnOnce() + Send + 'static,
) -> T {
    let wait = Arc::new((Mutex::new(true), Condvar::new()));
    let timer_wait = wait.clone();
    thread::spawn(move || {
        let (mutex, condvar) = &*timer_wait;
        let timer = condvar
            .wait_timeout_while(mutex.lock().unwrap(), timeout, |&mut is_executing| {
                is_executing
            })
            .unwrap();
        if timer.1.timed_out() {
            timed_out_fn();
        }
    });

    let result = execute_fn();
    let (mutex, condvar) = &*wait;
    *mutex.lock().unwrap() = false;
    condvar.notify_one();
    result
}

/// A JavaScript value.
///
/// `Value`s can either hold direct values (undefined, null, booleans, numbers, dates) or references
/// (strings, arrays, functions, other objects). Cloning values (via Rust's `Clone`) of the direct
/// types defers to Rust's `Copy`, while cloning values of the referential types results in a simple
/// reference clone similar to JavaScript's own "by-reference" semantics.
#[derive(Clone)]
pub(crate) enum Value {
    /// The JavaScript value `undefined`.
    Undefined,
    /// The JavaScript value `null`.
    Null,
    /// The JavaScript value `true` or `false`.
    Boolean(bool),
    /// A JavaScript floating point number.
    Number(f64),
    /// An immutable JavaScript string, managed by V8.
    String(String),
    /// Reference to a JavaScript arrray.
    Array(Array),
    /// Reference to a JavaScript function.
    Function(Function),
    /// Reference to a JavaScript object. If a value is a function or an array in JavaScript, it
    /// will be converted to `Value::Array` or `Value::Function` instead of `Value::Object`.
    Object(Object),
}

impl Value {
    /// A wrapper around `FromValue::from_value`.
    fn into<T: FromValue>(self, mv8: &MiniV8) -> Result<T> {
        T::from_value(self, mv8)
    }

    /// Coerces a value to a boolean. Returns `true` if the value is "truthy", `false` otherwise.
    fn coerce_boolean(&self, mv8: &MiniV8) -> bool {
        match self {
            &Value::Boolean(b) => b,
            value => mv8.scope(|scope| value.to_v8_value(scope).boolean_value(scope)),
        }
    }

    /// Coerces a value to a string. Nearly all JavaScript values are coercible to strings, but this
    /// may fail with a runtime error if `toString()` fails or under otherwise extraordinary
    /// circumstances (e.g. if the ECMAScript `ToString` implementation throws an error).
    pub(crate) fn coerce_string(&self, mv8: &MiniV8) -> Result<String> {
        match self {
            Value::String(s) => Ok(s.clone()),
            value => mv8.try_catch(|scope| {
                let maybe = value.to_v8_value(scope).to_string(scope);
                mv8.exception(scope).map(|_| String {
                    mv8: mv8.clone(),
                    handle: v8::Global::new(scope, maybe.unwrap()),
                })
            }),
        }
    }

    fn type_name(&self) -> &'static str {
        match *self {
            Value::Undefined => "undefined",
            Value::Null => "null",
            Value::Boolean(_) => "boolean",
            Value::Number(_) => "number",
            Value::Function(_) => "function",
            Value::Array(_) => "array",
            Value::Object(_) => "object",
            Value::String(_) => "string",
        }
    }

    fn from_v8_value(
        mv8: &MiniV8,
        scope: &mut v8::HandleScope,
        value: v8::Local<v8::Value>,
    ) -> Value {
        if value.is_undefined() {
            Value::Undefined
        } else if value.is_null() {
            Value::Null
        } else if value.is_boolean() {
            Value::Boolean(value.boolean_value(scope))
        } else if value.is_int32() {
            Value::Number(value.int32_value(scope).unwrap() as f64)
        } else if value.is_number() {
            Value::Number(value.number_value(scope).unwrap())
        } else if value.is_string() {
            let value: v8::Local<v8::String> = value.try_into().unwrap();
            let handle = v8::Global::new(scope, value);
            Value::String(String {
                mv8: mv8.clone(),
                handle,
            })
        } else if value.is_array() {
            let value: v8::Local<v8::Array> = value.try_into().unwrap();
            let handle = v8::Global::new(scope, value);
            Value::Array(Array {
                mv8: mv8.clone(),
                handle,
            })
        } else if value.is_function() {
            let value: v8::Local<v8::Function> = value.try_into().unwrap();
            let handle = v8::Global::new(scope, value);
            Value::Function(Function {
                mv8: mv8.clone(),
                handle,
            })
        } else if value.is_object() {
            let value: v8::Local<v8::Object> = value.try_into().unwrap();
            let handle = v8::Global::new(scope, value);
            Value::Object(Object {
                mv8: mv8.clone(),
                handle,
            })
        } else {
            Value::Undefined
        }
    }

    fn to_v8_value<'s>(&self, scope: &mut v8::HandleScope<'s>) -> v8::Local<'s, v8::Value> {
        match self {
            Value::Undefined => v8::undefined(scope).into(),
            Value::Null => v8::null(scope).into(),
            Value::Boolean(v) => v8::Boolean::new(scope, *v).into(),
            Value::Number(v) => v8::Number::new(scope, *v).into(),
            Value::Function(v) => v8::Local::new(scope, v.handle.clone()).into(),
            Value::Array(v) => v8::Local::new(scope, v.handle.clone()).into(),
            Value::Object(v) => v8::Local::new(scope, v.handle.clone()).into(),
            Value::String(v) => v8::Local::new(scope, v.handle.clone()).into(),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Undefined => write!(f, "undefined"),
            Value::Null => write!(f, "null"),
            Value::Boolean(b) => write!(f, "{:?}", b),
            Value::Number(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "{:?}", s),
            Value::Array(a) => write!(f, "{:?}", a),
            Value::Function(u) => write!(f, "{:?}", u),
            Value::Object(o) => write!(f, "{:?}", o),
        }
    }
}

/// Trait for types convertible to `Value`.
pub(crate) trait ToValue {
    /// Performs the conversion.
    fn to_value(self, mv8: &MiniV8) -> Result<Value>;
}

/// Trait for types convertible from `Value`.
pub(crate) trait FromValue: Sized {
    /// Performs the conversion.
    fn from_value(value: Value, mv8: &MiniV8) -> Result<Self>;
}

/// A collection of multiple JavaScript values used for interacting with function arguments.
#[derive(Clone)]
pub(crate) struct Values(Vec<Value>);

impl Values {
    /// Creates an empty `Values`.
    fn new() -> Values {
        Values(Vec::new())
    }

    fn from_vec(vec: Vec<Value>) -> Values {
        Values(vec)
    }

    fn into_vec(self) -> Vec<Value> {
        self.0
    }
}

impl FromIterator<Value> for Values {
    fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        Values::from_vec(Vec::from_iter(iter))
    }
}

impl IntoIterator for Values {
    type Item = Value;
    type IntoIter = vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Values {
    type Item = &'a Value;
    type IntoIter = slice::Iter<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// Trait for types convertible to any number of JavaScript values.
///
/// This is a generalization of `ToValue`, allowing any number of resulting JavaScript values
/// instead of just one. Any type that implements `ToValue` will automatically implement this trait.
pub(crate) trait ToValues {
    /// Performs the conversion.
    fn to_values(self, mv8: &MiniV8) -> Result<Values>;
}

/// Trait for types that can be created from an arbitrary number of JavaScript values.
///
/// This is a generalization of `FromValue`, allowing an arbitrary number of JavaScript values to
/// participate in the conversion. Any type that implements `FromValue` will automatically implement
/// this trait.
trait FromValues: Sized {
    /// Performs the conversion.
    ///
    /// In case `values` contains more values than needed to perform the conversion, the excess
    /// values should be ignored. Similarly, if not enough values are given, conversions should
    /// assume that any missing values are undefined.
    fn from_values(values: Values, mv8: &MiniV8) -> Result<Self>;
}

/// Wraps a variable number of `T`s.
///
/// Can be used to work with variadic functions more easily. Using this type as the last argument of
/// a Rust callback will accept any number of arguments from JavaScript and convert them to the type
/// `T` using [`FromValue`]. `Variadic<T>` can also be returned from a callback, returning a
/// variable number of values to JavaScript.
#[derive(Clone)]
struct Variadic<T>(Vec<T>);

impl<T> Deref for Variadic<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// `std::result::Result` specialized for this crate's `Error` type.
type Result<T> = StdResult<T, Error>;

/// An error originating from `MiniV8` usage.
#[derive(Debug)]
pub(crate) enum Error {
    /// A JavaScript value could not be converted to the expected Rust type.
    FromJsConversionError {
        /// Name of the JavaScript type that could not be converted.
        from: &'static str,
        /// Name of the Rust type that could not be created.
        to: &'static str,
    },
    /// An evaluation timeout occurred.
    Timeout,
    /// An evaluation timeout was specified from within a Rust function embedded in V8.
    InvalidTimeout,
    /// An exception that occurred within the JavaScript environment.
    Value(Value),
}

impl Error {
    /// Normalizes an error into a JavaScript value.
    pub(crate) fn to_value(self, mv8: &MiniV8) -> Value {
        match self {
            Error::Value(value) => value,
            Error::FromJsConversionError { .. } => {
                let object = mv8.create_object();
                let _ = object.set("name", "TypeError");
                let _ = object.set("message", self.to_string());
                Value::Object(object)
            }
            _ => {
                let object = mv8.create_object();
                let _ = object.set("name", "Error");
                let _ = object.set("message", self.to_string());
                Value::Object(object)
            }
        }
    }

    fn from_js_conversion(from: &'static str, to: &'static str) -> Error {
        Error::FromJsConversionError { from, to }
    }
}

impl StdError for Error {
    fn description(&self) -> &'static str {
        "JavaScript execution error"
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::FromJsConversionError { from, to } => {
                write!(fmt, "error converting JavaScript {} to {}", from, to)
            }
            Error::Timeout => write!(fmt, "evaluation timed out"),
            Error::InvalidTimeout => write!(fmt, "invalid request for evaluation timeout"),
            Error::Value(v) => write!(fmt, "JavaScript runtime error ({})", v.type_name()),
        }
    }
}

#[derive(Clone)]
pub(crate) struct Function {
    mv8: MiniV8,
    handle: v8::Global<v8::Function>,
}

impl Function {
    /// Calls the function with the given arguments, with `this` set to `undefined`.
    pub(crate) fn call<A, R>(&self, args: A) -> Result<R>
    where
        A: ToValues,
        R: FromValue,
    {
        self.call_method(Value::Undefined, args)
    }

    /// Calls the function with the given `this` and arguments.
    fn call_method<T, A, R>(&self, this: T, args: A) -> Result<R>
    where
        T: ToValue,
        A: ToValues,
        R: FromValue,
    {
        let this = this.to_value(&self.mv8)?;
        let args = args.to_values(&self.mv8)?;
        self.mv8
            .try_catch(|scope| {
                let function = v8::Local::new(scope, self.handle.clone());
                let this = this.to_v8_value(scope);
                let args = args.into_vec();
                let args_v8: Vec<_> = args.into_iter().map(|v| v.to_v8_value(scope)).collect();
                let result = function.call(scope, this, &args_v8);
                self.mv8.exception(scope)?;
                Ok(Value::from_v8_value(&self.mv8, scope, result.unwrap()))
            })
            .and_then(|v| v.into(&self.mv8))
    }
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<function>")
    }
}

#[derive(Clone)]
pub(crate) struct String {
    mv8: MiniV8,
    handle: v8::Global<v8::String>,
}

impl String {
    /// Returns a Rust string converted from the V8 string.
    pub(crate) fn to_rust_string(&self) -> StdString {
        self.mv8
            .scope(|scope| v8::Local::new(scope, self.handle.clone()).to_rust_string_lossy(scope))
    }
}

impl fmt::Debug for String {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.to_rust_string())
    }
}

impl ToValue for Value {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(self)
    }
}

impl FromValue for Value {
    fn from_value(value: Value, _mv8: &MiniV8) -> Result<Self> {
        Ok(value)
    }
}

impl ToValue for () {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Undefined)
    }
}

impl FromValue for () {
    fn from_value(_value: Value, _mv8: &MiniV8) -> Result<Self> {
        Ok(())
    }
}

impl<T: ToValue> ToValue for Option<T> {
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        match self {
            Some(val) => val.to_value(mv8),
            None => Ok(Value::Null),
        }
    }
}

impl<T: FromValue> FromValue for Option<T> {
    fn from_value(value: Value, mv8: &MiniV8) -> Result<Self> {
        match value {
            Value::Null | Value::Undefined => Ok(None),
            value => Ok(Some(T::from_value(value, mv8)?)),
        }
    }
}

impl ToValue for String {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::String(self))
    }
}

impl FromValue for String {
    fn from_value(value: Value, mv8: &MiniV8) -> Result<String> {
        value.coerce_string(mv8)
    }
}

impl ToValue for Array {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Array(self))
    }
}

impl FromValue for Array {
    fn from_value(value: Value, _mv8: &MiniV8) -> Result<Array> {
        match value {
            Value::Array(a) => Ok(a),
            value => Err(Error::from_js_conversion(value.type_name(), "Array")),
        }
    }
}

impl ToValue for Function {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Function(self))
    }
}

impl FromValue for Function {
    fn from_value(value: Value, _mv8: &MiniV8) -> Result<Function> {
        match value {
            Value::Function(f) => Ok(f),
            value => Err(Error::from_js_conversion(value.type_name(), "Function")),
        }
    }
}

impl ToValue for Object {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Object(self))
    }
}

impl FromValue for Object {
    fn from_value(value: Value, _mv8: &MiniV8) -> Result<Object> {
        match value {
            Value::Object(o) => Ok(o),
            value => Err(Error::from_js_conversion(value.type_name(), "Object")),
        }
    }
}

impl<K, V, S> ToValue for HashMap<K, V, S>
where
    K: Eq + Hash + ToValue,
    V: ToValue,
    S: BuildHasher,
{
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        let object = mv8.create_object();
        for (k, v) in self.into_iter() {
            object.set(k, v)?;
        }
        Ok(Value::Object(object))
    }
}

impl<K, V, S> FromValue for HashMap<K, V, S>
where
    K: Eq + Hash + FromValue,
    V: FromValue,
    S: BuildHasher + Default,
{
    fn from_value(value: Value, _mv8: &MiniV8) -> Result<Self> {
        match value {
            Value::Object(o) => o.properties(false)?.collect(),
            value => Err(Error::from_js_conversion(value.type_name(), "HashMap")),
        }
    }
}

impl<K, V> ToValue for BTreeMap<K, V>
where
    K: Ord + ToValue,
    V: ToValue,
{
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        let object = mv8.create_object();
        for (k, v) in self.into_iter() {
            object.set(k, v)?;
        }
        Ok(Value::Object(object))
    }
}

impl<K, V> FromValue for BTreeMap<K, V>
where
    K: Ord + FromValue,
    V: FromValue,
{
    fn from_value(value: Value, _mv8: &MiniV8) -> Result<Self> {
        match value {
            Value::Object(o) => o.properties(false)?.collect(),
            value => Err(Error::from_js_conversion(value.type_name(), "BTreeMap")),
        }
    }
}

impl<V: ToValue> ToValue for BTreeSet<V> {
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        let array = mv8.create_array();
        for v in self.into_iter() {
            array.push(v)?;
        }
        Ok(Value::Array(array))
    }
}

impl<V: ToValue> ToValue for HashSet<V> {
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        let array = mv8.create_array();
        for v in self.into_iter() {
            array.push(v)?;
        }
        Ok(Value::Array(array))
    }
}

impl<V: ToValue> ToValue for Vec<V> {
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        let array = mv8.create_array();
        for v in self.into_iter() {
            array.push(v)?;
        }
        Ok(Value::Array(array))
    }
}

impl ToValue for bool {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Boolean(self))
    }
}

impl FromValue for bool {
    fn from_value(value: Value, mv8: &MiniV8) -> Result<Self> {
        Ok(value.coerce_boolean(mv8))
    }
}

impl ToValue for StdString {
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        Ok(Value::String(mv8.create_string(&self)))
    }
}

impl FromValue for StdString {
    fn from_value(value: Value, mv8: &MiniV8) -> Result<Self> {
        Ok(value.coerce_string(mv8)?.to_rust_string())
    }
}

impl<'a> ToValue for &'a str {
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        Ok(Value::String(mv8.create_string(self)))
    }
}

impl ToValue for i32 {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Number(self as f64))
    }
}

impl ToValue for f64 {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Number(self as f64))
    }
}

impl ToValues for Values {
    fn to_values(self, _mv8: &MiniV8) -> Result<Values> {
        Ok(self)
    }
}

impl FromValues for Values {
    fn from_values(values: Values, _mv8: &MiniV8) -> Result<Self> {
        Ok(values)
    }
}

impl<T: ToValue> ToValues for Variadic<T> {
    fn to_values(self, mv8: &MiniV8) -> Result<Values> {
        self.0
            .into_iter()
            .map(|value| value.to_value(mv8))
            .collect()
    }
}

impl<T: FromValue> FromValues for Variadic<T> {
    fn from_values(values: Values, mv8: &MiniV8) -> Result<Self> {
        values
            .into_iter()
            .map(|value| T::from_value(value, mv8))
            .collect::<Result<Vec<T>>>()
            .map(Variadic)
    }
}

impl ToValues for () {
    fn to_values(self, _mv8: &MiniV8) -> Result<Values> {
        Ok(Values::new())
    }
}

impl FromValues for () {
    fn from_values(_values: Values, _mv8: &MiniV8) -> Result<Self> {
        Ok(())
    }
}

#[derive(Clone)]
pub(crate) struct Object {
    mv8: MiniV8,
    handle: v8::Global<v8::Object>,
}

impl Object {
    /// Get an object property value using the given key. Returns `Value::Undefined` if no property
    /// with the key exists.
    ///
    /// Returns an error if `ToValue::to_value` fails for the key or if the key value could not be
    /// cast to a property key string.
    pub(crate) fn get<K: ToValue, V: FromValue>(&self, key: K) -> Result<V> {
        let key = key.to_value(&self.mv8)?;
        self.mv8
            .try_catch(|scope| {
                let object = v8::Local::new(scope, self.handle.clone());
                let key = key.to_v8_value(scope);
                let result = object.get(scope, key);
                self.mv8.exception(scope)?;
                Ok(Value::from_v8_value(&self.mv8, scope, result.unwrap()))
            })
            .and_then(|v| v.into(&self.mv8))
    }

    /// Sets an object property using the given key and value.
    ///
    /// Returns an error if `ToValue::to_value` fails for either the key or the value or if the key
    /// value could not be cast to a property key string.
    pub(crate) fn set<K: ToValue, V: ToValue>(&self, key: K, value: V) -> Result<()> {
        let key = key.to_value(&self.mv8)?;
        let value = value.to_value(&self.mv8)?;
        self.mv8.try_catch(|scope| {
            let object = v8::Local::new(scope, self.handle.clone());
            let key = key.to_v8_value(scope);
            let value = value.to_v8_value(scope);
            object.set(scope, key, value);
            self.mv8.exception(scope)
        })
    }

    /// Returns an array containing all of this object's enumerable property keys. If
    /// `include_inherited` is `false`, then only the object's own enumerable properties will be
    /// collected (similar to `Object.getOwnPropertyNames` in Javascript). If `include_inherited` is
    /// `true`, then the object's own properties and the enumerable properties from its prototype
    /// chain will be collected.
    fn keys(&self, include_inherited: bool) -> Result<Array> {
        self.mv8.try_catch(|scope| {
            let object = v8::Local::new(scope, self.handle.clone());
            let keys = if include_inherited {
                object.get_property_names(scope, Default::default())
            } else {
                object.get_own_property_names(scope, Default::default())
            };
            self.mv8.exception(scope)?;
            Ok(Array {
                mv8: self.mv8.clone(),
                handle: v8::Global::new(scope, keys.unwrap()),
            })
        })
    }

    /// Converts the object into an iterator over the object's keys and values, acting like a
    /// `for-in` loop.
    ///
    /// For information on the `include_inherited` argument, see `Object::keys`.
    fn properties<K, V>(self, include_inherited: bool) -> Result<Properties<K, V>>
    where
        K: FromValue,
        V: FromValue,
    {
        let keys = self.keys(include_inherited)?;
        Ok(Properties {
            object: self,
            keys,
            index: 0,
            _phantom: PhantomData,
        })
    }
}

impl fmt::Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let keys = match self.keys(false) {
            Ok(keys) => keys,
            Err(_) => return write!(f, "<object with keys exception>"),
        };

        let len = keys.len();
        if len == 0 {
            return write!(f, "{{}}");
        }

        write!(f, "{{ ")?;
        for i in 0..len {
            if let Ok(k) = keys
                .get::<Value>(i)
                .and_then(|k| k.coerce_string(&self.mv8))
            {
                write!(f, "{:?}: ", k)?;
                match self.get::<_, Value>(k) {
                    Ok(v) => write!(f, "{:?}", v)?,
                    Err(_) => write!(f, "?")?,
                };
            } else {
                write!(f, "?")?;
            }
            if i + 1 < len {
                write!(f, ", ")?;
            }
        }
        write!(f, " }}")
    }
}

/// An iterator over an object's keys and values, acting like a `for-in` loop.
struct Properties<K, V> {
    object: Object,
    keys: Array,
    index: u32,
    _phantom: PhantomData<(K, V)>,
}

impl<K, V> Iterator for Properties<K, V>
where
    K: FromValue,
    V: FromValue,
{
    type Item = Result<(K, V)>;

    /// This will return `Some(Err(...))` if the next property's key or value failed to be converted
    /// into `K` or `V` respectively (through `ToValue`).
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.keys.len() {
            return None;
        }

        let key = self.keys.get::<Value>(self.index);
        self.index += 1;

        let key = match key {
            Ok(v) => v,
            Err(e) => return Some(Err(e)),
        };

        let value = match self.object.get::<_, V>(key.clone()) {
            Ok(v) => v,
            Err(e) => return Some(Err(e)),
        };

        let key = match key.into(&self.object.mv8) {
            Ok(v) => v,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok((key, value)))
    }
}

#[derive(Clone)]
pub(crate) struct Array {
    mv8: MiniV8,
    handle: v8::Global<v8::Array>,
}

impl Array {
    /// Get the value using the given array index. Returns `Value::Undefined` if no element at the
    /// index exists.
    ///
    /// Returns an error if `FromValue::from_value` fails for the element.
    fn get<V: FromValue>(&self, index: u32) -> Result<V> {
        self.mv8
            .try_catch(|scope| {
                let array = v8::Local::new(scope, self.handle.clone());
                let result = array.get_index(scope, index);
                self.mv8.exception(scope)?;
                Ok(Value::from_v8_value(&self.mv8, scope, result.unwrap()))
            })
            .and_then(|v| v.into(&self.mv8))
    }

    /// Sets an array element using the given index and value.
    ///
    /// Returns an error if `ToValue::to_value` fails for the value.
    fn set<V: ToValue>(&self, index: u32, value: V) -> Result<()> {
        let value = value.to_value(&self.mv8)?;
        self.mv8.try_catch(|scope| {
            let array = v8::Local::new(scope, self.handle.clone());
            let value = value.to_v8_value(scope);
            array.set_index(scope, index, value);
            self.mv8.exception(scope)
        })
    }

    /// Returns the number of elements in the array.
    fn len(&self) -> u32 {
        self.mv8
            .scope(|scope| v8::Local::new(scope, self.handle.clone()).length())
    }

    /// Pushes an element to the end of the array. This is a shortcut for `set` using `len` as the
    /// index.
    fn push<V: ToValue>(&self, value: V) -> Result<()> {
        self.set(self.len(), value)
    }
}

impl fmt::Debug for Array {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let len = self.len();
        write!(f, "[")?;
        for i in 0..len {
            match self.get::<Value>(i) {
                Ok(v) => write!(f, "{:?}", v)?,
                Err(_) => write!(f, "?")?,
            };
            if i + 1 < len {
                write!(f, ", ")?;
            }
        }
        write!(f, "]")
    }
}
