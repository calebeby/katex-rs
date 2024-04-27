use std::cell::RefCell;
use std::fmt;
use std::iter::FromIterator;
use std::rc::Rc;
use std::result::Result as StdResult;
use std::string::String as StdString;
use std::sync::Once;
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

    pub(crate) fn call_global_function<A>(&self, func_name: StdString, args: A) -> Result<Value>
    where
        A: ToValues,
    {
        let global = self.scope(|scope| {
            let global = scope.get_current_context().global(scope);
            v8::Global::new(scope, global)
        });
        let key = func_name.to_value(self)?;
        let args = args.to_values(self)?;
        self.try_catch(|scope| {
            let object = v8::Local::new(scope, global);
            let key = key.to_v8_value(scope);
            let result: v8::Local<'_, v8::Value> = object.get(scope, key).unwrap();
            let function: v8::Local<'_, v8::Function> = result.try_into().unwrap();
            self.exception(scope)?;
            let this = Value::Undefined;
            let this = this.to_v8_value(scope);
            let args = args.into_vec();
            let args_v8: Vec<_> = args.into_iter().map(|v| v.to_v8_value(scope)).collect();
            let result = function.call(scope, this, &args_v8);
            self.exception(scope)?;
            Ok(Value::from_v8_value(self, scope, result.unwrap()))
        })
    }

    /// Executes a JavaScript script and returns its result.
    pub(crate) fn eval(&self, script: &str) -> Result<Value> {
        self.try_catch(|scope| {
            let source = create_string(scope, script);
            let script = v8::Script::compile(scope, source, None);
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
    // will cause a panic.
    fn scope<F, T>(&self, func: F) -> T
    where
        F: FnOnce(&mut v8::ContextScope<v8::HandleScope>) -> T,
    {
        self.interface.scope(func)
    }

    // Opens a new try-catch scope in the global context. Nesting calls to this or `MiniV8::scope`
    // will cause a panic.
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
}

fn create_string<'s>(scope: &mut v8::HandleScope<'s>, value: &str) -> v8::Local<'s, v8::String> {
    v8::String::new(scope, value).expect("string exceeds maximum length")
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
    /// Reference to a JavaScript object.
    Object(Object),
}

impl Value {
    /// A wrapper around `FromValue::from_value`.
    fn into<T: FromValue>(self, mv8: &MiniV8) -> Result<T> {
        T::from_value(self, mv8)
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

/// `std::result::Result` specialized for this crate's `Error` type.
type Result<T> = StdResult<T, Error>;

/// An error originating from `MiniV8` usage.
#[derive(Debug)]
pub(crate) enum Error {
    /// An evaluation timeout occurred.
    Timeout,
    /// An exception that occurred within the JavaScript environment.
    Value(Value),
}

impl Error {
    /// Normalizes an error into a JavaScript value.
    pub(crate) fn to_value(self, mv8: &MiniV8) -> Value {
        match self {
            Error::Value(value) => value,
            _ => {
                let object = mv8.create_object();
                let _ = object.set("name", "Error");
                let _ = object.set("message", self.to_string());
                Value::Object(object)
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Timeout => write!(fmt, "evaluation timed out"),
            Error::Value(v) => write!(fmt, "JavaScript runtime error ({})", v.type_name()),
        }
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

impl ToValue for String {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::String(self))
    }
}

impl ToValue for bool {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Boolean(self))
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
        Ok(Value::Number(self))
    }
}

impl ToValues for Values {
    fn to_values(self, _mv8: &MiniV8) -> Result<Values> {
        Ok(self)
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
}

impl fmt::Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let keys = match self.mv8.try_catch(|scope| -> Result<Vec<String>> {
            let object = v8::Local::new(scope, self.handle.clone());
            let keys = object.get_own_property_names(scope, Default::default());
            self.mv8.exception(scope)?;
            let keys = keys.unwrap();
            let len = keys.length();
            let keys: Result<Vec<String>> = (0..len)
                .map(|index| -> Result<String> {
                    let key = keys.get_index(scope, index).unwrap();
                    self.mv8.exception(scope)?;
                    Value::from_v8_value(&self.mv8, scope, key).coerce_string(&self.mv8)
                })
                .collect();
            keys
        }) {
            Ok(keys) => keys,
            Err(_) => return write!(f, "<object with keys exception>"),
        };

        if keys.is_empty() {
            return write!(f, "{{}}");
        }

        write!(f, "{{ ")?;
        for (i, k) in keys.iter().cloned().enumerate() {
            write!(f, "{:?}: ", k)?;
            match self.get::<_, Value>(k) {
                Ok(v) => write!(f, "{:?}", v)?,
                Err(_) => write!(f, "?")?,
            };
            if i + 1 < keys.len() {
                write!(f, ", ")?;
            }
        }
        write!(f, " }}")
    }
}
