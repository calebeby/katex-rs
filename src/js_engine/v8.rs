//! JS Engine implemented by [v8](https://crates.io/crates/v8).

use crate::js_engine::{JsEngine, JsValue};
use crate::Result;

use crate::Error;
use std::cell::RefCell;
use std::fmt;
use std::iter::FromIterator;
use std::rc::Rc;
use std::sync::Once;
use std::vec;

/// v8 Engine.
pub struct Engine(MiniV8);

impl JsEngine for Engine {
    type JsValue<'a> = Value<'a>;

    fn new() -> Result<Self> {
        Ok(Self(MiniV8::new()))
    }

    fn eval<'a>(&'a self, code: &str) -> Result<Self::JsValue<'a>> {
        let result = self.0.eval(code)?;
        Ok(Value {
            value: result,
            engine: &self.0,
        })
    }

    fn call_function<'a>(
        &'a self,
        func_name: &str,
        args: impl Iterator<Item = Self::JsValue<'a>>,
    ) -> Result<Self::JsValue<'a>> {
        let args: Values = args.map(|v| v.value).collect();
        let result = self.0.call_global_function(func_name.to_owned(), args)?;
        Ok(Value {
            value: result,
            engine: &self.0,
        })
    }

    fn create_bool_value(&self, input: bool) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: {
                let _mv8 = &self.0;
                Ok(MV8Value::Boolean(input))
            }?,
            engine: &self.0,
        })
    }

    fn create_int_value(&self, input: i32) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: {
                let _mv8 = &self.0;
                Ok(MV8Value::Number(input as f64))
            }?,
            engine: &self.0,
        })
    }

    fn create_float_value(&self, input: f64) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: {
                let _mv8 = &self.0;
                Ok(MV8Value::Number(input))
            }?,
            engine: &self.0,
        })
    }

    fn create_string_value(&self, input: String) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: {
                let mv8 = &self.0;
                Ok(MV8Value::String(mv8.create_string(&input)))
            }?,
            engine: &self.0,
        })
    }

    fn create_object_value<'a>(
        &'a self,
        input: impl Iterator<Item = (String, Self::JsValue<'a>)>,
    ) -> Result<Self::JsValue<'a>> {
        let obj = self.0.create_object();
        for (k, v) in input {
            obj.set(k, v.value)?;
        }
        Ok(Value {
            value: MV8Value::Object(obj),
            engine: &self.0,
        })
    }
}

/// v8 Value.
pub struct Value<'a> {
    value: MV8Value,
    engine: &'a MiniV8,
}

impl<'a> JsValue<'a> for Value<'a> {
    fn into_string(self) -> Result<String> {
        String::from_value(self.value, self.engine)
    }
}

impl<'a> fmt::Debug for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Value").field("value", &self.value).finish()
    }
}

#[derive(Clone)]
struct MiniV8 {
    interface: Interface,
}

impl MiniV8 {
    fn new() -> MiniV8 {
        initialize_v8();
        let mut isolate = v8::Isolate::new(Default::default());
        initialize_slots(&mut isolate);
        MiniV8 {
            interface: Interface::new(isolate),
        }
    }

    fn call_global_function<A>(&self, func_name: String, args: A) -> Result<MV8Value>
    where
        A: ToValues,
    {
        let global = self.scope(|scope| {
            let global = scope.get_current_context().global(scope);
            v8::Global::new(scope, global)
        });
        let key = Ok(MV8Value::String(self.create_string(&func_name)))?;
        let args = args.to_values(self)?;
        self.try_catch(|scope| {
            let object = v8::Local::new(scope, global);
            let key = key.to_v8_value(scope);
            let result: v8::Local<'_, v8::Value> = object.get(scope, key).unwrap();
            let function: v8::Local<'_, v8::Function> = result.try_into().unwrap();
            let this = MV8Value::Undefined;
            let this = this.to_v8_value(scope);
            let args = args.into_vec();
            let args_v8: Vec<_> = args.into_iter().map(|v| v.to_v8_value(scope)).collect();
            let result = function
                .call(scope, this, &args_v8)
                .ok_or(Error::JsExecError(
                    "Function call did not return a result".to_string(),
                ))?;
            Ok(MV8Value::from_v8_value(self, scope, result))
        })
    }

    /// Executes a JavaScript script and returns its result.
    fn eval(&self, script: &str) -> Result<MV8Value> {
        self.try_catch(|scope| {
            let source = create_string(scope, script);
            let script = v8::Script::compile(scope, source, None);
            let result = script.unwrap().run(scope);
            Ok(MV8Value::from_v8_value(self, scope, result.unwrap()))
        })
    }

    /// Creates and returns a string managed by V8.
    ///
    /// # Panics
    ///
    /// Panics if source value is longer than `(1 << 28) - 16` bytes.
    fn create_string(&self, value: &str) -> MV8String {
        self.scope(|scope| {
            let string = create_string(scope, value);
            MV8String {
                mv8: self.clone(),
                handle: v8::Global::new(scope, string),
            }
        })
    }

    /// Creates and returns an empty `Object` managed by V8.
    fn create_object(&self) -> Object {
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

    // Opens a new try-catch scope in the global context.
    // Nesting calls to this or `MiniV8::scope` will cause a panic.
    fn try_catch<F, T>(&self, func: F) -> Result<T>
    where
        F: FnOnce(&mut v8::TryCatch<v8::HandleScope>) -> Result<T>,
    {
        self.interface.try_catch(func)
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
    fn try_catch<F, T>(&self, func: F) -> Result<T>
    where
        F: FnOnce(&mut v8::TryCatch<v8::HandleScope>) -> Result<T>,
    {
        self.scope(|scope| {
            let mut try_catch = v8::TryCatch::new(scope);
            let result = func(&mut try_catch);
            match try_catch.exception() {
                Some(val) => Err(Error::JsExecError(val.to_rust_string_lossy(&mut try_catch))),
                None => Ok(result?),
            }
        })
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
enum MV8Value {
    /// The JavaScript value `undefined`.
    Undefined,
    /// The JavaScript value `null`.
    Null,
    /// The JavaScript value `true` or `false`.
    Boolean(bool),
    /// A JavaScript floating point number.
    Number(f64),
    /// An immutable JavaScript string, managed by V8.
    String(MV8String),
    /// Reference to a JavaScript object.
    Object(Object),
}

impl MV8Value {
    /// Coerces a value to a string. Nearly all JavaScript values are coercible to strings, but this
    /// may fail with a runtime error if `toString()` fails or under otherwise extraordinary
    /// circumstances (e.g. if the ECMAScript `ToString` implementation throws an error).
    fn coerce_string(&self, mv8: &MiniV8) -> Result<MV8String> {
        match self {
            MV8Value::String(s) => Ok(s.clone()),
            value => mv8.try_catch(|scope| {
                let maybe = value.to_v8_value(scope).to_string(scope);
                Ok(MV8String {
                    mv8: mv8.clone(),
                    handle: v8::Global::new(scope, maybe.unwrap()),
                })
            }),
        }
    }

    fn from_v8_value(
        mv8: &MiniV8,
        scope: &mut v8::HandleScope,
        value: v8::Local<v8::Value>,
    ) -> MV8Value {
        if value.is_undefined() {
            MV8Value::Undefined
        } else if value.is_null() {
            MV8Value::Null
        } else if value.is_boolean() {
            MV8Value::Boolean(value.boolean_value(scope))
        } else if value.is_int32() {
            MV8Value::Number(value.int32_value(scope).unwrap() as f64)
        } else if value.is_number() {
            MV8Value::Number(value.number_value(scope).unwrap())
        } else if value.is_string() {
            let value: v8::Local<v8::String> = value.try_into().unwrap();
            let handle = v8::Global::new(scope, value);
            MV8Value::String(MV8String {
                mv8: mv8.clone(),
                handle,
            })
        } else if value.is_object() {
            let value: v8::Local<v8::Object> = value.try_into().unwrap();
            let handle = v8::Global::new(scope, value);
            MV8Value::Object(Object {
                mv8: mv8.clone(),
                handle,
            })
        } else {
            MV8Value::Undefined
        }
    }

    fn to_v8_value<'s>(&self, scope: &mut v8::HandleScope<'s>) -> v8::Local<'s, v8::Value> {
        match self {
            MV8Value::Undefined => v8::undefined(scope).into(),
            MV8Value::Null => v8::null(scope).into(),
            MV8Value::Boolean(v) => v8::Boolean::new(scope, *v).into(),
            MV8Value::Number(v) => v8::Number::new(scope, *v).into(),
            MV8Value::Object(v) => v8::Local::new(scope, v.handle.clone()).into(),
            MV8Value::String(v) => v8::Local::new(scope, v.handle.clone()).into(),
        }
    }
}

impl fmt::Debug for MV8Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MV8Value::Undefined => write!(f, "undefined"),
            MV8Value::Null => write!(f, "null"),
            MV8Value::Boolean(b) => write!(f, "{:?}", b),
            MV8Value::Number(n) => write!(f, "{}", n),
            MV8Value::String(s) => write!(f, "{:?}", s),
            MV8Value::Object(o) => write!(f, "{:?}", o),
        }
    }
}

/// Trait for types convertible to `Value`.
trait ToValue {
    /// Performs the conversion.
    fn to_value(self, mv8: &MiniV8) -> Result<MV8Value>;
}

/// Trait for types convertible from `Value`.
trait FromValue: Sized {
    /// Performs the conversion.
    fn from_value(value: MV8Value, mv8: &MiniV8) -> Result<Self>;
}

/// A collection of multiple JavaScript values used for interacting with function arguments.
#[derive(Clone)]
struct Values(Vec<MV8Value>);

impl Values {
    fn from_vec(vec: Vec<MV8Value>) -> Values {
        Values(vec)
    }

    fn into_vec(self) -> Vec<MV8Value> {
        self.0
    }
}

impl FromIterator<MV8Value> for Values {
    fn from_iter<I: IntoIterator<Item = MV8Value>>(iter: I) -> Self {
        Values::from_vec(Vec::from_iter(iter))
    }
}

/// Trait for types convertible to any number of JavaScript values.
///
/// This is a generalization of `ToValue`, allowing any number of resulting JavaScript values
/// instead of just one. Any type that implements `ToValue` will automatically implement this trait.
trait ToValues {
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

#[derive(Clone)]
struct MV8String {
    mv8: MiniV8,
    handle: v8::Global<v8::String>,
}

impl MV8String {
    /// Returns a Rust string converted from the V8 string.
    fn to_rust_string(&self) -> String {
        self.mv8
            .scope(|scope| v8::Local::new(scope, self.handle.clone()).to_rust_string_lossy(scope))
    }
}

impl fmt::Debug for MV8String {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.to_rust_string())
    }
}

impl ToValue for MV8Value {
    fn to_value(self, _mv8: &MiniV8) -> Result<MV8Value> {
        Ok(self)
    }
}

impl FromValue for MV8Value {
    fn from_value(value: MV8Value, _mv8: &MiniV8) -> Result<Self> {
        Ok(value)
    }
}

impl FromValue for String {
    fn from_value(value: MV8Value, mv8: &MiniV8) -> Result<Self> {
        Ok(value.coerce_string(mv8)?.to_rust_string())
    }
}

impl ToValues for Values {
    fn to_values(self, _mv8: &MiniV8) -> Result<Values> {
        Ok(self)
    }
}

#[derive(Clone)]
struct Object {
    mv8: MiniV8,
    handle: v8::Global<v8::Object>,
}

impl Object {
    /// Get an object property value using the given key. Returns `Value::Undefined` if no property
    /// with the key exists.
    ///
    /// Returns an error if `ToValue::to_value` fails for the key or if the key value could not be
    /// cast to a property key string.
    fn get<V: FromValue>(&self, key: MV8String) -> Result<V> {
        self.mv8.try_catch(|scope| {
            let object = v8::Local::new(scope, self.handle.clone());
            let key = MV8Value::String(key).to_v8_value(scope);
            let result = object.get(scope, key);
            V::from_value(
                MV8Value::from_v8_value(&self.mv8, scope, result.unwrap()),
                &self.mv8,
            )
        })
    }

    /// Sets an object property using the given key and value.
    ///
    /// Returns an error if `ToValue::to_value` fails for either the key or the value or if the key
    /// value could not be cast to a property key string.
    fn set<V: ToValue>(&self, key: String, value: V) -> Result<()> {
        let key = {
            let mv8 = &self.mv8;
            Ok(MV8Value::String(mv8.create_string(&key)))
        }?;
        let value = value.to_value(&self.mv8)?;
        self.mv8.try_catch(|scope| {
            let object = v8::Local::new(scope, self.handle.clone());
            let key = key.to_v8_value(scope);
            let value = value.to_v8_value(scope);
            object.set(scope, key, value);
            Ok(())
        })
    }
}

impl fmt::Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let keys = match self.mv8.try_catch(|scope| -> Result<Vec<MV8String>> {
            let object = v8::Local::new(scope, self.handle.clone());
            let keys = object.get_own_property_names(scope, Default::default());
            let keys = keys.unwrap();
            let len = keys.length();
            let keys: Result<Vec<MV8String>> = (0..len)
                .map(|index| -> Result<MV8String> {
                    let key = keys.get_index(scope, index).unwrap();
                    MV8Value::from_v8_value(&self.mv8, scope, key).coerce_string(&self.mv8)
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
            match self.get::<MV8Value>(k) {
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
