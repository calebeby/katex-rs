//! JS Engine implemented by [v8](https://crates.io/crates/v8).

use crate::js_engine::{JsEngine, JsValue};
use crate::Result;

use crate::Error;
use std::cell::RefCell;
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
        let args: Vec<MV8Value> = args.map(|v| v.value).collect();
        let result = self.0.call_global_function(func_name.to_owned(), args)?;
        Ok(Value {
            value: result,
            engine: &self.0,
        })
    }

    fn create_bool_value(&self, input: bool) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: MV8Value::Boolean(input),
            engine: &self.0,
        })
    }

    fn create_int_value(&self, input: i32) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: MV8Value::Number(input as f64),
            engine: &self.0,
        })
    }

    fn create_float_value(&self, input: f64) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: MV8Value::Number(input),
            engine: &self.0,
        })
    }

    fn create_string_value(&self, input: String) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: MV8Value::String(self.0.scope(|scope| {
                let string = v8::String::new(scope, &input).unwrap();
                v8::Global::new(scope, string)
            })),
            engine: &self.0,
        })
    }

    fn create_object_value<'a>(
        &'a self,
        input: impl Iterator<Item = (String, Self::JsValue<'a>)>,
    ) -> Result<Self::JsValue<'a>> {
        let obj_handle = self.0.scope(|scope| {
            let local = v8::Object::new(scope);
            v8::Global::new(scope, local)
        });
        for (k, v) in input {
            self.0.try_catch(|scope| {
                let key = v8::String::new(scope, &k).unwrap();
                let object = v8::Local::new(scope, obj_handle.clone());
                let value = v.value.to_v8_value(scope);
                object.set(scope, key.into(), value);
                Ok(())
            })?;
        }
        Ok(Value {
            value: MV8Value::Object(obj_handle),
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
        self.engine.try_catch(|scope| {
            let maybe = self.value.to_v8_value(scope).to_string(scope).unwrap();
            Ok(maybe.to_rust_string_lossy(scope))
        })
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

    fn call_global_function(&self, func_name: String, args: Vec<MV8Value>) -> Result<MV8Value> {
        let global = self.scope(|scope| {
            let global = scope.get_current_context().global(scope);
            v8::Global::new(scope, global)
        });
        self.try_catch(|scope| {
            let object = v8::Local::new(scope, global);
            let key = v8::String::new(scope, &func_name).unwrap();
            let result: v8::Local<'_, v8::Value> = object.get(scope, key.into()).unwrap();
            let function: v8::Local<'_, v8::Function> = result.try_into().unwrap();
            let this = MV8Value::Undefined;
            let this = this.to_v8_value(scope);
            let args_v8: Vec<v8::Local<'_, v8::Value>> =
                args.into_iter().map(|v| v.to_v8_value(scope)).collect();
            let result = function
                .call(scope, this, &args_v8)
                .ok_or(Error::JsExecError(
                    "Function call did not return a result".to_string(),
                ))?;
            Ok(MV8Value::from_v8_value(scope, result))
        })
    }

    /// Executes a JavaScript script and returns its result.
    fn eval(&self, script: &str) -> Result<MV8Value> {
        self.try_catch(|scope| {
            let source = v8::String::new(scope, script).unwrap();
            let script = v8::Script::compile(scope, source, None);
            let result = script.unwrap().run(scope);
            Ok(MV8Value::from_v8_value(scope, result.unwrap()))
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
    String(v8::Global<v8::String>),
    /// Reference to a JavaScript object.
    Object(v8::Global<v8::Object>),
}

impl MV8Value {
    fn from_v8_value(scope: &mut v8::HandleScope, value: v8::Local<v8::Value>) -> MV8Value {
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
            MV8Value::String(handle)
        } else if value.is_object() {
            let value: v8::Local<v8::Object> = value.try_into().unwrap();
            let handle = v8::Global::new(scope, value);
            MV8Value::Object(handle)
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
            MV8Value::Object(v) => v8::Local::new(scope, v.clone()).into(),
            MV8Value::String(v) => v8::Local::new(scope, v.clone()).into(),
        }
    }
}
