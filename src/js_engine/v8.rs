//! JS Engine implemented by [v8](https://crates.io/crates/v8).

use crate::js_engine::{JsEngine, JsValue};
use crate::Result;

use crate::Error;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Once;

/// v8 Engine.
pub struct Engine(Rc<RefCell<MiniV8>>);

impl JsEngine for Engine {
    type JsValue<'a> = Value;

    fn new() -> Result<Self> {
        Ok(Self(Rc::new(RefCell::new(MiniV8::new()))))
    }

    fn eval<'a>(&'a self, code: &str) -> Result<Self::JsValue<'a>> {
        let result = self.0.borrow_mut().eval(code)?;
        Ok(Value {
            value: result,
            engine: Rc::clone(&self.0),
        })
    }

    fn call_function<'a>(
        &'a self,
        func_name: &str,
        args: impl Iterator<Item = Self::JsValue<'a>>,
    ) -> Result<Self::JsValue<'a>> {
        let args = args.map(|v| v.value).collect();
        let result = self
            .0
            .borrow_mut()
            .call_global_function(func_name.to_owned(), args)?;
        Ok(Value {
            value: result,
            engine: Rc::clone(&self.0),
        })
    }

    fn create_bool_value(&self, input: bool) -> Result<Self::JsValue<'_>> {
        let engine: &mut MiniV8 = &mut self.0.borrow_mut();
        let scope = &mut engine.scope();
        let local = v8::Local::from(v8::Boolean::new(scope, input));
        Ok(Value {
            value: v8::Global::new(scope, local),
            engine: Rc::clone(&self.0),
        })
    }

    fn create_int_value(&self, input: i32) -> Result<Self::JsValue<'_>> {
        let engine: &mut MiniV8 = &mut self.0.borrow_mut();
        let scope = &mut engine.scope();
        let local = v8::Local::from(v8::Integer::new(scope, input));
        Ok(Value {
            value: v8::Global::new(scope, local),
            engine: Rc::clone(&self.0),
        })
    }

    fn create_float_value(&self, input: f64) -> Result<Self::JsValue<'_>> {
        let engine: &mut MiniV8 = &mut self.0.borrow_mut();
        let scope = &mut engine.scope();
        let local = v8::Local::from(v8::Number::new(scope, input));
        Ok(Value {
            value: v8::Global::new(scope, local),
            engine: Rc::clone(&self.0),
        })
    }

    fn create_string_value(&self, input: String) -> Result<Self::JsValue<'_>> {
        let engine: &mut MiniV8 = &mut self.0.borrow_mut();
        let scope = &mut engine.scope();
        let local = v8::Local::from(v8::String::new(scope, &input).unwrap());
        Ok(Value {
            value: v8::Global::new(scope, local),
            engine: Rc::clone(&self.0),
        })
    }

    fn create_object_value<'a>(
        &'a self,
        input: impl Iterator<Item = (String, Self::JsValue<'a>)>,
    ) -> Result<Self::JsValue<'a>> {
        let input = input.collect::<Vec<_>>();
        let engine: &mut MiniV8 = &mut self.0.borrow_mut();
        let scope = &mut engine.scope();
        let object = v8::Object::new(scope);
        for (k, v) in input {
            let key = v8::String::new(scope, &k).unwrap();
            let value = v8::Local::new(scope, v.value);
            object.set(scope, key.into(), value);
        }
        let obj_handle = v8::Global::new(scope, v8::Local::from(object));

        Ok(Value {
            value: obj_handle,
            engine: Rc::clone(&self.0),
        })
    }
}

pub struct Value {
    value: v8::Global<v8::Value>,
    engine: Rc<RefCell<MiniV8>>,
}

impl JsValue<'_> for Value {
    fn into_string(self) -> Result<String> {
        self.engine.borrow_mut().try_catch(|scope| {
            let maybe = v8::Local::new(scope, self.value).to_string(scope).unwrap();
            Ok(maybe.to_rust_string_lossy(scope))
        })
    }
}

struct MiniV8 {
    isolate: v8::OwnedIsolate,
}

impl MiniV8 {
    fn new() -> MiniV8 {
        initialize_v8();
        let mut isolate = v8::Isolate::new(Default::default());
        {
            let scope = &mut v8::HandleScope::new(&mut isolate);
            let context = v8::Context::new(scope);
            let scope = &mut v8::ContextScope::new(scope, context);
            let global_context = v8::Global::new(scope, context);
            scope.set_slot(Global {
                context: global_context,
            });
        }
        MiniV8 { isolate }
    }

    fn call_global_function(
        &mut self,
        func_name: String,
        args: Vec<v8::Global<v8::Value>>,
    ) -> Result<v8::Global<v8::Value>> {
        self.try_catch(|scope| {
            let global = {
                let global = scope.get_current_context().global(scope);
                v8::Global::new(scope, global)
            };
            let object = v8::Local::new(scope, global);
            let key = v8::String::new(scope, &func_name).unwrap();
            let result = object.get(scope, key.into()).unwrap();
            let function = v8::Local::<v8::Function>::try_from(result).unwrap();
            let this = v8::undefined(scope).into();
            let args: Vec<_> = args
                .into_iter()
                .map(|arg| v8::Local::new(scope, arg))
                .collect();
            let result = function.call(scope, this, &args).ok_or(Error::JsExecError(
                "Function call did not return a result".to_string(),
            ))?;
            Ok(v8::Global::new(scope, result))
        })
    }

    fn eval(&mut self, script: &str) -> Result<v8::Global<v8::Value>> {
        self.try_catch(|scope| {
            let source = v8::String::new(scope, script).unwrap();
            let script = v8::Script::compile(scope, source, None);
            let result = script.unwrap().run(scope).unwrap();
            Ok(v8::Global::new(scope, result))
        })
    }

    fn scope(&mut self) -> v8::HandleScope {
        let context = self.isolate.get_slot::<Global>().unwrap().context.clone();
        v8::HandleScope::with_context(&mut self.isolate, context)
    }

    fn try_catch<F, T>(&mut self, func: F) -> Result<T>
    where
        F: FnOnce(&mut v8::TryCatch<v8::HandleScope>) -> Result<T>,
    {
        let scope = &mut self.scope();
        let mut try_catch = v8::TryCatch::new(scope);
        let result = func(&mut try_catch);
        match try_catch.exception() {
            Some(val) => Err(Error::JsExecError(val.to_rust_string_lossy(&mut try_catch))),
            None => Ok(result?),
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
