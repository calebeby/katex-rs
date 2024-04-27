//! JS Engine implemented by [v8](https://crates.io/crates/v8).

use crate::js_engine::{JsEngine, JsValue};
use crate::Result;
use core::fmt;
use mini_v8::{FromValue, ToValue};

/// v8 Engine.
pub struct Engine(mini_v8::MiniV8);

mod mini_v8;

impl JsEngine for Engine {
    type JsValue<'a> = Value<'a>;

    fn new() -> Result<Self> {
        Ok(Self(mini_v8::MiniV8::new()))
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
        let args: mini_v8::Values = args.map(|v| v.value).collect();
        let result = self.0.call_global_function(func_name.to_owned(), args)?;
        Ok(Value {
            value: result,
            engine: &self.0,
        })
    }

    fn create_bool_value(&self, input: bool) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: input.to_value(&self.0)?,
            engine: &self.0,
        })
    }

    fn create_int_value(&self, input: i32) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: input.to_value(&self.0)?,
            engine: &self.0,
        })
    }

    fn create_float_value(&self, input: f64) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: input.to_value(&self.0)?,
            engine: &self.0,
        })
    }

    fn create_string_value(&self, input: String) -> Result<Self::JsValue<'_>> {
        Ok(Value {
            value: input.to_value(&self.0)?,
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
            value: mini_v8::Value::Object(obj),
            engine: &self.0,
        })
    }
}

/// v8 Value.
pub struct Value<'a> {
    value: mini_v8::Value,
    engine: &'a mini_v8::MiniV8,
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
