use std::any::Any;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
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

    /// Inserts any sort of keyed value of type `T` into the `MiniV8`, typically for later retrieval
    /// from within Rust functions called from within JavaScript. If a value already exists with the
    /// key, it is returned.
    fn set_user_data<K, T>(&self, key: K, data: T) -> Option<Box<dyn Any>>
    where
        K: ToString,
        T: Any,
    {
        self.interface
            .use_slot(|m: &AnyMap| m.0.borrow_mut().insert(key.to_string(), Box::new(data)))
    }

    /// Calls a function with a user data value by its key, or `None` if no value exists with the
    /// key. If a value exists but it is not of the type `T`, `None` is returned. This is typically
    /// used by a Rust function called from within JavaScript.
    fn use_user_data<F, T: Any, U>(&self, key: &str, func: F) -> U
    where
        F: FnOnce(Option<&T>) -> U + 'static,
    {
        self.interface
            .use_slot(|m: &AnyMap| func(m.0.borrow().get(key).and_then(|d| d.downcast_ref::<T>())))
    }

    /// Removes and returns a user data value by its key. Returns `None` if no value exists with the
    /// key.
    fn remove_user_data(&self, key: &str) -> Option<Box<dyn Any>> {
        self.interface
            .use_slot(|m: &AnyMap| m.0.borrow_mut().remove(key))
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

    /// Creates and returns an `Object` managed by V8 filled with the keys and values from an
    /// iterator. Keys are coerced to object properties.
    ///
    /// This is a thin wrapper around `MiniV8::create_object` and `Object::set`. See `Object::set`
    /// for how this method might return an error.
    fn create_object_from<K, V, I>(&self, iter: I) -> Result<Object>
    where
        K: ToValue,
        V: ToValue,
        I: IntoIterator<Item = (K, V)>,
    {
        let object = self.create_object();
        for (k, v) in iter {
            object.set(k, v)?;
        }
        Ok(object)
    }

    /// Wraps a Rust function or closure, creating a callable JavaScript function handle to it.
    ///
    /// The function's return value is always a `Result`: If the function returns `Err`, the error
    /// is raised as a JavaScript exception, which can be caught within JavaScript or bubbled up
    /// back into Rust by not catching it. This allows using the `?` operator to propagate errors
    /// through intermediate JavaScript code.
    ///
    /// If the function returns `Ok`, the contained value will be converted to a JavaScript value.
    /// For details on Rust-to-JavaScript conversions, refer to the `ToValue` and `ToValues` traits.
    ///
    /// If the provided function panics, the executable will be aborted.
    fn create_function<F, R>(&self, func: F) -> Function
    where
        F: Fn(Invocation) -> Result<R> + 'static,
        R: ToValue,
    {
        let func = move |mv8: &MiniV8, this: Value, args: Values| {
            func(Invocation {
                mv8: mv8.clone(),
                this,
                args,
            })?
            .to_value(mv8)
        };

        self.scope(|scope| {
            let callback = Box::new(func);
            let callback_info = CallbackInfo {
                mv8: self.clone(),
                callback,
            };
            let ptr = Box::into_raw(Box::new(callback_info));
            let ext = v8::External::new(scope, ptr as _);

            let v8_func = |scope: &mut v8::HandleScope,
                           fca: v8::FunctionCallbackArguments,
                           mut rv: v8::ReturnValue| {
                let data = fca.data();
                let ext = v8::Local::<v8::External>::try_from(data).unwrap();
                let callback_info_ptr = ext.value() as *mut CallbackInfo;
                let callback_info = unsafe { &mut *callback_info_ptr };
                let CallbackInfo { mv8, callback } = callback_info;
                let ptr = scope as *mut v8::HandleScope;
                // We can erase the lifetime of the `v8::HandleScope` safely because it only lives
                // on the interface stack during the current block:
                let ptr: *mut v8::HandleScope<'static> = unsafe { std::mem::transmute(ptr) };
                mv8.interface.push(ptr);
                let this = Value::from_v8_value(mv8, scope, fca.this().into());
                let len = fca.length();
                let mut args = Vec::with_capacity(len as usize);
                for i in 0..len {
                    args.push(Value::from_v8_value(mv8, scope, fca.get(i)));
                }
                match callback(mv8, this, Values::from_vec(args)) {
                    Ok(v) => {
                        rv.set(v.to_v8_value(scope));
                    }
                    Err(e) => {
                        let exception = e.to_value(mv8).to_v8_value(scope);
                        scope.throw_exception(exception);
                    }
                };
                mv8.interface.pop();
            };

            let value = v8::Function::builder(v8_func)
                .data(ext.into())
                .build(scope)
                .unwrap();
            // TODO: `v8::Isolate::adjust_amount_of_external_allocated_memory` should be called
            // appropriately with the following external resource size calculation. This cannot be
            // done as of now, since `v8::Weak::with_guaranteed_finalizer` does not provide a
            // `v8::Isolate` to the finalizer callback, and so the downward adjustment cannot be
            // made.
            //
            // let func_size = mem::size_of_val(&func); let ext_size = func_size +
            // mem::size_of::<CallbackInfo>;
            let drop_ext = Box::new(move || drop(unsafe { Box::from_raw(ptr) }));
            add_finalizer(scope, value, drop_ext);
            Function {
                mv8: self.clone(),
                handle: v8::Global::new(scope, value),
            }
        })
    }

    /// Wraps a mutable Rust closure, creating a callable JavaScript function handle to it.
    ///
    /// This is a version of `create_function` that accepts a FnMut argument. Refer to
    /// `create_function` for more information about the implementation.
    fn create_function_mut<F, R>(&self, func: F) -> Function
    where
        F: FnMut(Invocation) -> Result<R> + 'static,
        R: ToValue,
    {
        let func = RefCell::new(func);
        self.create_function(move |invocation| {
            (*func
                .try_borrow_mut()
                .map_err(|_| Error::RecursiveMutCallback)?)(invocation)
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

    fn push(&self, handle_scope: *mut v8::HandleScope<'static>) {
        self.0
            .borrow_mut()
            .push(Rc::new(RefCell::new(InterfaceEntry::HandleScope(
                handle_scope,
            ))));
    }

    fn pop(&self) {
        self.0.borrow_mut().pop();
    }

    fn use_slot<F, T: 'static, U>(&self, func: F) -> U
    where
        F: FnOnce(&T) -> U,
    {
        self.top(|entry| func(entry.get_slot()))
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
    HandleScope(*mut v8::HandleScope<'static>),
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
            InterfaceEntry::HandleScope(ref ptr) => {
                let scope: &mut v8::HandleScope = unsafe { &mut **ptr };
                let scope = &mut v8::ContextScope::new(scope, scope.get_current_context());
                func(scope)
            }
        }
    }

    fn get_slot<T: 'static>(&self) -> &T {
        match self {
            InterfaceEntry::Isolate(isolate) => isolate.get_slot::<T>().unwrap(),
            InterfaceEntry::HandleScope(ref ptr) => {
                let scope: &mut v8::HandleScope = unsafe { &mut **ptr };
                scope.get_slot::<T>().unwrap()
            }
        }
    }

    fn isolate_handle(&self) -> v8::IsolateHandle {
        match self {
            InterfaceEntry::Isolate(isolate) => isolate.thread_safe_handle(),
            InterfaceEntry::HandleScope(ref ptr) => {
                let scope: &mut v8::HandleScope = unsafe { &mut **ptr };
                scope.thread_safe_handle()
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
    scope.set_slot(AnyMap(Rc::new(RefCell::new(BTreeMap::new()))));
}

fn create_string<'s>(scope: &mut v8::HandleScope<'s>, value: &str) -> v8::Local<'s, v8::String> {
    v8::String::new(scope, value).expect("string exceeds maximum length")
}

fn add_finalizer<T: 'static>(
    isolate: &mut v8::Isolate,
    handle: impl v8::Handle<Data = T>,
    finalizer: impl FnOnce() + 'static,
) {
    let rc = Rc::new(RefCell::new(None));
    let weak = v8::Weak::with_guaranteed_finalizer(
        isolate,
        handle,
        Box::new({
            let rc = rc.clone();
            move || {
                let weak = rc.replace(None).unwrap();
                finalizer();
                drop(weak);
            }
        }),
    );
    rc.replace(Some(weak));
}

type Callback = Box<dyn Fn(&MiniV8, Value, Values) -> Result<Value>>;

struct CallbackInfo {
    mv8: MiniV8,
    callback: Callback,
}

struct AnyMap(Rc<RefCell<BTreeMap<StdString, Box<dyn Any>>>>);

// A JavaScript script.
#[derive(Clone, Debug, Default)]
struct Script {
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
    /// Elapsed milliseconds since Unix epoch.
    Date(f64),
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
    /// Returns `true` if this is a `Value::Undefined`, `false` otherwise.
    fn is_undefined(&self) -> bool {
        if let Value::Undefined = *self {
            true
        } else {
            false
        }
    }

    /// Returns `true` if this is a `Value::Null`, `false` otherwise.
    fn is_null(&self) -> bool {
        if let Value::Null = *self {
            true
        } else {
            false
        }
    }

    /// Returns `true` if this is a `Value::Boolean`, `false` otherwise.
    fn is_boolean(&self) -> bool {
        if let Value::Boolean(_) = *self {
            true
        } else {
            false
        }
    }

    /// Returns `true` if this is a `Value::Number`, `false` otherwise.
    fn is_number(&self) -> bool {
        if let Value::Number(_) = *self {
            true
        } else {
            false
        }
    }

    /// Returns `true` if this is a `Value::Date`, `false` otherwise.
    fn is_date(&self) -> bool {
        if let Value::Date(_) = *self {
            true
        } else {
            false
        }
    }

    /// Returns `true` if this is a `Value::String`, `false` otherwise.
    fn is_string(&self) -> bool {
        if let Value::String(_) = *self {
            true
        } else {
            false
        }
    }

    /// Returns `true` if this is a `Value::Array`, `false` otherwise.
    fn is_array(&self) -> bool {
        if let Value::Array(_) = *self {
            true
        } else {
            false
        }
    }

    /// Returns `true` if this is a `Value::Function`, `false` otherwise.
    fn is_function(&self) -> bool {
        if let Value::Function(_) = *self {
            true
        } else {
            false
        }
    }

    /// Returns `true` if this is a `Value::Object`, `false` otherwise.
    fn is_object(&self) -> bool {
        if let Value::Object(_) = *self {
            true
        } else {
            false
        }
    }

    /// Returns `Some(())` if this is a `Value::Undefined`, `None` otherwise.
    fn as_undefined(&self) -> Option<()> {
        if let Value::Undefined = *self {
            Some(())
        } else {
            None
        }
    }

    /// Returns `Some(())` if this is a `Value::Null`, `None` otherwise.
    fn as_null(&self) -> Option<()> {
        if let Value::Undefined = *self {
            Some(())
        } else {
            None
        }
    }

    /// Returns `Some` if this is a `Value::Boolean`, `None` otherwise.
    fn as_boolean(&self) -> Option<bool> {
        if let Value::Boolean(value) = *self {
            Some(value)
        } else {
            None
        }
    }

    /// Returns `Some` if this is a `Value::Number`, `None` otherwise.
    fn as_number(&self) -> Option<f64> {
        if let Value::Number(value) = *self {
            Some(value)
        } else {
            None
        }
    }

    /// Returns `Some` if this is a `Value::Date`, `None` otherwise.
    fn as_date(&self) -> Option<f64> {
        if let Value::Date(value) = *self {
            Some(value)
        } else {
            None
        }
    }

    /// Returns `Some` if this is a `Value::String`, `None` otherwise.
    fn as_string(&self) -> Option<&String> {
        if let Value::String(ref value) = *self {
            Some(value)
        } else {
            None
        }
    }

    /// Returns `Some` if this is a `Value::Array`, `None` otherwise.
    fn as_array(&self) -> Option<&Array> {
        if let Value::Array(ref value) = *self {
            Some(value)
        } else {
            None
        }
    }

    /// Returns `Some` if this is a `Value::Function`, `None` otherwise.
    fn as_function(&self) -> Option<&Function> {
        if let Value::Function(ref value) = *self {
            Some(value)
        } else {
            None
        }
    }

    /// Returns `Some` if this is a `Value::Object`, `None` otherwise.
    fn as_object(&self) -> Option<&Object> {
        if let Value::Object(ref value) = *self {
            Some(value)
        } else {
            None
        }
    }

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

    /// Coerces a value to a number. Nearly all JavaScript values are coercible to numbers, but this
    /// may fail with a runtime error under extraordinary circumstances (e.g. if the ECMAScript
    /// `ToNumber` implementation throws an error).
    ///
    /// This will return `std::f64::NAN` if the value has no numerical equivalent.
    fn coerce_number(&self, mv8: &MiniV8) -> Result<f64> {
        match self {
            &Value::Number(n) => Ok(n),
            value => mv8.try_catch(|scope| {
                let maybe = value.to_v8_value(scope).to_number(scope);
                mv8.exception(scope).map(|_| maybe.unwrap().value())
            }),
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
            Value::Date(_) => "date",
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
        } else if value.is_date() {
            let value: v8::Local<v8::Date> = value.try_into().unwrap();
            Value::Date(value.value_of())
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
            Value::Date(v) => v8::Date::new(scope, *v).unwrap().into(),
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
            Value::Date(d) => write!(f, "date:{}", d),
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

    fn get(&self, index: usize) -> Value {
        self.0
            .get(index)
            .map(Clone::clone)
            .unwrap_or(Value::Undefined)
    }

    fn from<T: FromValue>(&self, mv8: &MiniV8, index: usize) -> Result<T> {
        T::from_value(
            self.0
                .get(index)
                .map(Clone::clone)
                .unwrap_or(Value::Undefined),
            mv8,
        )
    }

    fn into<T: FromValues>(self, mv8: &MiniV8) -> Result<T> {
        T::from_values(self, mv8)
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn iter(&self) -> impl Iterator<Item = &'_ Value> {
        self.0.iter()
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

/// Wraps a variable number of `T`s.
///
/// Can be used to work with variadic functions more easily. Using this type as the last argument of
/// a Rust callback will accept any number of arguments from JavaScript and convert them to the type
/// `T` using [`FromValue`]. `Variadic<T>` can also be returned from a callback, returning a
/// variable number of values to JavaScript.
#[derive(Clone)]
struct Variadic<T>(Vec<T>);

impl<T> Variadic<T> {
    /// Creates an empty `Variadic` wrapper containing no values.
    fn new() -> Variadic<T> {
        Variadic(Vec::new())
    }

    fn from_vec(vec: Vec<T>) -> Variadic<T> {
        Variadic(vec)
    }

    fn into_vec(self) -> Vec<T> {
        self.0
    }
}

impl<T> FromIterator<T> for Variadic<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Variadic(Vec::from_iter(iter))
    }
}

impl<T> IntoIterator for Variadic<T> {
    type Item = T;
    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> Deref for Variadic<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Variadic<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// `std::result::Result` specialized for this crate's `Error` type.
type Result<T> = StdResult<T, Error>;

/// An error originating from `MiniV8` usage.
#[derive(Debug)]
pub(crate) enum Error {
    /// A Rust value could not be converted to a JavaScript value.
    ToJsConversionError {
        /// Name of the Rust type that could not be converted.
        from: &'static str,
        /// Name of the JavaScript type that could not be created.
        to: &'static str,
    },
    /// A JavaScript value could not be converted to the expected Rust type.
    FromJsConversionError {
        /// Name of the JavaScript type that could not be converted.
        from: &'static str,
        /// Name of the Rust type that could not be created.
        to: &'static str,
    },
    /// An evaluation timeout occurred.
    Timeout,
    /// A mutable callback has triggered JavaScript code that has called the same mutable callback
    /// again.
    ///
    /// This is an error because a mutable callback can only be borrowed mutably once.
    RecursiveMutCallback,
    /// An evaluation timeout was specified from within a Rust function embedded in V8.
    InvalidTimeout,
    /// A custom error that occurs during runtime.
    ///
    /// This can be used for returning user-defined errors from callbacks.
    ExternalError(Box<dyn StdError + 'static>),
    /// An exception that occurred within the JavaScript environment.
    Value(Value),
}

impl Error {
    /// Normalizes an error into a JavaScript value.
    pub(crate) fn to_value(self, mv8: &MiniV8) -> Value {
        match self {
            Error::Value(value) => value,
            Error::ToJsConversionError { .. } | Error::FromJsConversionError { .. } => {
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
            Error::ToJsConversionError { from, to } => {
                write!(fmt, "error converting {} to JavaScript {}", from, to)
            }
            Error::FromJsConversionError { from, to } => {
                write!(fmt, "error converting JavaScript {} to {}", from, to)
            }
            Error::Timeout => write!(fmt, "evaluation timed out"),
            Error::RecursiveMutCallback => write!(fmt, "mutable callback called recursively"),
            Error::InvalidTimeout => write!(fmt, "invalid request for evaluation timeout"),
            Error::ExternalError(ref err) => err.fmt(fmt),
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
    /// Consumes the function and downgrades it to a JavaScript object.
    fn into_object(self) -> Object {
        self.mv8.clone().scope(|scope| {
            let object: v8::Local<v8::Object> = v8::Local::new(scope, self.handle.clone()).into();
            Object {
                mv8: self.mv8,
                handle: v8::Global::new(scope, object),
            }
        })
    }

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

    /// Calls the function as a constructor function with the given arguments.
    fn call_new<A, R>(&self, args: A) -> Result<R>
    where
        A: ToValues,
        R: FromValue,
    {
        let args = args.to_values(&self.mv8)?;
        self.mv8
            .try_catch(|scope| {
                let function = v8::Local::new(scope, self.handle.clone());
                let args = args.into_vec();
                let args_v8: Vec<_> = args.into_iter().map(|v| v.to_v8_value(scope)).collect();
                let result = function.new_instance(scope, &args_v8);
                self.mv8.exception(scope)?;
                Ok(Value::from_v8_value(
                    &self.mv8,
                    scope,
                    result.unwrap().into(),
                ))
            })
            .and_then(|v| v.into(&self.mv8))
    }
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<function>")
    }
}

/// A bundle of information about an invocation of a function that has been embedded from Rust into
/// JavaScript.
struct Invocation {
    /// The `MiniV8` within which the function was called.
    mv8: MiniV8,
    /// The value of the function invocation's `this` binding.
    this: Value,
    /// The list of arguments with which the function was called.
    args: Values,
}

#[derive(Clone)]
pub(crate) struct String {
    mv8: MiniV8,
    handle: v8::Global<v8::String>,
}

impl String {
    /// Returns a Rust string converted from the V8 string.
    pub(crate) fn to_string(&self) -> StdString {
        self.mv8
            .scope(|scope| v8::Local::new(scope, self.handle.clone()).to_rust_string_lossy(scope))
    }
}

impl fmt::Debug for String {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.to_string())
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
        Ok(value.coerce_string(mv8)?.to_string())
    }
}

impl<'a> ToValue for &'a str {
    fn to_value(self, mv8: &MiniV8) -> Result<Value> {
        Ok(Value::String(mv8.create_string(self)))
    }
}

macro_rules! convert_number {
    ($prim_ty: ty) => {
        impl ToValue for $prim_ty {
            fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
                Ok(Value::Number(self as f64))
            }
        }

        impl FromValue for $prim_ty {
            fn from_value(value: Value, mv8: &MiniV8) -> Result<Self> {
                Ok(value.coerce_number(mv8)? as $prim_ty)
            }
        }
    };
}

convert_number!(i8);
convert_number!(u8);
convert_number!(i16);
convert_number!(u16);
convert_number!(i32);
convert_number!(u32);
convert_number!(i64);
convert_number!(u64);
convert_number!(isize);
convert_number!(usize);
convert_number!(f32);
convert_number!(f64);

impl ToValue for Duration {
    fn to_value(self, _mv8: &MiniV8) -> Result<Value> {
        Ok(Value::Date(
            (self.as_secs() as f64) + (self.as_nanos() as f64) / 1_000_000_000.0,
        ))
    }
}

impl FromValue for Duration {
    fn from_value(value: Value, _mv8: &MiniV8) -> Result<Duration> {
        match value {
            Value::Date(timestamp) => {
                let secs = timestamp / 1000.0;
                let nanos = ((secs - secs.floor()) * 1_000_000.0).round() as u32;
                Ok(Duration::new(secs as u64, nanos))
            }
            value => Err(Error::from_js_conversion(value.type_name(), "Duration")),
        }
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

macro_rules! impl_tuple {
    ($($name:ident),*) => (
        impl<$($name),*> ToValues for ($($name,)*)
        where
            $($name: ToValue,)*
        {
            #[allow(non_snake_case)]
            fn to_values(self, mv8: &MiniV8) -> Result<Values> {
                let ($($name,)*) = self;
                let reservation = $({ let _ = &$name; 1 } +)* 0;
                let mut results = Vec::with_capacity(reservation);
                $(results.push($name.to_value(mv8)?);)*
                Ok(Values::from_vec(results))
            }
        }

        impl<$($name),*> FromValues for ($($name,)*)
        where
            $($name: FromValue,)*
        {
            #[allow(non_snake_case, unused_mut, unused_variables)]
            fn from_values(values: Values, mv8: &MiniV8) -> Result<Self> {
                let mut iter = values.into_vec().into_iter();
                Ok(($({
                    let $name = ();
                    FromValue::from_value(iter.next().unwrap_or(Value::Undefined), mv8)?
                },)*))
            }
        }

        impl<$($name,)* VAR> ToValues for ($($name,)* Variadic<VAR>)
        where
            $($name: ToValue,)*
            VAR: ToValue,
        {
            #[allow(non_snake_case)]
            fn to_values(self, mv8: &MiniV8) -> Result<Values> {
                let ($($name,)* variadic) = self;
                let reservation = $({ let _ = &$name; 1 } +)* 1;
                let mut results = Vec::with_capacity(reservation);
                $(results.push($name.to_value(mv8)?);)*
                if results.is_empty() {
                    Ok(variadic.to_values(mv8)?)
                } else {
                    results.append(&mut variadic.to_values(mv8)?.into_vec());
                    Ok(Values::from_vec(results))
                }
            }
        }

        impl<$($name,)* VAR> FromValues for ($($name,)* Variadic<VAR>)
        where
            $($name: FromValue,)*
            VAR: FromValue,
        {
            #[allow(non_snake_case, unused_mut, unused_variables)]
            fn from_values(values: Values, mv8: &MiniV8) -> Result<Self> {
                let mut values = values.into_vec();
                let len = values.len();
                let split = $({ let $name = (); 1 } +)* 0;

                if len < split {
                    values.reserve(split - len);
                    for _ in len..split {
                        values.push(Value::Undefined);
                    }
                }

                let last_values = Values::from_vec(values.split_off(split));
                let variadic = FromValues::from_values(last_values, mv8)?;

                let mut iter = values.into_iter();
                let ($($name,)*) = ($({ let $name = (); iter.next().unwrap() },)*);

                Ok(($(FromValue::from_value($name, mv8)?,)* variadic))
            }
        }
    )
}

impl_tuple!(A);
impl_tuple!(A, B);
impl_tuple!(A, B, C);
impl_tuple!(A, B, C, D);
impl_tuple!(A, B, C, D, E);
impl_tuple!(A, B, C, D, E, F);
impl_tuple!(A, B, C, D, E, F, G);
impl_tuple!(A, B, C, D, E, F, G, H);
impl_tuple!(A, B, C, D, E, F, G, H, I);
impl_tuple!(A, B, C, D, E, F, G, H, I, J);
impl_tuple!(A, B, C, D, E, F, G, H, I, J, K);
impl_tuple!(A, B, C, D, E, F, G, H, I, J, K, L);
impl_tuple!(A, B, C, D, E, F, G, H, I, J, K, L, M);
impl_tuple!(A, B, C, D, E, F, G, H, I, J, K, L, M, N);
impl_tuple!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O);
impl_tuple!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P);

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

    /// Removes the property associated with the given key from the object. This function does
    /// nothing if the property does not exist.
    ///
    /// Returns an error if `ToValue::to_value` fails for the key or if the key value could not be
    /// cast to a property key string.
    fn remove<K: ToValue>(&self, key: K) -> Result<()> {
        let key = key.to_value(&self.mv8)?;
        self.mv8.try_catch(|scope| {
            let object = v8::Local::new(scope, self.handle.clone());
            let key = key.to_v8_value(scope);
            object.delete(scope, key);
            self.mv8.exception(scope)
        })
    }

    /// Returns `true` if the given key is a property of the object, `false` otherwise.
    ///
    /// Returns an error if `ToValue::to_value` fails for the key or if the key value could not be
    /// cast to a property key string.
    fn has<K: ToValue>(&self, key: K) -> Result<bool> {
        let key = key.to_value(&self.mv8)?;
        self.mv8.try_catch(|scope| {
            let object = v8::Local::new(scope, self.handle.clone());
            let key = key.to_v8_value(scope);
            let has = object.has(scope, key);
            self.mv8.exception(scope)?;
            Ok(has.unwrap())
        })
    }

    /// Calls the function at the key with the given arguments, with `this` set to the object.
    /// Returns an error if the value at the key is not a function.
    fn call_prop<K, A, R>(&self, key: K, args: A) -> Result<R>
    where
        K: ToValue,
        A: ToValues,
        R: FromValue,
    {
        let func: Function = self.get(key)?;
        func.call_method(self.clone(), args)
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
struct Array {
    mv8: MiniV8,
    handle: v8::Global<v8::Array>,
}

impl Array {
    /// Consumes the array and downgrades it to a JavaScript object.
    fn into_object(self) -> Object {
        self.mv8.clone().scope(|scope| {
            let object: v8::Local<v8::Object> = v8::Local::new(scope, self.handle.clone()).into();
            Object {
                mv8: self.mv8,
                handle: v8::Global::new(scope, object),
            }
        })
    }

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
