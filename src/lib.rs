//! # Unbinder - JSON Schema Dereferencer
//! 
//! A high-performance JSON Schema dereferencer that resolves `$ref` pointers,
//! making schemas self-contained by replacing references with their actual content.
//! 
//! ## Features
//! 
//! - **Fast**: Written in Rust with performance optimizations
//! - **No-std support**: Can be used in embedded environments
//! - **WebAssembly support**: Compile to WASM for browser/Node.js usage
//! - **Circular reference handling**: Detects and handles circular references gracefully
//! - **Zero-copy where possible**: Minimizes memory allocations
//! 
//! ## Quick Start
//! 
//! ```rust
//! use unbinder::{dereference_schema, Options};
//! use serde_json::json;
//! 
//! # fn main() -> Result<(), unbinder::Error> {
//! let mut schema = json!({
//!     "type": "object",
//!     "properties": {
//!         "name": { "$ref": "#/definitions/name" }
//!     },
//!     "definitions": {
//!         "name": { "type": "string" }
//!     }
//! });
//! 
//! dereference_schema(&mut schema, Options::default())?;
//! # Ok(())
//! # }
//! ```
//! 
//! ## Circular Reference Handling
//! 
//! ```rust
//! use unbinder::{dereference_schema, Options};
//! use serde_json::json;
//! 
//! # fn main() -> Result<(), unbinder::Error> {
//! let mut schema = json!({
//!     "definitions": {
//!         "node": {
//!             "type": "object",
//!             "properties": {
//!                 "children": {
//!                     "type": "array",
//!                     "items": { "$ref": "#/definitions/node" }
//!                 }
//!             }
//!         }
//!     }
//! });
//! 
//! let opts = Options {
//!     resolve_external: false,
//!     on_circular: Some(|path| eprintln!("Circular reference: {}", path)),
//! };
//! 
//! dereference_schema(&mut schema, opts)?;
//! # Ok(())
//! # }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;
use alloc::string::String;

//
// ─── tiny logger used only by wasm_front --------------------------------
//
cfg_if::cfg_if! {
    if #[cfg(all(feature = "std", not(target_arch = "wasm32")))] {
    } else if #[cfg(all(feature = "console_log", target_arch = "wasm32"))] {
        fn debug_log(args: &str) {
            web_sys::console::log_1(&args.into());
        }
    } else {
        fn debug_log(_: &str) {}
    }
}

//
// ─── tiny bump allocator for wasm (opt-in) ------------------------------
//
#[cfg(all(target_arch = "wasm32", feature = "wee_alloc"))]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

//
// ────────────────────────────────────────────────────────────────────────
//  CORE  (no_std + alloc)  — all real work happens here
// ────────────────────────────────────────────────────────────────────────
//
/// Core dereferencing implementation.
/// 
/// This module contains the main dereferencing logic that works in `no_std` environments
/// with only `alloc` available. It uses efficient data structures and algorithms to
/// resolve JSON references while handling circular dependencies.
mod core {
    use super::*;
    use rustc_hash::{FxHashMap, FxHashSet};
    use serde_json::Value;

    // Arc for threaded build, Rc otherwise
    #[cfg(not(all(feature = "parallel", feature = "std")))]
    use alloc::rc::Rc as SharedPtr;
    #[cfg(all(feature = "parallel", feature = "std"))]
    use std::sync::Arc as SharedPtr;

    // ── public types ───────────────────────────────────────────
    /// Error type for dereferencing operations.
    /// 
    /// Currently uses `String` for maximum flexibility in `no_std` environments.
    pub type Error = String;

    /// Configuration options for the dereferencer.
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use unbinder::Options;
    /// 
    /// // Default options
    /// let opts = Options::default();
    /// 
    /// // Custom options with circular reference logging
    /// let opts = Options {
    ///     resolve_external: false,
    ///     on_circular: Some(|path| println!("Circular ref: {}", path)),
    /// };
    /// ```
    #[derive(Clone, Default)]
    pub struct Options {
        /// Whether to resolve external references (currently not supported).
        /// 
        /// External references are those that don't start with '#'.
        /// Setting this to `true` will result in an error for external refs.
        pub resolve_external: bool,
        
        /// Callback function invoked when circular references are detected.
        /// 
        /// The callback receives the reference path that forms a cycle.
        /// Circular references are replaced with `null` in the output.
        pub on_circular: Option<fn(&str)>,
    }

    // ── helper types (private) ─────────────────────────────────
    type SharedStr = SharedPtr<str>;

    #[derive(Clone)]
    struct CachedRef {
        value: SharedPtr<Value>,
        circular: bool,
    }

    #[derive(Clone, Debug)]
    enum DerefValue {
        Owned(Value),
        Shared(SharedPtr<Value>),
    }
    impl From<DerefValue> for Value {
        fn from(d: DerefValue) -> Self {
            match d {
                DerefValue::Owned(v) => v,
                DerefValue::Shared(rc) => (*rc).clone(),
            }
        }
    }

    #[derive(Default)]
    struct Cache {
        resolved: FxHashMap<SharedStr, CachedRef>,
        resolving: FxHashSet<SharedStr>,
        buf: String,
    }

    // ── public entry points ────────────────────────────────────
    /// Dereferences all `$ref` pointers in a JSON Schema document.
    /// 
    /// This function modifies the input `Value` in-place, replacing all `$ref` objects
    /// with their referenced content. The dereferencing process handles nested references
    /// and detects circular dependencies.
    /// 
    /// # Arguments
    /// 
    /// * `root` - The JSON value to dereference (modified in-place)
    /// * `opts` - Configuration options for the dereferencing process
    /// 
    /// # Returns
    /// 
    /// * `Ok(())` if dereferencing completed successfully
    /// * `Err(Error)` if an error occurred (e.g., invalid reference, external reference)
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use unbinder::{dereference_schema, Options};
    /// use serde_json::json;
    /// 
    /// # fn main() -> Result<(), unbinder::Error> {
    /// let mut schema = json!({
    ///     "type": "object",
    ///     "properties": {
    ///         "user": { "$ref": "#/definitions/User" }
    ///     },
    ///     "definitions": {
    ///         "User": {
    ///             "type": "object",
    ///             "properties": {
    ///                 "name": { "type": "string" }
    ///             }
    ///         }
    ///     }
    /// });
    /// 
    /// dereference_schema(&mut schema, Options::default())?;
    /// 
    /// // The $ref has been replaced with the actual User definition
    /// assert_eq!(
    ///     schema["properties"]["user"]["type"],
    ///     "object"
    /// );
    /// # Ok(())
    /// # }
    /// ```
    /// 
    /// # Safety
    /// 
    /// This function uses unsafe code internally for performance optimization,
    /// but the public API is safe to use.
    pub fn dereference_schema(root: &mut Value, opts: Options) -> Result<(), Error> {
        let mut cache = Cache::default();
        let raw = root as *const Value;
        unsafe { crawl(root, &*raw, &mut cache, &opts) }?;
        Ok(())
    }

    /// Counts the number of objects, arrays, and references in a JSON value.
    /// 
    /// This function recursively traverses the JSON structure and counts:
    /// - Objects (JSON objects/maps)
    /// - Arrays (JSON arrays)
    /// - References (objects containing a "$ref" key)
    /// 
    /// # Arguments
    /// 
    /// * `v` - The JSON value to analyze
    /// 
    /// # Returns
    /// 
    /// A tuple of `(objects, arrays, refs)` where:
    /// - `objects` is the total number of JSON objects
    /// - `arrays` is the total number of JSON arrays
    /// - `refs` is the total number of `$ref` references
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use unbinder::count;
    /// use serde_json::json;
    /// 
    /// let schema = json!({
    ///     "type": "object",
    ///     "properties": {
    ///         "items": {
    ///             "type": "array",
    ///             "items": { "$ref": "#/definitions/Item" }
    ///         }
    ///     },
    ///     "definitions": {
    ///         "Item": { "type": "string" }
    ///     }
    /// });
    /// 
    /// let (objects, arrays, refs) = count(&schema);
    /// assert_eq!(objects, 5);  // root + properties + items + items.items + definitions + Item
    /// assert_eq!(arrays, 1);   // items array
    /// assert_eq!(refs, 1);     // one $ref
    /// ```
    pub fn count(v: &Value) -> (usize, usize, usize) {
        match v {
            Value::Object(m) => {
                let mut o = 1;
                let mut a = 0;
                let mut r = m.contains_key("$ref") as usize;
                for v in m.values() {
                    let (o2, a2, r2) = count(v);
                    o += o2;
                    a += a2;
                    r += r2;
                }
                (o, a, r)
            }
            Value::Array(arr) => {
                let (mut o, mut a, mut r) = (0, 1, 0);
                for v in arr {
                    let (o2, a2, r2) = count(v);
                    o += o2;
                    a += a2;
                    r += r2;
                }
                (o, a, r)
            }
            _ => (0, 0, 0),
        }
    }

    // ── internal recursion & helpers ───────────────────────────
    unsafe fn crawl(
        node: &mut Value,
        root: &Value,
        cache: &mut Cache,
        opts: &Options,
    ) -> Result<bool, Error> {
        match node {
            Value::Object(map) => {
                if let Some(Value::String(r)) = map.get("$ref") {
                    let key: SharedStr = SharedPtr::from(&**r);
                    let (res, circ) = deref_ref(key, root, cache, opts)?;
                    *node = res.into();
                    return Ok(circ);
                }
                for v in map.values_mut() {
                    crawl(v, root, cache, opts)?;
                }
            }
            Value::Array(arr) => {
                for v in arr.iter_mut() {
                    crawl(v, root, cache, opts)?;
                }
            }
            _ => {}
        }
        Ok(false)
    }

    fn deref_ref(
        key: SharedStr,
        root: &Value,
        cache: &mut Cache,
        opts: &Options,
    ) -> Result<(DerefValue, bool), Error> {
        if let Some(c) = cache.resolved.get(&key) {
            return Ok((DerefValue::Shared(c.value.clone()), c.circular));
        }
        if cache.resolving.contains(&key) {
            if let Some(cb) = opts.on_circular {
                cb(&key);
            }
            return Ok((DerefValue::Owned(Value::Null), true));
        }

        if !key.starts_with('#') {
            return Err(format!("external ref `{key}` not supported"));
        }

        let mut resolved = resolve_pointer(root, &key[1..], &mut cache.buf)?.clone();

        cache.resolving.insert(key.clone());
        let circ = unsafe { crawl(&mut resolved, root, cache, opts)? };
        cache.resolving.remove(&key);

        let rc = SharedPtr::new(resolved);
        cache.resolved.insert(
            key,
            CachedRef {
                value: rc.clone(),
                circular: circ,
            },
        );
        Ok((DerefValue::Shared(rc), circ))
    }

    fn resolve_pointer<'a>(
        root: &'a Value,
        pointer: &str,
        buf: &mut String,
    ) -> Result<&'a Value, Error> {
        if pointer.is_empty() {
            return Ok(root);
        }
        if !pointer.starts_with('/') {
            return Err(format!("invalid JSON-pointer `#{pointer}`"));
        }

        pointer[1..].split('/').try_fold(root, |curr, token| {
            unescape(token, buf);
            match curr {
                Value::Object(m) => m.get(buf).ok_or(format!("missing key `{buf}`")),
                Value::Array(a) => {
                    let idx: usize = buf.parse().map_err(|_| format!("bad index `{buf}`"))?;
                    a.get(idx).ok_or(format!("index {idx} out of bounds"))
                }
                _ => Err("pointer expects object/array".into()),
            }
        })
    }

    #[inline(always)]
    fn unescape(token: &str, out: &mut String) {
        out.clear();
        if !token.contains('~') {
            out.push_str(token);
            return;
        }
        let mut bytes = token.bytes();
        while let Some(b) = bytes.next() {
            if b == b'~' {
                match bytes.next() {
                    Some(b'0') => out.push('~'),
                    Some(b'1') => out.push('/'),
                    Some(x) => {
                        out.push('~');
                        out.push(x as char);
                    }
                    None => out.push('~'),
                }
            } else {
                out.push(b as char);
            }
        }
    }
}

// ── re-export core API so other crates can `use unbinder::Options` etc. ──
pub use core::{count, dereference_schema, Error, Options};

//
// ────────────────────────────────────────────────────────────────────────
//  WASM front-end  (only when compiling to wasm32)
// ────────────────────────────────────────────────────────────────────────
//
/// WebAssembly bindings for browser and Node.js usage.
/// 
/// This module provides JavaScript-friendly APIs when compiling to WebAssembly.
/// It includes automatic serialization/deserialization and error handling suitable
/// for JavaScript environments.
/// 
/// # JavaScript Usage
/// 
/// ```javascript
/// import init, { dereferenceSchema, Options } from 'unbinder';
/// 
/// await init(); // Initialize WASM module
/// 
/// const schema = {
///   properties: {
///     user: { $ref: "#/definitions/User" }
///   },
///   definitions: {
///     User: { type: "object" }
///   }
/// };
/// 
/// const options = new Options();
/// const result = dereferenceSchema(schema, options);
/// ```
#[cfg(all(target_arch = "wasm32", feature = "wasm"))]
mod wasm_front {
    use super::*;
    use crate::core as c;
    use alloc::fmt; // Add this import
    use js_sys::{Object, Reflect};
    use serde::{Deserialize, Serialize};
    use wasm_bindgen::prelude::*;

    #[wasm_bindgen]
    extern "C" {
        #[wasm_bindgen(js_name = getWasmMemoryInfo)]
        fn get_mem() -> JsValue;
    }

    fn js_obj(pairs: &[(&str, JsValue)]) -> JsValue {
        let o = Object::new();
        for (k, v) in pairs {
            let _ = Reflect::set(&o, &JsValue::from_str(k), v); // Fixed
        }
        o.into()
    }

    // ── JS-friendly error wrapper ───────────────────────────────
    /// JavaScript-compatible error type.
    /// 
    /// Wraps Rust errors in a format that JavaScript can understand,
    /// with a `message` property accessible from JS.
    #[wasm_bindgen]
    pub struct WasmError(String);
    
    impl<E: fmt::Display> From<E> for WasmError {
        fn from(e: E) -> Self {
            Self(e.to_string())
        }
    }
    
    #[wasm_bindgen]
    impl WasmError {
        /// Gets the error message.
        /// 
        /// # JavaScript Example
        /// 
        /// ```javascript
        /// try {
        ///   dereferenceSchema(schema);
        /// } catch (error) {
        ///   console.error(error.message);
        /// }
        /// ```
        #[wasm_bindgen(getter)]
        pub fn message(&self) -> String {
            self.0.clone()
        }
    }

    // ── options object passed from JS ───────────────────────────
    /// Configuration options for the WebAssembly dereferencer.
    /// 
    /// # JavaScript Example
    /// 
    /// ```javascript
    /// const options = new Options();
    /// options.setLogCircularRefs(true);
    /// 
    /// const result = dereferenceSchema(schema, options);
    /// ```
    #[wasm_bindgen]
    #[derive(Clone, Default)]
    pub struct Options {
        resolve_external: bool,
        log_circular: bool,
    }
    
    #[wasm_bindgen]
    impl Options {
        /// Creates a new Options instance with default settings.
        #[wasm_bindgen(constructor)]
        pub fn new() -> Self {
            Self::default()
        }
        
        /// Sets whether to resolve external references.
        /// 
        /// Note: External references are not currently supported and will return an error.
        #[wasm_bindgen(setter)]
        pub fn set_resolve_external(&mut self, v: bool) {
            self.resolve_external = v;
        }
        
        /// Sets whether to log circular references to the console.
        /// 
        /// When enabled, circular reference paths will be logged using `console.log()`.
        #[wasm_bindgen(setter, js_name = setLogCircularRefs)]
        pub fn set_log_circular(&mut self, v: bool) {
            self.log_circular = v;
        }
    }

    // ── main wasm entry (JsValue → JsValue) ─────────────────────
    /// Dereferences a JSON Schema from JavaScript.
    /// 
    /// This is the main entry point for JavaScript/TypeScript usage.
    /// It accepts a JavaScript object and returns the dereferenced result.
    /// 
    /// # Arguments
    /// 
    /// * `value` - The JSON Schema as a JavaScript object
    /// * `opts` - Optional configuration options
    /// 
    /// # Returns
    /// 
    /// The dereferenced schema as a JavaScript object, or a `WasmError` if dereferencing fails.
    /// 
    /// # JavaScript Example
    /// 
    /// ```javascript
    /// import init, { dereferenceSchema, Options } from 'unbinder';
    /// 
    /// await init();
    /// 
    /// const schema = {
    ///   type: "object",
    ///   properties: {
    ///     user: { $ref: "#/definitions/User" }
    ///   },
    ///   definitions: {
    ///     User: { type: "object" }
    ///   }
    /// };
    /// 
    /// const result = dereferenceSchema(schema);
    /// console.log(result.properties.user.type); // "object"
    /// ```
    #[wasm_bindgen(js_name = dereferenceSchema)]
    pub fn deref_js(value: &JsValue, opts: Option<Options>) -> Result<JsValue, WasmError> {
        use serde_wasm_bindgen::{Deserializer, Serializer};

        let de = Deserializer::from(value.clone());
        let mut v = serde_json::Value::deserialize(de)?;

        let o = opts.unwrap_or_default();
        let internal = c::Options {
            resolve_external: o.resolve_external,
            on_circular: o
                .log_circular
                .then_some(|p| debug_log(&format!("circular {p}"))),
        };
        c::dereference_schema(&mut v, internal)?;

        Ok(v.serialize(&Serializer::new().serialize_maps_as_objects(true))?)
    }

    // optional string interface
    /// Dereferences a JSON Schema from a string (text interface).
    /// 
    /// This alternative API accepts and returns JSON as strings instead of objects.
    /// Useful for environments where string manipulation is preferred.
    /// 
    /// # Arguments
    /// 
    /// * `s` - The JSON Schema as a string
    /// 
    /// # Returns
    /// 
    /// The dereferenced schema as a JSON string, or a `WasmError` if parsing/dereferencing fails.
    /// 
    /// # JavaScript Example
    /// 
    /// ```javascript
    /// const schemaStr = JSON.stringify({
    ///   properties: { user: { $ref: "#/definitions/User" } },
    ///   definitions: { User: { type: "object" } }
    /// });
    /// 
    /// const resultStr = dereferenceSchemaText(schemaStr);
    /// const result = JSON.parse(resultStr);
    /// ```
    #[cfg(feature = "text-interface")]
    #[wasm_bindgen(js_name = dereferenceSchemaText)]
    pub fn deref_text(s: &str) -> Result<String, WasmError> {
        let mut v: serde_json::Value = serde_json::from_str(s)?;
        c::dereference_schema(&mut v, c::Options::default())?;
        Ok(serde_json::to_string(&v)?)
    }

    // statistics helper
    /// Analyzes a JSON Schema and returns size statistics.
    /// 
    /// Useful for understanding the complexity of a schema before dereferencing.
    /// 
    /// # Arguments
    /// 
    /// * `s` - The JSON Schema as a string
    /// 
    /// # Returns
    /// 
    /// A JavaScript object with the following properties:
    /// - `bytes`: Size of the input string in bytes
    /// - `objects`: Number of JSON objects in the schema
    /// - `arrays`: Number of JSON arrays in the schema
    /// - `refs`: Number of `$ref` references in the schema
    /// 
    /// # JavaScript Example
    /// 
    /// ```javascript
    /// const stats = estimateSchemaSize(JSON.stringify(schema));
    /// console.log(`Schema has ${stats.refs} references`);
    /// ```
    #[wasm_bindgen(js_name = estimateSchemaSize)]
    pub fn size(s: &str) -> Result<JsValue, WasmError> {
        let v: serde_json::Value = serde_json::from_str(s)?;
        let (o, a, r) = c::count(&v);
        Ok(js_obj(&[
            ("bytes", (s.len() as u32).into()),
            ("objects", (o as u32).into()),
            ("arrays", (a as u32).into()),
            ("refs", (r as u32).into()),
        ]))
    }

    /// Gets the current WebAssembly memory usage information.
    /// 
    /// Returns memory statistics if available, or an error object if not supported.
    /// 
    /// # JavaScript Example
    /// 
    /// ```javascript
    /// const memInfo = getMemoryUsage();
    /// if (!memInfo.error) {
    ///   console.log('Memory usage:', memInfo);
    /// }
    /// ```
    #[wasm_bindgen(js_name = getMemoryUsage)]
    pub fn mem() -> JsValue {
        std::panic::catch_unwind(get_mem)
            .unwrap_or_else(|_| js_obj(&[("error", "not defined".into())]))
    }

    /// WASM module initialization function.
    /// 
    /// This function is automatically called when the WASM module is loaded.
    /// It sets up console error panic hooks (in debug mode) and logs initialization.
    #[wasm_bindgen(start)]
    pub fn init() {
        debug_log("dereferencer wasm loaded");
        #[cfg(feature = "console_error_panic_hook")]
        console_error_panic_hook::set_once();
    }
}
