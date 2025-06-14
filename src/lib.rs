use js_sys::{Object, Reflect};
use rustc_hash::{FxHashMap, FxHashSet};
use serde::Serialize;
use serde_json::Value;
use std::rc::Rc;
use wasm_bindgen::prelude::*;

// Use web-sys for safer console logging
#[cfg(feature = "console_log")]
use web_sys::console;

// Import JavaScript function to get memory info
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_name = getWasmMemoryInfo)]
    fn get_wasm_memory_info() -> JsValue;
}

// Macro for easier console logging
#[cfg(feature = "console_log")]
macro_rules! console_log {
    ($($t:tt)*) => {
        console::log_1(&format_args!($($t)*).to_string().into())
    }
}

#[cfg(not(feature = "console_log"))]
macro_rules! console_log {
    ($($t:tt)*) => {
        // No-op when console logging is disabled
    };
}

// Macro for creating JavaScript objects
macro_rules! js_object {
    ($($key:expr => $value:expr),* $(,)?) => {{
        let obj = Object::new();
        $(
            let _ = Reflect::set(&obj, &$key.into(), &$value.into());
        )*
        obj
    }};
}

/// JavaScript-friendly error type
#[wasm_bindgen]
#[derive(Debug, Clone)]
pub struct WasmError {
    message: String,
}

#[wasm_bindgen]
impl WasmError {
    #[wasm_bindgen(getter)]
    pub fn message(&self) -> String {
        self.message.clone()
    }
}

impl From<String> for WasmError {
    fn from(message: String) -> Self {
        Self { message }
    }
}

impl From<&str> for WasmError {
    fn from(message: &str) -> Self {
        Self {
            message: message.to_string(),
        }
    }
}

/// JavaScript-friendly options for dereferencing
#[wasm_bindgen]
#[derive(Default, Clone)]
pub struct WasmDereferenceOptions {
    resolve_external: bool,
    log_circular_refs: bool,
}

#[wasm_bindgen]
impl WasmDereferenceOptions {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self::default()
    }

    #[wasm_bindgen(setter, js_name = setResolveExternal)]
    pub fn set_resolve_external(&mut self, value: bool) {
        self.resolve_external = value;
    }

    #[wasm_bindgen(getter, js_name = resolveExternal)]
    pub fn resolve_external(&self) -> bool {
        self.resolve_external
    }

    #[wasm_bindgen(setter, js_name = setLogCircularRefs)]
    pub fn set_log_circular_refs(&mut self, value: bool) {
        self.log_circular_refs = value;
    }

    #[wasm_bindgen(getter, js_name = logCircularRefs)]
    pub fn log_circular_refs(&self) -> bool {
        self.log_circular_refs
    }
}

/// Main WASM entry point for dereferencing schemas
#[wasm_bindgen(js_name = dereferenceSchema)]
pub fn dereference_schema_wasm(
    schema_json: &str,
    options: Option<WasmDereferenceOptions>,
) -> Result<String, WasmError> {
    // Parse the input JSON
    let mut schema: Value = serde_json::from_str(schema_json)
        .map_err(|e| WasmError::from(format!("Failed to parse JSON: {}", e)))?;

    let options = options.unwrap_or_default();
    let internal_options = DereferenceOptions {
        resolve_external: options.resolve_external,
        on_circular: if options.log_circular_refs {
            Some(|path: &str| console_log!("Circular reference detected: {}", path))
        } else {
            None
        },
    };

    // Dereference the schema
    dereference_schema(&mut schema, internal_options).map_err(WasmError::from)?;

    // Serialize back to JSON
    serde_json::to_string(&schema)
        .map_err(|e| WasmError::from(format!("Failed to serialize result: {}", e)))
}

/// Alternative entry point that works with JavaScript objects directly
#[wasm_bindgen(js_name = dereferenceSchemaJs)]
pub fn dereference_schema_js(
    schema: &JsValue,
    options: Option<WasmDereferenceOptions>,
) -> Result<JsValue, WasmError> {
    // Convert JsValue to Rust Value
    let mut schema: Value = serde_wasm_bindgen::from_value(schema.clone())
        .map_err(|e| WasmError::from(format!("Failed to convert JS value: {}", e)))?;

    let options = options.unwrap_or_default();
    let internal_options = DereferenceOptions {
        resolve_external: options.resolve_external,
        on_circular: if options.log_circular_refs {
            Some(|path: &str| console_log!("Circular reference detected: {}", path))
        } else {
            None
        },
    };

    // Dereference the schema
    dereference_schema(&mut schema, internal_options).map_err(WasmError::from)?;

    // Convert back to JsValue
    let serializer = serde_wasm_bindgen::Serializer::new().serialize_maps_as_objects(true);
    let js_val = schema
        .serialize(&serializer)
        .map_err(|e| WasmError::from(format!("Failed to convert result to JS: {e}")))?;

    Ok(js_val)
}

/// Get memory usage statistics for debugging - returns a proper JS object
#[wasm_bindgen(js_name = getMemoryUsage)]
pub fn get_memory_usage() -> JsValue {
    // Try to get memory info from JavaScript helper function
    match std::panic::catch_unwind(get_wasm_memory_info) {
        Ok(js_value) => js_value,
        Err(_) => {
            // Fallback: create basic stats using js_object! macro
            let stats = js_object! {
                "error" => "Memory info unavailable - ensure getWasmMemoryInfo is defined"
            };
            stats.into()
        }
    }
}

// Internal types and functions (mostly unchanged from your original)

/// Shared string type to eliminate repeated string allocations
type SharedStr = Rc<str>;

/// A value that can be either owned or shared via Rc to minimize cloning
#[derive(Clone, Debug)]
pub enum DerefValue {
    Owned(Value),
    Shared(Rc<Value>),
}

impl From<DerefValue> for Value {
    fn from(d: DerefValue) -> Self {
        match d {
            DerefValue::Owned(v) => v,
            DerefValue::Shared(rc) => (*rc).clone(),
        }
    }
}

/// Cached resolved reference that can share data efficiently
#[derive(Clone, Debug)]
pub struct CachedRef {
    pub value: Rc<Value>,
    pub circular: bool,
}

/// Options to control the dereferencing process (internal)
#[derive(Clone, Default)]
pub struct DereferenceOptions {
    pub resolve_external: bool,
    pub on_circular: Option<fn(path: &str)>,
}

/// A unified cache using shared strings to reduce allocations
#[derive(Default)]
struct DerefCache {
    resolved_refs: FxHashMap<SharedStr, CachedRef>,
    resolving: FxHashSet<SharedStr>,
    unescape_buffer: String,
}

impl DerefCache {
    fn new() -> Self {
        Self {
            resolved_refs: FxHashMap::default(),
            resolving: FxHashSet::default(),
            unescape_buffer: String::with_capacity(64),
        }
    }
}

/// Dereferences a JSON Schema, resolving all `$ref` pointers.
pub fn dereference_schema(schema: &mut Value, options: DereferenceOptions) -> Result<(), String> {
    let mut cache = DerefCache::new();

    // Use the safe raw pointer optimization from your original
    let root_ptr: *const Value = schema;
    crawl(schema, unsafe { &*root_ptr }, &mut cache, &options)?;
    Ok(())
}

/// Recursively crawls and dereferences a JSON value.
fn crawl(
    current_value: &mut Value,
    root_schema: &Value,
    cache: &mut DerefCache,
    options: &DereferenceOptions,
) -> Result<bool, String> {
    match current_value {
        Value::Object(map) => {
            if let Some(Value::String(ref_str_val)) = map.get("$ref") {
                let shared_ref_str: SharedStr = Rc::from(ref_str_val.as_str());

                let (resolved_value, is_circular) =
                    dereference_ref(shared_ref_str, root_schema, cache, options)?;

                *current_value = resolved_value.into();
                return Ok(is_circular);
            }

            for (_key, value) in map.iter_mut() {
                crawl(value, root_schema, cache, options)?;
            }
        }
        Value::Array(arr) => {
            for value in arr.iter_mut() {
                crawl(value, root_schema, cache, options)?;
            }
        }
        _ => {}
    }
    Ok(false)
}

/// Dereferences a single `$ref` string using shared strings and optimized caching.
fn dereference_ref(
    ref_str: SharedStr,
    root_schema: &Value,
    cache: &mut DerefCache,
    options: &DereferenceOptions,
) -> Result<(DerefValue, bool), String> {
    // Check for a fully resolved cache entry
    if let Some(cached) = cache.resolved_refs.get(&ref_str) {
        return Ok((
            DerefValue::Shared(Rc::clone(&cached.value)),
            cached.circular,
        ));
    }

    // Check for a circular reference
    if cache.resolving.contains(&ref_str) {
        if let Some(on_circular) = options.on_circular {
            on_circular(&ref_str);
        }
        return Ok((DerefValue::Owned(Value::Null), true));
    }

    // Resolve the JSON pointer
    if let Some(pointer) = ref_str.strip_prefix('#') {
        let mut resolved =
            resolve_json_pointer(root_schema, pointer, &mut cache.unescape_buffer)?.clone();

        cache.resolving.insert(Rc::clone(&ref_str));

        let crawl_result = crawl(&mut resolved, root_schema, cache, options);

        cache.resolving.remove(&ref_str);

        let is_circular = crawl_result?;

        let resolved_rc = Rc::new(resolved);
        let cached_ref = CachedRef {
            value: Rc::clone(&resolved_rc),
            circular: is_circular,
        };
        cache.resolved_refs.insert(ref_str, cached_ref);

        Ok((DerefValue::Shared(resolved_rc), is_circular))
    } else if options.resolve_external {
        // In WASM, we can't resolve external references directly
        // This would need to be handled by JavaScript callbacks
        Err(format!(
            "External reference resolution not supported in WASM: {}. Use JavaScript to resolve external references.",
            ref_str
        ))
    } else {
        Err(format!(
            "External reference resolution disabled for: {}",
            ref_str
        ))
    }
}

/// JSON pointer resolution with zero-allocation unescaping
fn resolve_json_pointer<'a>(
    root: &'a Value,
    pointer: &str,
    unescape_buffer: &mut String,
) -> Result<&'a Value, String> {
    if pointer.is_empty() {
        return Ok(root);
    }

    if !pointer.starts_with('/') {
        return Err(format!("Invalid JSON pointer: #{}", pointer));
    }

    pointer[1..].split('/').try_fold(root, |current, token| {
        unescape_json_pointer_token(token, unescape_buffer);

        match current {
            Value::Object(obj) => obj
                .get(unescape_buffer)
                .ok_or_else(|| format!("Token '{}' not found in object", unescape_buffer)),
            Value::Array(arr) => {
                let index: usize = unescape_buffer
                    .parse()
                    .map_err(|_| format!("Invalid array index '{}'", unescape_buffer))?;
                arr.get(index)
                    .ok_or_else(|| format!("Index {} out of bounds", index))
            }
            _ => Err("Pointer traversal expected object or array".to_string()),
        }
    })
}

/// Fast, zero-allocation JSON pointer token unescaping
fn unescape_json_pointer_token(token: &str, out: &mut String) {
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

/// Iterative version optimized for WASM (avoids deep recursion)
#[wasm_bindgen(js_name = dereferenceSchemaIterative)]
pub fn dereference_schema_iterative_wasm(
    schema_json: &str,
    options: Option<WasmDereferenceOptions>,
) -> Result<String, WasmError> {
    let mut schema: Value = serde_json::from_str(schema_json)
        .map_err(|e| WasmError::from(format!("Failed to parse JSON: {}", e)))?;

    let options = options.unwrap_or_default();
    let internal_options = DereferenceOptions {
        resolve_external: options.resolve_external,
        on_circular: if options.log_circular_refs {
            Some(|path: &str| console_log!("Circular reference detected: {}", path))
        } else {
            None
        },
    };

    dereference_schema_iterative(&mut schema, internal_options).map_err(WasmError::from)?;

    serde_json::to_string(&schema)
        .map_err(|e| WasmError::from(format!("Failed to serialize result: {}", e)))
}

/// Iterative traversal to eliminate recursion overhead for very deep schemas
pub fn dereference_schema_iterative(
    schema: &mut Value,
    options: DereferenceOptions,
) -> Result<(), String> {
    let mut cache = DerefCache::new();
    let root_ptr: *const Value = schema;
    let root_schema = unsafe { &*root_ptr };

    let mut stack = vec![schema as *mut Value];

    while let Some(node_ptr) = stack.pop() {
        let node = unsafe { &mut *node_ptr };

        match node {
            Value::Object(map) => {
                if let Some(Value::String(ref_str_val)) = map.get("$ref") {
                    let shared_ref_str: SharedStr = Rc::from(ref_str_val.as_str());

                    let (resolved_value, _is_circular) =
                        dereference_ref(shared_ref_str, root_schema, &mut cache, &options)?;

                    *node = resolved_value.into();
                } else {
                    for value in map.values_mut() {
                        stack.push(value);
                    }
                }
            }
            Value::Array(arr) => {
                for value in arr.iter_mut() {
                    stack.push(value);
                }
            }
            _ => {}
        }
    }

    Ok(())
}

// Initialize WASM module
#[wasm_bindgen(start)]
pub fn main() {
    console_log!("JSON Schema Dereferencer WASM module loaded");

    // Set up panic hook for better error reporting
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
}

/// Estimate schema size - returns a plain JS object using js_object! macro
#[wasm_bindgen(js_name = estimateSchemaSize)]
pub fn estimate_schema_size(schema_json: &str) -> Result<JsValue, WasmError> {
    let schema: Value = serde_json::from_str(schema_json)
        .map_err(|e| WasmError::from(format!("Failed to parse JSON: {}", e)))?;

    let (object_count, array_count, ref_count) = count_elements(&schema);

    // Create a plain JavaScript object using the js_object! macro
    let stats = js_object! {
        "estimatedBytes" => schema_json.len(),
        "objectCount" => object_count,
        "arrayCount" => array_count,
        "refCount" => ref_count,
    };

    Ok(stats.into())
}

fn count_elements(value: &Value) -> (usize, usize, usize) {
    match value {
        Value::Object(map) => {
            let mut object_count = 1;
            let mut array_count = 0;
            let mut ref_count = if map.contains_key("$ref") { 1 } else { 0 };

            for (_, v) in map {
                let (o, a, r) = count_elements(v);
                object_count += o;
                array_count += a;
                ref_count += r;
            }

            (object_count, array_count, ref_count)
        }
        Value::Array(arr) => {
            let mut object_count = 0;
            let mut array_count = 1;
            let mut ref_count = 0;

            for v in arr {
                let (o, a, r) = count_elements(v);
                object_count += o;
                array_count += a;
                ref_count += r;
            }

            (object_count, array_count, ref_count)
        }
        _ => (0, 0, 0),
    }
}
