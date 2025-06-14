//! JSON-Schema dereferencer: `no_std` core + optional WASM front-end.

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
    pub type Error = String;

    #[derive(Clone, Default)]
    pub struct Options {
        pub resolve_external: bool,
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
    pub fn dereference_schema(root: &mut Value, opts: Options) -> Result<(), Error> {
        let mut cache = Cache::default();
        let raw = root as *const Value;
        unsafe { crawl(root, &*raw, &mut cache, &opts) }?;
        Ok(())
    }

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
    #[wasm_bindgen]
    pub struct WasmError(String);
    impl<E: fmt::Display> From<E> for WasmError {
        fn from(e: E) -> Self {
            Self(e.to_string())
        }
    }
    #[wasm_bindgen]
    impl WasmError {
        #[wasm_bindgen(getter)]
        pub fn message(&self) -> String {
            self.0.clone()
        }
    }

    // ── options object passed from JS ───────────────────────────
    #[wasm_bindgen]
    #[derive(Clone, Default)]
    pub struct Options {
        resolve_external: bool,
        log_circular: bool,
    }
    #[wasm_bindgen]
    impl Options {
        #[wasm_bindgen(constructor)]
        pub fn new() -> Self {
            Self::default()
        }
        #[wasm_bindgen(setter)]
        pub fn set_resolve_external(&mut self, v: bool) {
            self.resolve_external = v;
        }
        #[wasm_bindgen(setter, js_name = setLogCircularRefs)]
        pub fn set_log_circular(&mut self, v: bool) {
            self.log_circular = v;
        }
    }

    // ── main wasm entry (JsValue → JsValue) ─────────────────────
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
    #[cfg(feature = "text-interface")]
    #[wasm_bindgen(js_name = dereferenceSchemaText)]
    pub fn deref_text(s: &str) -> Result<String, WasmError> {
        let mut v: serde_json::Value = serde_json::from_str(s)?;
        c::dereference_schema(&mut v, c::Options::default())?;
        Ok(serde_json::to_string(&v)?)
    }

    // statistics helper
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

    #[wasm_bindgen(js_name = getMemoryUsage)]
    pub fn mem() -> JsValue {
        std::panic::catch_unwind(get_mem)
            .unwrap_or_else(|_| js_obj(&[("error", "not defined".into())]))
    }

    #[wasm_bindgen(start)]
    pub fn init() {
        debug_log("dereferencer wasm loaded");
        #[cfg(feature = "console_error_panic_hook")]
        console_error_panic_hook::set_once();
    }
}
