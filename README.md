# Unbinder

A high-performance JSON Schema dereferencer written in Rust with WebAssembly
support. Unbinder resolves `$ref` pointers in JSON Schema documents, making them
self-contained by replacing references with their actual content.

## Features

-   🚀 **Fast** - Written in Rust for maximum performance
-   🌐 **WebAssembly Support** - Use in browsers and Node.js environments
-   🔄 **Circular Reference Detection** - Handles circular references gracefully
-   🎯 **Zero Dependencies** - Minimal footprint with `no_std` support
-   🔧 **Flexible** - Available as both Rust crate and npm package

## Installation

### As a Rust Crate

```toml
[dependencies]
unbinder = "0.1.7"
```

### As an npm Package

```bash
npm install unbinder
```

## Usage

### Rust

```rust
use unbinder::{dereference_schema, Options};
use serde_json::json;

fn main() -> Result<(), unbinder::Error> {
    let mut schema = json!({
        "type": "object",
        "properties": {
            "name": { "$ref": "#/definitions/name" },
            "age": { "$ref": "#/definitions/age" }
        },
        "definitions": {
            "name": { "type": "string" },
            "age": { "type": "integer", "minimum": 0 }
        }
    });

    // Dereference with default options
    dereference_schema(&mut schema, Options::default())?;

    // Or with custom options
    let opts = Options {
        resolve_external: false,
        on_circular: Some(|path| println!("Circular reference detected: {}", path)),
    };
    dereference_schema(&mut schema, opts)?;

    println!("{}", serde_json::to_string_pretty(&schema)?);
    Ok(())
}
```

### JavaScript/TypeScript

**Important:** WebAssembly modules must be initialized before use

```javascript
import init, { dereferenceSchema, Options } from "unbinder";

// Initialize the WASM module (required!)
await init();

const schema = {
    type: "object",
    properties: {
        name: { $ref: "#/definitions/name" },
        age: { $ref: "#/definitions/age" },
    },
    definitions: {
        name: { type: "string" },
        age: { type: "integer", minimum: 0 },
    },
};

// Create options (optional)
const options = new Options();
options.logCircularRefs = true;

// Dereference the schema
const dereferenced = dereferenceSchema(schema, options);
console.log(JSON.stringify(dereferenced, null, 2));
```

#### Browser Usage

```html
<script type="module">
    import init, {
        dereferenceSchema,
        Options,
    } from "./node_modules/unbinder/unbinder.js";

    async function run() {
        // Initialize WASM
        await init();

        // Now you can use dereferenceSchema
        const result = dereferenceSchema(mySchema);
    }

    run();
</script>
```

### TypeScript

The package includes TypeScript definitions:

```typescript
import init, { dereferenceSchema, Options, WasmError } from "unbinder";

async function processSchema() {
    // Initialize WASM first
    await init();
    
    try {
        const result = dereferenceSchema(schema, new Options());
        return result;
    } catch (error) {
        if (error instanceof WasmError) {
            console.error("Dereferencing failed:", error.message);
        }
    }
}
```

## API Reference

### Rust API

#### `dereference_schema(root: &mut Value, opts: Options) -> Result<(), Error>`

Dereferences all `$ref` pointers in the given JSON value in-place.

-   `root`: The JSON value to dereference (modified in-place)
-   `opts`: Options for controlling the dereferencing behavior

#### `Options`

```rust
pub struct Options {
    pub resolve_external: bool,              // Whether to resolve external references
    pub on_circular: Option<fn(&str)>,       // Callback for circular references
}
```

#### `count(v: &Value) -> (usize, usize, usize)`

Returns statistics about the JSON structure:

-   Number of objects
-   Number of arrays
-   Number of `$ref` references

### JavaScript API

#### `dereferenceSchema(value: any, options?: Options): any`

Dereferences all `$ref` pointers in the given JSON object.

#### `Options` class

```javascript
class Options {
  constructor()
  setResolveExternal(value: boolean): void
  setLogCircularRefs(value: boolean): void
}
```

#### `estimateSchemaSize(json: string): object`

Returns statistics about the JSON structure:

```javascript
{
  bytes: number,    // Size in bytes
  objects: number,  // Number of objects
  arrays: number,   // Number of arrays
  refs: number      // Number of $ref references
}
```

## Building from Source

### Prerequisites

-   I have only used with Rust 1.88, it might work for earlier versions
-   wasm-pack (for WebAssembly builds)
-   Node.js (for npm package)

### Building the Rust Crate

```bash
cargo build --release
```

### Building the WebAssembly Module

```bash
# Install wasm-pack if not already installed
cargo install wasm-pack

# Build the WASM module
wasm-pack build --target web --out-dir pkg
```

## Features

The crate supports several feature flags:

-   `std` (default): Standard library support
-   `wasm`: WebAssembly bindings
-   `parallel`: Parallel processing support
-   `console_log`: Console logging in WASM
-   `wee_alloc`: Use wee_alloc as the global allocator
-   `text-interface`: String-based API for WASM

## Performance

Unbinder is optimized for performance:

-   Uses `FxHashMap` for faster hash operations
-   Implements zero-copy parsing where possible
-   Supports `no_std` environments for embedded use
-   Optional parallel processing for large schemas
-   Tiny WASM bundle size with wee_alloc

## Limitations

-   Currently only supports internal references (starting with `#`)
-   External references (URLs) are not yet supported
-   JSON Pointer syntax follows RFC 6901

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file
for details.

## Author

Jakob Lochinski

## See Also

-   [JSON Schema Specification](https://json-schema.org/)
-   [JSON Pointer (RFC 6901)](https://tools.ietf.org/html/rfc6901)
