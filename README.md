# dynamic_range

A Rust library for handling various types of ranges dynamically.

## Usage

```console
cargo add --git "https://github.com/T1mVo/dynamic_range" --tag v0.2.0
```

## Example

```rust
use dynamic_range::DynamicRange;

fn main() {
    let range = DynamicRange::<u8>::try_from("..").expect("Could not parse range");

    for i in range.into_iter() {
        println!("{i}");
    }
}
```

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
