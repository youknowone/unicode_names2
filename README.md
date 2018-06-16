# unicode_names2

[![Build Status](https://travis-ci.org/huonw/unicode_names2.png)](https://travis-ci.org/huonw/unicode_names2) [![Coverage Status](https://coveralls.io/repos/huonw/unicode_names2/badge.svg)](https://coveralls.io/r/huonw/unicode_names2)

Time and memory efficiently mapping characters to and from their
Unicode 7.0 names, at runtime and compile-time.

```rust
extern crate unicode_names2;

fn main() {
    println!("☃ is called {}", unicode_names2::name('☃')); // SNOWMAN
    println!("{} is happy", unicode_names2::character("white smiling face")); // ☺
    // (NB. case insensitivity)
}
```

The maps are compressed using similar tricks to Python's `unicodedata`
module, although those here are about 70KB (12%) smaller.

[**Documentation**](http://huonw.github.io/unicode_names/unicode_names)
