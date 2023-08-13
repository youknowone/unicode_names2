# v1.0.0

*2023-08-13*

Breaking:

* Bump minimum Rust version from 1.48 to 1.63
* Bump dependencies ([#22](https://github.com/progval/unicode_names2/pull/22), [#23](https://github.com/progval/unicode_names2/pull/23))

Features:

* Build the perfect-hash function deterministically ([#13](https://github.com/progval/unicode_names2/pull/13)
* Build the perfect-hash function at compile time from unicode data, instead of being
  in version control and shipped on crates.io ([#17](https://github.com/progval/unicode_names2/pull/17))

Internal:

* Run Rustfmt + Clippy on CI and fix warnings ([#14](https://github.com/progval/unicode_names2/pull/14), [#15](https://github.com/progval/unicode_names2/pull/15))

# v0.6.0

*2022-10-13*

Data:

* Update data for Unicode 15 ([#10](https://github.com/progval/unicode_names2/pull/))

# v0.5.1

*2022-08-09*

Bug fixes:

* Fix panic when character() is passed a string over 88 chars ([#7](https://github.com/progval/unicode_names2/pull/7))
* Fix compilation warnings ([#5](https://github.com/progval/unicode_names2/pull/5))

Internal:

* Replace Travis with Github Workflows as CI ([#8](https://github.com/progval/unicode_names2/pull/8))
* Run CI on sub-crates ([#9](https://github.com/progval/unicode_names2/pull/9))

# v0.5.0

*2022-02-06*

Data:

* Update to Unicode 14.0.0 ([#4](https://github.com/progval/unicode_names2/pull/4))
