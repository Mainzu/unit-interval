# Unit Interval

[![Crates.io](https://img.shields.io/crates/v/unit_interval.svg)](https://crates.io/crates/unit_interval)
[![Documentation](https://docs.rs/unit_interval/badge.svg)](https://docs.rs/unit_interval)

A small crate that provide type-level constrain for numerical values.

## Features

- Type level representation of values in [0, 1]
- Checked and clamped arithmetic operations
- Conversion to and from the underlying numeric type
- Error types for values outside the interval
- Support for various numeric types through generics

## Documentation

For examples and information about the API, please check the [documentation](https://docs.rs/unit_interval).

## Motivation

This crate came about as an over-engineered way to work with fractions at a type-level for a ratio type.
