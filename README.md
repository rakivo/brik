# brik

**brik** is a library for constructing RISC-V object files from scratch.

Think of it as the building block for custom assemblers, linkers, and binary tools - raw, minimal, and designed for maximum control.

---

## Status

> [!Warning]
> Early stage development. APIs are unstable and are very likely to change.

---

## Usage

Currently under active development.
Check back soon for examples and API docs.

## `no_std` Support

`brik` is fully compatible with **`no_std`** environments.
This means you can use it in:
- Embedded RISC-V firmware
- OS kernels
- Bare-metal environments
- WASM (without standard library)

## RISC-V Coverage

| Extension    | Name                                   | RV32 | RV64 | Status / Notes                      |
|--------------|----------------------------------------|------|------|-------------------------------------|
| **I**        | Base Integer Instruction Set           | ✅   | ✅   | Almost all instructions implemented |
| **M**        | Integer Multiplication & Division      | ✅   | ✅   | Fully implemented                   |
| **A**        | Atomic Instructions                    | ✅   | ✅   | Fully implemented                   |
| **F**        | Single-Precision Floating Point        | ❌   | ❌   | Not yet implemented                 |
| **D**        | Double-Precision Floating Point        | ❌   | ❌   | Not yet implemented                 |
| **Q**        | Quad-Precision Floating Point          | ❌   | ❌   | Not yet implemented                 |
| **C**        | Compressed Instructions                | ❌   | ❌   | Not yet implemented                 |
| **B**        | Bit-Manipulation Instructions          | ❌   | ❌   | Not yet implemented                 |
| **J**        | Dynamically Translated Languages       | ❌   | ❌   | Not yet implemented                 |
| **T**        | Transactional Memory                   | ❌   | ❌   | Not yet implemented                 |
| **P**        | Packed-SIMD / Vector                   | ❌   | ❌   | Not yet implemented                 |
| **V**        | Vector Extension                       | ❌   | ❌   | Not yet implemented                 |
| **Zicsr**    | Control and Status Register Access     | ❌   | ❌   | Not yet implemented                 |
| **Zifencei** | Instruction-Fetch Fence                | ❌   | ❌   | Not yet implemented                 |

## Contributing

We welcome contributions from everyone! Whether it's fixing bugs, implementing missing instructions, improving documentation, or adding new features, your help is greatly appreciated.

