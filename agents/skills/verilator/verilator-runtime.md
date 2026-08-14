---
name: verilator-runtime
description: Verilator runtime library (include/) patterns: C++14 baseline, fixed-width types, thread safety, VPI, coverage, tracing
---

# Verilator Runtime Library Skill

## Overview

The runtime (`include/`) is **separate from the compiler** (`src/`). The compiler emits C++ that calls into this library; this code runs during simulation. Optimize for **execution speed and portability**, not compile-time clarity.

## Key Files

| File | Purpose |
|------|---------|
| `verilated.h` | Core model API |
| `verilated_types.h` | Fixed-width data types (`CData`, `SData`, `IData`, `QData`, `VlWide`) |
| `verilated_random.cpp` | Constrained-random runtime (SMT-LIB 2.6) |
| `verilated_cov.*` | Coverage runtime |
| `verilated_threads.*` | MT runtime |
| `verilated_timing.*` | `--timing` runtime |
| `verilated_vcd_c.*` / `verilated_fst_c.*` | Tracing |

## C++14 Baseline Rule

```cpp
// Runtime MUST build under --no-timing with C++14
// C++20 features ONLY in --timing code paths

// Example: std::countl_zero (C++20) with fallback
#if __cplusplus >= 202002L
    return std::countl_zero(value);
#else
    // Portable fallback
    return __builtin_clz(value);
#endif
```

## Public API Conventions

```cpp
// Prefix public classes/types with Verilated/Vl to avoid user code collisions
class VerilatedModel { ... };
class VlWide { ... };

// Document with /// comments - feeds doc generation
/// Return the current simulation time
VL_PURE uint64_t Verilated::time() { ... }
```

## Fixed-Width Model Types (CRITICAL)

```cpp
// NEVER use size_t for model data
// Use fixed-width types from verilated_types.h:

CData   // 8-bit  (char)
SData   // 16-bit (short)
IData   // 32-bit (int)
QData   // 64-bit (long long)
VlWide  // Arbitrary width (array of QData)

// Word-by-word operations - NEVER bit-by-bit or byte-by-byte
VL_ZERO_W(dst, words);           // Zero wide array
VL_MEMCPY_W(dst, src, words);    // Copy wide array
VL_WORDS_I(bits);                // Words needed for bits
VL_MASK_I(bits);                 // Mask for partial top word
VL_BITWORD_I(bit);               // Word index for bit

// Include verilatedos.h for VL_* macros - NOT <cstdint> directly
#include "verilatedos.h"
```

## Thread Safety Hierarchy

```cpp
// Annotate everything - annotations MUST match implementation
VL_PURE        // No side effects, calls only PURE functions
VL_MT_SAFE     // Safe under locks (internal synchronization)
VL_MT_STABLE   // Safe only while tree topology stable

// Mutex-protected members
class MyClass {
    VL_GUARDED_BY(m_mutex) int m_counter = 0;
    mutable std::mutex m_mutex;
};

// Document acquisition ordering if multiple mutexes
// Prefer has-a over is-a: guarded wrapper around unguarded internal
```

## Performance Rules (Runtime)

```cpp
// No exceptions in runtime code - use error returns or assertions
// Exceptions add overhead on EVERY path

// Do all string parsing at VERILATION TIME - never during simulation
// Emit structured data or compile-time hints instead

// Keep per-cycle code lean:
//   - No vtables on high-frequency objects (8 bytes/instance)
//   - Guard optional features: hasClasses()/hasEvents() checks
//   - Per-cycle functions: avoid mutexes - use atomics or lockless

// Emit NO runtime loops the compiler could have expanded at verilation time
// Prefer single runtime call over emitted loop
```

## Coverage Runtime (`verilated_cov.cpp`)

```cpp
// Shared by ALL models - keep per-point overhead minimal
// On-disk format MUST stay stable for verilator_coverage tool

// Instrumentation contexts = opt-in (allowlist), NEVER blocklist
// Blocklists silently break when new contexts appear
```

## Constrained Random (`verilated_random.cpp`)

```cpp
// Emit ONLY portable SMT-LIB 2.6
// NO solver-specific or MaxSMT extensions
// Generated solver text = model's runtime constraint interface

// SMT-LIB 2.6 standard commands:
//   (set-logic QF_BV)
//   (declare-fun ...)
//   (assert ...)
//   (check-sat)
//   (get-value ...)
```

## VPI Support

```cpp
// VPI = Verilog Procedural Interface for external tools
// --vpi flag generates VPI registration code

// Lazy VPI (--vpi-lazy-public-rw): demand-driven reconstruction
// Only reconstruct signals actually accessed via VPI

// t_vpi_* tests in test_regress/t/
```

## Tracing (VCD/FST)

```cpp
// verilated_vcd_c.cpp / verilated_fst_c.cpp
// Zero-trimming optimization (PR #7852):
//   - Use __builtin_clz / _BitScanReverse / std::countl_zero
//   - Let compiler decide branch prediction on zero checks
//   - Signed negative values: emit full two's complement

// t_trace_basic.v covers all trace formats
```

## File-Specific Rules

| File | Rule |
|------|------|
| `verilated_random.cpp` | Emit only portable SMT-LIB 2.6 - no solver-specific/MaxSMT extensions |
| `verilated_cov.cpp` | Keep per-point overhead minimal; on-disk format stable for `verilator_coverage` |

## Common Runtime Fixes

### Adding New Runtime Function
```cpp
// 1. Declare in verilated.h with /// doc
// 2. Implement in verilated.cpp
// 3. Annotate thread safety (VL_PURE / VL_MT_SAFE / VL_MT_STABLE)
// 4. Use fixed-width types (CData/SData/IData/QData/VlWide)
// 5. No exceptions - error returns or assertions
// 6. Test in t_* test with actual simulation
```

### Fixing Trace Output
```cpp
// VCD: verilated_vcd_c.cpp - emitVcdValue()
// FST: verilated_fst_c.cpp - emitFstValue()
// Add test case to t_trace_basic.v with HARNESS_UPDATE_GOLDEN=1
```

### Coverage Bug
```cpp
// verilated_cov.cpp - coverage point/bucket handling
// Test: t_cov_* tests, run verilator_coverage to verify
```

## Testing Runtime Changes

```bash
# Runtime-only fix: does NOT rebuild verilator_bin
# Test with existing regression:
test_regress/t/t_<name>.py

# Or create minimal test:
# test.v + test.py with test.compile() + test.execute()
```