---
name: verilator-performance
description: Verilator performance optimization patterns: memory efficiency, O(n^2) elimination, compile-time vs runtime, thread safety, fixed-width types
---

# Verilator Performance Optimization Skill

## Core Philosophy

> **Almost every decision is made at verilation (compile) time; the generated C++ just advances state each evaluation. Optimize for verilation-time work over runtime work.**

## Memory Efficiency

### AST Node Allocation
```cpp
// NEVER allocate AstNode on stack or by value - always pointers
// Use astgen-generated accessors, not manual memory management

// Deferred deletion in visitors - safe against re-entry and unlinking order
VL_DO_DANGLING(pushDeletep(nodep), nodep);  // NOT deleteTree()

// deleteTree() ONLY for fresh nodes that never entered the tree

// When raw node pointers key a map/set, ERASE entries when node deleted
// Allocators reuse addresses -> stale entries alias new nodes
```

### Container Optimization
```cpp
// std::map for per-module structures (many small instances)
// unordered_map ONLY for one-per-netlist data
// NEVER let unordered_* iteration order reach generated output

// Prefer emplace over insert; check returned .second instead of separate find()
map.emplace(key, value);  // NOT insert + find

// reserve() strings and vectors when size estimable
vector.reserve(estimated_size);
string.reserve(estimated_size);

// NO new static or global mutable data - statics being eliminated for future parallelism
```

### Fixed-Width Types (Runtime & Compiler)
```cpp
// Model data: CData/SData/IData/QData/VlWide - NEVER size_t
// Process wide data word-by-word:
VL_ZERO_W(dst, words);           // Zero wide array
VL_MEMCPY_W(dst, src, words);    // Copy wide array
VL_WORDS_I(bits);                // Words needed for bits
VL_MASK_I(bits);                 // Mask for partial word

// Include verilatedos.h for VL_* macros - NOT <cstdint> directly
#include "verilatedos.h"

// For compiler internal data: same principle - avoid heap in hot paths
```

## Eliminating O(n^2) Patterns

### Before (Quadratic)
```cpp
// BAD: Linear search in loop = O(n^2)
for (auto item : items) {
    for (auto other : items) { ... }
}

// BAD: backp() for parent lookup = O(n^2) hunts
while (nodep->backp()) { nodep = nodep->backp(); }

// BAD: Linear name lookups
for (auto var : vars) { if (var->name() == target) ... }
```

### After (Linear/Logarithmic)
```cpp
// GOOD: Build map for batch lookups
std::map<std::string, AstVar*> nameMap;
for (auto var : vars) nameMap[var->name()] = var;
// Then O(log n) or O(1) lookups

// GOOD: Capture context during forward traversal
struct Context { AstModule* currentModule; std::vector<AstVar*> vars; };
// Pass context through VL_RESTORER

// GOOD: VMemberMap for name lookups - O(1)
VMemberMap<AstVar*> varMap;
varMap.insert(var->name(), var);
if (auto found = varMap.findMember(name)) { ... }
```

### Common O(n^2) Sources & Fixes

| Pattern | Fix |
|---------|-----|
| `backp()` hunting | Build parent map during forward walk |
| Linear name search | `VMemberMap` / `std::map` / `unordered_map` |
| Nested foreach on same container | Pre-build index/map |
| Repeated `dtypep()->width()` | Cache in local variable |
| String concatenation for paths | Use structured `AstDot` nodes |
| Iterating all nodes for one type | New `visit()` handler in existing visitor |

## Compile-Time vs Runtime Optimization

### Verilation-Time (Compiler) - Invest Heavily
```cpp
// Constant folding: V3Const.cpp
// Expression simplification: V3Simplify
// Dead code elimination: V3Dead
// Loop unrolling: V3Unroll
// Function inlining: V3Inline
// Parameter resolution: V3Param
// Width/type assignment: V3Width
// Scheduling: V3Sched

// String parsing at verilation time - NEVER during simulation
// Emit structured data or compile-time hints instead
```

### Runtime (Generated C++) - Minimize Overhead
```cpp
// No vtables on high-frequency objects (8 bytes/instance)
// Guard optional features: hasClasses()/hasEvents() checks
// Per-cycle functions: avoid mutexes - use atomics or lockless
// No runtime loops compiler could expand at verilation time
// Prefer single runtime call over emitted loops

// Thread safety annotations (must match implementation):
VL_PURE        // No side effects, calls only PURE
VL_MT_SAFE     // Safe under locks
VL_MT_STABLE   // Safe only while tree topology stable

// Mutex-protected: VL_GUARDED_BY(mutex) + document acquisition order
```

## Pass-Level Performance

### V3Stats - Deterministic Regression Anchors
```cpp
// Count what every new pass does via V3Stats
// Stats become deterministic regression anchors
V3Stats::addStat("pass_name", "metric_name", count);

// Example: NFA ring buffer optimization (PR #8101)
// Before: O(N) clear on every assertion reset
// After: Lazy invalidation - O(1) reset + O(1) per element on next use
```

### Scheduler (V3Sched) - High Risk Area
```cpp
// Every change needs test proving necessity
// Isolate unrelated scheduler changes into separate PRs
// MT scheduling: stepCost removed (PR #8032)
// Static init ordering: dependency across call graphs (PR #7207)
```

### DFG Optimizer (V3Dfg)
```cpp
// Circular logic optimization (PR #7902)
// Combinational logic -> data-flow graph
// Word-by-word processing for wide signals
```

## Thread Safety for Performance

```cpp
// Annotate everything: VL_PURE > VL_MT_SAFE > VL_MT_STABLE
// Annotations MUST match implementation

// Never include verilated.h in compiler - use verilatedos.h

// ++ on shared state NOT thread-safe
// container.empty() NOT thread-safe

// Prefer has-a over is-a:
//   Guarded class wrapping unguarded internal
//   Guarded version = default public API
```

## Specific Optimization Patterns from PRs

### Ring Buffer Lazy Invalidation (PR #8101)
```cpp
// Before: clear entire delay-ring vector (O(N)) on every assertion reset
// After:
void reset() {
    m_liveCount = 0;        // O(1)
    m_ringIndex = 0;        // O(1)
    m_wrapped = false;      // O(1) - marks existing contents as stale
}
// Elements overwritten on next use - amortized O(1)
```

### VCD Zero Trimming (PR #7852)
```cpp
// Use __builtin_clz / _BitScanReverse / std::countl_zero
// Zero values common - let compiler decide branch prediction
// MSVC fallback: _BitScanReverse
// Don't require AVX2/LZCNT explicitly - compiler selects
```

### Constraint Solver (PR #8042, #7675)
```cpp
// Avoid exponential backtracking
// Unigen2 algorithm for large spaces
// Budget-based solver timeout (wall-clock ms)
// SMT-LIB 2.6 portable - no solver-specific extensions
```

### Randomization (PR #7991, #8055)
```cpp
// Redesign solver session to avoid breaking randomize
// Route std::randomize through process RNG
// randc cycling with solve...before - separate phases
```

## Memory Leak Prevention

```cpp
// Use VL_DO_DANGLING for deferred deletion in visitors
// Erase map/set entries when nodes deleted (address reuse)
// No static/global mutable data
// astgen-generated cloneRelink() propagates all stateful flags
// broken() override for cross-tree pointers
// VNUser1InUse/VNUser2InUse guards document user field ownership
```

## Profiling & Measurement

```bash
# Build with --enable-ccwarn so new compiler warnings stop build
autoconf && ./configure --enable-ccwarn && make -j8

# Run specific test with timing
time test_regress/t/t_<name>.py

# Full regression (requires --enable-longtests)
make test

# Coverage report shows uncovered branches
# Patch coverage in CI shows which paths tests exercise
```

## Anti-Patterns to Avoid

| Anti-Pattern | Why | Replacement |
|--------------|-----|-------------|
| `auto` for non-iterators | Hides type, prevents const | Explicit type with `const` |
| C-style casts | Bypasses type safety | `static_cast` / `VN_CAST` |
| `backp()` in loops | O(n^2) parent hunt | Forward-traversal context map |
| `deleteTree()` in visitors | Unsafe re-entry | `VL_DO_DANGLING(pushDeletep)` |
| Raw string paths | Breaks `--protect`, FileLine | `AstDot` / parse-ref chains |
| Column-aligned test decls | Style test fails | Flush-left, single space |
| Hand-written `.out` goldens | Harness normalizes paths | `HARNESS_UPDATE_GOLDEN=1` |
| `v3fatalSrc` for user errors | Not user-triggerable | `v3error` / `v3warn` |
| `unordered_*` iteration in output | Non-deterministic | `std::map` or explicit sort |
| Stack AstNode | Lifetime bugs | Heap pointers only |