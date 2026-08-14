---
name: verilator-architecture
description: Understand Verilator's compiler architecture: pipeline stages, AST, visitors, passes
---

# Verilator Architecture Skill

## Pipeline Stages (in source order)

| Stage | Purpose | Key Files |
|-------|---------|-----------|
| Preprocess + Parse | Lex/parse SystemVerilog -> raw AST | `verilog.l`, `verilog.y` |
| Link/Elaborate | Resolve names, scopes, parameters, instantiate hierarchy | `V3LinkParse`, `V3LinkDot`, `V3Param` |
| Width/Type | Assign/check data types and bit widths | `V3Width` |
| Transform/Optimize/Schedule | Const fold, lower features, schedule events | `V3Const`, `V3Randomize`, `V3Assert*`, `V3Sched`, `V3Timing`, `V3Dfg` |
| Emit | Lower final AST -> generated C++ | `V3EmitC*` |
| Runtime | Library the generated model links against | `include/verilated*` |

**Rule**: Almost every decision is made at verilation (compile) time; generated C++ just advances state. Optimize for verilation-time work.

## AST Fundamentals

- **Everything is an `AstNode`**: Each construct = `Ast*` subclass (`AstAdd`, `AstVar`, `AstIf`)
- **Tree structure**: Design = one tree, statement lists threaded by `nextp()` sibling links
- **Children in slots**: `op1p()`..`op4p()` accessed by **named accessors** (`lhsp()`, `condp()`, `thensp()`) - never raw slots
- **astgen generates boilerplate**: Declare children/pointers with `@astgen op` / `@astgen ptr` in `V3AstNode*.h` headers
- **Top of tree**: `AstNetlist` - check for this to detect tree root

## Visitor/Pass Model

```cpp
// Standard pass pattern (e.g., TimingSuspendableVisitor in V3Timing.cpp)
class MyPassVisitor : public VNVisitor {
    // Private constructor, static apply() entry point
    static void apply(AstNetlist* nodep) { MyPassVisitor().iterate(nodep); }
    
    // Visit handlers for node types of interest
    void visit(AstIf* nodep) { ...; iterateChildren(nodep); }
    void visit(AstVar* nodep) { ...; iterateChildren(nodep); }
    
    // Use VL_RESTORER on every member modified before iterating children
    VL_RESTORER(m_someState);
};
```

**Key visitor conventions**:
- Private constructor + static `apply()` named after file
- Walk tree via `visit(AstFoo*)` handlers + `iterateChildren()`
- Top-of-file comment in every `.cpp` explains the algorithm
- Scratch state on nodes: `user1p()`..`user5p()` claimed with `VNUser1InUse/VNUser2InUse/etc.` guard
- Save/restore visitor members across recursion with `VL_RESTORER`

## Critical Downcasts (never mix)

| Macro | Behavior | Use When |
|-------|----------|----------|
| `VN_IS(nodep, Type)` | Returns `bool` | Type check only |
| `VN_CAST(nodep, Type)` | Returns `nullptr` on mismatch | **Preferred** - single conditional cast |
| `VN_AS(nodep, Type)` | Asserts type | Only when impossible to be wrong |

```cpp
// BAD: redundant double check
if (VN_IS(nodep, VarRef)) { AstVarRef* const refp = VN_AS(nodep, VarRef); }

// GOOD: single conditional cast
if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) { ... }
```

## Pass Ordering Matters

```cpp
// V3Width runs BEFORE V3Randomize, so AstConstraintExpr comes from grammar
// V3AssertPre runs BEFORE V3AssertNfa - sensitivity trees not yet attached
// V3Sched runs AFTER most transforms - sees optimized AST
```

## Cross-Node Pointers Require Special Handling

- Pointers outside `op1p`..`op4p` need `broken()` override + `cloneRelink()` support
- Avoid storing out-of-tree node pointers when possible
- Use `VMemberMap`/`findMember()` for name lookups - O(1) vs quadratic scans

## Key Internal References

- `docs/internals.rst` - authoritative reference for AST, pass list, node lifetime
- `V3Graph` / `V3GraphVertex` / `V3GraphEdge` - graph algorithms (dump, color, rank, topo sort)
- `DfgGraph` - data-flow graph optimizer for combinational logic

## When to Create a New Pass

When a change outgrows local rewrites, create a dedicated pass instead of growing an existing one. State explicitly how side effects are preserved in optimizations involving purity, expression lifting, or simplification.