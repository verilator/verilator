---
name: verilator-onboarding
description: Quick-start guide for any AI agent to understand Verilator architecture and contribute effectively in minutes
---

# Verilator Quick-Start for AI Agents

## What is Verilator?

**Verilator is a compiler**, not an interpreter. It translates synthesizable (and much behavioral) SystemVerilog into a cycle-accurate C++ model that you then compile and run. 

> **Key insight**: Almost every decision is made at verilation (compile) time; the generated C++ just advances state each evaluation. **Optimize for verilation-time work over runtime work.**

## 5-Minute Mental Model

```
SystemVerilog Source
        |
        v
+-------------------+
| Preprocess/Parse  |  verilog.l + verilog.y  ->  Raw AST
+-------------------+
        |
        v
+-------------------+
| Link/Elaborate    |  V3LinkParse, V3LinkDot, V3Param  ->  Resolved AST
+-------------------+
        |
        v
+-------------------+
| Width/Type        |  V3Width  ->  Typed AST with bit widths
+-------------------+
        |
        v
+-------------------+
| Transform/Optimize|  V3Const, V3Randomize, V3Assert*,  ->  Optimized AST
| Schedule          |  V3Sched, V3Timing, V3Dfg
+-------------------+
        |
        v
+-------------------+
| Emit              |  V3EmitC*  ->  Generated C++ model
+-------------------+
        |
        v
+-------------------+
| Runtime           |  include/verilated*  ->  Simulation executable
+-------------------+
```

## Where to Make Changes

| Symptom / Feature Area | Start In |
|------------------------|----------|
| Type/width error, "what type is this", implicit conversion | `V3Width` |
| Name/scope/parameter resolution ("Can't find...", hierarchy) | `V3LinkDot`, `V3Param` |
| `randomize` / `constraint` / `rand` / `randc` | `V3Randomize` |
| `assert` / `property` / `sequence` / `cover` | `V3Assert`, `V3AssertPre`, `V3AssertNfa` |
| `fork` / timing / `#delay` / NBA / event scheduling | `V3Sched`, `V3Timing`, `V3Fork` |
| Syntax wrongly accepted or rejected | `verilog.y`, `verilog.l` |
| Wrong generated C++ | `V3EmitC*` |
| Runtime model behavior | `include/verilated*` |

## Build & Test in 3 Commands

```bash
# 1. Build (from repo root)
autoconf && ./configure --enable-ccwarn && make -j8

# 2. Run ONE test
test_regress/t/t_<name>.py

# 3. Full regression (needs --enable-longtests)
make test
```

## Essential Files to Read First

| File | Purpose |
|------|---------|
| `AGENTS.md` (repo root) | This file - orientation + PR checklist |
| `src/AGENTS.md` | Compiler C++ sources: AST, visitors, passes, parser, style |
| `docs/internals.rst` | **Authoritative reference** - AST, pass list, node lifetime |
| `include/AGENTS.md` | Runtime library (C++14, MT-safety, fixed-width types) |
| `test_regress/AGENTS.md` | Regression tests: harness, drivers, golden files |

## The AST in 3 Rules

1. **Everything is an `AstNode`** - subclasses: `AstAdd`, `AstVar`, `AstIf`, etc.
2. **Children in slots `op1p()`..`op4p()`** - use **named accessors** (`lhsp()`, `condp()`, `thensp()`), never raw slots
3. **`astgen` generates boilerplate** - declare with `@astgen op` / `@astgen ptr` in `V3AstNode*.h`

## The Visitor Pattern (Every Pass)

```cpp
// Standard pass = visitor class with private constructor + static apply()
class MyPassVisitor : public VNVisitor {
    VL_RESTORER(m_state);  // Save/restore across recursion
    
    static void apply(AstNetlist* nodep) { MyPassVisitor().iterate(nodep); }
    
    void visit(AstIf* nodep) { ...; iterateChildren(nodep); }
    void visit(AstVar* nodep) { ...; iterateChildren(nodep); }
};
```

## Critical Conventions (Memorize These)

| Convention | Rule |
|------------|------|
| **Const-correctness** | Mark everything `const` possible; pointers: `Type* const ptr` |
| **Downcasts** | `VN_CAST` (preferred) / `VN_AS` (assert) / `VN_IS` (bool) - never mix |
| **Deferred delete** | `VL_DO_DANGLING(pushDeletep(nodep), nodep)` in visitors |
| **dtype comparisons** | **Always** `dtypep()->skipRefp()` - missing breaks typedefs |
| **Name lookups** | `VMemberMap`/`findMember()` - O(1) vs quadratic |
| **Error API** | `v3error` = user error (needs `_bad` test), `v3warn` = suspicious (needs test), `v3error("Unsupported:")` = unimplemented (needs `_unsup` test) |
| **No O(n^2)** | Build maps for batch lookups; any quadratic needs comment justification |
| **Tests** | Every diagnostic needs test + golden; regenerate with `HARNESS_UPDATE_GOLDEN=1` |

## Common Tasks & Where to Start

### "Add support for new SystemVerilog construct"
1. Parser: `verilog.y` (grammar) + `verilog.l` (tokens)
2. AST node: `V3AstNode*.h` with `@astgen` + `V3Ast.cpp` (dump/clone/isSame)
3. Link/width passes: `V3LinkDot`, `V3Width`
4. Transform passes as needed
5. Emit: `V3EmitC*`
6. Test: `t_<category>_<feature>.v` + `.py` + golden

### "Fix type/width error"
- `V3Width.cpp` - check `computeCastableImp()` for composite types

### "Fix name resolution / hierarchy"
- `V3LinkDot.cpp` - uses `VMemberMap` for O(1) lookups

### "Fix assert/property/cover"
- `V3Assert.cpp`, `V3AssertPre.cpp`, `V3AssertNfa.cpp`

### "Fix scheduling / timing / NBA"
- `V3Sched.cpp`, `V3Timing.cpp`, `V3Fork.cpp`

### "Wrong generated C++"
- `V3EmitC*.cpp` - use `VL_*` macros from `verilatedos.h`

### "Runtime crash / behavior"
- `include/verilated*.h/.cpp` - C++14 baseline, fixed-width types

## Test Patterns

```bash
# Run single test
test_regress/t/t_lint_unused_bad.py

# Regenerate golden output
HARNESS_UPDATE_GOLDEN=1 python3 test_regress/t/t_lint_unused_bad.py

# Test uses checkd/checkh macros (not manual $display/$stop)
# Non-power-of-2 widths: 7, 15, 31, 33, 63, 65, 95
# Typedef-wrapped variants for type tests
```

## Before You Submit (Mental Checklist)

- [ ] `make format && make cppcheck && make lint-py` pass
- [ ] Self-reviewed diff: no debug code, stale comments, copy-paste errors, non-ASCII
- [ ] Every `v3error`/`v3warn` has test + golden
- [ ] Issue reproducer committed and **fails without fix**
- [ ] Existing error strings unchanged (or goldens regenerated)
- [ ] `docs/guide/warnings.rst` updated for new/changed warnings
- [ ] No new static/global mutable data
- [ ] All classes `final` or `VL_NOT_FINAL`
- [ ] Const-correctness throughout
- [ ] `VN_CAST` used, not `VN_IS`+`VN_AS`
- [ ] `VL_RESTORER` on all modified visitor members
- [ ] `skipRefp()` on all dtype comparisons
- [ ] `AstForeach` not unrolled loops
- [ ] Test uses `checkd`/`checkh`, non-power-of-2 widths, typedef variants
- [ ] No O(n^2) loops without justification comment
- [ ] PR is single-purpose (refactors, drive-by fixes, new features = separate PRs)

## Pro Tips from Maintainers

> **Maintainer**: "Search open PRs and issues - duplicating in-flight work wastes review time."
> 
> **Maintainer**: "Fix the general root cause, not just the reported case - if it affects other modules, cover them or expect rejection."
> 
> **Maintainer**: "Rather than overriding phaseResultp, add the new condition to the LoopTest below."
> 
> **Maintainer**: "Let's just check inside the test if these values are correct."
> 
> **Maintainer**: "The four new large assertions imply 1'b1 - they elaborate but can never fail; an off-by-one would be invisible."
> 
> **Maintainer**: "sameNode should be overridden to compare m_propertyControl."

## One-Page Reference: Key Files

| Area | Key Files |
|------|-----------|
| Main flow | `Verilator.cpp::process()` |
| AST nodes | `V3AstNodeExpr.h`, `V3AstNodeOther.h`, `V3AstNodeDType.h`, `V3AstNodeStmt.h` |
| astgen | `astgen/` - run after editing `@astgen` in headers |
| Visitor base | `VNVisitor.h` |
| Graph algorithms | `V3Graph.h`, `V3GraphVertex.h`, `V3GraphEdge.h`, `V3GraphAlg.cpp` |
| Error system | `V3Error.h`, `V3Error.cpp` |
| Options | `V3Options.cpp` - `DECL_OPTION()` |
| Stats | `V3Stats.cpp` - deterministic regression anchors |
| Parser | `verilog.y`, `verilog.l` |
| Runtime | `include/verilated.h`, `verilated_types.h`, `verilatedos.h` |

---

**You're ready.** Start with the task, map to the pass, read that pass's top-of-file comment, and make the minimal correct change.