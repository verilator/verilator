---
name: verilator-master
description: Master index for Verilator development skills - unified entry point for any AI agent
---

# Verilator Development Skills - Master Index

## Skill Catalog

| Skill | Purpose | When to Use |
|-------|---------|-------------|
| `verilator-skill-router` | **ALWAYS FIRST** - routes task to right skills | Every task starts here |
| `verilator-onboarding` | 5-minute mental model + quick start | **First read** - any new agent |
| `verilator-architecture` | Pipeline stages, AST, visitors, passes | Understanding code flow, mapping symptoms to passes |
| `verilator-coding-conventions` | C++ style, AST rules, visitors, errors, performance | Writing/modifying compiler code |
| `verilator-testing` | Test structure, drivers, goldens, naming | Adding/running tests |
| `verilator-pr-review` | Maintainer feedback patterns, pre-PR checklist | **Before submitting any PR** |
| `verilator-performance` | Memory, O(n^2) elimination, compile vs runtime | Optimizing passes, fixing perf bugs |
| `verilator-runtime` | include/ library: C++14, fixed-width, threads | Runtime fixes, VPI, coverage, tracing |
| `verilator-examples` | Worked examples: new pass, AST node, bug fix, warning | **Copy-paste starting points** |
| `verilator-performance-guard` | 10 mandatory performance gates (before commit) | **Before every commit** |
| `verilator-debugging` | Debug AST dumps, --dumpi-*, JSON, graphviz, minimal tests | Debugging crashes, wrong behavior |
| `verilator-parser` | Lexer/grammar: tokens, precedence, //UNSUP, error recovery | Syntax bugs, adding keywords |
| `verilator-release` | Release process: ccwarn, longtests, version, tagging | Maintainer release prep |
| `verilator-vpi` | VPI callbacks, verilated_vpi.cpp, --vpi vs --vpi-lazy | VPI/PLI integration |
| `verilator-code-map` | Symptom->function/class map for efficient edit navigation | Find exact function to edit |

---

## Recommended Reading Order

### For New Agents (Start Here)
1. `verilator-onboarding` - 5-minute mental model
2. `verilator-architecture` - pipeline + AST + visitors
3. `verilator-coding-conventions` - style rules to follow

### For Specific Tasks

| Task | Read These |
|------|------------|
| Add new SystemVerilog feature | `onboarding` -> `architecture` -> `coding-conventions` -> `examples` (Ex 1, 2) |
| Fix type/width bug | `architecture` (V3Width) -> `coding-conventions` (dtype rules) -> `examples` (Ex 6) |
| Fix assert/property bug | `architecture` (V3Assert*) -> `coding-conventions` -> `examples` |
| Fix scheduling/NBA bug | `architecture` (V3Sched) -> `performance` (scheduler) -> `examples` |
| Add new warning | `coding-conventions` (diagnostics) -> `examples` (Ex 4) -> `testing` |
| Optimize slow pass | `performance` (O(n^2) patterns) -> `examples` (Ex 5) |
| Fix runtime crash | `runtime` -> `testing` |
| Fix VPI/coverage/trace | `runtime` -> `testing` |
| Debug wrong behavior | `debugging` -> `architecture` (dump AST) |
| Fix parser/syntax | `parser` -> `architecture` |
| Prepare PR for submission | `pr-review` (full checklist) |

---

## Quick Decision Map

```
SYMPTOM -> WHERE TO LOOK
-------------------------------------------------------------
Type error / width mismatch          -> V3Width.cpp
"Can't find module/signal/param"     -> V3LinkDot.cpp, V3Param.cpp
randomize / constraint failure       -> V3Randomize.cpp
assert/property/cover error          -> V3Assert.cpp, V3AssertPre.cpp, V3AssertNfa.cpp
fork/delay/NBA scheduling issue      -> V3Sched.cpp, V3Timing.cpp, V3Fork.cpp
Syntax accepted/rejected incorrectly -> verilog.y, verilog.l
Wrong generated C++                  -> V3EmitC*.cpp
Runtime crash / wrong simulation     -> include/verilated*.h/.cpp
Memory leak / OOM                    -> performance (deferred delete, static data)
Slow verilation                      -> performance (O(n^2) patterns, V3Stats)
Debug wrong behavior                 -> debugging (--dumpi-*, JSON AST)
Syntax/parser error                  -> parser (verilog.y, verilog.l)
```

---

## Golden Rules (Memorize)

1. **Verilator is a compiler** - optimize verilation time, not runtime
2. **Minimal correct change** - no drive-by refactors, no clever abstractions
3. **Every diagnostic needs a test + golden** - `HARNESS_UPDATE_GOLDEN=1`
4. **Const-correctness everywhere** - `Type* const ptr`, `const` methods
5. **VN_CAST not VN_IS+VN_AS** - single conditional cast
6. **Always skipRefp() on dtype** - missing = typedef bugs
7. **No O(n^2)** - build maps, use VMemberMap
8. **No static/global mutable data** - breaks future parallelism
9. **AstForeach not unrolled loops** - constant code size
10. **Single-purpose PRs** - refactors, fixes, features = separate PRs

---

## Maintainer Feedback Cheat Sheet

### Most Common Rejections (Avoid These)

| # | Rejection | Prevention |
|---|-----------|------------|
| 1 | Missing test for new diagnostic | Add test + golden in same commit |
| 2 | O(n^2) algorithm | Build map for batch lookup |
| 3 | Changed existing error string | Keep wording; regen goldens if must change |
| 4 | Not const-correct | Mark everything `const` possible |
| 5 | VN_IS + VN_AS instead of VN_CAST | Use single conditional cast |
| 6 | Missing skipRefp() on dtype | Always `dtypep()->skipRefp()` |
| 7 | Dead code / unused functions | Remove or use |
| 8 | PR not single-purpose | Split into multiple PRs |
| 9 | Hand-edited .out files | `HARNESS_UPDATE_GOLDEN=1` only |
| 10 | "Unsupported:" for user error | Only for unimplemented features |

### Maintainer Keywords to Watch For

- **Maintainer A**: "O(n^2)", "const", "skipRefp", "VN_CAST", "single-purpose", "warn-coverage"
- **Maintainer B**: "AstNode::exists", "VL_RESTORER", "thread safety", "vtable overhead"
- **Maintainer C**: "check inside test", "while(true)", "one-line names", "separate PR"
- **Maintainer D**: "anchor expected constant", "off-by-one invisible", "implicit 1'b1"
- **Maintainer E**: "sameNode override", "leak", "dead branch", "duplicate logic"

---

## Build & Test Commands

```bash
# Full build with strict warnings
autoconf && ./configure --enable-ccwarn && make -j8

# Single test
test_regress/t/t_<name>.py

# Regenerate golden output
HARNESS_UPDATE_GOLDEN=1 python3 test_regress/t/t_<name>.py

# Full regression (needs --enable-longtests)
make test

# Format & lint
make format && make cppcheck && make lint-py
```

---

## File Layout Reference

```
verilator/
+-- AGENTS.md                    # Root guidance (read first)
+-- src/                         # Compiler (C++17)
|   +-- AGENTS.md               # Compiler conventions
|   +-- verilog.y / verilog.l   # Parser/lexer
|   +-- V3*.cpp / V3*.h         # Passes (alphabetical by stage)
|   +-- Verilator.cpp           # Main flow (process())
|   +-- astgen/                 # AST code generator
+-- include/                     # Runtime (C++14)
|   +-- AGENTS.md               # Runtime conventions
|   +-- verilated*.h/.cpp       # Public API
|   +-- verilatedos.h           # VL_* macros (fixed-width)
+-- test_regress/
|   +-- AGENTS.md               # Test conventions
|   +-- t/                      # 4000+ tests
|   |   +-- t_*.v               # SystemVerilog sources
|   |   +-- t_*.py              # Python drivers
|   |   +-- t_*.out             # Golden outputs (auto-gen)
|   +-- t/vltest_bootstrap.py     # Harness
+-- docs/
|   +-- internals.rst           # AUTHORITATIVE architecture ref
|   +-- guide/warnings.rst      # Warning documentation
|   +-- AGENTS.md               # Doc conventions
++-- agents/skills/verilator/   # These skills
```

---

## Emergency Debugging

```bash
# Dump AST after pass
verilator --dumpi-tree 9 --dumpi-V3Width 9 test.v

# JSON AST dump
verilator --dumpi-tree-json 9 --no-json-ids test.v

# Debug emit Verilog
verilator --debug-emitv --dumpi-V3EmitV 9 test.v

# Stats output
verilator --stats-vars test.v
```

---

## For AI Agents: How to Use These Skills

1. **Read `verilator-onboarding` first** - builds mental model in 5 minutes
2. **Use the decision map** - maps symptom to file instantly
3. **Copy from `verilator-examples`** - worked patterns for common tasks
4. **Run `verilator-pr-review` checklist** - catches 90% of maintainer rejections
5. **Follow `verilator-coding-conventions`** - style that passes `make format/cppcheck/lint-py`

These skills are **agent-agnostic** - they work for Claude, Codex, Cursor, or any coding assistant. The patterns are derived from 40+ real PR reviews by Verilator maintainers (Verilator maintainers).