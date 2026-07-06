<!-- DESCRIPTION: Verilator: src/ guidelines for AI coding agents
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# src/ -- Verilator compiler sources

Covers all C++ under `src/`, including astgen inputs and the parser/lexer
(`verilog.y`, `verilog.l`). Read the repository-root [AGENTS.md](../AGENTS.md)
first. This file has two parts: **Orientation** explains the AST and pass model;
**Before you open a PR** is the style and correctness checklist.

______________________________________________________________________

# Orientation: the AST and the visitor model

- **Everything is an `AstNode`.** Each construct is an `Ast*` subclass (`AstAdd`,
  `AstVar`, `AstIf`). The design under analysis is one tree, with statement lists
  threaded by sibling `nextp()` links.
- **Children sit in numbered slots `op1p()`..`op4p()`, accessed by name.** Use the
  named accessors (`lhsp()`, `condp()`, `thensp()`), not the raw slots -- the
  numbering is an implementation detail.
- **`astgen` generates node boilerplate.** Declare children and cross-node
  pointers with `@astgen op` / `@astgen ptr` annotations in the `V3AstNode*.h`
  headers; it emits accessors, clone, and broken-check code. Do not hand-write
  what astgen can generate.
- **A pass is a visitor.** Convention: a class with a private constructor and a
  static `apply()` entry point, named after its file (`TimingSuspendableVisitor`
  in `V3Timing.cpp`). It walks the tree through `visit(AstFoo*)` handlers and
  `iterateChildren()`. To understand a pass, read its top-of-file comment first --
  every `.cpp` opens with one describing the algorithm.
- **Scratch state lives on nodes.** Passes stash data in `user1p()`..`user5p()`
  (and `user1()`..`user5()`), claimed for the pass lifetime with a `VNUser*InUse`
  guard. Save and restore visitor members across recursion with `VL_RESTORER`.
- **Three downcasts, three null behaviors:** `VN_IS` returns bool, `VN_CAST`
  returns nullptr on mismatch, `VN_AS` asserts the type. `V3Broken` re-validates
  tree invariants between passes, so trust resolved pointers (`dtypep()`,
  `varp()`) instead of adding defensive null checks for impossible cases.
- `docs/internals.rst` is the authoritative reference for the AST, the pass list,
  and node lifetime.

______________________________________________________________________

# Before you open a PR

## Code style

- Mark every variable, parameter, pointer, and member function `const` where possible.
- Pointer variables take a `p` suffix and pointer locals are doubly const where
  possible: `AstVar* const varp`; non-pointers never use the `p` suffix.
- Do not use `auto` except for iterators or genuinely unwieldy types.
- Use pre-increment (`++i`) unless you specifically need post-increment's old value.
- Brace-initialize node and struct construction: `new AstIf{fl, condp, thenp, elsep}`.
- Never use C-style casts; instead use `static_cast<T>` for non-AST types and
  `VN_AS`/`VN_CAST` for AST downcasts.
- `static constexpr` for compile-time constants, not `#define` or file-scope const.
- Mark every `class`/`struct` `final` or `VL_NOT_FINAL` -- a distribution test
  scans all definitions.
- Keep functions under roughly 100-150 lines; thread shared state through a
  context struct rather than long parameter lists.
- Keep headers lean: move implementation to `.cpp`; convert large lambdas into
  named member functions -- lambdas are opaque in stack traces and block reuse.
- Start every new `.cpp` with a top-of-file comment explaining the algorithm.
- Comments are capitalized sentences written for an unknown future reader, without
  "I"/"we"/"our"; remove commented-out code -- version control preserves history.
- No `using namespace`; prefix non-namespaced symbols with `VL`/`Vl`.
- Prefer semantic predicates over enum comparisons: `varp->isClassMember()`, not
  `varp->varType() == VVarType::MEMBER`.
- `new*` functions return a `new` object; `make*` functions do something more
  complex -- pick the prefix accordingly.
- Name compiler-created temporaries with a `__V` prefix plus a context suffix
  (`__VInside`, `__VCase`); runtime utility functions use a `vl_` prefix.
- Use `VL_*` bit/word macros from `verilatedos.h` (`VL_WORDS_I`, `VL_MASK_I`); do
  not include `<cstdint>` directly.
- Replace magic numbers with named `static constexpr` constants.

## AST construction and manipulation

- Build logic as AST nodes, never as raw C text in `AstCStmt` -- later passes
  (V3Name, `--protect`) rename AST identifiers but cannot see into raw strings.

- Know the cast forms (above) and never pair `VN_IS` with `VN_AS` on the same
  node -- use a single `VN_CAST`:

  ```cpp
  // BAD: redundant double check
  if (VN_IS(nodep, VarRef)) { AstVarRef* const refp = VN_AS(nodep, VarRef); }
  // GOOD: single conditional cast
  if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) { ... }
  ```

- Use `UASSERT_OBJ(cond, nodep, "...")` over `UASSERT` when a node is in scope;
  use `v3fatalSrc("...")` for unreachable paths, never a silent `if (!ptr) return;`.

- Use `VL_DO_DANGLING(pushDeletep(nodep), nodep)` instead of `deleteTree()` in
  visitors -- deferred deletion is safe against re-entry and unlinking order.
  `deleteTree()` is only for fresh nodes that never entered the tree.

- Every new AST member needs both `dump()` and `dumpJson()` support -- never wrap
  these in `LCOV_EXCL`; cover them by adding a construct to `t_debug_emitv.v`.
  Override `isSame()` to include any new semantically meaningful field.

- Pointers to nodes outside op1p-op4p require a `broken()` override and
  `cloneRelink()` support -- avoid storing out-of-tree node pointers when possible.

- Never allocate AstNode objects on the stack or by value -- always pointers.

- Prefer a new `visit()` in an existing visitor over `nodep->foreach(...)` --
  better for runtime, and handles diverse node types better. Prefer named
  accessors over `op1p()`..`op4p()`, and verify traversal order is preserved
  when converting manual iteration.

- Prefer `AstForeach` over generating unrolled loop bodies -- constant-size code
  instead of O(N); wrap the body in `AstBegin` for scope isolation.

- Always `skipRefp()` when comparing or resolving dtypes -- missing it breaks
  typedef support; prove the paths with typedef tests.

- Use `num().isOpaque()` rather than `isDouble() || isString()` when guarding
  V3Number comparisons against non-integer types.

- Use `FileLine::operatorCompare` for source-position ordering -- never hand-roll
  filename/lineno comparisons.

- Identify compiler-generated constructs by an attribute flag on the node (with
  dump support), never by name-pattern matching -- magic names break with escaped
  identifiers.

- Use `V3Number` arithmetic for `AstConst` values wider than 32 bits -- `1 << i`
  silently overflows at `i >= 32`.

- Use `VMemberMap`/`findMember()` for name lookups in structs, classes, modules,
  and packages -- O(1) versus quadratic linear scans.

- Never emit raw source filenames or identifiers in generated code -- pass them
  through `protect()`/`putsQuoted` so `--protect` does not leak source.

## Visitors and passes

- `VL_RESTORER` on every visitor member a `visit()` modifies before iterating
  children -- even when nesting "cannot happen" today.
- Every pass using `userNp()` needs a `VNUserNInUse` guard, and the header
  documents which user fields it uses.
- Use `iterateAndNextNull()` rather than `iterate()` -- the null-safe form
  prevents copy-paste errors during refactors.
- Derive read-only visitors from `VNVisitorConst` with `iterateChildrenConst`.
- Reset per-module visitor state in `visit(AstNodeModule*)`, including numeric ID
  counters, to keep generated names stable.
- Capture first-occurrence module state inside the node's own `visit()` handler,
  not via a `foreach` pre-scan from `visit(AstNodeModule)` -- source order already
  matches IEEE declaration-before-use.
- Avoid `backp()` -- it returns parent or prior sibling depending on position and
  causes O(n^2) hunts; build maps or capture context during forward traversal.
- When raw node pointers key a map or set, erase entries when the node is deleted
  -- allocators reuse addresses, so stale entries alias new nodes.
- Derive graph-shaped passes from V3Graph (`V3GraphVertex`/`V3GraphEdge`) -- it
  gives dump, color, rank, topological sort, and reachability for free.
- When a change outgrows local rewrites, create a dedicated pass instead of
  growing an existing one.
- State explicitly how side effects are preserved in optimizations involving
  purity, expression lifting, or simplification.

## Errors and warnings

(See the root checklist for choosing the diagnostic API and its required test.)

- Append `nodep->prettyNameQ()` for user-facing names; use `name()` only in
  debug/UINFO output. Enclose specific values in single quotes: `'value'`.
- End messages with periods, never exclamation marks; do not write "Error:" in the
  text -- the macro prints the prefix.
- State what was attempted and what was found: "Instance attempts to connect to
  'PARAM' as a parameter, but it is a variable". Add a `warnMore()` suggestion
  where possible.
- Name warning codes object-first and short (`ASCRANGE`, not `RANGEASC`); rename
  via `renamedTo()` so old suppressions keep working.
- Set warning suppression on `AstVar`, not `AstVarRef` -- VarRefs get recreated
  and lose `warnIsOff`.
- "Unsupported:" messages describe the specific unsupported context, not just the
  construct name -- each message must be distinct.
- When replacing or refactoring a pass, keep existing user-facing error strings --
  `.out` goldens and documentation depend on the wording.

## Performance and memory

- O(n^2) is never acceptable -- build maps for batch lookups; any quadratic loop
  needs explicit justification in a comment.
- Prefer `std::map` for per-module structures (many small instances); use
  `unordered_map` only for one-per-netlist data, and never let `unordered_*`
  iteration order reach generated output.
- Prefer `emplace` over `insert` and check the returned `.second` instead of a
  separate `find()`. `reserve()` strings and vectors when the size is estimable.
- Add no new static or global mutable data -- statics are being eliminated for
  future parallelism.
- Use Verilator's fixed-width data types for model data (`CData`/`SData`/`IData`/
  `QData`/`VlWide`), not `size_t`. Process wide data word-by-word
  (`VL_ZERO_W`, `VL_MEMCPY_W`), never bit-by-bit.
- No exceptions in verilated runtime code; do string parsing at verilation time,
  never during simulation.
- Wrap unlikely hot-path branches in `VL_UNLIKELY`/`VL_LIKELY`.
- Count what every new pass does via V3Stats -- stats become deterministic
  regression anchors.

## Thread safety

- Annotate with the hierarchy `VL_PURE` > `VL_MT_SAFE` > `VL_MT_STABLE`: PURE has
  no side effects and calls only PURE; MT_SAFE is safe under locks; MT_STABLE is
  safe only while tree topology is stable. Annotations must match the
  implementation.
- Never include `verilated.h` in the compiler itself -- use `verilatedos.h`.
- Annotate mutex-protected members with `VL_GUARDED_BY` and document acquisition
  ordering. `++` on shared state and container `empty()` are not thread-safe.

## Parser and lexer (verilog.y, verilog.l)

- Preserve IEEE Appendix A BNF comments (`// IEEE: {rule}`); comment explicitly
  when accepting syntax beyond IEEE as an extension.
- The parser only builds AST nodes -- defer semantic validation, `VN_IS` checks,
  and context-dependent logic to V3LinkParse/V3Width and later passes.
- Represent hierarchical paths as structured nodes (`AstDot`/parse-ref chains via
  `idDotted`), never concatenated strings -- preserves per-segment FileLine.
- Prefer tightening a grammar rule's operand type over a runtime cast-chain guard
  in a later visitor -- illegal operands then fail with a clean syntax error.
- Solve ambiguities with token-pipeline look-ahead (`tokenPipeScan*`) rather than
  limiting grammar rules; mark unsupported rules with `//UNSUP`.
- Sort token declarations alphabetically by string literal; sort `yD_*`
  productions by token name.
- Add a test for every `|` alternative and optional clause of a new or changed
  grammar rule -- untested alternatives are where parse regressions hide.

## File-specific rules

| File | Rule |
|---|---|
| `src/V3Options.cpp` | Chain `.notForRerun()` onto `DECL_OPTION()` for options that do not affect semantic output |
| `src/V3Ast.cpp` | For composite types (queues, dynamic arrays) use `computeCastableImp()` on subtypes -- shallow `width()`/`similarDType()` checks miss nested incompatibility |
| `src/V3AstNode*.h` | Every node class gets a what-construct comment and every member a semantic-purpose comment; put enum type definitions in `V3AstAttr.h` |
| `src/V3AstNodeExpr.h` | `CCast` is only for basic C types (char/short/int/QData) -- never 4-state logic or structs |
| `src/V3AstNodeOther.h` | `cloneRelink` must propagate all stateful flags (e.g. `maybePointedTo`) and update internal references |
| `src/V3Const.cpp` | Check `keepIfEmpty` before removing empty functions -- flagged functions must survive for codegen/side effects |
| `src/V3Coverage.cpp` | Instrumentation contexts are opt-in (allowlist), never blocklist -- blocklists silently break when new contexts appear |
| `src/V3Inline.cpp` | Preserve `VarXRef::varp()` during passes -- pin-reconnection needs it before V3LinkDot re-resolves |
| `src/V3Sched*.cpp` | Every change needs a test proving necessity; isolate unrelated scheduler changes into separate PRs -- high-risk area |
