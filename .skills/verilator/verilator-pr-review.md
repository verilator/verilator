---
name: verilator-pr-review
description: Anticipate and avoid maintainer review feedback - patterns from 40+ PR reviews
---

# Verilator PR Review Avoidance Skill

## Maintainer Feedback Patterns (from 40+ PRs reviewed)

### 1. Diagnostic & Error Message Discipline
```cpp
// Maintainer: "End messages with periods, never exclamation marks"
// Maintainer: "Don't write 'Error:' in the text - the macro prints the prefix"
// Maintainer: "State what was attempted and what was found"
// Maintainer: "Use nodep->prettyNameQ() for user-facing names; name() only in debug"
// Maintainer: "Enclose values in single quotes: 'value'"
// Maintainer: "Cite IEEE clause when enforcing spec: IEEE 1800-2023 11.4.7"
// Maintainer: "Update docs/guide/warnings.rst when adding/changing warnings"
// Maintainer: "Keep existing error strings - .out goldens and docs depend on wording"
// Maintainer: "On error paths, clean up invalid AST (AstConst::BitFalse) so later passes don't crash"
// Maintainer: "Error should be v3error not v3fatalSrc for user-triggerable cases"
```

### 2. Test Requirements
```cpp
// Maintainer: "Every v3error/v3warn needs a test - enforced by warn-coverage distribution test"
// Maintainer: "Include the issue's own reproducer as a committed test"
// Maintainer: "VERIFY it fails without the fix"
// Maintainer: "Need repeat loop, check randomize results too"
// Maintainer: "Use checkd/checkh macros, not manual $display/$stop"
// Maintainer: "Test both [high:low] and [low:high] + non-zero bounds [3:1]"
// Maintainer: "Test non-power-of-2 widths: 7, 15, 31, 33, 63, 65, 95"
// Maintainer: "Add _protect_ids variant when feature emits user identifiers"
// Maintainer: "When feature lands, remove now-supported entries from t_*_unsup.v in SAME change"
// Maintainer: "Let's just check inside the test if these values are correct"
// Maintainer: "Do we have it covered by the tests?"
```

### 3. Code Quality & Style
```cpp
// Maintainer: "Please avoid you/we elsewhere - don't assume the reader"
// Maintainer: "Comment all member vars"
// Maintainer: "Shorten comment so fits, or put comment on line above"
// Maintainer: "Use } else { when using else"
// Maintainer: "Mark every variable, parameter, pointer, member function const where possible"
// Maintainer: "Every class/struct: final or VL_NOT_FINAL"
// Maintainer: "No non-ASCII characters - write -- not em-dash, plain ' not smart quote"
// Maintainer: "Lists stay sorted: tokens, options, enums, configure features"
// Maintainer: "Keep functions under 100-150 lines; thread state through context struct"
// Maintainer: "Move implementation to .cpp; convert large lambdas to named member functions"
// Maintainer: "No using namespace; prefix with VL/Vl"
// Maintainer: "Start every new .cpp with top-of-file algorithm comment"
// Maintainer: "Remove ifdef TRACE_VCD, update other format golden files"
// Maintainer: "Revert unrelated whitespace change"
// Maintainer: "Please use 2 space indents"
```

### 4. Performance & Algorithmic Correctness
```cpp
// Maintainer: "O(n^2) NEVER acceptable - build maps for batch lookups"
// Maintainer: "Any quadratic loop needs explicit justification in comment"
// Maintainer: "But this appears called in a loop across all bins, so isn't it O(n^2)?"
// Maintainer: "Should memoize these so can reuse identical dtypes"
// Maintainer: "Prefer std::map for per-module; unordered_map only for one-per-netlist"
// Maintainer: "NEVER let unordered_* iteration order reach generated output"
// Maintainer: "Prefer emplace over insert; check .second instead of separate find()"
// Maintainer: "reserve() strings/vectors when size estimable"
// Maintainer: "Add no new static/global mutable data - statics being eliminated for parallelism"
// Maintainer: "The four new large assertions imply 1'b1 - they elaborate but can never fail"
// Maintainer: "An off by one in ring exit timing would be invisible here"
// Maintainer: "Rather than iterating everything twice, make part of earlier visit"
// Maintainer: "Use AstNode::exists instead of manual iteration"
```

### 5. AST & Visitor Correctness
```cpp
// Maintainer: "Use VN_CAST not VN_IS + VN_AS - single conditional cast"
// Maintainer: "Use UASSERT_OBJ(cond, nodep, ...) over UASSERT when node in scope"
// Maintainer: "Use VL_DO_DANGLING(pushDeletep(nodep), nodep) instead of deleteTree()"
// Maintainer: "deleteTree() ONLY for fresh nodes that never entered the tree"
// Maintainer: "Always skipRefp() when comparing/resolving dtypes - missing breaks typedefs"
// Maintainer: "Use VMemberMap/findMember() for name lookups - O(1) vs quadratic"
// Maintainer: "Build logic as AST nodes, NEVER raw C text in AstCStmt"
// Maintainer: "Every new AST member needs dump() AND dumpJson() - never LCOV_EXCL"
// Maintainer: "Override isSame() to include new semantically meaningful fields"
// Maintainer: "Pointers outside op1p-op4p need broken() override + cloneRelink()"
// Maintainer: "Prefer new visit() in existing visitor over nodep->foreach(...)"
// Maintainer: "Prefer AstForeach over unrolled loops - constant code size"
// Maintainer: "Identify compiler-generated constructs by attribute flag, NOT name-pattern"
// Maintainer: "Use V3Number arithmetic for AstConst > 32 bits - 1 << i overflows at i>=32"
// Maintainer: "Use FileLine::operatorCompare for source-position ordering"
// Maintainer: "Can curDTypep be nullptr? If so, don't set didWidth=true"
// Maintainer: "Typedefs should always have non-null subDTypep()"
// Maintainer: "VarRefs always have non-null varp() - remove pointless checks"
// Maintainer: "Use UASSERT_OBJ for impossible cases, not defensive if-checks"
// Maintainer: "Use checkd/checkh macros for all value comparisons"
// Maintainer: "sameNode should be overridden to compare m_propertyControl"
// Maintainer: "This now leaks: cover sequence without proper cleanup"
```

### 6. Thread Safety & Runtime
```cpp
// Maintainer: "Annotate hierarchy: VL_PURE > VL_MT_SAFE > VL_MT_STABLE - annotations must match implementation"
// Maintainer: "Never include verilated.h in compiler - use verilatedos.h"
// Maintainer: "Mutex-protected members: VL_GUARDED_BY + document acquisition ordering"
// Maintainer: "++ on shared state and container empty() are NOT thread-safe"
// Maintainer: "No exceptions in runtime code - string parsing at verilation time only"
// Maintainer: "Use fixed-width model types: CData/SData/IData/QData/VlWide - NOT size_t"
// Maintainer: "Process wide data word-by-word: VL_ZERO_W, VL_MEMCPY_W - NEVER bit-by-bit"
// Maintainer: "Can we just use existing AstNodeExpr::isLValue() in emit to pick .atWrite vs .at?"
```

### 7. Option & Flag Management
```cpp
// Maintainer: "We keep old options forever - keep V3Option parsing to ignore it"
// Maintainer: "Test deprecated options in t_flag_deprecated_bad.py"
// Maintainer: "If we don't have limit for large bit-vectors, we should - reuse this flag"
// Maintainer: "Chain .notForRerun() on DECL_OPTION() for options not affecting semantic output"
// Maintainer: "Undocumented options: .undocumented() + t_opt_*_bad test"
```

### 8. PR Structure & Process
```cpp
// Maintainer: "PR is single-purpose - refactors, drive-by fixes, new features each in separate PRs"
// Maintainer: "Land standalone cleanups first"
// Maintainer: "Please put in separate PR, can be before/after this one"
// Maintainer: "This also seems unrelated, please make separate PR"
// Maintainer: "Fix the general root cause, not just the reported case"
// Maintainer: "If it also affects other modules/classes/interfaces, cover them or expect rejection"
// Maintainer: "Search open PRs and issues - duplicating in-flight work wastes review time"
// Maintainer: "Please click Resolve on these - don't message 'done'"
// Maintainer: "Let's try to avoid while(true) - put stop condition directly"
// Maintainer: "Please avoid one-line variable names"
```

### 8b. Additional Historical Patterns (from 100+ PRs across 2018-2026)
```cpp
// Maintainer: "Don't use the word 'accept' unless related to visitor accept() function"
// Maintainer: "Inline new expressions used only once - easier to read at call site"
// Maintainer: "Replace bare deletes with VL_DO_DANGLING(pushDeletep) for linked nodes"
// Maintainer: "deleteTree() OK for orphan subtrees never linked into AST"
// Maintainer: "Rename variables that don't match type (e.g., 'Node' for non-AstNode)"
// Maintainer: "Add bounds checks for exponential growth (2^N) with comments"
// Maintainer: "What is common about these? Add isSomething() predicate to Ast node class"
// Maintainer: "Constructor should do the work - check other constructors"
// Maintainer: "Emit means dump to disk - don't use 'emit' for internal functions"
// Maintainer: "Add hint comments for casual readers on complex config options"
// Maintainer: "Keep 'one other' comments across tests for stability tracking"
// Maintainer: "Test deprecated options in t_flag_deprecated_bad.py"
// Maintainer: "Chain .notForRerun() on DECL_OPTION() for semantic-neutral options"
// Maintainer: "This won't scale if we need multiple - use separate CXXFLAGS/LDFLAGS"
// Maintainer: "According to man page - verify system call behavior before adding error handling"
// Maintainer: "Use TREEOP vs TREEOPC appropriately - prefer TREEOP for readability"
```

### 9. Specific Anti-Patterns Flagged by Maintainers
```cpp
// --- Dead else branches - collapse to single return
// --- Unused functions/fields - remove entirely
// --- Duplicated logic - extract to common function (e.g., isNonPackedArray)
// --- Magic numbers - replace with static constexpr
// --- Column-aligned declarations in tests - flush-left only
// --- Hand-written .out golden files - always regenerate with HARNESS_UPDATE_GOLDEN=1
// --- "Unsupported:" for user mistakes - ONLY for not-yet-implemented features
// --- v3fatalSrc for user-triggerable paths - use v3error
// --- Warning suppression on AstVarRef - use AstVar (VarRefs recreated)
// --- unordered_* iteration order in generated output - use std::map or sort
// --- Static/global mutable data - eliminates future parallelism
// --- Stack-allocated AstNode - always pointers
// --- C-style casts - static_cast or VN_CAST/VN_AS only
// --- Raw string concatenation for hierarchical paths - use AstDot/parse-ref chains
// --- Limiting grammar rules to solve ambiguities - use tokenPipeScan* look-ahead
// --- Untested grammar alternatives - every | and optional clause needs test
// --- One-line variable names - use descriptive names
// --- While(true) with complex condition - use do-while with explicit condition
// --- Comment explaining "before fix" behavior - test comments explain what test ASSERTs
// --- Large test files duplicating existing tests - extend existing tests instead
// --- VL_UNLIKELY on zero checks - let compiler decide branch prediction
```

### 10. Positive Patterns Maintainers Approve
```cpp
// -- VN_CAST single conditional cast
// -- VL_RESTORER on every modified visitor member
// -- VNUser1InUse/VNUser2InUse/etc. guard for userNp() fields
// -- iterateAndNextNull() over iterate()
// -- VNVisitorConst for read-only visitors
// -- AstForeach over unrolled loops
// -- VMemberMap/findMember() for O(1) lookups
// -- skipRefp() on all dtype comparisons
// -- checkd/checkh/checks macros in tests
// -- Non-power-of-2 widths in tests
// -- Typedef-wrapped variants in type tests
// -- Runtime-varying inputs (CRC/LFSR) to defeat constant folding
// -- Multiple clock cycle assertions post-NBA
// -- Regenerate goldens with HARNESS_UPDATE_GOLDEN=1
// -- IEEE clause citations in spec-restriction errors
// -- warnMore() suggestions with warnings
// -- renamedTo() for warning code changes
// -- Memoization of repeated computations
// -- reserve()/emplace for containers
// -- Top-of-file algorithm comments in .cpp
// -- Const-correctness everywhere
// -- final or VL_NOT_FINAL on all classes
// -- Named accessors (lhsp, condp) over op1p/op2p
// -- Attribute flags for compiler-generated constructs
// -- dump() + dumpJson() + isSame() for new AST members
```

## Pre-PR Checklist (Run Before Every Submit)

```bash
# 1. Format & lint
make format && make cppcheck && make lint-py

# 2. Self-review diff for:
#    - Leftover debug code
#    - Stale comments
#    - Copy-paste errors
#    - Non-ASCII characters
#    - Unsorted lists

# 3. Run relevant tests (at minimum):
#    - make test (full regression on at least one OS)
#    - t_dist_* distribution tests (headers, sorted lists, warnings, ASCII)

# 4. Verify:
#    [ ] Every v3error/v3warn has test + golden
#    [ ] Issue reproducer committed and FAILS without fix
#    [ ] Error strings unchanged (or intentionally updated with golden regen)
#    [ ] docs/guide/warnings.rst updated for new/changed warnings
#    [ ] No new static/global mutable data
#    [ ] All classes final or VL_NOT_FINAL
#    [ ] Const-correctness throughout
#    [ ] VN_CAST used, not VN_IS+VN_AS
#    [ ] VL_RESTORER on all modified visitor members
#    [ ] skipRefp() on dtype comparisons
#    [ ] AstForeach not unrolled loops
#    [ ] Test uses checkd/checkh, non-power-of-2 widths, typedef variants
#    [ ] No O(n^2) loops without justification comment
#    [ ] PR is single-purpose
```

## Quick Reference: Most Common Rejection Reasons

| Rank | Reason | Prevention |
|------|--------|------------|
| 1 | Missing test for new diagnostic | Add test + golden in same commit |
| 2 | O(n^2) algorithm | Build map for batch lookup |
| 3 | Changed existing error string | Keep wording; if must change, regen all goldens |
| 4 | Not const-correct | Mark everything const possible |
| 5 | VN_IS + VN_AS instead of VN_CAST | Single conditional cast |
| 6 | Missing skipRefp() on dtype | Always use dtypep->skipRefp() |
| 7 | Dead code / unused functions | Remove or use |
| 8 | PR not single-purpose | Split into multiple PRs |
| 9 | Hand-edited .out files | HARNESS_UPDATE_GOLDEN=1 only |
| 10 | "Unsupported:" for user error | Use only for unimplemented features |