<!-- DESCRIPTION: Verilator: test_regress/ guidelines for AI coding agents
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# test_regress/ Guidelines -- regression tests

When to check: before adding or editing any test under `test_regress/` (`.v` sources, `.py` drivers, `.out` golden files).
Read the repository-root [AGENTS.md](../AGENTS.md) first for process and cross-cutting rules.

## Naming

- Name tests `t_{category}_{description}` in snake_case; the first word groups the category (`t_lint_unused_func_bad`, not `t_unused_func_lint_bad`) -- category prefixes make related tests findable and runnable together.

- Use the `_bad` suffix when the test code is illegal SystemVerilog, `_unsup` when the code is legal but Verilator does not yet support it, `_off` for disabled-behavior tests -- never `_fail`.

- Keep filenames under roughly 30-35 characters, abbreviating where needed -- concise names stay readable in test output.

## Files and drivers

- Every `.v` file needs a matching `.py` driver -- without one the test never runs and becomes dead code giving false coverage confidence.

- Drivers must actually call `test.compile()` and `test.execute()` (or `test.lint()` for lint-only tests) -- a driver that sets up but never runs hides coverage gaps silently.

- Copy the license header from an existing file: `.v` tests carry the Creative Commons Public Domain (CC0) notice with matching SPDX tags; `.py` drivers carry the standard driver header -- distribution tests check headers on every committed file.

- Use `--binary` instead of `--exe --main --timing` (or subsets of them) -- `--binary` implies the others; shorter and clearer.

- Error tests use `test.compile(fails=True, expect_filename=test.golden_filename)` (or `test.lint(...)`) and must not call `test.execute()` -- compilation is supposed to fail.

- Use `test.lint()` rather than `test.compile()` for static-analysis-only tests -- clearer intent, no needless simulation.

- `test.compile()` defaults are richer than they look: the vlt driver auto-injects `--exe` and a generated main, so bare `test.compile()` plus `test.execute()` produces a runnable binary, and `assert property` fires its action blocks without `--assert` -- try the simple form before adding flags.

- Use `.out` golden files with `expect_filename` instead of inline `expect` regex strings -- goldens are diffable and maintainable in version control.

- Prefer inline assertion macros for simple deterministic values; use `test.execute(expect_filename=test.golden_filename)` only for complex or multi-line output.

- Use `test.glob_one()`/`test.glob_some()` instead of `glob.glob()` with manual count checks -- clearer assertions and better error messages.

- Use `test.timeout()` for time budgets, not manual `time.time()` measurements -- the framework handles machine-speed variation.

- Coverage tests must run `verilator_coverage` and verify individual bins and points, not just aggregate percentages -- aggregate-only checks mask per-bin regressions.

- Add override/suppression test cases when introducing a new suppressible warning code -- proves users can actually turn it off.

- Verify external tool availability with a minimal functional command, not `--version` -- proves the tool works for its purpose, not just that the binary exists.

- Assert optimization stats with exact expected counts: `test.file_grep(test.stats, r'Optimizations, ...\s+(\d+)', N)` -- presence-only matches miss algorithmic drift; use an expected count of 0 (not `file_grep_not`) to prove a stat is exactly zero.

- Add a `-fno-inline` driver variant (reusing the same `.v` via `test.top_filename`) for scope-dependent features -- module inlining changes scope handling.

- Add a `_protect_ids` variant when a feature emits user identifiers or filenames -- verifies nothing from the source leaks in `--protect-ids` mode.

- Use conservative thread counts (2 or fewer) in multithreaded tests -- CI machines run many tests in parallel and contention causes flakiness.

- Extend existing test files with related cases instead of creating many single-purpose files; keep one test concept per file when concepts genuinely differ.

- Keep drivers minimal -- test logic and descriptions belong in the `.v`/`.cpp` files, common patterns in `driver.py` functions.

- Place a single support/config file directly in `t/` with a descriptive name -- a subdirectory holding one file is clutter.

- Use `test.files_identical_sorted()` for output whose ordering is non-deterministic -- `expect_filename` comparison fails on ordering noise.

- When running tests from a checkout, set `VERILATOR_ROOT` to the checkout root before invoking `python3 t/<name>.py` -- the harness compiles generated C++ against the headers it finds there.

- The `t_dist_*` tests enforce repository conventions (headers, sorted lists, warning documentation) -- run the relevant ones before submitting.

## Golden .out files

- Never hand-write or hand-edit `.out` goldens -- generate them with `HARNESS_UPDATE_GOLDEN=1 python3 t/<name>.py`; the harness handles path normalization, version markers, and line-number masking that hand edits get wrong.

- When a feature lands, remove its now-supported entries from `t_*_unsup.v`/`t_*_bad.v` in the same change and regenerate the goldens -- stale entries no longer error, and reviewers will flag them.

## Verilog style

- Use 2-space indentation and no tabs -- matches `nodist/verilog_format` and common online-editor settings.

- Declarations are flush-left with a single space between type and name; never column-align declarations:

  ```systemverilog
  // WRONG: column-aligned
  bit [63:0] crc    = 64'h5aef0c8d_d70a4497;
  int        cyc    = 0;

  // RIGHT: flush-left
  bit [63:0] crc = 64'h5aef0c8d_d70a4497;
  int cyc = 0;
  ```

- Run `nodist/verilog_format` on new `.v` files; wrap test macro definitions in `// verilog_format: off`/`on` so the formatter does not split them.

- Use `$display("%0d", ...)` not `%d` -- avoids leading-space padding in output.

- Wrap Verilator-specific test code (e.g. `$c`) in `` `ifdef VERILATOR`` -- keeps tests portable to other simulators.

- Use inline `// verilator lint_off WARNCODE` directives (unquoted code names) instead of `-Wno-*` driver flags, and only suppress a warning when that warning is itself under test -- fix root causes otherwise.

- Use only IEEE 1800-compliant constructs that other simulators also accept -- tests must validate standard behavior, not Verilator's parser leniency.

- Omit optional end labels on `endmodule`/`endclass`/`endtask`/`endfunction` -- matches the prevailing test suite style.

## Self-checking

- Use the `checkh`/`checkd`/`checks` assertion macros, not manual `if`/`$display`/`$stop` sequences -- standard macros keep assertion style uniform across the suite.

- Note `checkh` prints with `%p`, which renders integers as hex (`'h11` for 17) -- use `checkd` for integer comparisons and reserve `checkh` for structs/arrays where `%p` shows the assignment-pattern shape.

- Use the `` `stop`` macro rather than direct `$stop` -- allows centralized control of stop behavior.

- Verify against CRC-checked or generated sequences rather than single inline spot checks -- sequence verification catches edge cases that spot checks miss.

- Exercise runtime behavior over multiple clock cycles, not just initial values -- initial blocks are optimized differently from dynamic data flow.

- Drive logic with variable inputs (counters, CRC registers) so constant folding and dead-code elimination cannot evaluate the logic under test at compile time.

- Loop randomization/constraint tests 10-20 iterations and check that values actually differ across iterations -- for variables wider than 1 bit, 10 identical draws is effectively impossible.

- Use the minimum iteration count that reliably detects the bug, not an arbitrary large number -- keeps the regression suite fast.

- For constraint-enforcement tests, pick a narrow value space (e.g. `bit [3:0]` with 4-5 elements) so a violation is probable per run -- and verify the test fails on an unfixed tree before submitting.

## Test design

- Use non-power-of-2, non-word-aligned widths (e.g. 7, 15, 31, 33, 63, 65, 95) -- exposes masking and word-boundary bugs in the under-32, 33-64, and over-64 bit representations that widths like 32/64/128 hide.

- Test both `[high:low]` and `[low:high]` orderings plus non-zero bounds like `[3:1]` and `[5:4]` -- catches endianness and offset bugs that zero-based ranges miss.

- Use different ranges for each axis of multidimensional arrays (`[2:1][3:1] arr [5:4][6:3]`) -- uniform dimensions hide iteration and offset-calculation bugs.

- When adding type support, test all basic types (chandle, string, real, ...) and typedef-wrapped variants -- proves each either works or produces a clear error, and exercises the typedef-resolution paths.

- Test constructs in all control-flow contexts (loop conditions, increments, `if`, `case`) and test sibling operators in the same optimization domain -- shared compiler code paths break together.

- Include the issue's own reproducer as a committed test, and verify the test fails without the fix -- prevents false-positive regressions.

- Use DPI-C imports for external C functions, not VPI or `$c`, where the test allows -- keeps tests portable across simulators.

- Instantiate parameterized interfaces multiple times with varying parameters -- single-instance tests miss instance-specific connection bugs.

- Test dual-use methods both as void statements and in value-returning contexts -- catches bugs where return values are ignored or misused.

- Test constraints involving array methods with all comparison operators (`==`, `!=`, `<`, `>`, `<=`, `>=`) -- rarely used operators regress silently.

- Assert non-blocking-assignment results in the cycle immediately after they take effect, before later overwrites, and use indices that change post-NBA -- verifies NBA timing and index capture, not just the final value.

- Keep standard idioms like `do ... while (0)` macro wrapping in test code even if a compiler pass mishandles them -- fix the compiler, not the test.
