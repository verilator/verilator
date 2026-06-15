<!-- DESCRIPTION: Verilator: test_regress/ guidelines for AI coding agents
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# test_regress/ -- regression tests

Covers `.v`/`.sv` sources, `.py` drivers, and `.out` golden files under
`test_regress/`. Read the repository-root [AGENTS.md](../AGENTS.md) first. This
file has two parts: **Orientation** explains how the harness runs a test;
**Before you open a PR** is the test-authoring checklist.

______________________________________________________________________

# Orientation: how the harness works

- **A test is a `.v`/`.sv` source plus a matching `.py` driver in `t/`.** The
  driver calls `test.compile()`, `test.execute()`, and/or `test.lint()`. Without a
  `.py` the source never runs and is dead code giving false coverage confidence.
- **Golden output lives in `.out` files**, compared via `expect_filename`.
  Generate them with `HARNESS_UPDATE_GOLDEN=1 python3 t/<name>.py` -- never
  hand-write them; the harness normalizes paths, version markers, and line numbers
  that hand edits get wrong.
- **Run one test from the repository root:** `test_regress/t/t_<name>.py`. When
  running from a checkout, set `VERILATOR_ROOT` to the checkout root first so the
  harness compiles the generated C++ against the right headers.
- **`test.compile()` defaults are richer than they look:** the vlt driver
  auto-injects `--exe` and a generated main, and `assert property` fires its
  action blocks without `--assert` -- try the simple form before adding flags.
- **The `t_dist_*` tests enforce repository conventions** (file headers, sorted
  lists, warning documentation, ASCII-only) -- run the relevant ones before
  submitting.

______________________________________________________________________

# Before you open a PR

## Naming

- Name tests `t_{category}_{description}` in snake_case; the first word groups the
  category (`t_lint_unused_func_bad`, not `t_unused_func_lint_bad`) so related
  tests are findable and runnable together.
- Use `_bad` when the code is illegal SystemVerilog, `_unsup` when it is legal but
  unsupported, `_off` for disabled-behavior tests -- never `_fail`.
- Keep filenames under roughly 30-35 characters.

## Files and drivers

- Every `.v` needs a matching `.py` driver that actually calls `test.compile()`
  and `test.execute()` (or `test.lint()` for static-analysis-only tests) -- a
  driver that sets up but never runs hides coverage gaps silently.
- Copy the license header from an existing file: `.v` tests carry the CC0 notice,
  `.py` drivers carry the standard driver header -- distribution tests check
  headers on every committed file.
- Use `--binary` instead of `--exe --main --timing` -- it implies the others.
- Error tests use `test.compile(fails=True, expect_filename=test.golden_filename)`
  (or `test.lint(...)`) and must not call `test.execute()`.
- Use `.out` golden files with `expect_filename` instead of inline `expect`
  regex strings -- goldens are diffable and maintainable.
- Use `test.glob_one()`/`test.glob_some()` and `test.timeout()` instead of raw
  `glob.glob()` and manual `time.time()` measurements.
- Coverage tests run `verilator_coverage` and verify individual bins and points,
  not just aggregate percentages.
- Assert optimization stats with exact expected counts:
  `test.file_grep(test.stats, r'Optimizations, ...\s+(\d+)', N)`.
- Add a `_protect_ids` variant when a feature emits user identifiers or filenames;
  use conservative thread counts (2 or fewer) in multithreaded tests.
- Extend existing test files with related cases instead of creating many
  single-purpose files; keep drivers minimal -- test logic belongs in the `.v`.

## Golden .out files

- Never hand-write or hand-edit `.out` goldens -- regenerate with
  `HARNESS_UPDATE_GOLDEN=1`.
- When a feature lands, remove its now-supported entries from `t_*_unsup.v` /
  `t_*_bad.v` in the same change and regenerate the goldens -- stale entries no
  longer error and reviewers will flag them.

## Verilog style

- 2-space indentation, no tabs.

- Declarations are flush-left with a single space between type and name; never
  column-align:

  ```systemverilog
  // WRONG: column-aligned
  bit [63:0] crc    = 64'h5aef0c8d_d70a4497;
  int        cyc    = 0;
  // RIGHT: flush-left
  bit [63:0] crc = 64'h5aef0c8d_d70a4497;
  int cyc = 0;
  ```

- Run `nodist/verilog_format` on new `.v` files; wrap macro definitions in
  `// verilog_format: off`/`on` so the formatter does not split them.

- Use `$display("%0d", ...)` not `%d` -- avoids leading-space padding.

- Wrap Verilator-specific test code (e.g. `$c`) in `` `ifdef VERILATOR ``.

- Use inline `// verilator lint_off WARNCODE` only when that warning is itself
  under test -- fix root causes otherwise.

- Use only IEEE 1800-compliant constructs other simulators also accept -- tests
  validate standard behavior, not Verilator's parser leniency.

- Omit optional end labels on `endmodule`/`endclass`/`endtask`/`endfunction`.

## Self-checking

- Use the `checkh`/`checkd`/`checks` assertion macros, not manual
  `if`/`$display`/`$stop` sequences. Note `checkh` prints with `%p`, which renders
  integers as hex -- use `checkd` for integer comparisons.
- Use the `` `stop `` macro rather than direct `$stop`.
- Drive logic with runtime-varying inputs (counters, CRC/LFSR registers) so
  constant folding cannot pre-evaluate the logic under test; check behavior across
  multiple clock cycles, not just initial values.
- For a test whose pass/fail depends on varying or random values, loop enough
  iterations that the values demonstrably differ and size the value space so a
  failure is probable per run, then confirm the test fails on an un-fixed tree
  before submitting.

## Test design

- Use non-power-of-2, non-word-aligned widths (7, 15, 31, 33, 63, 65, 95) --
  exposes masking and word-boundary bugs that 32/64/128 hide.
- Test both `[high:low]` and `[low:high]` orderings plus non-zero bounds like
  `[3:1]`; use different ranges for each axis of multidimensional arrays.
- When adding type support, test all basic types (chandle, string, real) and
  typedef-wrapped variants.
- Include the issue's own reproducer as a committed test, and verify it fails
  without the fix.
- Assert non-blocking-assignment results in the cycle immediately after they take
  effect, before later overwrites, using indices that change post-NBA.
