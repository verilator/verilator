---
name: verilator-testing
description: Verilator regression test patterns: test structure, drivers, golden files, naming, coverage, self-checking
---

# Verilator Testing Skill

## Test Structure

```
test_regress/
  t/                    # All test drivers and sources
    t_<category>_<description>.py   # Python driver
    t_<category>_<description>.v    # SystemVerilog source
    t_<category>_<description>.out  # Golden output (auto-generated)
  t/vltest_bootstrap.py   # Test harness entry point
  coverage_common.py    # Coverage test helpers
```

### Test = Source + Driver
- Every `.v`/`.sv` needs a matching `.py` driver calling `test.compile()` and `test.execute()` (or `test.lint()` for static-only)
- Without a driver, source never runs -> dead code, false coverage confidence
- Golden `.out` files compared via `expect_filename` - **never hand-write**; regenerate with `HARNESS_UPDATE_GOLDEN=1`

## Running Tests

```bash
# From repository root
test_regress/t/t_<name>.py              # Single test
VERILATOR_ROOT=/path/to/checkout test_regress/t/t_<name>.py  # From checkout
make test                               # Full regression (needs --enable-longtests)
```

## Test Naming

```python
# t_{category}_{description} in snake_case
# First word groups category so related tests are findable/runnable together
t_lint_unused_func_bad    # GOOD: category = lint
t_unused_func_lint_bad    # BAD:  category unclear

# Suffixes:
#   _bad    = illegal SystemVerilog (expects v3error)
#   _unsup  = legal SV not yet supported (expects v3error Unsupported:)
#   _off    = disabled-behavior test
#   NEVER _fail

# Filenames <= 30-35 characters
```

## Driver Patterns

```python
import vltest_bootstrap

test.scenarios('simulator')  # or 'vlt' for lint-only

# Compile + execute (most tests)
test.compile()
test.execute()
test.passes()

# Lint-only (static analysis)
test.lint(v_flags=["--lint-only", "--Wno-XXX"])

# Error test (expects failure)
test.compile(fails=True, expect_filename=test.golden_filename)
# Must NOT call test.execute()

# Use test.glob_one/glob_some and test.timeout() - NOT raw glob/time.time()

# Coverage: run verilator_coverage, verify individual bins/points - not just aggregate %

# Assert optimization stats exactly:
test.file_grep(test.stats, r'Optimizations, ...\s+(\d+)', N)

# Add _protect_ids variant when feature emits user identifiers/filenames
# Use conservative threads (<=2) in multithreaded tests

# Extend existing test files with related cases - not many single-purpose files
# Keep drivers minimal; test logic belongs in the .v
```

## Golden .out Files

```bash
# NEVER hand-write or hand-edit - regenerate:
HARNESS_UPDATE_GOLDEN=1 python3 t/<name>.py

# When feature lands: remove now-supported entries from t_*_unsup.v / t_*_bad.v
# in SAME change, regenerate goldens - stale entries no longer error
```

## Verilog Style in Tests

```systemverilog
// 2-space indent, no tabs

// Declarations flush-left, single space between type and name
// NO column-align
bit [63:0] crc = 64'h5aef0c8d_d70a4497;  // RIGHT
int cyc = 0;                               // RIGHT

// bit [63:0] crc    = 64'h...;  // WRONG
// int        cyc    = 0;        // WRONG

// $display("%0d", ...) not %d - avoids leading-space padding

// Wrap Verilator-specific code in `ifdef VERILATOR
// inline // verilator lint_off WARNCODE only when THAT warning is under test

// Use only IEEE 1800-compliant constructs - tests validate standard behavior
// Omit optional end labels on endmodule/endclass/endtask/endfunction
```

## Self-Checking Patterns

```systemverilog
// Use checkh/checkd/checks macros - NOT manual if/$display/$stop
// checkh prints with %p (hex) - use checkd for integer comparisons

// Use `stop macro, not direct $stop

// Drive logic with runtime-varying inputs (counters, CRC/LFSR)
// So constant folding CANNOT pre-evaluate logic under test

// Check behavior across MULTIPLE clock cycles, not just initial values

// For pass/fail depending on varying/random values:
//   Loop enough iterations that values demonstrably differ
//   Size value space so failure is probable per run
//   CONFIRM test fails on un-fixed tree before submitting
```

## Test Design Principles

```systemverilog
// Non-power-of-2, non-word-aligned widths: 7, 15, 31, 33, 63, 65, 95
// Exposes masking/word-boundary bugs that 32/64/128 hide

// Both [high:low] and [low:high] orderings + non-zero bounds [3:1]
// Different ranges for each axis of multidimensional arrays

// When adding type support: test ALL basic types (chandle, string, real)
// + typedef-wrapped variants

// Include issue's own reproducer as committed test
// VERIFY it fails without the fix

// Assert NBA results in cycle IMMEDIATELY after they take effect
// Before later overwrites, using indices that change post-NBA
```

## Coverage Tests

- Run `verilator_coverage` and verify **individual bins and points**
- Not just aggregate percentages
- Use `coverage_common.py` helpers

## Debug Emit Test (V3EmitV coverage)

```python
# t_debug_emitv.py pattern
test.lint(v_flags=[
    "--lint-only", "--Wno-COVERIGN", "--timing",
    "--dumpi-tree 9 --dumpi-V3EmitV 9 --debug-emitv",
    "--dump-graph --dumpi-tree-json 9 --no-json-ids"
])
output_vs = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "_*_width.tree.v")
for output_v in output_vs:
    test.files_identical(output_v, test.golden_filename)
```