<!-- DESCRIPTION: Verilator: Repository-wide guidelines for AI coding agents
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# Verilator Coding Guidelines

When to check: read this file before making any change in this repository, then read the directory guide for the area being edited.

## Topic guides

- [src/AGENTS.md](src/AGENTS.md) -- compiler C++ sources: style, AST, visitors, parser, file-specific rules
- [test_regress/AGENTS.md](test_regress/AGENTS.md) -- regression tests: naming, drivers, golden files, Verilog style
- [docs/AGENTS.md](docs/AGENTS.md) -- documentation (`*.rst`) writing rules
- `docs/internals.rst` -- architecture, AST, and pass overview
- `docs/CONTRIBUTING.rst` -- contribution process

## Build and test

- Build in the source tree: `autoconf && ./configure && make -j8`; developers should configure with `--enable-ccwarn` to stop the build on new warnings.

- Run a single test from the repository root: `test_regress/t/t_<name>.py`; run the full regression with `make test`.

## Error classification

Choose the diagnostic API by what went wrong; the choice determines which test must accompany the change.

| API | Output | Meaning | Required test |
|---|---|---|---|
| `v3error("...")` | `%Error:` | User wrote invalid SystemVerilog (IEEE violation) | `t_*_bad*.v` + `.out` golden |
| `v3error("Unsupported: ...")` | `%Error-UNSUPPORTED:` | Legal SystemVerilog that Verilator does not yet support | `t_*_unsup*.v` + `.out` golden |
| `v3warn(CODE, "...")` | `%Warning-CODE:` | Legal but suspicious code | warning test + `.out` golden |
| `v3fatalSrc("...")` | `%Error: Internal Error` | Should-never-happen internal assertion | none -- not user-triggerable |

- Include the IEEE reference in errors about spec-defined restrictions: `(IEEE 1800-2023 XX.X)` -- makes the restriction verifiable.

- Every `v3error`/`v3warn` message needs a test in `test_regress/t/` -- enforced by the warn-coverage distribution test; `v3fatalSrc` is exempt.

- Reserve "Unsupported:" for not-yet-implemented features, never for user mistakes; when partially implementing a feature, keep errors on the still-unsupported sub-features.

- On error paths, clean up or replace invalid AST (e.g. with `AstConst::BitFalse`) so later passes do not crash after the error.

- Update `docs/guide/warnings.rst` when adding or changing warnings -- documentation for every warning is enforced by a distribution test.

## Process

- Search existing open pull requests and issues for overlapping work before starting -- duplicating an open PR wastes both author and reviewer time.

- Cite IEEE 1800-2023 with section numbers in error messages, code comments, and PR text -- verify against the actual standard text, not recalled knowledge.

- Do not edit `docs/CONTRIBUTORS` -- only humans may edit it; remind the user to read and agree to the statement in it.

- Do not edit the `Changes` file unless explicitly asked -- the maintainer updates it near release time; contributor edits cause merge conflicts.

- Fix the general case, not just the reported case -- if the root cause also affects modules/classes/interfaces beyond the trigger scenario, cover them or expect the fix to be rejected.

- Keep changes single-purpose: refactoring, drive-by bug fixes found along the way, and new features belong in separate PRs; land standalone cleanups first.

- Split large features into a chain of small, independently mergeable PRs, each adding one dimension of complexity -- keeps review scope bounded.

- Do not expand scope opportunistically -- even an IEEE-justified diagnostic tightening reclassifies user-facing behavior, re-goldens existing tests, and widens the review blast radius; file it as its own PR.

- When changing a warning's or error's classification, update the warning documentation and regression expectations in the same change -- diagnostic class and suppressibility are part of the user-facing contract.

- Very large PRs include an explicit risk summary: what semantics changed, what stayed invariant, and what validation proves safety -- review bandwidth drops sharply as changed-file count grows.

- Build, export, or reporting features must show that a downstream consumer can actually parse the produced output -- format-only checks miss consumer-visible breakage.

- After a framework PR lands, plan a follow-up that simplifies and unifies what review revealed -- a negative line count in the follow-up is a sign of maturity, not failure.

- Every bug fix includes a test that fails without the fix; include the issue's own reproducer as a regression test when possible.

- Aim for 100% line coverage on new code and justify or remove uncovered branches -- branch coverage markedly below line coverage signals guards that callers never violate; request a CI coverage report and check it.

- Run `make format` (clang-format) and `make cppcheck` before pushing; self-review the diff for leftover debug code, stale comments, and copy-paste errors.

- Apply new code patterns globally or not at all -- do not introduce a one-off convention in a single file.

## Commits

- Commit messages are one short line referencing issue and PR numbers: `Short description (#issue) (#pr)`.

- Do not add Co-Authored-By or any AI attribution to commits.

## Cross-cutting code rules

- No non-ASCII characters in C++ sources or headers -- use `--` not em dashes and plain `'` not smart quotes, at write time, not just when CI complains.

- Keep lists sorted: lexer/parser tokens, option declarations, enum values, configure feature lists, documented option lists.

- `bin/` scripts must be Python -- they are distributed cross-platform; `nodist/` may use bash and platform-specific code (developer-only, not packaged).

- Runtime code in `include/` targets C++14 (`--no-timing` builds must work); C++20 features are allowed only in timing code paths.

- In `include/` public headers, prefix public classes and types with `Verilated`/`Vl` and use `///` comments for API documentation -- prevents collisions with user code and feeds doc generation.

- Apply the same const, naming, and portability discipline in infrastructure and test code as in core passes -- review standards are not relaxed for helper code.

- Keep deprecated command-line options active with warning-only handlers (`v3warn(DEPRECATED, ...)`) -- removing an option outright breaks existing user scripts.
