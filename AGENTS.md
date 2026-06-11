<!-- DESCRIPTION: Verilator: Repository-wide guidelines for AI coding agents
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# Verilator Guidelines for AI Coding Agents

This file has two parts. **Orientation** gets you productive in the codebase from
a cold start. **Before you open a PR** is the checklist of conventions reviewers
otherwise have to enforce by hand -- read it before submitting any change.

Then read the directory guide for the area you are editing:

- [src/AGENTS.md](src/AGENTS.md) -- compiler C++ sources: AST, visitors, passes, parser, style
- [include/AGENTS.md](include/AGENTS.md) -- runtime library (`verilated*`): C++14, MT-safety, fixed-width types
- [test_regress/AGENTS.md](test_regress/AGENTS.md) -- regression tests: harness, drivers, golden files
- [docs/AGENTS.md](docs/AGENTS.md) -- documentation (`*.rst`)

---

# Orientation

## What Verilator is

Verilator is a *compiler*, not an interpreter. It translates synthesizable (and
much behavioral) SystemVerilog into a cycle-accurate C++ model that you then
compile and run. Almost every decision is made at compile ("verilation") time;
the generated C++ just advances state each evaluation. Optimize for verilation-
time work over runtime work.

## The pipeline is the spine

A run is an ordered sequence of passes over one shared AST (abstract syntax
tree). In source order:

| Stage | What it does | Key files |
|---|---|---|
| Preprocess + parse | Lex and parse text into a raw AST -- builds nodes only, no semantic checks | `verilog.l`, `verilog.y` |
| Link / elaborate | Resolve names, scopes, parameters; instantiate the hierarchy | `V3LinkParse`, `V3LinkDot`, `V3Param` |
| Width / type | Assign and check data types and bit widths | `V3Width` |
| Transform / optimize / schedule | Constant fold, lower language features, schedule events | `V3Const`, `V3Randomize`, `V3Assert*`, `V3Sched`, `V3Timing`, `V3Dfg` |
| Emit | Lower the final AST to generated C++ | `V3EmitC*` |
| Runtime | Library the generated model links against | `include/verilated*` |

`docs/internals.rst` is the authoritative architecture and pass reference. Read
it before any non-trivial change.

## Where to make a change

Map the symptom to the pass that owns it, then start by reading that pass's
top-of-file comment.

| Symptom or feature area | Start in |
|---|---|
| Type/width error, "what type is this", implicit conversion | `V3Width` |
| Name/scope/parameter resolution ("Can't find...", hierarchy) | `V3LinkDot`, `V3Param` |
| `randomize` / `constraint` / `rand` / `randc` | `V3Randomize` |
| `assert` / `property` / `sequence` / `cover` | `V3Assert`, `V3AssertPre`, `V3AssertNfa` |
| `fork` / timing / `#delay` / NBA / event scheduling | `V3Sched`, `V3Timing`, `V3Fork` |
| Syntax wrongly accepted or rejected | `verilog.y`, `verilog.l` |
| Wrong generated C++ | `V3EmitC*` |
| Runtime model behavior | `include/verilated*` |

## Build and run a test

- Build in the source tree: `autoconf && ./configure && make -j8`. Configure with
  `--enable-ccwarn` so a new compiler warning stops the build.
- Run one test from the repository root: `test_regress/t/t_<name>.py`.
- Run the full regression: `make test`.

---

# Before you open a PR

## Scope and process

- [ ] Searched open PRs and issues -- duplicating in-flight work wastes review time.
- [ ] Fixed the general root cause, not just the reported case -- if it also
      affects other modules/classes/interfaces, cover them or expect rejection.
- [ ] PR is single-purpose. Refactors, drive-by fixes found along the way, and new
      features each go in separate PRs; land standalone cleanups first.
- [ ] Every bug fix has a test that fails *without* the fix; include the issue's
      own reproducer when possible.
- [ ] New code aims for 100% line coverage; branch coverage far below line coverage
      signals guards callers never violate -- justify or remove them.
- [ ] Ran `make format` (clang-format) and `make cppcheck`; self-reviewed the diff
      for leftover debug code, stale comments, and copy-paste errors.
- [ ] Did not edit `docs/CONTRIBUTORS` (humans only) or `Changes` (maintainer
      updates it near release).

## Pick the right diagnostic (and its required test)

The API you choose determines which test must accompany the change.

| API | Output | Meaning | Required test |
|---|---|---|---|
| `v3error("...")` | `%Error:` | User wrote invalid SystemVerilog | `t_*_bad*.v` + `.out` golden |
| `v3error("Unsupported: ...")` | `%Error-UNSUPPORTED:` | Legal SV that Verilator does not yet support | `t_*_unsup*.v` + `.out` golden |
| `v3warn(CODE, "...")` | `%Warning-CODE:` | Legal but suspicious code | warning test + `.out` golden |
| `v3fatalSrc("...")` | `%Error: Internal Error` | Should-never-happen internal assertion | none -- not user-triggerable |

- Every `v3error`/`v3warn` needs a test in `test_regress/t/` -- enforced by the
  warn-coverage distribution test. `v3fatalSrc` is exempt.
- Reserve "Unsupported:" for not-yet-implemented features, never for user mistakes.
- When an error enforces a spec-defined restriction, cite the clause
  (`IEEE 1800-2023 11.4.7`) so it is verifiable. Update `docs/guide/warnings.rst`
  when adding or changing a warning.
- On error paths, clean up or replace invalid AST (e.g. `AstConst::BitFalse`) so
  later passes do not crash after the error.

## Cross-cutting code rules

- [ ] No non-ASCII characters in C++ sources or headers -- `--` not em dashes,
      plain `'` not smart quotes. At write time, not when CI complains.
- [ ] Lists stay sorted: lexer/parser tokens, option declarations, enum values,
      configure feature lists, documented option lists.
- [ ] `bin/` scripts are Python (distributed cross-platform); `nodist/` may use
      bash and platform-specific code (developer-only, not packaged).
- [ ] Runtime code in `include/` targets C++14 (`--no-timing` builds must work);
      C++20 only in timing code paths.
- [ ] In `include/` public headers, prefix public classes with `Verilated`/`Vl`
      and document the API with `///` comments.
- [ ] A new code pattern is applied globally or not at all -- no one-off
      convention in a single file.

## Commits

- Subject line is short and imperative and conventionally ends with the PR number:
  `Support property case (#7721)`. A body is optional and common for non-trivial
  changes.
