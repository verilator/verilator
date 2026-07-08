<!-- DESCRIPTION: Verilator: docs/ guidelines for AI coding agents
     SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
     SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0 -->

# docs/ Guidelines -- Verilator documentation (\*.rst)

When to check: before editing anything under `docs/`.
Read the repository-root [AGENTS.md](../AGENTS.md) first for process and cross-cutting rules.

## Writing rules

- Rewrap paragraphs after editing -- keep consistent line length in `*.rst` files.

- Document only stable, implemented features -- never planned or in-development capabilities; prevents user confusion and support burden.

- Explain WHAT and WHEN, not HOW -- conceptual purpose and practical use cases over implementation mechanics; describe behavior ("optimized as pure", not "treated as pure") and clarify ambiguous referents ("in the internals of Verilator").

- Keep terminology consistent -- one term per concept; update docs when renaming code constructs; spell out full terms, avoiding abbreviations like "sim"/"sims".

- Use "how many" for countable nouns (threads, tasks, workers) and "how much" for uncountable quantities.

- Mark internal or experimental features "for internal use only" -- prevents user dependence and forced deprecation cycles later.

- Use specific IEEE references: `IEEE {number}-{year}` plus the section (e.g. `Annex I`) -- a vague "IEEE spec requires" is unverifiable.

- Document all flags with descriptions, not just syntax.

## reStructuredText mechanics

- Use the `:vlopt:` role for Verilator option references -- makes cross-references clickable and consistent.

- Escape angle brackets (`\<`, `\>`) in link targets -- prevents broken links to command-line options.

- Generate documentation examples with `test.extract` from `test_regress` test files -- examples stay synced with actually tested behavior.

## Hard constraint

- Never edit `docs/CONTRIBUTORS` -- only humans may, after reading and agreeing to its statement; remind the user instead.
