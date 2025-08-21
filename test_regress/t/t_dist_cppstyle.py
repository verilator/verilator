#!/usr/bin/env python3
# DESCRIPTION: Verilator: Primitive C++ style checker
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

root = ".."


def get_source_files(root):
    git_files = test.run_capture("cd " + root + " && git ls-files")
    if test.verbose:
        print("MF " + git_files)
    files = {}
    for filename in git_files.split():
        if filename == '':
            continue
        files[filename] = True
    return files


def check_pattern(filename, contents, pattern, not_pattern, message):
    # Pattern uses match, so must include skipping leading whitespace if necessary
    lineno = 0
    buffer_lineno = 0
    buffer = "\n"
    for line in contents.splitlines():
        lineno += 1
        if buffer == "\n":
            buffer_lineno = lineno
        if line != "":
            # Don't do whole file at once - see issue #4085
            # Build a buffer until a newline so we check a block at a time.
            buffer += line + "\n"
            continue
        m = re.search(r"\n" + pattern, buffer)
        if m:
            if not not_pattern or not re.search(not_pattern, buffer):
                test.error_keep_going(filename + ":" + str(buffer_lineno) + ": " + message +
                                      m.group(0))
        buffer = "\n"


if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

files = get_source_files(root)

for filename in sorted(files.keys()):
    filename = os.path.join(root, filename)
    if not os.path.exists(filename):  # git file might be deleted but not yet staged
        continue
    if not re.search(r'\.(h|c|cpp)(\.in)?$', filename):
        continue
    if '/gtkwave/' in filename:
        continue

    contents = test.file_contents(filename) + "\n\n"

    check_pattern(filename, contents, r"[^\']*virtual[^{};\n]+override[^\n]*", None,
                  "'virtual' keyword is redundant on 'override' method")

    check_pattern(filename, contents,
                  r'    \s*(\w+ )*\s*(inline) [^;]+?\([^;]*?\)[^;]+?(?:{|:|=\s*default[^\n]*)',
                  None, "'inline' keyword is redundant on method definitions inside classes")

    check_pattern(
        filename, contents, r'\s*inline \S+ [^;:(]+::[^;:(]+\([^;]*\)[^;]+{[^\n]*', r'template',
        "Use 'inline' only on declaration inside classes"
        " (except for template specializations)")

    check_pattern(
        filename,
        contents,
        r'.*[( ]new [a-zA-Z0-9]+\([^\n]*',
        # Ignore common ok narrowing conversions, on int vs uint32_t arguments
        r'(Need \(\)|new AstArraySel|new AstConst|new AstRange)',
        "Use brace instead of parenthesis-style new constructors e.g. 'new ...{...}'")

    check_pattern(
        filename,
        contents,
        r'.*(\n *[:,]|,\n) +m_[a-zA-Z0-9]+\(',
        # Ignore common m_e enum constructors
        r'.*(Need \(\)|: m_e\()|V3OPTION_PARSER_DEF',
        "Use brace instead of parenthesis-style constructors e.g. ': m_...{...}'")

    if re.search(r'\.(c|cpp)', filename):
        check_pattern(filename, contents, r'(\w+\s+)*(\binline\b)[^\n]*', None,
                      "'inline' keyword is on functions defined in .cpp files")

test.passes()
