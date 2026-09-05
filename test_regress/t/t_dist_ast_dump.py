#!/usr/bin/env python3
# pylint: disable=W0603
# DESCRIPTION: Verilator: Primitive C++ style checker
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

EXEMPT_MEMBERS = """
    m_name
    m_origName
    m_purity
    m_pinNum
    m_tag
    m_text
    m_timeunit
    m_uniqueNum
    """
AstMethods = {}


def read_ast_methods():
    for filename in (test.glob_some(test.root + "/src/V3AstNode*.h")):
        with open(filename, 'r', encoding="latin-1") as fh:
            lineno = 0
            class_name = ""
            suppress_next = False
            for line in fh:
                lineno += 1
                line = line.rstrip()
                if re.match(r'^\s*//\s*dist-ast-dump-suppress', line):
                    suppress_next = True
                m = re.match(r'^class\s+(Ast[0-9A-Za-z]+)', line)
                if m:
                    class_name = m.group(1)
                    if test.verbose:
                        print("-class: %s" % class_name)
                if re.match(r'^};', line):
                    class_name = None
                if class_name:
                    m = re.match(r'^\s+(const\s+)?([a-zA-Z_:<>]+)\s+m_([0-9a-zA-Z]+)\s*[=;{]',
                                 line)
                    if m:
                        dtype = m.group(2)
                        if dtype in ('operation', 'return'):
                            continue
                        member_no_m = m.group(3)
                        key = class_name + '::m_' + member_no_m
                        if test.verbose:
                            print("- member: %s" % key)
                        AstMethods[key] = {
                            'class': class_name,
                            'dtype': dtype,
                            'member': 'm_' + member_no_m,
                            'key': key,
                            'fileline': ("%s:%05d" % (filename, lineno)),
                            'dump': False,
                            'dumpJson': False,
                            'suppressed': suppress_next
                        }
                        suppress_next = False
                    # Anything in name() is automatically dumped by default, track them
                    if re.match(r'^\s*(std::)?string name\(\) const', line):
                        record_founds_in_line(class_name, "dump", line)
                        record_founds_in_line(class_name, "dumpJson", line)


def read_ast_dumps():
    for filename in (test.glob_some(test.root + "/src/V3AstNodes.cpp")):
        with open(filename, 'r', encoding="latin-1") as fh:
            class_name = None
            for line in fh:
                line = line.rstrip()
                m = re.match(r'^void (Ast\S+)::(dump|dumpJson)\(', line)
                if m:
                    class_name = m.group(1)
                    dumper = m.group(2)
                    continue
                if re.match(r'}', line):
                    class_name = None
                if class_name:
                    record_founds_in_line(class_name, dumper, line)


def record_founds_in_line(class_name, dumper, line):
    if test.verbose:
        print("-ln: %s" % line)
    for m in re.finditer(r'\bm_([a-zA-Z0-9]+)\b', line):
        record_found_sym(class_name, m.group(1), dumper)
    # foo()
    # isFoo()
    # dumpJson...(, foo)
    for m in re.finditer(r'\b([a-zA-Z0-9]+)[()]', line):
        record_found_sym(class_name, m.group(1), dumper)
        m_is = re.match(r'^is([A-Z])(.*)', m.group(1))
        if m_is:
            record_found_sym(class_name, m_is.group(1).lower() + m_is.group(2), dumper)


def record_found_sym(class_name, method, dumper):
    key = class_name + '::m_' + method
    if key in AstMethods:
        if test.verbose:
            print("- WordFound: %s::%s: %s" % (class_name, method, dumper))
        AstMethods[key][dumper] = True
    else:
        if test.verbose:
            print("- NOT-wordFound: %s::%s: %s" % (class_name, method, dumper))


def check():
    # pprint(AstMethods)
    exempt_members = {i: True for i in list(map(re.escape, EXEMPT_MEMBERS.split()))}

    errors = 0
    passes = 0
    exempted = 0
    metacomment_exemptions = 0
    for key in sorted(AstMethods.keys(), key=lambda key: AstMethods[key]['fileline']):
        k = AstMethods[key]
        if k['member'] in exempt_members or k['key'] in exempt_members:
            exempted += 1
            continue
        if k['suppressed']:
            metacomment_exemptions += 1
            continue
        missings = ""
        for dumper in ['dump', 'dumpJson']:
            if not k[dumper]:
                if missings != "":
                    missings += ", "
                missings += "'" + k['class'] + "::" + dumper + "()'"
            else:
                if test.verbose:
                    print("- Found: Member " + k['key'] + " in " + dumper + "()")
                passes += 1

        if missings != "":
            errors += 1
            test.error_keep_going(k['fileline'] + ": Member '" + k['dtype'] + " " + k['key'] +
                                  "' is declared but not printed in " + missings)
            # pprint(k)

    print("Errors %d, passes %d, hardcoded-exempted %d, metacomment-exempted %d" %
          (errors, passes, exempted, metacomment_exemptions))
    if passes < 10:
        test.error("Not enough passed validations, something broke")


if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

print(
    """Validating that Ast* class m_member variables are dumped in AstNodes.cpp dump/dumpJson routines.

Ways to satisfy this check:
  1. Usually the correct way, the Ast{class}::dump()/dumpJson() functions
     in V3AstNodes.cpp must have a m_memberName or memberName() or isMemberName() usage.
  2. Use m_memberName or memberName() in the Ast{class}::name() function.
  3. Add metacomment '// dist-ast-dump-suppress' to the line above where
     m_member is declared in Ast{class}.
  4. Add hardcoded exception in t_dist_ast_dump.py.
""")
read_ast_methods()
read_ast_dumps()
check()

test.passes()
