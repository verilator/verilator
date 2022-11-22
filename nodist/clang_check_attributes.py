#!/usr/bin/env python3
# pylint: disable=C0114,C0115,C0116,C0209
#
# Copyright 2022 by Wilson Snyder. Verilator is free software; you
# can redistribute it and/or modify it under the terms of either the GNU Lesser
# General Public License Version 3 or the Apache License 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Apache-2.0
#
# Based on the work of (Guillaume "Vermeille" Sanchez)[https://github.com/Vermeille/clang-callgraph]
# licensed under Apache 2.0

import sys
import os
import glob
import pathlib
from pprint import pprint
from clang.cindex import CursorKind, Index


# https://stackoverflow.com/a/74205044
class FixSizedDict(dict):

    def __init__(self, *args, maxlen=0, **kwargs):
        self._maxlen = maxlen
        super().__init__(*args, **kwargs)

    def __setitem__(self, key, value):
        dict.__setitem__(self, key, value)
        if self._maxlen > 0:
            if len(self) > self._maxlen:
                self.pop(next(iter(self)))


INDEX = Index.create()
CLANG_ARGS = []
TRANSLATE_UNITS = FixSizedDict(maxlen=20)
PRINTED = []

# by definition constructor is MT safe,
# but functions that constructor call are not!
MT_SAFE_KINDS = [CursorKind.CONSTRUCTOR]
UNSAFE_CALLS = []
VERILATOR_ROOT = pathlib.Path(__file__).parent.parent.resolve()


def get_diag_info(diag):
    return {
        'severity': diag.severity,
        'location': diag.location,
        'spelling': diag.spelling,
        'ranges': list(diag.ranges),
        'fixits': list(diag.fixits)
    }


def get_translate_unit(file, cfg):
    file = str(file)
    try:
        translate_unit = TRANSLATE_UNITS[file]
    except KeyError:
        translate_unit = INDEX.parse(file, cfg['clang_args'])
        if not translate_unit:
            print(f"unable to load translate_unit from file: {file}")
            sys.exit(1)
        for diag in translate_unit.diagnostics:
            if diag.severity in [diag.Error, diag.Fatal]:
                if "sc_time_stamp" in diag.spelling:
                    continue
                pprint(('diags',
                        list(map(get_diag_info, translate_unit.diagnostics))))
                sys.exit(1)
        TRANSLATE_UNITS[file] = translate_unit
    return translate_unit


def print_node(node, level):
    if fully_qualified_pretty(node) not in PRINTED:
        annotations = get_annotations(node)
        filepath = pathlib.Path(str(node.location.file)).resolve()
        try:
            relative = filepath.relative_to(VERILATOR_ROOT)
            print('%s %-35s %-100s %s [%s:%s - %s:%s] \t %s  %s' %
                  (' ' * level, node.kind, fully_qualified_pretty(node), ' ' *
                   (20 - level), node.extent.start.line,
                   node.extent.start.column, node.extent.end.line,
                   node.extent.end.column, relative, annotations))
        except ValueError:
            # Dont print functions that are not defined in verilator repository
            pass
        PRINTED.append(fully_qualified_pretty(node))


def get_annotations(node):
    return [
        c.displayname for c in node.get_children()
        if c.kind == CursorKind.ANNOTATE_ATTR
    ]


def fully_qualified(cursor):
    if cursor is None:
        return ''
    if cursor.kind == CursorKind.TRANSLATION_UNIT:
        return ''

    res = fully_qualified(cursor.semantic_parent)
    if res != '':
        return res + '::' + cursor.spelling
    return cursor.spelling


def fully_qualified_pretty(cursor):
    if cursor is None:
        return ''
    if cursor.kind == CursorKind.TRANSLATION_UNIT:
        return ''

    res = fully_qualified(cursor.semantic_parent)
    if res != '':
        return res + '::' + cursor.displayname
    return cursor.displayname


def is_excluded(node, cfg):
    xfiles = cfg['excluded_paths']
    xprefs = cfg['excluded_prefixes']
    if not node.extent.start.file:
        return False

    for xfile in xfiles:
        if node.extent.start.file.name.startswith(xfile):
            return True

    fqp = fully_qualified_pretty(node)

    for xpref in xprefs:
        if fqp.startswith(xpref):
            return True

    return False


def get_call_expr(node):
    call_expr = []
    for cursor in node.get_children():
        call_expr.extend(get_call_expr(cursor))
    if node.kind == CursorKind.CALL_EXPR:
        call_expr.append(node)
    return call_expr


def find_usr(file, usr, cfg):
    translate_unit = get_translate_unit(file, cfg)
    for cursor in translate_unit.cursor.get_children():
        if cursor.get_usr() == usr:
            return cursor
    return None


def check_attributes(cursor, search_attributes):
    if cursor.kind in MT_SAFE_KINDS:
        return True
    for attribute in search_attributes:
        if attribute in get_annotations(cursor):
            return True
    return False


def find_funcs(node, cfg, search_attributes):
    funcs = get_call_expr(node)
    for func in funcs:
        if not func.referenced:
            continue
        if is_excluded(func.referenced, cfg):
            continue
        call = func.referenced
        # Don't recurse into already printed nodes
        # it some cases in increases printing nodes by a lot
        if fully_qualified_pretty(call) in PRINTED:
            continue
        if str(call.location.file).endswith(".h"):
            if os.path.exists(str(call.location.file).replace(".h", ".cpp")):
                tu_call = find_usr(
                    str(call.location.file).replace(".h", ".cpp"),
                    call.get_usr(), cfg)
                if tu_call is not None:
                    call = tu_call

        if call is not None:
            if fully_qualified_pretty(call) not in PRINTED:
                PRINTED.append(fully_qualified_pretty(call))

            if not check_attributes(call, search_attributes):
                return False
            if call.kind in [
                    CursorKind.CXX_METHOD, CursorKind.CONSTRUCTOR,
                    CursorKind.FUNCTION_DECL
            ]:
                return find_funcs(call, cfg, search_attributes)
    return True


def print_funcs(node, cfg, search_attributes, level=1):
    funcs = get_call_expr(node)
    for func in funcs:
        if not func.referenced:
            continue
        if is_excluded(func.referenced, cfg):
            continue
        call = func.referenced
        # Don't recurse into already printed nodes
        # it some cases in increases printing nodes by a lot
        if fully_qualified_pretty(call) in PRINTED:
            continue
        if str(call.location.file).endswith(".h"):
            if os.path.exists(str(call.location.file).replace(".h", ".cpp")):
                tu_call = find_usr(
                    str(call.location.file).replace(".h", ".cpp"),
                    call.get_usr(), cfg)
                if tu_call is not None:
                    call = tu_call

        if call is not None:
            print_node(call, level)
            if call.kind in [
                    CursorKind.CXX_METHOD, CursorKind.CONSTRUCTOR,
                    CursorKind.FUNCTION_DECL
            ]:
                print_funcs(call, cfg, search_attributes, level + 1)


def get_info(node, cfg):
    if node.kind == CursorKind.CXX_METHOD:
        annotations = get_annotations(node)
        if "MT_SAFE" in annotations:
            if not find_funcs(node, cfg, ["MT_SAFE", "PURE"]):
                UNSAFE_CALLS.append(node)
        if "PURE" in annotations:
            if not find_funcs(node, cfg, ["PURE"]):
                UNSAFE_CALLS.append(node)
        if "MT_START" in annotations:
            if not find_funcs(node, cfg, ["MT_SAFE", "PURE"]):
                UNSAFE_CALLS.append(node)
    for cursor in node.get_children():
        get_info(cursor, cfg)


def get_files(filename):
    files = list(glob.glob(f"{filename}/*.cpp"))
    # Dont process test files
    files = [f for f in files if "_test.cpp" not in f]
    # Dont process Verilator coverage files
    files = [f for f in files if "Vlc" not in f]
    # We want to use V3Const after astgen
    files = [f for f in files if "V3Const.cpp" not in f]
    # Skip SystemC files
    files = [f for f in files if "_sc" not in f]
    # Skip parser files
    files = [f for f in files if ".yy.cpp" not in f]
    # Make sure list is unique
    files = list(dict.fromkeys(files))
    # Make filepaths absolute
    files = [os.path.abspath(f) for f in files]
    return files


def read_args(args):
    base_folders = []
    clang_args = []
    excluded_prefixes = []
    excluded_paths = ['/usr']
    i = 0
    while i < len(args):
        if args[i] == '-x':
            i += 1
            excluded_prefixes = args[i].split(',')
        elif args[i] == '-p':
            i += 1
            excluded_paths = args[i].split(',')
        elif args[i][0] == '-':
            clang_args.append(args[i])
        else:
            base_folders.append(args[i])
        i += 1
    return {
        'base_folders': base_folders,
        'clang_args': clang_args,
        'excluded_prefixes': excluded_prefixes,
        'excluded_paths': excluded_paths,
    }


def main():
    if len(sys.argv) < 2:
        print('usage: ' + sys.argv[0] + ' folder [extra clang args...]')
        return

    cfg = read_args(sys.argv)

    files = []
    for folder in cfg['base_folders']:
        files.extend(get_files(folder))
    files.sort()
    for file in files:
        translate_unit = get_translate_unit(file, cfg)
        get_info(translate_unit.cursor, cfg)

    for call in UNSAFE_CALLS:
        PRINTED.clear()
        search_attributes = ["PURE"]
        attributes = get_annotations(call)
        if "MT_SAFE" in attributes or "MT_START" in attributes:
            search_attributes.append("MT_SAFE")
        print(f"::group::{fully_qualified_pretty(call)}")
        print_node(call, 0)
        print_funcs(call, cfg, search_attributes, level=1)
        print("::endgroup::")

    print(
        f"Number of functions marked as MT_SAFE calling unsafe functions: {len(UNSAFE_CALLS)}"
    )


if __name__ == '__main__':
    main()
