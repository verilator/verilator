#!/usr/bin/env python3
# DESCRIPTION: Verilator: Shared helpers for subgraph scheduling tests
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# Copyright 2026 Yutetsu TAKATSUKASA
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json


def check_subgraph_specializations(test, tree_filename, orig_name, minimum=2):
    with open(tree_filename, "r", encoding="utf8") as fh:
        tree = json.load(fh)

    modules = []

    def visit(value):
        if isinstance(value, dict):
            if value.get("type") == "MODULE" and value.get("origName") == orig_name:
                modules.append(value)
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(tree)

    originals = [module for module in modules if module.get("name") == orig_name]
    specializations = [module for module in modules if module.get("name") != orig_name]
    if not originals:
        test.error("No original module found for " + orig_name)
    if len(specializations) < minimum:
        test.error("Too few specialized modules found for " + orig_name)

    unmarked = [module.get("name") for module in modules if not module.get("subgraphBoundary")]
    if unmarked:
        test.error("Subgraph boundary missing on modules: " + ", ".join(unmarked))
