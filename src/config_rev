#!/usr/bin/env python3
# pylint: disable=C0103,C0114
######################################################################
#
# Copyright 2005-2022 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################
# DESCRIPTION: Query git to get version number

import argparse
import os
import re
import sys

parser = argparse.ArgumentParser()
parser.add_argument('directory')
Args = parser.parse_args()

os.chdir(Args.directory)

rev = 'UNKNOWN_REV'
data = os.popen('git describe').read()

match = re.search(r'^(v[0-9].*)', data)
if match:
    rev = match.group(1)
rev = re.sub('_', '.', rev)

data = os.popen('git status').read()
if (re.search('Changed but not updated', data, flags=re.IGNORECASE)
        or re.search('Changes to be committed', data, flags=re.IGNORECASE)
        or re.search('Changes not staged', data, flags=re.IGNORECASE)):
    rev += " (mod)"

print("static const char* const DTVERSION_rev = \"" + rev + "\";")

# Warn after the print, so at least the header has good contents
if re.search('UNKNOWN', rev):
    print("%Warning: No git revision found in config_rev.py", file=sys.stderr)
