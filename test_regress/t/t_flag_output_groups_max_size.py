#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

MAX_SIZE_BYTES = 1024 * 1024
VARS = ("VM_CLASSES_FAST", "VM_CLASSES_SLOW")

classes_mk = test.obj_dir + "/" + test.vm_prefix + "_classes.mk"


def file_size(filename):
    return os.path.getsize(test.obj_dir + "/" + filename)


def class_entries(var):
    # Files compiled for the given make variable, in order, each a list of .cpp files
    entries = []
    with open(classes_mk, 'r', encoding="utf8") as fh:
        in_var = False
        for line in fh:
            if line.startswith(var + " +="):
                in_var = True
            elif in_var:
                m = re.match(r'\s+(\S+) \\$', line)
                if not m:
                    break
                name = m.group(1)
                if "_vm_classes_" in name:
                    with open(test.obj_dir + "/" + name + ".cpp", 'r', encoding="utf8") as gfh:
                        entries.append(re.findall(r'#include "(.*)"', gfh.read()))
                else:
                    entries.append([name + ".cpp"])
    return entries


# Without a size limit each bucket is one group, record the first file of each
test.compile(
    verilator_flags2=["--output-split 1000", "--output-groups 3", "--output-groups-size 0"],
    verilator_make_gmake=False)
bucket_starts = {files[0] for var in VARS for files in class_entries(var)}

test.compile(verilator_flags2=[
    "--output-split 1000", "--output-groups 3", "--output-groups-size",
    str(MAX_SIZE_BYTES)
])

test.execute()

# Buckets would exceed the size limit, so more groups than buckets are created
test.file_grep(classes_mk, r'vm_classes_3')

header_bytes = sum(os.path.getsize(f) for f in test.glob_some(test.obj_dir + "/*.h"))
for var in VARS:
    entries = class_entries(var)
    for i, files in enumerate(entries):
        # No group crosses a bucket boundary
        if any(f in bucket_starts for f in files[1:]):
            test.error(var + " group " + str(i) + " spans several buckets")
        if len(files) < 2:
            continue
        group_bytes = header_bytes + sum(file_size(f) for f in files)
        # Each group together with the generated headers fits in the limit
        if group_bytes > MAX_SIZE_BYTES:
            test.error(var + " group " + str(i) + " is " + str(group_bytes) + " bytes")
        # Each group is as large as possible, the next file of its bucket would not fit
        if (i + 1 < len(entries) and entries[i + 1][0] not in bucket_starts
                and group_bytes + file_size(entries[i + 1][0]) <= MAX_SIZE_BYTES):
            test.error(var + " group " + str(i) + " of " + str(group_bytes) +
                       " bytes could include the next file")

test.passes()
