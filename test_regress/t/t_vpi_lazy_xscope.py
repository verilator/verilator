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

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["--exe --vpi --vpi-lazy --no-l2name --stats", test.pli_filename])

# Only 'canonr's two ports; 'canon's are cones, whose ports the encoding cannot name, so
# they stay on the floor instead
test.file_grep(test.stats, r'VPI, lazy cross-scope copy descriptors\s+(\d+)', 2)
test.file_grep(test.stats, r'VPI, lazy floor residual, port \(comb-driven\)\s+(\d+)', 2)
# A per-instance source offset, so one table per instance rather than one per module class
# A cross-scope copy row: a signed Syms-relative delta, and no shape of its own - it is just a
# copy row whose source happens to live in another scope
test.file_grep_count(
    test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
    r'\{nullptr, \(int32_t\)\(\(std::ptrdiff_t\)offsetof\(\S+__Syms, \S+\)'
    r' \+ \(std::ptrdiff_t\)offsetof\(\S+ \S+\)'
    r' - \(std::ptrdiff_t\)offsetof\(\S+__Syms, \S+\)\), VLVF_LAZY_COPY\}', 2)
# The delta is narrowed to int32_t, so the emitter guards the Syms size that would overflow it
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'Symbol table too large for a 32 bit --vpi-lazy copy offset')

# 'rcanonr' and 'scanonr' are stored drivers of the same shape as 'canonr', so each would be a
# cross-scope copy too but for its type: neither has a memcpy width, which is why the count
# above is still two. Both stay retained, and their ports read through to them.
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'"rcanonr",.*VLVF_LAZY_RETAINED')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'"scanonr",.*VLVF_LAZY_RETAINED')

test.execute()

test.passes()
