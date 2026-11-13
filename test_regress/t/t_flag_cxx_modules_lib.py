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
test.clean_objs()
test.top_filename = test.t_dir + '/t_flag_cxx_modules.v'

common = [
    '--cc',
    '--cxx-modules',
    test.t_dir + '/t_flag_cxx_modules_user.cppm',
]

# Default library mode
default_dir = test.obj_dir + '/default'
test.compile(make_main=False,
             verilator_make_gmake=False,
             verilator_make_cmake=False,
             verilator_flags2=['--Mdir', default_dir] + common)
test.file_grep(default_dir + '/' + test.vm_prefix + '.mk',
               r'^lib.*\.a: .*\| \$\(VM_PREFIX\)__ALL\.a')

# --lib-create library mode
libcreate_dir = test.obj_dir + '/libcreate'
test.compile(make_main=False,
             verilator_make_gmake=False,
             verilator_make_cmake=False,
             verilator_flags2=['--Mdir', libcreate_dir] + common + ['--lib-create', 'sub'])
test.file_grep(libcreate_dir + '/' + test.vm_prefix + '.mk',
               r'^libsub\.a: .*\| \$\(VM_PREFIX\)__ALL\.a')

# Non-module builds keep the old rule without the order-only archive
plain_dir = test.obj_dir + '/plain'
test.compile(make_main=False,
             verilator_make_gmake=False,
             verilator_make_cmake=False,
             verilator_flags2=['--Mdir', plain_dir, '--cc'])
test.file_grep_not(plain_dir + '/' + test.vm_prefix + '.mk', r'\| \$\(VM_PREFIX\)__ALL\.a')
test.passes()
