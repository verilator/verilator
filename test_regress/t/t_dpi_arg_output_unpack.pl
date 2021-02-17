#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2020 by Geza Lore. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

if ($Self->{nc}) {
    # For NC, compile twice, first just to generate DPI headers
    compile(
        nc_flags2 => ["+ncdpiheader+$Self->{obj_dir}/dpi-exp.h",
                      "+ncdpiimpheader+$Self->{obj_dir}/dpi-imp.h"]
        );
}

compile(
    v_flags2 => ["t/$Self->{name}.cpp"],
    # --no-decoration so .out file doesn't comment on source lines
    verilator_flags2 => ["-Wall -Wno-DECLFILENAME --no-decoration"],
    # NC: Gdd the obj_dir to the C include path
    nc_flags2 => ["+ncscargs+-I$Self->{obj_dir}"],
    # ModelSim: Generate DPI header, add obj_dir to the C include path
    ms_flags2 => ["-dpiheader $Self->{obj_dir}/dpi.h",
                  "-ccflags -I$Self->{obj_dir}"],
    );

if ($Self->{vlt_all}) {
    files_identical("$Self->{obj_dir}/$Self->{VM_PREFIX}__Dpi.h",
                    "t/$Self->{name}__Dpi.out");
}

execute(
    check_finished => 1,
    );

ok(1);
1;
