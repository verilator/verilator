#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# test whether jtree gdb command doesn't crash

scenarios(vlt => 1);

{
    my $cmd = qq{astsee_verilator -h >/dev/null 2>&1};
    print "\t$cmd\n" if $::Debug;
    system($cmd) and do { skip("No astsee installed\n"); return 1 }
}

setenv("VERILATOR_GDB", "gdb --return-child-result --batch-silent --quiet"
                        . ' -init-eval-command "set auto-load no"'
                        . " --command $ENV{VERILATOR_ROOT}/src/.gdbinit"
                        . " --command $Self->{t_dir}/t_gdb_jtree.gdb");

top_filename("t/t_dump.v");

lint(v_flags => ["--gdb", "--debug"]);

ok(1);

1;
