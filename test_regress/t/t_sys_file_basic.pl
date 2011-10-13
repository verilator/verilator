#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

unlink("$Self->{obj_dir}/t_sys_file_basic_test.log");

compile (
    v_flags2 => ['+incdir+../include'],
    # Build without cached objects, see bug363
    verilator_flags2 => ["--exe ../$Self->{main_filename}"],
    make_flags=>'MAKE_MAIN=0 VM_PARALLEL_BUILDS=0',
    );

execute (
    check_finished=>1,
    );

file_grep ("$Self->{obj_dir}/t_sys_file_basic_test.log",
qr/\[0\] hello v=12345667
\[0\] Hello2
/);

ok(1);
1;
