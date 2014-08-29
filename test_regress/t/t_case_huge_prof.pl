#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

top_filename("t/t_case_huge.v");

compile (
    verilator_flags2 => ["--stats --profile-cfuncs -CFLAGS '-pg' -LDFLAGS '-pg'"],
    );

if ($Self->{vlt}) {
    file_grep ($Self->{stats}, qr/Optimizations, Tables created\s+(\d+)/i, 10);
    file_grep ($Self->{stats}, qr/Optimizations, Combined CFuncs\s+(\d+)/i, 10);
}

unlink $_ foreach (glob "$Self->{obj_dir}/gmon.out.*");
$ENV{GMON_OUT_PREFIX} = "$Self->{obj_dir}/gmon.out";

execute (
    check_finished=>1,
    );

my $gmon_path;
$gmon_path = $_ foreach (glob "$Self->{obj_dir}/gmon.out.*");
$gmon_path or $Self->error("Profiler did not create a gmon.out");
(my $gmon_base = $gmon_path) =~ s!.*[/\\]!!;

$Self->_run(cmd=>["cd $Self->{obj_dir} && gprof $Self->{VM_PREFIX} $gmon_base > gprof.out"],
	    check_finished=>0);

$Self->_run(cmd=>["cd $Self->{obj_dir} && $ENV{VERILATOR_ROOT}/bin/verilator_profcfunc gprof.out > cfuncs.out"],
	    check_finished=>0);

file_grep ("$Self->{obj_dir}/cfuncs.out", qr/Overall summary by/);

ok(1);
1;
