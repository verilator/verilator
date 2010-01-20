#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010-2010 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{golden_out} ||= "t/$Self->{name}.out";
my $stdout_filename = "$Self->{obj_dir}/$Self->{name}__test.vpp";

if (!$Self->{v3}) {
    ok(1);
} else {
    compile (
	v_flags2 => ['-E --pipe-filter \'perl t/t_pipe_filter.pf\' '],
	verilator_make_gcc=>0,
	stdout_filename => $stdout_filename,
	);
    ok(files_identical($stdout_filename, $Self->{golden_out}));
}

1;
