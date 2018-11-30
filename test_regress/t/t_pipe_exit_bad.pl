#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vlt => 1);

top_filename("t/t_pipe_filter.v");

compile(
    verilator_flags2 => ['-E --pipe-filter \'perl t/t_pipe_exit_bad.pf\' '],
    verilator_make_gcc => 0,
    make_top_shell => 0,
    make_main => 0,
    stdout_filename => $stdout_filename,
    fails => 1,
    expect =>
'%Error: t_pipe_exit_bad.pf: Intentional bad exit status....*',
    );
ok(1);

1;
