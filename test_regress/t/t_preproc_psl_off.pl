#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

my $stdout_filename = "obj_dir/$Last_Self->{name}__test.vpp";

top_filename("t/t_preproc_psl.v");

if (!$Last_Self->{v3}) {
    ok(1);
} else {
    compile (
	     v_flags2 => ['-E'],
	     verilator_make_gcc=>0,
	     stdout_filename => $stdout_filename,
	     );
    ok(files_identical($stdout_filename, "t/$Last_Self->{name}.out"));
}

1;
