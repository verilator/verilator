#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

my $pubtask = ($Self->{v3} && verilator_version() =~ /\(public_tasks\)/);  # TBD

top_filename("t/t_func_public.v");

compile (
	 verilator_flags2 => [($pubtask?'-DVERILATOR_PUBLIC_TASKS':''), "--trace"],
	 fails => $fail,
	 );

execute (
	 check_finished=>1,
	 );

ok(1);
1;
