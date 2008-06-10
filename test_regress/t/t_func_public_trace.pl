#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

my $pubtask = ($Last_Self->{v3} && verilator_version() =~ /\(public_tasks\)/);  # TBD

top_filename("t/t_func_public.v");

compile (
	 v_flags2 => [($pubtask?'-DVERILATOR_PUBLIC_TASKS':''), "--trace"],
	 fails => $fail,
	 );

execute (
	 check_finished=>1,
	 );

ok(1);
1;
