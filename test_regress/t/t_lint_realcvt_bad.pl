#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 make_top_shell => 0,
	 make_main => 0,
	 v_flags2 => ["--lint-only -Wwarn-REALCVT"],
	 verilator_make_gcc => 0,
	 fails=>1,
	 expect=>
'%Warning-REALCVT: t/t_lint_realcvt_bad.v:\d+: Implicit conversion of real to integer
%Warning-REALCVT: Use .* to disable this message.
%Error: Exiting due to.*',
    );

ok(1);
1;
