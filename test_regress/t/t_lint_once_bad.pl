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
	 verilator_flags2 => ["--lint-only -Wwarn-UNUSED"],
	 verilator_make_gcc => 0,
	 fails=>1,
	 expect=>
'%Warning-UNUSED: t/t_lint_once_bad.v:\d+: Signal is not driven, nor used: unus1
%Warning-UNUSED: Use .* to disable this message.
%Warning-UNUSED: t/t_lint_once_bad.v:\d+: Signal is not driven, nor used: unus2
%Error: Exiting due to.*',
	 );

ok(1);
1;
