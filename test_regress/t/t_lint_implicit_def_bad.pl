#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 verilator_flags2 => ["--lint-only -Wall -Wno-DECLFILENAME"],
	 fails=>1,
	 expect=>
'%Warning-IMPLICIT: t/t_lint_implicit_def_bad.v:\d+: Signal definition not found, creating implicitly: imp_warn
%Warning-IMPLICIT: Use "/\* verilator lint_off IMPLICIT \*/" and lint_on around source to disable this message.
%Error: t/t_lint_implicit_def_bad.v:\d+: Signal definition not found, and implicit disabled with `default_nettype: imp_err
%Error: Exiting due to.*',
	 );

ok(1);
1;

