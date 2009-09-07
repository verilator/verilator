#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>$Self->{v3},
	 expect=>
'%Error: t/t_var_bad_sv.v:\d+: Unexpected "do": "do" is a SystemVerilog keyword misused as an identifier.
%Error: t/t_var_bad_sv.v:\d+: Modify the Verilog-2001 code to avoid SV keywords, or use `begin_keywords or --language.
%Error: t/t_var_bad_sv.v:\d+: Unexpected "do": "do" is a SystemVerilog keyword misused as an identifier.
.*
%Error: Exiting due to.*',
	 );

ok(1);
1;
