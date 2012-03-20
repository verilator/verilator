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
	 fails=>1,
	 expect=>
q{%Warning-ENDLABEL: t/t_hierarchy_identifier_bad.v:\d+: End label 'if_cnt_finish_bad' does not match begin label 'if_cnt_finish'
%Warning-ENDLABEL: Use .*
%Warning-ENDLABEL: t/t_hierarchy_identifier_bad.v:\d+: End label 'generate_for_bad' does not match begin label 'generate_for'
%Warning-ENDLABEL: t/t_hierarchy_identifier_bad.v:\d+: End label 'generate_if_if_bad' does not match begin label 'generate_if_if'
%Warning-ENDLABEL: t/t_hierarchy_identifier_bad.v:\d+: End label 'generate_if_else_bad' does not match begin label 'generate_if_else'
%Warning-ENDLABEL: t/t_hierarchy_identifier_bad.v:\d+: End label 't_bad' does not match begin label 't'
%Error: Exiting due to.*},
     );

ok(1);
1;
