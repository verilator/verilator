#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 make_top_shell => 0,
	 make_main => 0,
	 v_flags2 => ["--lint-only"],
	 verilator_make_gcc => 0,
	 ) if $Last_Self->{v3};

foreach my $file (glob("obj_dir/*t_lint_only*")) {
    next if $file =~ /simx_compile.log/;  # Made by driver.pl, not Verilator
    $Last_Self->error("%Error: Created $file, but --lint-only shouldn't create files");
}

ok(1);
1;
