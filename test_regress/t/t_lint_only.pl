#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vlt => 1);

lint();

foreach my $file (glob("$Self->{obj_dir}/*t_lint_only*")) {
    next if $file =~ /simx_compile.log/;  # Made by driver.pl, not Verilator
    next if $file =~ /\.status/;  # Made by driver.pl, not Verilator
    error("%Error: Created $file, but --lint-only shouldn't create files");
}

ok(1);
1;
