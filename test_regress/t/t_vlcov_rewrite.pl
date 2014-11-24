#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

foreach my $basename ("t_vlcov_data_a.dat",
		      "t_vlcov_data_b.dat",
		      "t_vlcov_data_c.dat",
		      "t_vlcov_data_d.dat",
    ) {
    $Self->_run(cmd=>["../bin/verilator_coverage",
		      "t/${basename}",
		      "--write", "$Self->{obj_dir}/${basename}"
		],
		tee=>0,
	);
    ok(files_identical("$Self->{obj_dir}/${basename}", "t/${basename}"));
}
1;
