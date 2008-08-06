#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_assert_cover.v");

compile (
	 v_flags2 => [$Last_Self->{v3}?'--assert --sp --coverage-user':''],
	 nc_flags2 => ["+nccovoverwrite +nccoverage+all +nccovtest+$Last_Self->{name}"]
	 );

execute (
	 check_finished=>1,
	 );

if ($Last_Self->{nc}) {
    my $name = $Last_Self->{name};
    my $cf = "obj_dir/${name}__nccover.cf";
    {
	my $fh = IO::File->new(">$cf") or die "%Error: $! writing $cf,";
	$fh->printf("report_summary -module *\n");
	$fh->printf("report_detail -both -module *\n");
	$fh->printf("report_html -both -module * > obj_dir/${name}__nccover.html\n");
	$fh->close;
    }
    $Last_Self->_run (logfile=>"obj_dir/${name}__nccover.log",
		      tee=>0,
		      cmd=>[($ENV{VERILATOR_ICCR}||'iccr'),
			    "-test ${name} ${cf}"]);
}

file_grep ("obj_dir/$Last_Self->{name}_simx.log", qr/COVER: Cyc==4/);
file_grep ("obj_dir/$Last_Self->{name}_simx.log", qr/COVER: Cyc==5/);
file_grep ("obj_dir/$Last_Self->{name}_simx.log", qr/COVER: Cyc==6/);
file_grep ($Last_Self->{coverage_filename}, qr/cyc_eq_5.*,c=>[^0]/);

ok(1);
1;
