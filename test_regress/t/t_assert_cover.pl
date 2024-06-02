#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_assert_cover.v");

compile(
    verilator_flags2 => ['--assert --cc --coverage-user'],
    nc_flags2 => ["+nccovoverwrite +nccoverage+all +nccovtest+$Self->{name}"]
    );

execute(
    check_finished => 1,
    );

if ($Self->{nc}) {
    my $name = $Self->{name};
    my $cf = "$Self->{obj_dir}/${name}__nccover.cf";
    {
        my $fh = IO::File->new(">$cf") or die "%Error: $! writing $cf,";
        $fh->printf("report_summary -module *\n");
        $fh->printf("report_detail -both -instance *\n");
        $fh->printf("report_html -both -instance * > $Self->{obj_dir}/${name}__nccover.html\n");
        $fh->close;
    }
    run(logfile => "$Self->{obj_dir}/${name}__nccover.log",
        tee => 0,
        cmd => [($ENV{VERILATOR_ICCR} || 'iccr'),
                "-test ${name} ${cf}"]);
}

file_grep($Self->{run_log_filename}, qr/COVER: Cyc==4/);
file_grep($Self->{run_log_filename}, qr/COVER: Cyc==5/);
file_grep($Self->{run_log_filename}, qr/COVER: Cyc==6/);

# Allow old SystemC::Coverage format dump, or new binary dump
file_grep($Self->{coverage_filename}, qr/(cyc_eq_5.*,c=>[^0]|cyc_eq_5.* [1-9][0-9]*\n)/);

ok(1);
1;
