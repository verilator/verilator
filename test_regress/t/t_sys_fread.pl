#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
use IO::File;
#use Data::Dumper;
use strict;
use vars qw($Self);

scenarios(simulator => 1);

sub gen {
    my $filename = shift;

    my $fh = IO::File->new(">$filename");
    for (my $copy = 0; $copy < 32; ++$copy) {
        for (my $i = 0; $i <= 255; ++$i) {
            $fh->print(chr($i));
        }
    }
}

gen("$Self->{obj_dir}/t_sys_fread.mem");

compile(
    );

execute(
    check_finished => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
