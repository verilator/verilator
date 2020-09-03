#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

my $stdout_filename = "$Self->{obj_dir}/$Self->{name}__test.vpp";

compile(
    verilator_flags2 => ['-DDEF_A0 -DPREDEF_COMMAND_LINE -E'],
    verilator_make_gmake => 0,
    make_top_shell => 0,
    make_main => 0,
    stdout_filename => $stdout_filename,
    );

preproc_check($Self->{top_filename}, $stdout_filename);
files_identical($stdout_filename, $Self->{golden_filename});
ok(1);

sub preproc_check {
    my $filename1 = shift;
    my $filename2 = shift;

    my @Line_Checks;
    {   # Read line comments.
        my $fh = IO::File->new($filename1) or die "%Error: $! $filename1\n";
        while (defined(my $line = $fh->getline)) {
            if ($line =~ /^Line_Preproc_Check/) {
                push @Line_Checks, $.;
            }
        }
        $fh->close;
    }
    {   # See if output file agrees.
        my $fh = IO::File->new($filename2) or die "%Error: $! $filename2\n";
        my $lineno = 0;
        while (defined(my $line = $fh->getline)) {
            $lineno++;
            if ($line =~ /^\`line\s+(\d+)/) {
                $lineno = $1 - 1;
            }
            if ($line =~ /^Line_Preproc_Check\s+(\d+)/) {
                my $linecmt = $1;
                my $check = shift @Line_Checks;
                if (!$check) { error("$filename2:$.: Extra Line_Preproc_Check\n"); }
                if ($linecmt != $check) { error("$filename2:$.: __LINE__ inserted $linecmt, exp=$check\n"); }
                if ($lineno != $check)  { error("$filename2:$.: __LINE__ on `line $lineno, exp=$check\n"); }
            }
        }
        $fh->close;
    }
    if ($Line_Checks[0]) { error("$filename2: Missing a Line_Preproc_Check\n"); }
}

1;
