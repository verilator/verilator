#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

compile(
    verilator_flags2 => ["--prefix t_flag_prefix", # should be overridden
                         "--prefix Vprefix",
                         "--exe", "--main", "--stats", "--build"],
    verilator_make_cmake => 0,
    verilator_make_gmake => 0,
    make_main => 0,
    );

execute(
    check_finished => 1,
    executable => "$Self->{obj_dir}/Vprefix",
    );

sub check_files {
    foreach my $path (glob("$Self->{obj_dir}/*")) {
        my $filename = substr $path, ((length $Self->{obj_dir}) + 1);
        next if ($filename =~ /^.*\.log$/);
        if ($filename =~ /t_flag_prefix/) {
            error("bad filename $filename");
            next;
        }
        next if ($filename =~ /^(.*\.(o|a)|Vprefix)$/);
        my $fh = IO::File->new("<$path") or error("$! $filenme");
        while (defined(my $line = $fh->getline)) {
            $line =~ s/--prefix V?t_flag_prefix//g;
            $line =~ s/obj_vlt\/t_flag_prefix//g;
            $line =~ s/t\/t_flag_prefix\.v//g;
            error("bad line in $filename: $line") if $line =~ /t_flag_prefix/;
        }
    }
}

check_files();

ok(1);
1;
