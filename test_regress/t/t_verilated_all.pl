#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vltmt => 1);

my $root = "..";

compile(
    # Can't use --coverage and --savable together, so cheat and compile inline
    verilator_flags2 => ["--cc",
                         "--coverage-toggle --coverage-line --coverage-user",
                         "--trace --vpi ",
                         "--trace-threads 1",
                         "--prof-exec", "--prof-pgo",
                         "$root/include/verilated_save.cpp"],
    threads => 2
    );

execute(
    all_run_flags => [" +verilator+prof+exec+file+/dev/null",
                      " +verilator+prof+vlt+file+/dev/null",
                      ],
    check_finished => 1,
    );

my %hit;
foreach my $file (glob("$root/include/*.cpp $root/include/*.h")) {
    $file =~ s!.*/!!;

    # This file isn't actually used by the runtime (though
    # it might be in the future? hence it's under include/)
    # It is used to build verilator.
    if ($file =~ /verilated_unordered_set_map\.h/) { next; }

    print "NEED: $file\n" if $Self->{verbose};
    $hit{$file} = 0;
}
foreach my $dfile (glob("$Self->{obj_dir}/*.d")) {
    my $wholefile = file_contents($dfile);
    foreach my $file (split /\s+/, $wholefile) {
        $file =~ s!.*/!!;
        print "USED: $file\n" if $Self->{verbose};
        $hit{$file} = 1;
    }
}

foreach my $file (sort keys %hit) {
    if (!$hit{$file}
        && $file !~ /_sc/
        && $file !~ /_fst/
        && $file !~ /_heavy/
        && ($file !~ /_thread/)) {
        error("Include file not covered by t_verilated_all test: ", $file);
    }
}

ok(1);
1;
