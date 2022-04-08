#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t/t_flag_csplit.v");

while (1) {
    # Thi rule requires GNU make > 4.1 (or so, known broken in 3.81)
    #%__Slow.o: %__Slow.cpp
    #        $(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_SLOW) -c -o $@ $<
    if (make_version() < 4.1) {
        skip("Test requires GNU Make version >= 4.1");
        last;
    }

    compile(
        v_flags2 => ["--trace --output-split 0 --exe ../$Self->{main_filename}"],
        verilator_make_gmake => 0,
        );

    # We don't use the standard test_regress rules, as want to test the rules
    # properly build
    run(logfile => "$Self->{obj_dir}/vlt_gcc.log",
        tee => $self->{verbose},
        cmd=>[$ENV{MAKE},
              "-C " . $Self->{obj_dir},
              "-f $Self->{VM_PREFIX}.mk",
              "-j 4",
              "VM_PREFIX=$Self->{VM_PREFIX}",
              "TEST_OBJ_DIR=$Self->{obj_dir}",
              "CPPFLAGS_DRIVER=-D".uc($Self->{name}),
              ($opt_verbose ? "CPPFLAGS_DRIVER2=-DTEST_VERBOSE=1" : ""),
              "OPT_FAST=-O2",
              "OPT_SLOW=-O0",
              ($param{make_flags}||""),
        ]);

    execute(
        check_finished => 1,
        );

    # Never spliting, so should set VM_PARALLEL_BUILDS to 0 by default
    file_grep("$Self->{obj_dir}/$Self->{VM_PREFIX}_classes.mk", qr/VM_PARALLEL_BUILDS\s*=\s*0/);
    check_no_splits();
    check_all_file();
    check_gcc_flags("$Self->{obj_dir}/vlt_gcc.log");

    ok(1);
    last;
}
1;

sub check_no_splits {
    foreach my $file (glob("$Self->{obj_dir}/*.cpp")) {
        $file =~ s/__024root//;
        if ($file =~ qr/__[1-9]/) {
            error("Split file found: $file");
        }
    }
}

sub check_all_file {
    foreach my $file (glob("$Self->{obj_dir}/*.cpp")) {
        if ($file =~ qr/__ALL.cpp/) {
            return;
        }
    }
    error("__ALL.cpp file not found");
}

sub check_gcc_flags {
    my $filename = shift;
    my $fh = IO::File->new("<$filename") or error("$! $filenme");
    while (defined(my $line = $fh->getline)) {
        chomp $line;
        print ":log: $line\n" if $Self->{verbose};
        if ($line =~ /\.cpp/ && $line =~ qr/-O0/) {
            error("File built as slow (should be in __ALL.cpp) : $line");
        }
    }
}
