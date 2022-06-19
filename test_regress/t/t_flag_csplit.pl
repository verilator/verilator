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

while (1) {
    # Thi rule requires GNU make > 4.1 (or so, known broken in 3.81)
    #%__Slow.o: %__Slow.cpp
    #        $(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_SLOW) -c -o $@ $<
    if (make_version() < 4.1) {
        skip("Test requires GNU Make version >= 4.1");
        last;
    }

    compile(
        v_flags2 => ["--trace --output-split 1 --output-split-cfuncs 1 --exe ../$Self->{main_filename}"],
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
              "OPT_GLOBAL=-Os",
              ($param{make_flags}||""),
        ]);

    execute(
        check_finished => 1,
        );

    # Splitting should set VM_PARALLEL_BUILDS to 1 by default
    file_grep("$Self->{obj_dir}/$Self->{VM_PREFIX}_classes.mk", qr/VM_PARALLEL_BUILDS\s*=\s*1/);
    check_splits();
    check_no_all_file();
    check_gcc_flags("$Self->{obj_dir}/vlt_gcc.log");

    ok(1);
    last;
}
1;

sub check_splits {
    my $got1;
    my $gotSyms1;
    foreach my $file (glob("$Self->{obj_dir}/*.cpp")) {
        if ($file =~ /Syms__1/) {
            $gotSyms1 = 1;
        } elsif ($file =~ /__1/) {
            $got1 = 1;
        }
        check_cpp($file);
    }
    $got1 or error("No __1 split file found");
    $gotSyms1 or error("No Syms__1 split file found");
}

sub check_no_all_file {
    foreach my $file (glob("$Self->{obj_dir}/*.cpp")) {
        if ($file =~ qr/__ALL.cpp/) {
            error("__ALL.cpp file found: $file");
        }
    }
}

sub check_cpp {
    my $filename = shift;
    my $size = -s $filename;
    printf "  File %6d  %s\n", $size, $filename if $Self->{verbose};
    my $fh = IO::File->new("<$filename") or error("$! $filenme");
    my @funcs;
    while (defined(my $line = $fh->getline)) {
        if ($line =~ /^(void|IData)\s+(.*::.*){/) {
            my $func = $2;
            $func =~ s/\(.*$//;
            print "\tFunc $func\n" if $Self->{verbose};
            if ($func !~ /::_eval_initial_loop$/
                && $func !~ /::__Vconfigure$/
                && $func !~ /::trace$/
                && $func !~ /::traceInit$/
                && $func !~ /::traceFull$/
                && $func !~ /::final$/
                ) {
                push @funcs, $func;
            }
        }
    }
    if ($#funcs > 0) {
        error("Split had multiple functions in $filename\n\t" . join("\n\t", @funcs));
    }
}

sub check_gcc_flags {
    my $filename = shift;
    my $fh = IO::File->new("<$filename") or error("$! $filenme");
    while (defined(my $line = $fh->getline)) {
        chomp $line;
        print ":log: $line\n" if $Self->{verbose};
        if ($line =~ /$Self->{VM_PREFIX}\S*\.cpp/) {
            my $filetype = ($line =~ /Slow|Syms/) ? "slow" : "fast";
            my $opt = ($line !~ /-O2/) ? "slow" : "fast";
            print "$filetype, $opt, $line\n" if $Self->{verbose};
            if ($filetype ne $opt) {
                error("${filetype} file compiled as if was ${opt}: $line");
            }
        } elsif ($line =~ /\.cpp/ and $line !~ /-Os/) {
            error("library file not compiled with OPT_GLOBAL: $line");
        }
    }
}
