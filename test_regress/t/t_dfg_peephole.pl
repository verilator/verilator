#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

$Self->{sim_time} = 2000000;

# Read optimizations
my @optimizations = ();
{
    my $hdrFile = "../src/V3DfgPeephole.h";
    my $hdrFh = IO::File->new("<$hdrFile") or error("$! $hdrFile");
    my $prevOpt = "";
    my $lineno = 0;
    while (defined(my $line = $hdrFh->getline)) {
        $lineno = $lineno + 1;
        next if $line !~ /^\s*_FOR_EACH_DFG_PEEPHOLE_OPTIMIZATION_APPLY\(macro, (\w+)\)/;
        my $opt = $1;
        error("$hdrFile:$linenno: '$opt; is not in sorted order") if $prevOpt gt $opt;
        $prevOpt = $opt;
        push @optimizations, $opt;
    }
    error("no optimizations defined in $hdrFile") if scalar @optimizations == 0;
}

# Generate the equivalence checks and declaration boilerplate
my $rdFile = "$Self->{top_filename}";
my $plistFile = "$Self->{obj_dir}/portlist.vh";
my $pdeclFile = "$Self->{obj_dir}/portdecl.vh";
my $checkFile = "$Self->{obj_dir}/checks.h";
my $rdFh = IO::File->new("<$rdFile") or error("$! $rdFile");
my $plistFh = IO::File->new(">$plistFile") or error("$! $plistFile");
my $pdeclFh = IO::File->new(">$pdeclFile") or error("$! $pdeclFile");
my $checkFh = IO::File->new(">$checkFile") or error("$! $checkFile");
while (defined(my $line = $rdFh->getline)) {
    next if $line !~ /^\s*.*`signal\((\w+),/;
    my $signal = $1;
    print $plistFh "$signal,\n";
    print $pdeclFh "output $signal;\n";
    print $checkFh "if (ref.$signal != opt.$signal) {\n";
    print $checkFh "    std::cout << \"Mismatched $signal\" << std::endl;\n";
    print $checkFh "    std::cout << \"Ref: 0x\" << std::hex << (ref.$signal + 0) << std::endl;\n";
    print $checkFh "    std::cout << \"Opt: 0x\" << std::hex << (opt.$signal + 0) << std::endl;\n";
    print $checkFh "    std::exit(1);\n";
    print $checkFh "}\n";
}
close $rdFile;
close $wrFile;


# Compile un-optimized
compile(
    verilator_flags2 => ["--stats", "--build", "-fno-dfg", "+incdir+$Self->{obj_dir}",
                         "-Mdir", "$Self->{obj_dir}/obj_ref", "--prefix", "Vref"],
    verilator_make_gmake => 0,
    verilator_make_cmake => 0
    );

# Compile optimized - also builds executable
compile(
    verilator_flags2 => ["--stats", "--build", "--exe", "+incdir+$Self->{obj_dir}",
                         "-Mdir", "$Self->{obj_dir}/obj_opt", "--prefix", "Vopt",
                         "-fno-const-before-dfg", # Otherwise V3Const makes testing painful
                         "--dump-dfg", # To fill code coverage
                         "-CFLAGS \"-I .. -I ../obj_ref\"",
                         "../obj_ref/Vref__ALL.a",
                         "../../t/$Self->{name}.cpp"],
    verilator_make_gmake => 0,
    verilator_make_cmake => 0
    );

# Execute test to check equivalence
execute(
    executable => "$Self->{obj_dir}/obj_opt/Vopt",
    check_finished => 1,
    );

sub check {
  my $name = shift;
  $name = lc $name;
  $name =~ s/_/ /g;
  file_grep("$Self->{obj_dir}/obj_opt/Vopt__stats.txt", qr/DFG\s+(pre|post) inline Peephole, ${name}\s+([1-9]\d*)/i);
}

# Check all optimizations defined in
foreach my $opt (@optimizations) {
    check($opt);
}

ok(1);
1;
