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

# Compile un-optimized
compile(
    verilator_flags2 => ["--stats", "--build", "-fno-dfg", "+define+REF",
                         "-Mdir", "$Self->{obj_dir}/obj_ref", "--prefix", "Vref"],
    verilator_make_gmake => 0,
    verilator_make_cmake => 0
    );

# Generate the equivalence checks
my $rdFile = "$Self->{obj_dir}/obj_ref/Vref.h";
my $wrFile = "$Self->{obj_dir}/checks.h";
my $rfh = IO::File->new("<$rdFile") or error("$! $rdFile");
my $wfh = IO::File->new(">$wrFile") or error("$! $wrFile");
while (defined(my $line = $rfh->getline)) {
    next if $line !~ /.*\b(dfg_[A-Z_]*)\b/;
    my $signal = $1;
    print $wfh "if (ref.$signal != opt.$signal) {\n";
    print $wfh "    std::cout << \"Mismatched $signal\" << std::endl;\n";
    print $wfh "    std::cout << \"Ref: 0x\" << std::hex << (ref.$signal + 0) << std::endl;\n";
    print $wfh "    std::cout << \"Opt: 0x\" << std::hex << (opt.$signal + 0) << std::endl;\n";
    print $wfh "    std::exit(1);\n";
    print $wfh "}\n";
}
close $rdFile;
close $wrFile;

# Compile optimized - also builds executable
compile(
    verilator_flags2 => ["--stats", "--build", "--exe",
                         "-Mdir", "$Self->{obj_dir}/obj_opt", "--prefix", "Vopt",
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

# Check optimizations
check("SWAP_CONST_IN_COMMUTATIVE_BINARY");
check("SWAP_NOT_IN_COMMUTATIVE_BINARY");
check("SWAP_VAR_IN_COMMUTATIVE_BINARY");
check("PUSH_BITWISE_OP_THROUGH_CONCAT");
check("PUSH_COMPARE_OP_THROUGH_CONCAT");
#check("REMOVE_WIDTH_ONE_REDUCTION"); V3Const eats this
check("PUSH_REDUCTION_THROUGH_COND_WITH_CONST_BRANCH");
check("REPLACE_REDUCTION_OF_CONST");
check("REPLACE_EXTEND");
check("PUSH_NOT_THROUGH_COND");
check("REMOVE_NOT_NOT");
check("REPLACE_NOT_NEQ");
check("REPLACE_NOT_OF_CONST");
check("REPLACE_AND_OF_NOT_AND_NOT");
check("REPLACE_AND_OF_CONST_AND_CONST");
check("REPLACE_AND_WITH_ZERO");
check("REMOVE_AND_WITH_ONES");
check("REPLACE_CONTRADICTORY_AND");
check("REPLACE_OR_OF_NOT_AND_NOT");
check("REPLACE_OR_OF_NOT_AND_NEQ");
check("REPLACE_OR_OF_CONCAT_ZERO_LHS_AND_CONCAT_RHS_ZERO");
check("REPLACE_OR_OF_CONCAT_LHS_ZERO_AND_CONCAT_ZERO_RHS");
check("REPLACE_OR_OF_CONST_AND_CONST");
check("REMOVE_OR_WITH_ZERO");
check("REPLACE_OR_WITH_ONES");
check("REPLACE_TAUTOLOGICAL_OR");
check("REMOVE_SUB_ZERO");
check("REPLACE_SUB_WITH_NOT");
check("REMOVE_REDUNDANT_ZEXT_ON_RHS_OF_SHIFT");
check("REPLACE_EQ_OF_CONST_AND_CONST");
check("REMOVE_FULL_WIDTH_SEL");
check("REMOVE_SEL_FROM_RHS_OF_CONCAT");
check("REMOVE_SEL_FROM_LHS_OF_CONCAT");
check("PUSH_SEL_THROUGH_CONCAT");
check("PUSH_SEL_THROUGH_REPLICATE");
check("PUSH_SEL_THROUGH_NOT");
check("REPLACE_SEL_FROM_SEL");
check("PUSH_SEL_THROUGH_COND");
check("PUSH_SEL_THROUGH_SHIFTL");
check("REPLACE_SEL_FROM_CONST");
check("REPLACE_CONCAT_OF_CONSTS");
check("REPLACE_NESTED_CONCAT_OF_CONSTS_ON_LHS");
check("REPLACE_NESTED_CONCAT_OF_CONSTS_ON_RHS");
check("REPLACE_CONCAT_ZERO_AND_SEL_TOP_WITH_SHIFTR");
check("REPLACE_CONCAT_SEL_BOTTOM_AND_ZERO_WITH_SHIFTL");
check("PUSH_CONCAT_THROUGH_NOTS");
check("REMOVE_CONCAT_OF_ADJOINING_SELS");
check("REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_LHS");
check("REPLACE_NESTED_CONCAT_OF_ADJOINING_SELS_ON_RHS");
check("REMOVE_COND_WITH_FALSE_CONDITION");
check("REMOVE_COND_WITH_TRUE_CONDITION");
check("SWAP_COND_WITH_NOT_CONDITION");
check("SWAP_COND_WITH_NEQ_CONDITION");
check("PULL_NOTS_THROUGH_COND");
check("REPLACE_COND_WITH_THEN_BRANCH_ZERO");
check("REPLACE_COND_WITH_THEN_BRANCH_ONES");
check("REPLACE_COND_WITH_ELSE_BRANCH_ZERO");
check("REPLACE_COND_WITH_ELSE_BRANCH_ONES");

ok(1);
1;
