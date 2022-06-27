#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use File::Spec;

scenarios(simulator => 1);

my $self = $Self;
my $child_dir = "$Self->{obj_dir}_child";
mkdir $child_dir;

# Compile the child
{
    my @cmdargs = $Self->compile_vlt_cmd
        (VM_PREFIX => "$Self->{VM_PREFIX}_child",
         top_filename => "$Self->{name}_child.v",
         verilator_flags => ["-cc", "-Mdir", "${child_dir}", "--debug-check"],
         # Can't use multi threading (like hier blocks), but needs to be thread safe
         threads => $Self->{vltmt} ? 1 : 0,
        );

    run(logfile => "${child_dir}/vlt_compile.log",
        cmd => \@cmdargs);

    run(logfile => "${child_dir}/vlt_gcc.log",
        cmd => ["cd ${child_dir} && ",
                $ENV{MAKE}, "-f" . getcwd() . "/Makefile_obj",
                "CPPFLAGS_DRIVER=-D" . uc($self->{name}),
                ($opt_verbose ? "CPPFLAGS_DRIVER2=-DTEST_VERBOSE=1" : ""),
                "VM_PREFIX=$self->{VM_PREFIX}_child",
                "V$self->{name}_child__ALL.a",  # bypass default rule, make archive
                ($param{make_flags}||""),
        ]);
}

# Compile the parent (might be with other than verilator)
compile(
    v_flags2 => [File::Spec->rel2abs("${child_dir}/V$self->{name}_child__ALL.a"),
                 # TODO would be nice to have this in embedded archive
                 "t/t_embed1_c.cpp"],
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
