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

# Use --debug-protect to assist debug

# This test makes randomly named .cpp/.h files, which tend to collect, so remove them first
foreach my $filename (glob ("$Self->{obj_dir}/*_PS*.cpp"
                            . " $Self->{obj_dir}/*_PS*.h"
                            . " $Self->{obj_dir}/*.d")) {
    print "rm $filename\n" if $Self->{verbose};
    unlink $filename;
}

compile(
    verilator_flags2 => ["--protect-ids",
                         "--protect-key SECRET_KEY",
                         "--trace",
                         "--coverage",
                         "-Wno-INSECURE",
                         "t/t_protect_ids_c.cpp"],
    );

execute(
    check_finished => 1,
    );

# 'to="PS"' indicates means we probably mis-protected something already protected
# Use --debug-protect to assist debugging these
file_grep_not("$Self->{obj_dir}/$Self->{VM_PREFIX}__idmap.xml", qr/to="PS/);

if ($Self->{vlt_all}) {
    # Check for secret in any outputs
    my $any;
    foreach my $filename (glob $Self->{obj_dir} . "/*.[ch]*") {
        if ($filename =~ /secret/i) {
            $Self->error("Secret found in a filename: " . $filename);
        }
        file_grep_not($filename, qr/secret/i);
        $any = 1;
    }
    $any or $Self->error("No outputs found");
}

ok(1);
1;
