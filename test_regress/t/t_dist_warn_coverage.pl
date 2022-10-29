#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use IO::File;
use strict;
use vars qw($Self);

scenarios(dist => 1);

my $root = "..";
my $Debug = $Self->{verbose};
my %Messages;
my %Outputs;

my %Suppressed;
foreach my $s (
    ' exited with ',  # driver.pl filters out
    'EOF in unterminated string',  # Instead get normal unterminated
    # Not yet analyzed
    ' is not an in/out/inout/param/interface: ',
    ' loading non-variable',
    '$fopen mode should be <= 4 characters',
    '\'foreach\' loop variable expects simple variable name',
    '--coverage and --savable not supported together',
    '--pipe-filter protocol error, unexpected: ',
    '/*verilator sformat*/ can only be applied to last argument of ',
    'Argument needed for string.',
    'Array initialization has too few elements, need element ',
    'Assert not allowed under another assert',
    'Assigned pin is neither input nor output',
    'Assignment pattern key used multiple times: ',
    'Assignment pattern with no members',
    'Assignment pattern with too many elements',
    'Attempted parameter setting of non-parameter: Param ',
    'Attempting to extend using a non-class ',
    'Can\'t find varpin scope of ',
    'Can\'t resolve module reference: \'',
    'Cannot mix DPI import, DPI export, class methods, and/or public ',
    'Cannot write preprocessor output: ',
    'Circular logic when ordering code (non-cutable edge loop)',
    'Deferred assertions must use \'#0\' (IEEE 1800-2017 16.4)',
    'Define or directive not defined: `',
    'Duplicate declaration of member name: ',
    'EOF in (*',
    'Enum names without values only allowed on numeric types',
    'Enum ranges must be integral, per spec',
    'Exceeded limit of ',
    'Extern declaration\'s scope is not a defined class',
    'Format to $display-like function must have constant format string',
    'Forward typedef used as class/package does not resolve to class/package: ',
    'Illegal +: or -: select; type already selected, or bad dimension: ',
    'Illegal bit or array select; type already selected, or bad dimension: ',
    'Illegal range select; type already selected, or bad dimension: ',
    'In defparam, instance ',
    'Interface port ',
    'Member selection of non-struct/union object \'',
    'Modport item is not a function/task: ',
    'Modport item is not a variable: ',
    'Modport item not found: ',
    'Modport not referenced as <interface>.',
    'Modport not referenced from underneath an interface: ',
    'Multiple \'{ default: } clauses',
    'Non-interface used as an interface: ',
    'Not marked as function return var',
    'Parameter not found in sub-module: Param ',
    'Parameter type pin value isn\'t a type: Param ',
    'Parameter type variable isn\'t a type: Param ',
    'Pattern replication value of 0 is not legal.',
    'Return with return value isn\'t underneath a function',
    'Select from non-array ',
    'Signals inside functions/tasks cannot be marked forceable',
    'Size-changing cast to zero or negative size',
    'Slice size cannot be zero.',
    'Slices of arrays in assignments have different unpacked dimensions, ',
    'String of ',
    'Symbol matching ',
    'Syntax Error: Range \':\', \'+:\' etc are not allowed in the instance ',
    'Syntax error parsing real: \'',
    'Syntax error: \'virtual\' not allowed before var declaration',
    'This may be because there\'s no search path specified with -I<dir>.',
    'Unexpected connection to arrayed port',
    'Unhandled attribute type',
    'Unknown Error Code: ',
    'Unknown `pragma',
    'Unknown built-in event method ',
    'Unsized numbers/parameters not allowed in streams.',
    'Unsupported LHS tristate construct: ',
    'Unsupported RHS tristate construct: ',
    'Unsupported or syntax error: Unsized range in instance or other declaration',
    'Unsupported pullup/down (weak driver) construct.',
    'Unsupported tristate construct (not in propagation graph): ',
    'Unsupported tristate port expression: ',
    'Unsupported/Illegal: Assignment pattern',
    'Unsupported/unknown built-in dynamic array method ',
    'Unsupported: $bits for queue',
    'Unsupported: $c can\'t generate wider than 64 bits',
    'Unsupported: %l in $fscanf',
    'Unsupported: %m in $fscanf',
    'Unsupported: --no-structs-packed',
    'Unsupported: 4-state numbers in this context',
    'Unsupported: Concatenation to form ',
    'Unsupported: Non-variable on LHS of built-in method \'',
    'Unsupported: Only one PSL clock allowed per assertion',
    'Unsupported: Per-bit array instantiations ',
    'Unsupported: Public functions with >64 bit outputs; ',
    'Unsupported: RHS of ==? or !=? must be ',
    'Unsupported: Ranges ignored in port-lists',
    'Unsupported: Replication to form ',
    'Unsupported: Shifting of by over 32-bit number isn\'t supported.',
    'Unsupported: Signal strengths are unsupported ',
    'Unsupported: Size-changing cast on non-basic data type',
    'Unsupported: Slice of non-constant bounds',
    'Unsupported: Unclocked assertion',
    'Unsupported: don\'t know how to deal with ',
    'Unsupported: event arrays',
    'Unsupported: left < right of bit extract: ',
    'Unsupported: modport export',
    'Unsupported: static cast to ',
    'Unsupported: super',
    'Width of :+ or :- is < 0: ',
    'Width of :+ or :- is huge; vector of over 1billion bits: ',
    'Width of bit extract isn\'t a constant',
    'Width of bit range is huge; vector of over 1billion bits: 0x',
    'dynamic new() not expected in this context (data type must be dynamic array)',
    'dynamic new() not expected in this context (expected under an assign)',
    'line_length must be multiple of 4 for BASE64',
    'new() not expected in this context',
    'no_inline not supported for tasks',
    ) { $Suppressed{$s} = 1; }

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    check();
}

ok(1);
1;

sub check {
    read_messages();
    read_outputs();

    print "Number of suppressions = ", scalar(keys %Suppressed), "\n";
    print "Coverage = ", 100 - int(100 * scalar(keys %Suppressed) / scalar(keys %Messages)), "%\n";
    print "\n";

    print "Checking for v3error/v3warn messages in sources without coverage in test_regress/t/*.out:\n";
    print "\n";

    my %used_suppressed;
  msg:
    for my $msg (sort {$Messages{$a}{fileline} cmp $Messages{$b}{fileline}} keys %Messages) {
        my $fileline = $Messages{$msg}{fileline};
        for my $output (keys %Outputs) {
            if (index($output, $msg) != -1) {
                # print "$fileline: M '$msg' HIT '$output'\n";
                next msg;
            }
        }
        # Some exceptions
        next msg if ($msg =~ /internal:/i);

        my $line = $Messages{$msg}{line};
        chomp $line;
        $line =~ s/^\s+//;

        if (%Suppressed{$msg}) {
            $used_suppressed{$msg} = 1;
            print "$fileline: Suppressed check for message in source: '$msg'\n" if $Debug;
        } else {
            error("$fileline: Missing test_regress/t/*.out test for message in source: '$msg'");
            print("  Line is: ", $line, "\n") if $Debug;
        }
    }

    for my $msg (sort keys %Suppressed) {
        if (!$used_suppressed{$msg}) {
            print "Suppression not used: '$msg'\n";
        }
  }
}

sub read_messages {
    foreach my $filename (glob "$root/src/*") {
        my $fh = IO::File->new("<$filename")
            or error("$! $filename");
        my $lineno = 0;
        my $read_next;
      line:
        while (my $origline = ($fh && $fh->getline)) {
            my $line = $origline;
            ++$lineno;
            if ($line =~ /\b(v3error|v3warn)\b\($/g) {
                $read_next = 1 if $line !~ /LCOV_EXCL_LINE/;
                next line;
            }
            if ($line =~ s/.*\b(v3error|v3warn)\b//g) {
                $read_next = 1 if $line !~ /LCOV_EXCL_LINE/;
            }
            if ($read_next) {
                $read_next = 0;
                next if $line =~ /LCOV_EXCL_LINE/;
                next if $line =~ /\\/;  # \" messes up next part
                if ($line =~ /"([^"]*)"/) {
                    my $msg = $1;
                    my $fileline = $filename . ":" . $lineno;
                    # print "FFFF $fileline: $msg    LL $line\n";
                    $Messages{$msg}{fileline} = $fileline;
                    $Messages{$msg}{line} = $origline;
                }
            }
        }
    }
    print "Number of messages = ",scalar(keys %Messages), "\n";
}

sub read_outputs {
  file:
    foreach my $filename (glob ("$root/test_regress/t/*.pl"
                                . " $root/test_regress/t/*.out"
                                . " $root/docs/gen/*.rst")) {
        next if $filename =~ /t_dist_warn_coverage/;  # Avoid our own suppressions
        my $fh = IO::File->new("<$filename")
            or error("$! $filename");
        while (my $line = ($fh && $fh->getline)) {
            if ($line =~ /^\$date/) {
                # Assume it is a VCD file
                next file;
            }
            $Outputs{$line} = 1;
        }
    }
    print "Number of outputs = ",scalar(keys %Outputs), "\n";
}

# Local Variables:
# compile-command:"./t_dist_warn_coverage.pl"
# End:
