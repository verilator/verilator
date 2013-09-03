#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
    v_flags2 => ["--trace --output-split 1 --output-split-cfuncs 1"],
    );

execute (
    check_finished=>1,
    );

my $got1;
foreach my $file (glob("$Self->{obj_dir}/*.cpp")) {
    $got1 = 1 if $file =~ /__1/;
    check($file);
}
$got1 or $Self->error("No __1 split file found");

ok(1);
1;


sub check {
    my $filename = shift;
    my $size = -s $filename;
    printf "  File %6d  %s\n", $size, $filename if $Self->{verbose};
    my $fh = IO::File->new("<$filename") or $Self->error("$! $filenme");
    my @funcs;
    while (defined (my $line = $fh->getline)) {
	if ($line =~ /^(void|IData)\s+(.*::.*)/) {
	    my $func = $2;
	    $func =~ s/\(.*$//;
	    print "\tFunc $func\n" if $Self->{verbose};
	    if ($func !~ /::_eval_initial_loop$/
		&& $func !~ /::__Vconfigure$/
		&& $func !~ /::trace$/
		&& $func !~ /::traceInit$/
		&& $func !~ /::traceFull$/
		) {
		push @funcs, $func;
	    }
	}
    }
    if ($#funcs > 0) {
	$Self->error("Split had multiple functions in $filename\n\t".join("\n\t",@funcs));
    }
}
