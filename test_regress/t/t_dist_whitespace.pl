#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

my $root = "..";
my $Debug;

### Must trim output before and after our file list
my %files = %{get_manifest_files($root)};

foreach my $file (sort keys %files) {
    my $contents = file_contents("$root/$file");
    if ($file =~ /\.out$/) {
	# Ignore golden files
    } elsif ($contents =~ /[\001\002\003\004\005\006]/) {
	# Ignore binrary files
    } elsif ($contents =~ /[ \t]\n/) {
	$warns{$file} = "File contains trailing whitespace: $file";
    }
}

if (keys %warns) {
    # First warning lists everything as that's shown in the driver summary
    $Self->error("Files have whitespace errors: ",join(' ',sort keys %warns));
    foreach my $file (sort keys %warns) {
	$Self->error($warns{$file});
    }
}

ok(1);
1;

sub get_manifest_files {
    my $root = shift;
    `cd $root && make dist-file-list`;
    my $manifest_files = `cd $root && make dist-file-list`;
    $manifest_files =~ s!.*begin-dist-file-list:!!sg;
    $manifest_files =~ s!end-dist-file-list:.*$!!sg;
    print "MF $manifest_files\n" if $Self->{verbose};
    my %files;
    foreach my $file (split /\s+/,$manifest_files) {
	next if $file eq '';
	$files{$file} |= 1;
    }
    return \%files;
}
