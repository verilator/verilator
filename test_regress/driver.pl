#!/usr/bin/perl -w
# $Id$
######################################################################
#
# This program is Copyright 2003-2005 by Wilson Snyder.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of either the GNU General Public License or the
# Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

require 5.006_001;
BEGIN {
    if (my $Project=($ENV{DIRPROJECT}||$ENV{PROJECT})) {
	# Magic to allow author testing of perl packages in local directory
	require "$Project/hw/utils/perltools/boot.pl";
    }
}

use Getopt::Long;
use IO::File;
use Pod::Usage;
use Data::Dumper;
use strict;
use vars qw ($Debug %Vars $Driver $Fork);

$::Driver = 1;

eval "use Parallel::Forker; \$Fork=Parallel::Forker->new();";
$Fork = Forker->new() if !$Fork;
$SIG{CHLD} = sub { $Fork->sig_child() if $Fork; };
$SIG{TERM} = sub { $Fork->kill_tree_all('TERM') if $Fork; die "Quitting...\n"; };

#======================================================================

#======================================================================
# main

autoflush STDOUT 1;
autoflush STDERR 1;

our @Orig_ARGV = @ARGV;
our @Orig_ARGV_Sw;  foreach (@Orig_ARGV) { push @Orig_ARGV_Sw, $_ if /^-/ && !/^-j/; }

$Debug = 0;
my @opt_tests;
my $opt_nc;
my $opt_vcs;
my $opt_v3;
my $opt_stop;
my $opt_optimize;
my $opt_gdb;
my $opt_jobs = 1;
my $Opt_Verilated_Debug;
if (! GetOptions (
		  "help"	=> \&usage,
		  "debug"	=> \&debug,
		  "vcs!"	=> \$opt_vcs,
		  "verilated_debug!"	=> \$Opt_Verilated_Debug,
		  "j=i"		=> \$opt_jobs,
		  "v3!"		=> \$opt_v3,
		  "nc!"		=> \$opt_nc,
		  "gdb!"	=> \$opt_gdb,
		  "stop!"	=> \$opt_stop,
		  "optimize:s"	=> \$opt_optimize,
		  "<>"		=> \&parameter,
		  )) {
    usage();
}
$Fork->max_proc($opt_jobs);

if (!$opt_vcs && !$opt_nc && !$opt_v3) {
    $opt_v3 = 1;
}

if ($#opt_tests<0) {
    push @opt_tests, glob ("t/*.pl");
}

mkdir "obj_dir";
mkdir "logs";

my $okcnt=0; my $failcnt=0;
my @fails;

foreach my $testpl (@opt_tests) {
    one_test(pl_filename => $testpl, vcs=>1) if $opt_vcs;
    one_test(pl_filename => $testpl, nc=>1) if $opt_nc;
    one_test(pl_filename => $testpl, 'v3'=>1) if $opt_v3;
}

$Fork->wait_all();   # Wait for all children to finish

sub one_test {
    my @params = @_;
    $Fork->schedule
	(
	 run_on_start => sub {
	     print ("="x70,"\n");
	     my $test = new VTest(@params);
	     $test->oprint("="x50,"\n");
	     unlink $test->{status_filename};
	     $test->read;
	     if ($test->ok) {
		 $test->oprint("Test PASSED\n");
	     } else {
		 $test->error("Missing ok\n") if !$test->errors;
		 $test->oprint("%Error: $test->{errors}\n");
	     }
	     $test->write_status;
	 },
	 run_on_finish => sub {
	     my $test = new VTest(@params);
	     $test->read_status;
	     if ($test->ok) {
		 $okcnt++;
	     } else {
		 $test->oprint("FAILED: ","*"x60,"\n");
		 push @fails, "\t#".$test->soprint("%Error: $test->{errors}\n");
		 push @fails, "\t\tmake && ( cd test_regress ; "
		     .$test->{pl_filename}." ".join(' ',@Orig_ARGV_Sw)." )\n";
		 $failcnt++;
		 if ($opt_stop) { die "%Error: --stop and errors found\n"; }
	     }
	 },
	 )->ready();
}

print "\n";
print "="x70,"\n";
print "TESTS Passed $okcnt Failed $failcnt\n";
foreach my $f (@fails) {
    chomp $f;
    print "$f\n";
}
print "TESTS Passed $okcnt Failed $failcnt\n";
exit(10) if $failcnt;

#----------------------------------------------------------------------

sub usage {
    print '$Id$ ', "\n";
    pod2usage(-verbose=>2, -exitval => 2);
    exit (1);
}

sub debug {
    $Debug = 1;
}

sub parameter {
    my $param = shift;
    if ($param =~ /\.pl/) {
	push @opt_tests, $param;
    } else {
	die "%Error: Unknown parameter: $param\n";
    }
}
 
#######################################################################
#######################################################################
#######################################################################
#######################################################################
# Test class

package VTest;
use Data::Dumper;
use Carp;
use Cwd;

use vars qw ($Last_Self);
use strict;

sub new {
    my $class = shift;
    my $self = {
	name => undef, 		# Set below, name of this test
	mode => "",
	pl_filename => undef,	# Name of .pl file to get setup from
	make_top_shell => 1,	# Make a default __top.v file
	make_main => 1,		# Make __main.cpp
	# All compilers
	v_flags => [split(/\s+/," -f input.vc")],
	v_flags2 => [],  # Overridden in some sim files
	v_other_filenames => [],	# After the filename so we can spec multiple files
	# VCS
	vcs => 0,
	vcs_flags => [split(/\s+/,"+cli -I +define+vcs+1 -q +v2k")],
	# NC
	nc => 0,
	nc_flags => [split(/\s+/,"+licqueue +nowarn+LIBNOU +define+nc=1 -q +assert +sv31a")],
	# Verilator
	'v3' => 0,
	verilator_flags => [split(/\s+/,"-cc")],
	verilator_make_gcc => 1,
	stdout_filename => undef,	# Redirect stdout
	@_};
    bless $self, $class;

    $self->{name} ||= $1 if $self->{pl_filename} =~ m!.*/([^/]*)\.pl$!;
    $self->{mode} ||= "vcs" if $self->{vcs};
    $self->{mode} ||= "v3" if $self->{v3};
    $self->{mode} ||= "nc" if $self->{nc};
    $self->{VM_PREFIX} ||= "V".$self->{name};
    $self->{stats} ||= "obj_dir/V".$self->{name}."__stats.txt";
    $self->{status_filename} ||= "obj_dir/V".$self->{name}.".status";
    $self->{coverage_filename} ||= "obj_dir/V".$self->{name}."_coverage.pl";
    ($self->{top_filename} = $self->{pl_filename}) =~ s/\.pl$/\.v/;
    if (!$self->{make_top_shell}) {
	$self->{top_shell_filename} = $self->{top_filename};
    } else {
	$self->{top_shell_filename} = "obj_dir/$self->{VM_PREFIX}__top.v";
    }
    return $self;
}

sub soprint {
    my $self = shift;
    my $str = "$self->{mode}/$self->{name}: ".join('',@_);
    $str =~ s/\n\n+$/\n/s;
    return $str;
}

sub oprint {
    my $self = shift;
    print $self->soprint(@_);
}

sub error {
    my $self = shift;
    my $msg = join('',@_);
    warn "%Warning: $self->{mode}/$self->{name}: ".$msg."\n";
    $self->{errors} ||= $msg;
}

sub read {
    my $self = shift;
    # Read the control file
    (-r $self->{pl_filename})
	or return $self->error("Can't open $self->{pl_filename}\n");
    $Last_Self = $self;
    delete $INC{$self->{pl_filename}};
    require $self->{pl_filename};
}

sub write_status {
    my $self = shift;
    my $filename = $self->{status_filename};
    my $fh = IO::File->new($filename,"w") or die "%Error: $! $filename,";
    print $fh Dumper($self);
    print $fh "1;";
    $fh->close();
}

sub read_status {
    my $self = shift;
    my $filename = $self->{status_filename};
    use vars qw($VAR1);
    local $VAR1;
    require $filename or die "%Error: $! $filename,";
    %{$self} = %{$VAR1};
}

#----------------------------------------------------------------------
# Methods invoked by tests

sub compile {
    my $self = (ref $_[0]? shift : $Last_Self);
    my %param = (%{$self}, @_);	   # Default arguments are from $self
    return 1 if $self->errors;
    $self->oprint("Compile\n");

    $self->{sp} = 1 if (join(' ',@{$param{v_flags}},@{$param{v_flags2}}) =~ /-sp\b/);
    $self->{trace} = 1 if (join(' ',@{$param{v_flags}},@{$param{v_flags2}}) =~ /-trace\b/);
    $self->{coverage} = 1 if (join(' ',@{$param{v_flags}},@{$param{v_flags2}}) =~ /-coverage\b/);

    if ($param{vcs}) {
	$self->_make_top();
	$self->_run(logfile=>"obj_dir/".$self->{name}."_vcs_compile.log",
		    fails=>$param{fails},
		    cmd=>["vcs",
			  @{$param{vcs_flags}},
			  @{$param{v_flags}},
			  @{$param{v_flags2}},
			  $param{top_filename},
			  $param{top_shell_filename},
			  @{$param{v_other_filenames}},
			  ]);
    }
    if ($param{nc}) {
	$self->_make_top();
	$self->_run(logfile=>"obj_dir/".$self->{name}."_nc_compile.log",
		    fails=>$param{fails},
		    cmd=>["ncverilog",
			  @{$param{nc_flags}},
			  @{$param{v_flags}},
			  @{$param{v_flags2}},
			  $param{top_filename},
			  $param{top_shell_filename},
			  @{$param{v_other_filenames}},
			  ]);
    }
    if ($param{v3}) {
	$opt_gdb="gdbrun" if defined $opt_gdb;
	unshift @{$param{verilator_flags}}, "--gdb $opt_gdb" if $opt_gdb;
	unshift @{$param{verilator_flags}}, "--debug" if $::Debug;
#	unshift @{$param{verilator_flags}}, "--trace";
	if (defined $opt_optimize) {
	    my $letters = "";
	    if ($opt_optimize =~ /[a-zA-Z]/) {
		$letters = $opt_optimize;
	    } else {  # Randomly turn on/off different optimizations
		foreach my $l ('a'..'z') {
		    $letters .= ((rand() > 0.5) ? $l : uc $l);
		}
		unshift @{$param{verilator_flags}}, "--trace" if rand() > 0.5;
		unshift @{$param{verilator_flags}}, "--coverage" if rand() > 0.5;
	    }
	    unshift @{$param{verilator_flags}}, "--O".$letters;
	}

	my @v3args = ("perl","../bin/verilator",
		      "--prefix ".$self->{VM_PREFIX},
		      @{$param{verilator_flags}},
		      @{$param{v_flags}},
		      @{$param{v_flags2}},
		      $param{top_filename},
		      @{$param{v_other_filenames}},
		      ($param{stdout_filename}?"> ".$param{stdout_filename}:""),
		      );
	if ($self->sp && !defined $ENV{SYSTEMC}) {
	    $self->error("Test requires SystemC; ignore error since not installed\n");
	    return 1;
	}

	$self->_run(logfile=>"obj_dir/".$self->{name}."_simx_compile.log",
		    fails=>$param{fails},
		    expect=>$param{expect},
		    cmd=>\@v3args);
	return 1 if $self->errors;

	if (!$param{fails} && $param{verilator_make_gcc}) {
	    if ($param{make_main}) {
		$self->_make_main();
	    }
	    if ($self->sp) {
		$self->_sp_preproc(%param);
	    }
	    $self->oprint("GCC\n");
	    $self->_run(logfile=>"obj_dir/".$self->{name}."_simx_gcc.log",
			cmd=>["cd obj_dir && ",
			      "make", "-f".getcwd()."/Makefile_obj",
			      "VM_PREFIX=$self->{VM_PREFIX}",
			      ($param{make_main}?"":"MAKE_MAIN=0"),
			      "$self->{VM_PREFIX}",  # not default, as we don't need archive
			      ]);
	}
    }
    return 1;
}

sub execute {
    my $self = (ref $_[0]? shift : $Last_Self);
    return 1 if $self->errors;
    my %param = (%{$self}, @_);	   # Default arguments are from $self
    $self->oprint("Run\n");
    if ($param{vcs}) {
	#my $fh = IO::File->new("simv.key","w") or die "%Error: $! simv.key,";
	#$fh->print("quit\n"); $fh->close;
	$self->_run(logfile=>"obj_dir/".$self->{name}."_simv.log",
		    cmd=>["./simv",],
		    %param,
		    expect=>undef,	# vcs expect isn't the same
		    );
    }
    if ($param{v3}
	#&& (!$param{needs_v4} || -r "$ENV{VERILATOR_ROOT}/src/V3Gate.cpp")
	) {
	$self->_run(logfile=>"obj_dir/".$self->{name}."_simx.log",
		    cmd=>["obj_dir/$param{VM_PREFIX}",
			  ],
		    %param,
		    );
    }
}

#----------------------------------------------------------------------
# Accessors

sub ok {
    my $self = (ref $_[0]? shift : $Last_Self);
    $self->{ok} = $_[0] if defined $_[0];
    $self->{ok} = 0 if $self->{errors};
    return $self->{ok};
}

sub errors {
    my $self = (ref $_[0]? shift : $Last_Self);
    return $self->{errors};
}

sub top_filename {
    my $self = (ref $_[0]? shift : $Last_Self);
    $self->{top_filename} = shift if defined $_[0];
    return $self->{top_filename};
}

sub sp {
    my $self = (ref $_[0]? shift : $Last_Self);
    return $self->{sp};
}

#----------------------------------------------------------------------

sub _run {
    my $self = (ref $_[0]? shift : $Last_Self);
    my %param = (@_);
    my $command = join(' ',@{$param{cmd}});
    print "\t$command\n";

    if ($param{logfile}) {
	open(SAVEOUT, ">&STDOUT") or die "%Error: Can't dup stdout";
	open(SAVEERR, ">&STDERR") or die "%Error: Can't dup stderr";
	if (0) {close(SAVEOUT); close(SAVEERR);}	# Prevent unused warning
	open(STDOUT, "|tee $param{logfile}") or die "%Error: Can't redirect stdout";
	open(STDERR, ">&STDOUT") or die "%Error: Can't dup stdout";
	autoflush STDOUT 1;
	autoflush STDERR 1;
    }

    system "$command";
    my $status = $?;
    flush STDOUT;
    flush STDERR;

    if ($param{logfile}) {
	open (STDOUT, ">&SAVEOUT");
	open (STDERR, ">&SAVEERR");
    }

    if (!$param{fails} && $status) {
	$self->error("Exec of $param{cmd}[0] failed\n");
    }
    if ($param{fails} && $status) {
	print "(Exec expected to fail, and did.)\n";
    }
    if ($param{fails} && !$status) {
	$self->error("Exec of $param{cmd}[0] ok, but expected to fail\n");
    }
    return if $self->errors;

    # Read the log file a couple of times to allow for NFS delays
    for (my $try=7; $try>=0; $try--) {
	sleep 1 if ($try!=7);
	my $moretry = $try!=0;

	my $fh = IO::File->new($param{logfile},"r");
	next if !$fh && $moretry;
	local $/; undef $/;
	my $wholefile = <$fh>;
	$fh->close();

	# Strip debugging comments
	$wholefile =~ s/^- [^\n]+\n//mig;
	$wholefile =~ s/^- [a-z.0-9]+:\d+:[^\n]+\n//mig;
	$wholefile =~ s/^dot [^\n]+\n//mig;

        # Finished?
	if ($param{check_finished} && $wholefile !~ /\*\-\* All Finished \*\-\*/) {
	    next if $moretry;
	    $self->error("Missing All Finished\n");
	}
	if ($param{expect}) {
	    # Compare
	    my $quoted = quotemeta ($param{expect});
	    my $bad = ($wholefile !~ /$param{expect}/ms
		       && $wholefile !~ /$quoted/ms);
	    if ($bad) {
		#print "**BAD  $self->{name} $param{logfile} MT $moretry  $try\n";
		next if $moretry;
		$self->error("Mismatch in output from $param{cmd}[0]\n");
		print "GOT:\n";
		print $wholefile;
		print "ENDGOT\n";
		print "EXPECT:\n";
		print $param{expect};
		print "ENDEXPECT\n";
	    }
	}
	last;
    }
}

#######################################################################
# Little utilities

sub _make_main {
    my $self = shift;

    $self->_read_inputs();

    my $filename = "obj_dir/$self->{VM_PREFIX}__main.cpp";
    my $fh = IO::File->new($filename,"w") or die "%Error: $! $filename,";

    my $VM_PREFIX = $self->{VM_PREFIX};
    print $fh "#include \"$VM_PREFIX.h\"\n";
    
    print $fh "// Compile in-place for speed\n";
    print $fh "#include \"verilated.cpp\"\n";
    print $fh "#include \"systemc.h\"\n" if $self->{sc};
    print $fh "#include \"systemperl.h\"\n" if $self->sp;
    print $fh "#include \"SpTraceVcdC.cpp\"\n" if $self->{trace};
    print $fh "#include \"SpCoverage.cpp\"\n" if $self->{coverage};

    print $fh "$VM_PREFIX *top;\n";
    if (!$self->sp) {
	print $fh "unsigned int main_time = false;\n";
	print $fh "double sc_time_stamp () {\n";
	print $fh "    return main_time;\n";
	print $fh "}\n";
    }
    if ($self->sp) {
	print $fh "extern int sc_main(int argc, char **argv);\n";
	print $fh "int sc_main(int argc, char **argv) {\n";
	print $fh "    sc_signal<bool> fastclk;\n" if $self->{inputs}{fastclk};
	print $fh "    sc_signal<bool> clk;\n"  if $self->{inputs}{clk};
	print $fh "    sc_time sim_time (1000, SC_NS);\n";
    } else {
	print $fh "int main(int argc, char **argv, char **env) {\n";
	print $fh "    double sim_time = 1000;\n";
    }
    print $fh "    Verilated::debug(".($Opt_Verilated_Debug?1:0).");\n";
    print $fh "    top = new $VM_PREFIX (\"TOP\");\n";
    my $set;
    if ($self->sp) {
	print $fh "    SP_PIN(top,fastclk,fastclk);\n" if $self->{inputs}{fastclk};
	print $fh "    SP_PIN(top,clk,clk);\n" if $self->{inputs}{clk};
	$set = "";
    } else {
	print $fh "    top->eval();\n";
	$set = "top->";
    }
    print $fh "    ${set}fastclk = true;\n" if $self->{inputs}{fastclk};
    print $fh "    ${set}clk = true;\n" if $self->{inputs}{clk};
    print $fh "    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {\n";
    for (my $i=0; $i<5; $i++) {
	my $action;
	if ($self->{inputs}{fastclk}) {
	    print $fh "	${set}fastclk=!${set}fastclk;\n";
	    $action = 1;
	}
	if ($i==4 && $self->{inputs}{clk}) {
	    print $fh "	${set}clk=!${set}clk;\n";
	    $action = 1;
	}
	if ($self->sp) {
	    print $fh "	sc_start(1);\n";
	} else {
	    print $fh "	main_time+=1;\n";
	    print $fh "	${set}eval();\n" if $action;
	}
    }
    print $fh "    }\n";
    print $fh "    if (!Verilated::gotFinish()) {\n";
    print $fh '       vl_fatal(__FILE__,__LINE__,"main", "%Error: Timeout; never got a $finish");',"\n";
    print $fh "    }\n";
    print $fh "    top->final();\n";
    print $fh "    SpCoverage::write(\"",$self->{coverage_filename},"\");\n" if $self->{coverage};
    print $fh "    exit(0L);\n";
    print $fh "}\n";
    $fh->close();
}

#######################################################################

sub _make_top {
    my $self = shift;

    $self->_read_inputs();

    my $fh = IO::File->new($self->{top_shell_filename},"w") or die "%Error: $! $self->{top_shell_filename},";
    print $fh "module top;\n";
    foreach my $inp (sort (keys %{$self->{inputs}})) {
	print $fh "    reg ${inp};\n";
    }
    # Inst
    print $fh "    t t (\n";
    my $comma="";
    foreach my $inp (sort (keys %{$self->{inputs}})) {
	print $fh "\t${comma}.${inp} (${inp})\n";
	$comma=",";
    }
    print $fh "    );\n";

    # Test
    print $fh "    initial begin\n";
    print $fh "        fastclk=1;\n" if $self->{inputs}{fastclk};
    print $fh "        clk=1;\n" if $self->{inputs}{clk};
    print $fh "        while (\$time < 1000) begin\n";
    for (my $i=0; $i<5; $i++) {
	print $fh "          #1;\n";
	print $fh "          fastclk=!fastclk;\n" if $self->{inputs}{fastclk};
	print $fh "          clk=!clk;\n" if $i==4 && $self->{inputs}{clk};
    }
    print $fh "        end\n";
    print $fh "    end\n";

    print $fh "endmodule\n";
    $fh->close();
}

#######################################################################

sub _sp_preproc {
    my $self = shift;
    my %param = (%{$self}, @_);	   # Default arguments are from $self

    $self->oprint("Preproc\n");

    $self->_run(logfile=>"simx.log",
		fails=>0,
		cmd=>["cd obj_dir ; sp_preproc",
		      "--preproc",
		      "$self->{VM_PREFIX}.sp",
		      ]);
}

#######################################################################

sub _read_inputs {
    my $self = shift;
    my $filename = $self->{top_filename};
    $filename = "t/$filename" if !-r $filename;
    my $fh = IO::File->new($filename) or die "%Error: $! $filename,";
    while (defined(my $line = $fh->getline)) {
	if ($line =~ /^\s*input\s*(\S+)\s*(\/[^\/]+\/|)\s*;/) {
	    $self->{inputs}{$1} = $1;
	}
	if ($line =~ /^\s*(function|task|endmodule)/) {
	    last;
	}
    }
    $fh->close();
}

#######################################################################
# Verilator utilities

our $_Verilator_Version;
sub verilator_version {
    if (!defined $_Verilator_Version) {
	my @args = ("perl","../bin/verilator", "--version");
	my $args = join(' ',@args);
	$_Verilator_Version = `$args`;
	$_Verilator_Version or die "can't fork: $! ".join(' ',@args);
	chomp $_Verilator_Version;
    }
    return $_Verilator_Version if defined $_Verilator_Version;
}

#######################################################################
# File utilities

sub files_identical {
    my $fn1 = shift;
    my $fn2 = shift;
    my $f1 = IO::File->new ($fn1) or die "%Error: $! $fn1,";
    my $f2 = IO::File->new ($fn2) or die "%Error: $! $fn2,";
    my @l1 = $f1->getlines();
    my @l2 = $f2->getlines();
    my $nl = $#l1;  $nl = $#l2 if ($#l2 > $nl);
    for (my $l=0; $l<=$nl; $l++) {
	if (($l1[$l]||"") ne ($l2[$l]||"")) {
	    warn ("%Warning: Line ".($l+1)." mismatches; $fn1 != $fn2\n"
		  ."F1: ".($l1[$l]||"*EOF*\n")
		  ."F2: ".($l2[$l]||"*EOF*\n"));
	    return 0;
	}
    }
    return 1;
}

sub file_grep_not {
    my $self = (ref $_[0]? shift : $Last_Self);
    my $filename = shift;
    my $regexp = shift;

    my $contents = $self->file_contents($filename);
    return if ($contents eq "_Already_Errored_");
    if ($contents =~ /$regexp/) {
	$self->error("File_grep_not: $filename: Regexp found: $regexp\n");
    }
}

sub file_grep {
    my $self = (ref $_[0]? shift : $Last_Self);
    my $filename = shift;
    my $regexp = shift;

    my $contents = $self->file_contents($filename);
    return if ($contents eq "_Already_Errored_");
    if ($contents !~ /$regexp/) {
	$self->error("File_grep: $filename: Regexp not found: $regexp\n");
    }
}

my %_File_Contents_Cache;

sub file_contents {
    my $self = (ref $_[0]? shift : $Last_Self);
    my $filename = shift;

    if (!$_File_Contents_Cache{$filename}) {
	my $fh = IO::File->new($filename,"r");
	if (!$fh) {
	    $_File_Contents_Cache{$filename} = "_Already_Errored_";
	    $self->error("File_grep file not found: ".$filename."\n");
	    return $_File_Contents_Cache{$filename};
	}
	local $/; undef $/;
	my $wholefile = <$fh>;
	$fh->close();
	$_File_Contents_Cache{$filename} = $wholefile;
    }

    return $_File_Contents_Cache{$filename};
}

#######################################################################
#######################################################################
#######################################################################
#######################################################################
# Forker class

package Forker;
use strict;

# This is a shell that matches Parallel::Forker.
# If that package is not installed, this runs the tests in *series*

sub new {
    my $class = shift;
    my $self = {@_};
    bless $self, $class;
    return $self;
}
sub schedule {
    my $self = shift;
    my %params = (@_);
    &{$params{run_on_start}}();
    &{$params{run_on_finish}}();
    return $self;
}
sub max_proc {}
sub sig_child {}
sub kill_tree_all {}
sub wait_all {}
sub ready {}

#######################################################################
1;
package main;
__END__

=pod

=head1 NAME

driver.pl - Run regression tests

=head1 SYNOPSIS

  driver.pl

=head1 DESCRIPTION

driver.pl invokes Verilator or another simulator on each little test file.

=head1 ARGUMENTS

=over 4

=item --gdb

Run verilator under the debugger.

=item --help

Displays this message and program version and exits.

=item --j #

Run number of parallel tests.  Requires Parallel::Forker project.

=item --optimize

Randomly turn on/off different optimizations.  With specific flags,
use those optimization settings

=item --nc

Run using NC-Verilog.

=item --stop

Stop on the first error

=item --vcs

Run using VCS.

=item --v3

Run using Verilator.

=back

=head1 SEE ALSO

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=cut

######################################################################
