#!/usr/bin/env perl
# See copyright, etc in below POD section.
######################################################################

require 5.006_001;
use warnings;
use Cwd;
BEGIN {
    if (!$ENV{VERILATOR_ROOT} && -x "../bin/verilator") {
        $ENV{VERILATOR_ROOT} = Cwd::getcwd()."/..";
    }
}

use Getopt::Long;
use IO::File;
use Pod::Usage;
use Data::Dumper; $Data::Dumper::Sortkeys=1;
use FindBin qw($RealBin);
use strict;
use vars qw($Debug %Vars $Driver $Fork);
use version;
use POSIX qw(strftime);
use lib ".";
use Time::HiRes qw(usleep);

$::Driver = 1;
$::Have_Forker = 0;

eval "use Parallel::Forker; \$Fork=Parallel::Forker->new(use_sig_child=>1); \$::Have_Forker=1;";
$Fork = Forker->new(use_sig_child=>1) if !$Fork;
$SIG{CHLD} = sub { $Fork->sig_child() if $Fork; };
$SIG{TERM} = sub { $Fork->kill_tree_all('TERM') if $Fork; die "Quitting...\n"; };

#======================================================================

# Map of all scenarios, with the names used to enable them
our %All_Scenarios
    = (dist  => [                       "dist"],
       atsim => [          "simulator", "atsim"],
       ghdl  => ["linter", "simulator", "ghdl"],
       iv    => [          "simulator", "iv"],
       ms    => ["linter", "simulator", "ms"],
       nc    => ["linter", "simulator", "nc"],
       vcs   => ["linter", "simulator", "vcs"],
       xsim  => ["linter", "simulator", "xsim"],
       vlt   => ["linter", "simulator", "vlt_all", "vlt"],
       vltmt => [          "simulator", "vlt_all", "vltmt"],
    );

#======================================================================
# main

autoflush STDOUT 1;
autoflush STDERR 1;

our @Orig_ARGV = @ARGV;
our @Orig_ARGV_Sw;  foreach (@Orig_ARGV) { push @Orig_ARGV_Sw, $_ if /^-/ && !/^-j/; }
our $Start = time();
our $Vltmt_threads = 3;

$Debug = 0;
my $opt_benchmark;
my @opt_tests;
my $opt_dist;
my $opt_gdb;
my $opt_rr;
my $opt_gdbbt;
my $opt_gdbsim;
my $opt_hashset;
my $opt_jobs = 1;
my $opt_optimize;
my $opt_quiet;
my $opt_rerun;
my $opt_rrsim;
my %opt_scenarios;
my $opt_site;
my $opt_stop;
my $opt_trace;
my $opt_verbose;
my $Opt_Verilated_Debug;
our $Opt_Unsupported;
our $Opt_Verilation = 1;
our @Opt_Driver_Verilator_Flags;

Getopt::Long::config("pass_through");
if (! GetOptions(
          "benchmark:i" => sub { $opt_benchmark = $_[1] ? $_[1] : 1; },
          "debug"       => \&debug,
          #debugi          see parameter()
          "gdb!"        => \$opt_gdb,
          "gdbbt!"      => \$opt_gdbbt,
          "gdbsim!"     => \$opt_gdbsim,
          "golden!"     => sub { $ENV{HARNESS_UPDATE_GOLDEN} = 1; },
          "hashset=s"   => \$opt_hashset,
          "help"        => \&usage,
          "j=i"         => \$opt_jobs,
          "optimize:s"  => \$opt_optimize,
          "quiet!"      => \$opt_quiet,
          "rerun!"      => \$opt_rerun,
          "rr!"         => \$opt_rr,
          "rrsim!"      => \$opt_rrsim,
          "site!"       => \$opt_site,
          "stop!"       => \$opt_stop,
          "trace!"      => \$opt_trace,
          "unsupported!"=> \$Opt_Unsupported,
          "verbose!"    => \$opt_verbose,
          "verilation!"         => \$Opt_Verilation,  # Undocumented debugging
          "verilated-debug!"    => \$Opt_Verilated_Debug,
          #W               see parameter()
          # Scenarios
          "atsim|athdl!"=> sub { $opt_scenarios{atsim} = $_[1]; },
          "dist!"       => sub { $opt_scenarios{dist} = $_[1]; },
          "ghdl!"       => sub { $opt_scenarios{ghdl} = $_[1]; },
          "iv!"         => sub { $opt_scenarios{iv} = $_[1]; },
          "ms!"         => sub { $opt_scenarios{ms} = $_[1]; },
          "nc!"         => sub { $opt_scenarios{nc} = $_[1]; },
          "vlt!"        => sub { $opt_scenarios{vlt} = $_[1]; },
          "vltmt!"      => sub { $opt_scenarios{vltmt} = $_[1]; },
          "vcs!"        => sub { $opt_scenarios{vcs} = $_[1]; },
          "xsim!"       => sub { $opt_scenarios{xsim} = $_[1]; },
          "<>"          => \&parameter,
    )) {
    die "%Error: Bad usage, try '$0 --help'\n";
}

$opt_jobs = calc_jobs() if defined $opt_jobs && $opt_jobs==0;
$Fork->max_proc($opt_jobs);

if ((scalar keys %opt_scenarios) < 1) {
    $opt_scenarios{dist} = 1;
    $opt_scenarios{vlt} = 1;
}

our @Test_Dirs = "t";
push @Test_Dirs, split(/:/,$ENV{VERILATOR_TESTS_SITE})
    if (($#opt_tests<0 ? $opt_site : 1) && $ENV{VERILATOR_TESTS_SITE});

if ($#opt_tests<0) {  # Run everything
    my %uniq;
    foreach my $dir (@Test_Dirs) {
        my @stats = stat($dir);  # Uniquify by inode, so different paths to same place get combined
        next if !$stats[1] || $uniq{$stats[1]}++;
        push @opt_tests, sort(glob("${dir}/t_*.pl"));
    }
}
@opt_tests = _calc_hashset(@opt_tests) if $opt_hashset;

if ($#opt_tests>=2 && $opt_jobs>=2) {
    # Without this tests such as t_debug_sigsegv_bt_bad.pl will occasionally
    # block on input and cause a SIGSTOP, then a "fg" was needed to resume testing.
    if (!$::Have_Forker) {
        print STDERR "driver.pl: NO_FORKER: For faster testing 'sudo cpan install Parallel::Forker'\n";
    }
    print STDERR "== Many jobs; redirecting STDIN\n";
    open(STDIN, "+>/dev/null");
}


mkdir "obj_dist";
my $timestart = strftime("%Y%m%d_%H%M%S", localtime);

my $runner;
{
    $runner = Runner->new(
        driver_log_filename => "obj_dist/driver_${timestart}.log",
        quiet => $opt_quiet);
    foreach my $testpl (@opt_tests) {
        foreach my $scenario (sort keys %opt_scenarios) {
            next if !$opt_scenarios{$scenario};
            $runner->one_test(pl_filename => $testpl,
                              $scenario => 1);
        }
    }
    $runner->wait_and_report;
}

if ($opt_rerun && $runner->fail_count) {
    print("="x70,"\n");
    print("="x70,"\n");
    print("RERUN  ==\n\n");

    # Avoid parallel run to ensure that isn't causing problems
    # If > 10 failures something more wrong and get results quickly
    $Fork->max_proc(1) unless $runner->fail_count > 10;

    my $orig_runner = $runner;
    $runner = Runner->new(
        driver_log_filename => "obj_dist/driver_${timestart}_rerun.log",
        quiet => 0,
        fail1_cnt => $orig_runner->fail_count,
        ok_cnt => $orig_runner->{ok_cnt},
        skip_cnt => $orig_runner->{skip_cnt},
        unsup_cnt => $orig_runner->{unsup_cnt});
    foreach my $test (@{$orig_runner->{fail_tests}}) {
        if (0) {  # TBD if this is required - rare that intermediate results are bad
            # Remove old results to force hard rebuild
            system("rm", "-rf", "$test->{obj_dir}__fail1");
            system("mv", "$test->{obj_dir}", "$test->{obj_dir}__fail1");
        }
        # Reschedule test
        $runner->one_test(pl_filename => $test->{pl_filename},
                          $test->{scenario} => 1);
    }
    $runner->wait_and_report;
}

exit(10) if $runner->fail_count;

#----------------------------------------------------------------------

sub usage {
    pod2usage(-verbose=>2, -exitval=>0, -output=>\*STDOUT);
    exit(1);  # Unreachable
}

sub debug {
    $Debug = 1;
    push @Opt_Driver_Verilator_Flags, "--debug --no-skip-identical";
}

our $_Parameter_Next_Level;

sub parameter {
    my $param = shift;
    if ($_Parameter_Next_Level) {
        ($param =~ /^(\d+)$/)
            or die "%Error: Expected number following $_Parameter_Next_Level: $param\n";
        push @Opt_Driver_Verilator_Flags, $param;
        $_Parameter_Next_Level  = undef;
    }
    elsif ($param =~ /\.pl/) {
        push @opt_tests, $param;
    }
    elsif ($param =~ /^-?(-debugi|-dump-treei)/) {
        push @Opt_Driver_Verilator_Flags, $param;
        $_Parameter_Next_Level = $param;
    }
    elsif ($param =~ /^-?(-W||-debug-check)/) {
        push @Opt_Driver_Verilator_Flags, $param;
    }
    else {
        die "%Error: Unknown parameter: $param\n";
    }
}

sub max_procs {
    my $ok = eval "
        use Unix::Processors;
        return Unix::Processors->new->max_online;
    ";
    return $ok;
}

sub calc_threads {
    my $default = shift;
    my $ok = max_procs();
    $ok && !$@ or return $default;
    return ($ok < $default) ? $ok : $default;
}

sub calc_jobs {
    my $ok = max_procs();
    $ok && !$@ or die "%Error: Can't use -j: $@\n";
    print "driver.pl: Found $ok cores, using -j ",$ok+1,"\n";
    return $ok + 1;
}

sub _calc_hashset {
    my @in = @_;
    return @in if !$opt_hashset;
    $opt_hashset =~ m!^(\d+)/(\d+)$!
        or die "%Error: Need number/number format for --hashset: $opt_hashset\n";
    my ($set, $nsets) = ($1, $2);
    my @new;
    foreach my $t (@opt_tests) {
        my $checksum = do {
            local $/;
            unpack("%32W*", $t);
        };
        if (($set % $nsets) == ($checksum % $nsets)) {
            push @new, $t;
        }
    }
    return @new;
}

#######################################################################
#######################################################################
#######################################################################
#######################################################################
# Runner class

package Runner;
use strict;

sub new {
    my $class = shift;
    my $self = {
        # Parameters
        driver_log_filename => undef,
        quiet => 0,
        # Counts
        all_cnt => 0,
        left_cnt => 0,
        ok_cnt => 0,
        fail1_cnt => 0,
        fail_cnt => 0,
        skip_cnt => 0,
        unsup_cnt => 0,
        skip_msgs => [],
        fail_msgs => [],
        fail_tests => [],
        @_};
    bless $self, $class;
    return $self;
}

sub fail_count { return $_[0]->{fail_cnt}; }

sub one_test {
    my $self = shift;
    my @params = @_;
    my %params = (@params);
    $self->{all_cnt}++;
    $self->{left_cnt}++;
    $::Fork->schedule
        (
         test_pl_filename => $params{pl_filename},
         run_on_start => sub {
             # Running in context of child, so can't pass data to parent directly
             if ($self->{quiet}) {
                 open(STDOUT, ">/dev/null");
                 open(STDERR, ">&STDOUT");
             }
             print("="x70,"\n");
             my $test = VTest->new(@params);
             $test->oprint("="x50,"\n");
             unlink $test->{status_filename};
             $test->_prep;
             $test->_read;
             # Don't put anything other than _exit after _read,
             # as may call _exit via another path
             $test->_exit;
         },
         run_on_finish => sub {
             # Running in context of parent
             my $test = VTest->new(@params);
             $test->_read_status;
             if ($test->ok) {
                 $self->{ok_cnt}++;
             } elsif ($test->scenario_off && !$test->errors) {
             } elsif ($test->skips && !$test->errors) {
                 push @{$self->{skip_msgs}},
                     ("\t#".$test->soprint("-Skip:  $test->{skips}\n"));
                 $self->{skip_cnt}++;
             } elsif ($test->unsupporteds && !$test->errors) {
                 $self->{unsup_cnt}++;
             } else {
                 $test->oprint("FAILED: $test->{errors}\n");
                 my $j = ($opt_jobs>1?" -j":"");
                 my $makecmd = $ENV{VERILATOR_MAKE} || "make$j &&";
                 push @{$self->{fail_msgs}},
                     ("\t#".$test->soprint("%Error: $test->{errors}\n")
                      ."\t\t$makecmd test_regress/"
                      .$test->{pl_filename}
                      ." ".join(' ', _manual_args())
                      ." --".$test->{scenario}."\n");
                 push @{$self->{fail_tests}}, $test;
                 $self->{fail_cnt}++;
                 $self->report($self->{driver_log_filename});
                 my $other = "";
                 foreach my $proc ($::Fork->running) {
                     $other .= "  ".$proc->{test_pl_filename};
                 }
                 $test->oprint("Simultaneous running tests:",$other,"\n")
                     if $other && !$opt_quiet;
                 if ($opt_stop) { die "%Error: --stop and errors found\n"; }
             }
             $self->{left_cnt}--;
             $self->print_summary;
         },
         )->ready();
}

sub wait_and_report {
    my $self = shift;
    $self->print_summary(force=>1);
    # Wait for all children to finish
    while ($::Fork->is_any_left) {
        $::Fork->poll;
        if ((time() - ($self->{_last_summary_time} || 0) >= 30)
            && (!$opt_gdb && !$opt_gdbsim)) {  # Don't show for interactive gdb etc
            $self->print_summary(force=>1, show_running=>1);
        }
        Time::HiRes::usleep 100*1000;
    }
    $runner->report(undef);
    $runner->report($self->{driver_log_filename});
}

sub report {
    my $self = shift;
    my $filename = shift;

    my $fh = \*STDOUT;
    if ($filename) {
        $fh = IO::File->new(">$filename") or die "%Error: $! writing $filename,";
    }

    $fh->print("\n");
    $fh->print("="x70,"\n");
    foreach my $f (sort @{$self->{fail_msgs}}) {
        chomp $f;
        $fh->print("$f\n");
    }
    foreach my $f (sort @{$self->{skip_msgs}}) {
        chomp $f;
        $fh->print("$f\n");
    }
    my $sum = ($self->{fail_cnt} && "FAILED"
               || $self->{skip_cnt} && "PASSED w/SKIPS"
               || "PASSED");
    $fh->print("TESTS DONE, $sum: ".$self->sprint_summary."\n");
}

sub print_summary {
    my $self = shift;
    my %params = (force => 0, # Force printing
                  show_running => 0, # Show running processes
                  @_);
    if (!$self->{quiet} || $params{force}
        || ($self->{left_cnt} < 5)
        || (time() - ($self->{_last_summary_time} || 0) >= 15)) {  # Don't show for interactive gdb etc
        $self->{_last_summary_time} = time();
        print STDERR ("==SUMMARY: ".$self->sprint_summary."\n");
        if ($params{show_running}) {
            my $other;
            foreach my $proc ($::Fork->running) {
                $other .= "  ".$proc->{test_pl_filename};
            }
            print STDERR ("==STILL RUNNING: ".$other."\n");
        }
    }
}

sub sprint_summary {
    my $self = shift;

    my $delta = time() - $::Start;
    my $leftmsg = $::Have_Forker ? $self->{left_cnt} : "NO-FORKER";
    my $pct = int(100*($self->{left_cnt} / $self->{all_cnt}) + 0.999);
    my $eta = ($self->{all_cnt}
               * ($delta / (($self->{all_cnt} - $self->{left_cnt})+0.001))) - $delta;
    $eta = 0 if $delta < 10;
    my $out = "";
    $out .= "Left $leftmsg  " if $self->{left_cnt};
    $out .= "Passed $self->{ok_cnt}";
    # Ordered below most severe to least severe
    $out .= "  Failed $self->{fail_cnt}";
    $out .= "  Failed-First $self->{fail1_cnt}" if $self->{fail1_cnt};
    $out .= "  Skipped $self->{skip_cnt}" if $self->{skip_cnt};
    $out .= "  Unsup $self->{unsup_cnt}";
    $out .= sprintf("  Eta %d:%02d", int($eta/60), $eta%60) if $self->{left_cnt} > 10 && $eta > 10;
    $out .= sprintf("  Time %d:%02d", int($delta/60), $delta%60);
    return $out;
}

sub _manual_args {
    # Return command line with scenarios stripped
    my @out;
  arg:
    foreach my $arg (@Orig_ARGV_Sw) {
        foreach my $allsc (keys %All_Scenarios) {
            foreach my $allscarg (@{$All_Scenarios{$allsc}}) {
                next arg if ("--$allscarg" eq $arg);
            }
        }
        # Also strip certain flags that per-test debugging won't want
        next arg if $arg eq '--rerun';
        next arg if $arg eq '--quiet';
        push @out, $arg;
    }
    return @out;
}

#######################################################################
#######################################################################
#######################################################################
#######################################################################
# Test class

package VTest;
use Carp;
use Cwd;
use Data::Dumper;
use File::Spec;
use File::Path qw(mkpath);

use vars qw($Self $Self);
use strict;

sub defineOpt {
    my $xsim = shift;
    return $xsim ? "--define " : "+define+";
}

sub new {
    my $class = shift;
    my $self = {@_};

    $self->{name} ||= $2 if $self->{pl_filename} =~ m!^(.*/)?([^/]*)\.pl$!;

    $self->{scenario} = "";
    $self->{scenario} ||= "dist" if $self->{dist};
    $self->{scenario} ||= "atsim" if $self->{atsim};
    $self->{scenario} ||= "ghdl" if $self->{ghdl};
    $self->{scenario} ||= "vcs" if $self->{vcs};
    $self->{scenario} ||= "vlt" if $self->{vlt};
    $self->{scenario} ||= "vltmt" if $self->{vltmt};
    $self->{scenario} ||= "nc" if $self->{nc};
    $self->{scenario} ||= "ms" if $self->{ms};
    $self->{scenario} ||= "iv" if $self->{iv};
    $self->{scenario} ||= "xsim" if $self->{xsim};

    foreach my $dir (@::Test_Dirs) {
        # t_dir used both absolutely and under obj_dir
        if (-e "$dir/$self->{name}.pl") {
            # Note most tests require error messages of the form t/x.v
            # Therefore pl_filename must be t/ for local tests
            $self->{pl_filename} = File::Spec->abs2rel("$dir/$self->{name}.pl");
            # t_dir must be absolute - used under t or under obj_dir
            $self->{t_dir} ||= File::Spec->rel2abs($dir);
            last;
        }
    }
    $self->{t_dir} or die "%Error: Can't locate dir for $self->{name},";

    if (!$self->{obj_dir}) {
        my $scen_dir = File::Spec->abs2rel("$self->{t_dir}/../obj_$self->{scenario}");
        $scen_dir =~ s!^t/\.\./!!;  # Simplify filenames on local runs
        mkdir $scen_dir;  # Not a mkpath so find out if trying to build somewhere odd
        $self->{obj_dir} ="$scen_dir/$self->{name}";
    }

    my $define_opt = defineOpt($self->{xsim});

    $self = {
        name => undef,          # Set below, name of this test
        pl_filename => undef,   # Name of .pl file to get setup from
        make_top_shell => 1,    # Make a default __top.v file
        make_main => 1,         # Make __main.cpp
        make_pli => 0,          # need to compile pli
        sim_time => 1100,
        benchmark => $opt_benchmark,
        verbose => $opt_verbose,
        run_env => '',
        # All compilers
        v_flags => [split(/\s+/,
                          (($self->{xsim} ? " -f input.xsim.vc " :
                            (-r 'input.vc' ? " -f input.vc " : ""))
                           .($self->{t_dir} !~ m!/test_regress!  # Don't include standard dir, only site's
                             ? " +incdir+$self->{t_dir} -y $self->{t_dir}" : "")
                           . " ".$define_opt."TEST_OBJ_DIR=$self->{obj_dir}"
                           .($opt_verbose ? " ".$define_opt."TEST_VERBOSE=1":"")
                           .($opt_benchmark ? " ".$define_opt."TEST_BENCHMARK=$opt_benchmark":"")
                           .($opt_trace ? " ".$define_opt."WAVES=1":"")
                          ))],
        v_flags2 => [],  # Overridden in some sim files
        v_other_filenames => [],  # After the filename so we can spec multiple files
        all_run_flags => [],
        pli_flags => ["-I$ENV{VERILATOR_ROOT}/include/vltstd -fPIC -shared"
                      .(($^O eq "darwin" )
                        ? " -Wl,-undefined,dynamic_lookup"
                        : " -export-dynamic")
                      ." -o $self->{obj_dir}/libvpi.so"],
        # ATSIM
        atsim => 0,
        atsim_flags => [split(/\s+/,"-c +sv +define+ATSIM"),
                        "+sv_dir+$self->{obj_dir}/.athdl_compile"],
        atsim_flags2 => [],  # Overridden in some sim files
        atsim_run_flags => [],
        # GHDL
        ghdl => 0,
        ghdl_work_dir => "$self->{obj_dir}/ghdl_compile",
        ghdl_flags => [($::Debug?"-v":""),
                       "--workdir=$self->{obj_dir}/ghdl_compile", ],
        ghdl_flags2 => [],  # Overridden in some sim files
        ghdl_run_flags => [],
        # IV
        iv => 0,
        iv_flags => [split(/\s+/,"+define+iverilog -g2012 -o $self->{obj_dir}/simiv")],
        iv_flags2 => [],  # Overridden in some sim files
        iv_pli => 0,  # need to use pli
        iv_run_flags => [],
        # VCS
        vcs => 0,
        vcs_flags => [split(/\s+/,"+vcs+lic+wait +cli -debug_access +define+VCS+1 -q -sverilog -CFLAGS '-DVCS' ")],
        vcs_flags2 => [],  # Overridden in some sim files
        vcs_run_flags => [split(/\s+/,"+vcs+lic_wait")],
        # NC
        nc => 0,
        nc_flags => [split(/\s+/,("+licqueue +nowarn+LIBNOU +define+NC=1 -q +assert +sv -c "
                                  .($opt_trace ? " +access+r":"")))],
        nc_flags2 => [],  # Overridden in some sim files
        nc_run_flags => [split(/\s+/,"+licqueue -q +assert +sv -R")],
        # ModelSim
        ms => 0,
        ms_flags => [split(/\s+/,("-sv -work $self->{obj_dir}/work"))],
        ms_flags2 => [],  # Overridden in some sim files
        ms_pli => 1,  # need to use pli
        ms_run_flags => [split(/\s+/,"-lib $self->{obj_dir}/work -c -do 'run -all;quit' ")],
        # XSim
        xsim => 0,
        xsim_flags => [split(/\s+/,("--nolog --sv --define XSIM --work $self->{name}=$self->{obj_dir}/xsim"))],
        xsim_flags2 => [],  # Overridden in some sim files
        xsim_run_flags => [split(/\s+/,("--nolog --runall --lib $self->{name}=$self->{obj_dir}/xsim"
                                        .($opt_trace ? " --debug all":"")))],
        xsim_run_flags2 => [],  # Overridden in some sim files
        # Verilator
        vlt => 0,
        vltmt => 0,
        verilator_flags => ["-cc",
                            "-Mdir $self->{obj_dir}",
                            "-OD",  # As currently disabled unless -O3
                            "--debug-check",
                            "--comp-limit-members 10", ],
        verilator_flags2 => [],
        verilator_flags3 => ["--clk clk"],
        verilator_make_gmake => 1,
        verilator_make_cmake => 0,
        verilated_debug => $Opt_Verilated_Debug,
        stdout_filename => undef,  # Redirect stdout
        %$self};
    bless $self, $class;

    $self->{vlt_all} = $self->{vlt} || $self->{vltmt};  # Any Verilator scenario

    $self->{VM_PREFIX} ||= "V".$self->{name};
    $self->{stats} ||= "$self->{obj_dir}/V".$self->{name}."__stats.txt";
    $self->{status_filename} ||= "$self->{obj_dir}/V".$self->{name}.".status";
    $self->{run_log_filename} ||= "$self->{obj_dir}/vlt_sim.log";
    $self->{coverage_filename} ||= "$self->{obj_dir}/coverage.dat";
    $self->{main_filename} ||= "$self->{obj_dir}/$self->{VM_PREFIX}__main.cpp";
    ($self->{top_filename} ||= $self->{pl_filename}) =~ s/\.pl$//;
    ($self->{golden_filename} ||= $self->{pl_filename}) =~ s/\.pl$/.out/;
    if (-e ($self->{top_filename}.".vhd")) {  # If VHDL file exists
        $self->{vhdl} = 1;
        $self->{top_filename} .= ".vhd";
    } else {
        $self->{top_filename} .= ".v";
    }
    if (!$self->{make_top_shell}) {
        $self->{top_shell_filename} = $self->{top_filename};
    } else {
        $self->{top_shell_filename} = "$self->{obj_dir}/$self->{VM_PREFIX}__top.v";
    }
    $self->{pli_filename} ||= $self->{name}.".cpp";
    return $self;
}

sub soprint {
    my $self = (ref $_[0] ? shift : $Self);
    my $str = "$self->{scenario}/$self->{name}: ".join('',@_);
    $str =~ s/\n\n+$/\n/s;
    return $str;
}

sub oprint {
    my $self = (ref $_[0] ? shift : $Self);
    print $self->soprint(@_);
}

sub error {
    my $self = (ref $_[0] ? shift : $Self);
    my $msg = join('',@_);
    # Called from tests as: error("Reason message"[, ...]);
    warn "%Warning: $self->{scenario}/$self->{name}: ".$msg."\n";
    $self->{errors} ||= $msg;
}

sub skip {
    my $self = (ref $_[0] ? shift : $Self);
    my $msg = join('',@_);
    # Called from tests as: skip("Reason message"[, ...]);
    warn "-Skip: $self->{scenario}/$self->{name}: ".$msg."\n";
    $self->{skips} ||= "Skip: ".$msg;
}

sub unsupported {
    my $self = (ref $_[0] ? shift : $Self);
    my $msg = join('',@_);
    # Called from tests as: unsupported("Reason message"[, ...]);
    warn "-Unsupported: $self->{scenario}/$self->{name}: ".$msg."\n";
    if (!$::Opt_Unsupported) {
        $self->{unsupporteds} ||= "Unsupported: ".$msg;
    }
}

sub scenarios {
    my $self = (ref $_[0] ? shift : $Self);
    my %params = (@_);
    # Called from tests as: scenarios(...);
    # to specify which scenarios this test runs under.
    #  Where ... is one cases listed in All_Scenarios
    if ((scalar keys %params) < 1) {
        $params{simulators} = 1;
    }
    my %enabled_scenarios;
    foreach my $scenario (keys %params) {
        my $value = $params{$scenario};
        my $hit = 0;
        foreach my $allsc (keys %All_Scenarios) {
            foreach my $allscarg (@{$All_Scenarios{$allsc}}) {
                if ($scenario eq $allscarg) {
                    $hit = 1;
                    $enabled_scenarios{$allsc} = 1;
                }
            }
        }
        if (!$hit) {
            $self->error("scenarios('$scenario' => ...) has unknown scenario '$scenario',");
        }
    }

    if (!$enabled_scenarios{$self->{scenario}}) {
        $self->skip("scenario '$self->{scenario}' not enabled for test");
        $self->{scenario_off} ||= 1;
        $self->_exit();
    }
}

sub _prep {
    my $self = shift;
    mkdir $self->{obj_dir};  # Ok if already exists
}

sub _read {
    my $self = shift;
    # Read the control file
    (-r $self->{pl_filename})
        or return $self->error("Can't open $self->{pl_filename}\n");
    $Self = $self;
    delete $INC{$self->{pl_filename}};
    require $self->{pl_filename};
}

sub _exit {
    my $self = shift;
    if ($self->ok) {
        $self->oprint("Self PASSED\n");
    } elsif ($self->skips && !$self->errors) {
        $self->oprint("%Skip: $self->{skips}\n");
    } elsif ($self->unsupporteds && !$self->errors) {
        $self->oprint("%Unsupported: $self->{unsupporteds}\n");
    } else {
        $self->error("Missing ok\n") if !$self->errors;
        $self->oprint("%Error: $self->{errors}\n");
    }
    $self->_write_status;
    exit(0);
}

sub _write_status {
    my $self = shift;
    my $filename = $self->{status_filename};
    my $fh = IO::File->new(">$filename") or die "%Error: $! $filename,";
    $Data::Dumper::Indent = 1;
    $Data::Dumper::Sortkeys = 1;
    print $fh Dumper($self);
    print $fh "1;";
    $fh->close();
}

sub _read_status {
    my $self = shift;
    my $filename = $self->{status_filename};
    use vars qw($VAR1);
    local $VAR1;
    if (!-r $filename) {
        $self->error("driver.pl _read_status file missing: $filename");
        return;
    }
    {
        local %INC = ();
        require $filename or die "%Error: $! $filename,";
    }
    if ($VAR1) {
        %{$self} = %{$VAR1};
    } else {
        $self->error("driver.pl _read_status file empty: $filename");
        return;
    }
}

#----------------------------------------------------------------------
# Methods invoked by tests

sub compile_vlt_cmd {
    my $self = (ref $_[0]? shift : $Self);
    my %param = (%{$self}, @_);  # Default arguments are from $self
    return 1 if $self->errors || $self->skips || $self->unsupporteds;

    my @vlt_cmd = (
        "perl", "$ENV{VERILATOR_ROOT}/bin/verilator",
        $self->compile_vlt_flags(%param),
        $param{top_filename},
        @{$param{v_other_filenames}},
        $param{stdout_filename}?"> ".$param{stdout_filename}:""
    );
    return @vlt_cmd;
}

sub compile_vlt_flags {
    my $self = (ref $_[0]? shift : $Self);
    my %param = (%{$self}, @_);  # Default arguments are from $self
    return 1 if $self->errors || $self->skips || $self->unsupporteds;

    my $checkflags = join(' ',@{$param{v_flags}},
                          @{$param{v_flags2}},
                          @{$param{verilator_flags}},
                          @{$param{verilator_flags2}},
                          @{$param{verilator_flags3}});
    $self->{sc} = 1 if ($checkflags =~ /-sc\b/);
    $self->{trace} = ($opt_trace || $checkflags =~ /-trace\b/
                      || $checkflags =~ /-trace-fst\b/
                      || $checkflags =~ /-trace-fst-thread\b/);
    $self->{trace_format} = (($checkflags =~ /-trace-fst/ && 'fst-c')
                             || ($self->{sc} && 'vcd-sc')
                             || (!$self->{sc} && 'vcd-c'));
    $self->{savable} = 1 if ($checkflags =~ /-savable\b/);
    $self->{coverage} = 1 if ($checkflags =~ /-coverage\b/);

    my @verilator_flags = @{$param{verilator_flags}};
    unshift @verilator_flags, "--gdb" if $opt_gdb;
    unshift @verilator_flags, "--gdbbt" if $opt_gdbbt;
    unshift @verilator_flags, "--rr" if $opt_rr;
    unshift @verilator_flags, "--x-assign unique";  # More likely to be buggy
    unshift @verilator_flags, "--trace" if $opt_trace;
    my $threads = ::calc_threads($Vltmt_threads);
    unshift @verilator_flags, "--threads $threads" if $param{vltmt} && $checkflags !~ /-threads /;
    unshift @verilator_flags, "--trace-fst-thread" if $param{vltmt} && $checkflags =~ /-trace-fst/;
    unshift @verilator_flags, "--debug-partition" if $param{vltmt};
    unshift @verilator_flags, "--make gmake" if $param{verilator_make_gmake};
    unshift @verilator_flags, "--make cmake" if $param{verilator_make_cmake};
    unshift @verilator_flags, "--exe" if
        $param{make_main} && $param{verilator_make_gmake};
    unshift @verilator_flags, "../".$self->{main_filename} if
        $param{make_main} && $param{verilator_make_gmake};
    if (defined $opt_optimize) {
        my $letters = "";
        if ($opt_optimize =~ /[a-zA-Z]/) {
            $letters = $opt_optimize;
        } else {  # Randomly turn on/off different optimizations
            foreach my $l ('a'..'z') {
                $letters .= ((rand() > 0.5) ? $l : uc $l);
            }
            unshift @verilator_flags, "--trace" if rand() > 0.5;
            unshift @verilator_flags, "--coverage" if rand() > 0.5;
        }
        unshift @verilator_flags, "--O".$letters;
    }

    my @cmdargs = (
                   "--prefix ".$param{VM_PREFIX},
                   @verilator_flags,
                   @{$param{verilator_flags2}},
                   @{$param{verilator_flags3}},
                   @{$param{v_flags}},
                   @{$param{v_flags2}},
                   # Flags from driver cmdline override default flags and
                   # flags from the test itself
                   @Opt_Driver_Verilator_Flags,
        );
    return @cmdargs;
}

sub lint {
    my $self = (ref $_[0] ? shift : $Self);
    my %param = (#
                 %{$self},  # Default arguments are from $self
                 # Lint specific default overrides
                 make_main => 0,
                 make_top_shell => 0,
                 verilator_flags2 => ["--lint-only"],
                 verilator_make_gmake => 0,
                 @_);
    $self->compile(%param);
}

sub compile {
    my $self = (ref $_[0]? shift : $Self);
    my %param = (tee => 1,
                 %{$self}, @_);  # Default arguments are from $self
    return 1 if $self->errors || $self->skips || $self->unsupporteds;
    $self->oprint("Compile\n") if $self->{verbose};

    compile_vlt_cmd(%param);

    if (!$self->{make_top_shell}) {
        $param{top_shell_filename}
        = $self->{top_shell_filename} = $self->{top_filename};
    } else {
        $param{top_shell_filename}
        = $self->{top_shell_filename} = "$self->{obj_dir}/$self->{VM_PREFIX}__top.".$self->v_suffix;
    }

    if ($param{atsim}) {
        $self->_make_top();
        $self->_run(logfile=>"$self->{obj_dir}/atsim_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_ATSIM}||"atsim"),
                          @{$param{atsim_flags}},
                          @{$param{atsim_flags2}},
                          @{$param{v_flags}},
                          @{$param{v_flags2}},
                          $param{top_filename},
                          $param{top_shell_filename},
                          @{$param{v_other_filenames}},
                          ]);
    }
    elsif ($param{ghdl}) {
        mkdir $self->{ghdl_work_dir};
        $self->_make_top();
        $self->_run(logfile=>"$self->{obj_dir}/ghdl_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_GHDL}||"ghdl"),
                          # Add -c here, as having -c twice freaks it out
                          ((($ENV{VERILATOR_GHDL}||' ') =~ / -c\b/) ? "" : "-c"),
                          @{$param{ghdl_flags}},
                          @{$param{ghdl_flags2}},
                          #@{$param{v_flags}},  # Not supported
                          #@{$param{v_flags2}},  # Not supported
                          $param{top_filename},
                          $param{top_shell_filename},
                          @{$param{v_other_filenames}},
                          "-e t",
                          ]);
    }
    elsif ($param{vcs}) {
        $self->_make_top();
        $self->_run(logfile=>"$self->{obj_dir}/vcs_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_VCS}||"vcs"),
                          @{$param{vcs_flags}},
                          @{$param{vcs_flags2}},
                          @{$param{v_flags}},
                          @{$param{v_flags2}},
                          $param{top_filename},
                          $param{top_shell_filename},
                          @{$param{v_other_filenames}},
                          ]);
    }
    elsif ($param{nc}) {
        $self->_make_top();
        my @more_args;
        if ($self->vhdl) {
            ((my $ts = $param{top_shell_filename}) =~ s!\.v!!);
            $ts =~ s!.*/!!;;
            push @more_args, "-vhdltop", $ts;
        }
        $self->_run(logfile=>"$self->{obj_dir}/nc_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_NCVERILOG}||"ncverilog"),
                          @{$param{nc_flags}},
                          @{$param{nc_flags2}},
                          @{$param{v_flags}},
                          @{$param{v_flags2}},
                          $param{top_filename},
                          $param{top_shell_filename},
                          @{$param{v_other_filenames}},
                          @more_args
                          ]);
    }
    elsif ($param{ms}) {
        $self->_make_top();
        $self->_run(logfile=>"$self->{obj_dir}/ms_compile.log",
                    fails=>$param{fails},
                    cmd=>[("vlib $self->{obj_dir}/work && "),
                          ($ENV{VERILATOR_MODELSIM}||"vlog"),
                          @{$param{ms_flags}},
                          @{$param{ms_flags2}},
                          @{$param{v_flags}},
                          @{$param{v_flags2}},
                          $param{top_filename},
                          $param{top_shell_filename},
                          @{$param{v_other_filenames}}
                          ]);
    }
    elsif ($param{iv}) {
        $self->_make_top();
        my @cmd = (($ENV{VERILATOR_IVERILOG}||"iverilog"),
                   @{$param{iv_flags}},
                   @{$param{iv_flags2}},
                   @{$param{v_flags}},
                   @{$param{v_flags2}},
                   $param{top_filename},
                   $param{top_shell_filename},
                   @{$param{v_other_filenames}});
        @cmd = grep { s/\+define\+/-D /g; $_; } @cmd;

        $self->_run(logfile=>"$self->{obj_dir}/iv_compile.log",
                    fails=>$param{fails},
                    cmd=>\@cmd);
    }
    elsif ($param{xsim}) {
        $self->_make_top();
        $self->_run(logfile=>"$self->{obj_dir}/xsim_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_XVLOG}||"xvlog"),
                          @{$param{xsim_flags}},
                          @{$param{xsim_flags2}},
                          @{$param{v_flags}},
                          @{$param{v_flags2}},
                          $param{top_filename},
                          $param{top_shell_filename},
                          @{$param{v_other_filenames}}
                          ]);
    }
    elsif ($param{vlt_all}) {

        if ($self->sc && !$self->have_sc) {
            $self->skip("Test requires SystemC; ignore error since not installed\n");
            return 1;
        }

        if ($self->{vltmt} && !$self->cfg_with_threaded) {
            $self->skip("Test requires Verilator configured with threads\n");
            return 1;
        }

        if ($param{verilator_make_cmake} && !$self->have_cmake) {
            $self->skip("Test requires CMake; ignore error since not available or version too old\n");
            return 1;
        }

        if (!$param{fails} && $param{make_main}) {
            $self->_make_main();
        }

        if ($param{verilator_make_gmake}
            || (!$param{verilator_make_gmake} && !$param{verilator_make_cmake})) {
            my @vlt_cmd = $self->compile_vlt_cmd(%param);
            $self->oprint("Running Verilator (gmake)\n") if $self->{verbose};
            $self->_run(logfile => "$self->{obj_dir}/vlt_compile.log",
                        fails => $param{fails},
                        tee => $param{tee},
                        expect => $param{expect},
                        expect_filename => $param{expect_filename},
                        cmd => \@vlt_cmd) if $::Opt_Verilation;
            return 1 if $self->errors || $self->skips || $self->unsupporteds;
        }

        if ($param{verilator_make_cmake}) {
            my @vlt_args = $self->compile_vlt_flags(%param);
            $self->oprint("Running cmake\n") if $self->{verbose};
            mkdir $self->{obj_dir};
            my @csources = ();
            unshift @csources, $self->{main_filename} if $param{make_main};
            $self->_run(logfile => "$self->{obj_dir}/vlt_cmake.log",
                        fails => $param{fails},
                        tee => $param{tee},
                        expect => $param{expect},
                        expect_filename => $param{expect_filename},
                        cmd => ["cd \"".$self->{obj_dir}."\" && cmake",
                                "\"".$self->{t_dir}."/..\"",
                                "-DTEST_VERILATOR_ROOT=$ENV{VERILATOR_ROOT}",
                                "-DTEST_NAME=$self->{name}",
                                "-DTEST_CSOURCES=\"@csources\"",
                                "-DTEST_VERILATOR_ARGS=\"@vlt_args\"",
                                "-DTEST_VERILATOR_SOURCES=\"$param{top_filename} @{$param{v_other_filenames}}\"",
                                "-DTEST_VERBOSE=\"".($self->{verbose} ? 1 : 0)."\"",
                                "-DTEST_SYSTEMC=\"" .($self->sc ? 1 : 0). "\"",
                                "-DCMAKE_PREFIX_PATH=\"".(($ENV{SYSTEMC_INCLUDE}||$ENV{SYSTEMC}||'')."/..\""),
                                "-DTEST_OPT_FAST=\"" . ($param{benchmark} ? "-Os" : "") . "\"",
                                "-DTEST_VERILATION=\"" . $::Opt_Verilation . "\"",
                        ]);
            return 1 if $self->errors || $self->skips || $self->unsupporteds;
        }

        if (!$param{fails} && $param{verilator_make_gmake}) {
            $self->oprint("Running make (gmake)\n") if $self->{verbose};
            $self->_run(logfile => "$self->{obj_dir}/vlt_gcc.log",
                        entering => "$self->{obj_dir}",
                        cmd => ["make",
                                "-C ".$self->{obj_dir},
                                "-f ".$::RealBin."/Makefile_obj",
                                ($self->{verbose} ? "" : "--no-print-directory"),
                                "VM_PREFIX=$self->{VM_PREFIX}",
                                "TEST_OBJ_DIR=$self->{obj_dir}",
                                "CPPFLAGS_DRIVER=-D".uc($self->{name}),
                                ($self->{verbose} ? "CPPFLAGS_DRIVER2=-DTEST_VERBOSE=1":""),
                                ($param{benchmark} ? "OPT_FAST=-Os" : ""),
                                "$self->{VM_PREFIX}",  # bypass default rule, as we don't need archive
                                ($param{make_flags}||""),
                        ]);
        }

        if (!$param{fails} && $param{verilator_make_cmake}) {
            $self->oprint("Running cmake --build\n") if $self->{verbose};
            $self->_run(logfile => "$self->{obj_dir}/vlt_cmake_build.log",
                        cmd => ["cmake",
                                "--build", $self->{obj_dir},
                                ($self->{verbose}?"--verbose":""),
                        ]);
        }
    }
    else {
        $self->error("No compile step defined for '$self->{scenario}' scenario");
    }

    if ($param{make_pli}) {
        $self->oprint("Compile vpi\n") if $self->{verbose};
        my @cmd = ('c++', @{$param{pli_flags}}, "-DIS_VPI",
                   "$self->{t_dir}/$self->{pli_filename}");

        $self->_run(logfile=>"$self->{obj_dir}/pli_compile.log",
                    fails=>$param{fails},
                    cmd=>\@cmd);
    }

    return 1;
}

sub execute {
    my $self = (ref $_[0]? shift : $Self);
    return 1 if $self->errors || $self->skips || $self->unsupporteds;
    my %param = (%{$self}, @_);  # Default arguments are from $self
    # params may be expect or {tool}_expect
    $self->oprint("Run\n") if $self->{verbose};

    delete $ENV{SYSTEMC_DISABLE_COPYRIGHT_MESSAGE};
    $ENV{SYSTEMC_DISABLE_COPYRIGHT_MESSAGE} = "DISABLE" if !$self->{verbose};

    my $run_env = $param{run_env};
    $run_env .= ' ' if $run_env;

    if ($param{atsim}) {
        $self->_run(logfile=>"$self->{obj_dir}/atsim_sim.log",
                    fails=>$param{fails},
                    cmd=>["echo q | ".$run_env."$self->{obj_dir}/athdl_sv",
                          @{$param{atsim_run_flags}},
                          @{$param{all_run_flags}},
                          ],
                    %param,
                    expect=>$param{atsim_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{atsim_run_expect_filename},
                    );
    }
    elsif ($param{ghdl}) {
        $self->_run(logfile=>"$self->{obj_dir}/ghdl_sim.log",
                    fails=>$param{fails},
                    cmd=>[$run_env."$self->{obj_dir}/simghdl",
                          @{$param{ghdl_run_flags}},
                          @{$param{all_run_flags}},
                          ],
                    %param,
                    expect=>$param{ghdl_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{ghdl_run_expect_filename},
                    );
    }
    elsif ($param{iv}) {
        my @cmd = ($run_env."$self->{obj_dir}/simiv",
                   @{$param{iv_run_flags}},
                   @{$param{all_run_flags}},
                          );
        if ($param{iv_pli}) {
            # don't enter command line on $stop, include vpi
            unshift @cmd, "vvp -n -m $self->{obj_dir}/libvpi.so";
        }
        $self->_run(logfile=>"$self->{obj_dir}/iv_sim.log",
                    fails=>$param{fails},
                    cmd=> \@cmd,
                    %param,
                    expect=>$param{iv_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{iv_run_expect_filename},
                    );
    }
    elsif ($param{ms}) {
        my @pli_opt=();
        if ($param{ms_pli}) {
            unshift @pli_opt, "-pli $self->{obj_dir}/libvpi.so";
        }
        $self->_run(logfile=>"$self->{obj_dir}/ms_sim.log",
                    fails=>$param{fails},
                    cmd=>["echo q | ".$run_env.($ENV{VERILATOR_MODELSIM}||"vsim"),
                          @{$param{ms_run_flags}},
                          @{$param{all_run_flags}},
                          @{pli_opt},
                          (" top")
                          ],
                    %param,
                    expect=>$param{ms_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{ms_expect_filename},
                    );
    }
    elsif ($param{nc}) {
        $self->_run(logfile=>"$self->{obj_dir}/nc_sim.log",
                    fails=>$param{fails},
                    cmd=>["echo q | ".$run_env.($ENV{VERILATOR_NCVERILOG}||"ncverilog"),
                          @{$param{nc_run_flags}},
                          @{$param{all_run_flags}},
                          ],
                    %param,
                    expect=>$param{nc_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{nc_run_expect_filename},
                    );
    }
    elsif ($param{vcs}) {
        #my $fh = IO::File->new(">simv.key") or die "%Error: $! simv.key,";
        #$fh->print("quit\n"); $fh->close;
        $self->_run(logfile=>"$self->{obj_dir}/vcs_sim.log",
                    cmd=>["echo q | ".$run_env."./simv",
                          @{$param{vcs_run_flags}},
                          @{$param{all_run_flags}},
                          ],
                    %param,
                    expect=>$param{vcs_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{vcs_run_expect_filename},
                    );
    }
    elsif ($param{xsim}) {
        $self->_run(logfile=>"$self->{obj_dir}/xsim_sim.log",
                    fails=>$param{fails},
                    cmd=>[$run_env.($ENV{VERILATOR_XELAB}||"xelab"),
                          @{$param{xsim_run_flags}},
                          @{$param{xsim_run_flags2}},
                          @{$param{all_run_flags}},
                          (" $self->{name}.top")
                          ],
                    %param,
                    expect=>$param{xsim_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{xsim_expect_filename},
                    );
    }
    elsif ($param{vlt_all}
        #&& (!$param{needs_v4} || -r "$ENV{VERILATOR_ROOT}/src/V3Gate.cpp")
        ) {
        $param{executable} ||= "$self->{obj_dir}/$param{VM_PREFIX}";
        my $debugger = "";
        if ($opt_gdbsim) {
            $debugger = ($ENV{VERILATOR_GDB}||"gdb")." ";
        } elsif ($opt_rrsim) {
            $debugger = "rr record ";
        }
        $self->_run(logfile=>"$self->{obj_dir}/vlt_sim.log",
                    cmd=>[($run_env
                           .$debugger
                           .$param{executable}
                           .($opt_gdbsim ? " -ex 'run " : "")),
                          @{$param{all_run_flags}},
                          ($opt_gdbsim ? "'" : ""),
                    ],
                    %param,
                    expect=>$param{expect},  # backward compatible name
                    expect_filename=>$param{expect_filename},  # backward compatible name
                    );
    }
    else {
        $self->error("No execute step for this simulator");
    }
}

sub inline_checks {
    my $self = (ref $_[0]? shift : $Self);
    return 1 if $self->errors || $self->skips || $self->unsupporteds;
    return 1 if !$self->{vlt_all};

    my %param = (%{$self}, @_);  # Default arguments are from $self

    my $covfn = $Self->{coverage_filename};
    my $contents = $self->file_contents($covfn);

    $self->oprint("Extract checks\n") if $self->{verbose};
    my $fh = IO::File->new("<$self->{top_filename}");
    while (defined(my $line = $fh->getline)) {
        if ($line =~ /CHECK/) {
            if ($line =~ /CHECK_COVER *\( *([---0-9]+) *, *"([^"]+)" *, *("([^"]+)" *,|) *(\d+) *\)/) {
                my $lineno=($. + $1); my $hier=$2; my $comment=$4; my $count=$5;
                my $regexp = "\001l\002".$lineno;
                $regexp .= ".*\001o\002".quotemeta($comment) if $comment;
                $regexp .= ".*\001h\002".quotemeta($hier);
                $regexp .= ".*' ".$count;
                if ($contents !~ /$regexp/) {
                    $self->error("CHECK_COVER: $covfn: Regexp not found: $regexp\n".
                                 "From $self->{top_filename}:$.: $line");
                }
            }
            elsif ($line =~ /CHECK_COVER_MISSING *\( *([---0-9]+) *\)/) {
                my $lineno=($. + $1);
                my $regexp = "\001l\002".$lineno;
                if ($contents =~ /$regexp/) {
                    $self->error("CHECK_COVER_MISSING: $covfn: Regexp found: $regexp\n".
                                 "From $self->{top_filename}:$.: $line");
                }
            }
            else {
                $self->error("$self->{top_filename}:$.: Unknown CHECK request: $line");
            }
        }
    }
    $fh->close;
}

#----------------------------------------------------------------------
# Accessors

sub ok {
    my $self = (ref $_[0]? shift : $Self);
    $self->{ok} = $_[0] if defined $_[0];
    $self->{ok} = 0 if $self->{errors} || $self->{skips} || $self->unsupporteds;
    return $self->{ok};
}

sub continuing {
    my $self = (ref $_[0]? shift : $Self);
    return !($self->errors || $self->skips || $self->unsupporteds);
}

sub errors {
    my $self = (ref $_[0]? shift : $Self);
    return $self->{errors};
}

sub scenario_off {
    my $self = (ref $_[0]? shift : $Self);
    return $self->{scenario_off};
}

sub skips {
    my $self = (ref $_[0]? shift : $Self);
    return $self->{skips};
}

sub unsupporteds {
    my $self = (ref $_[0]? shift : $Self);
    return $self->{unsupporteds};
}

sub top_filename {
    my $self = (ref $_[0]? shift : $Self);
    $self->{top_filename} = shift if defined $_[0];
    return $self->{top_filename};
}

sub vhdl {
    my $self = (ref $_[0]? shift : $Self);
    $self->{vhdl} = shift if defined $_[0];
    if ($self->{vhdl}) {
        $self->{top_filename} =~ s/\.v$/\.vhdl/;
    }
    return $self->{vhdl};
}

sub v_suffix {
    my $self = (ref $_[0]? shift : $Self);
    # Suffix for file type, e.g. .vhdl or .v
    return $self->{vhdl} ? "vhdl" : "v";
}

sub sc {
    my $self = (ref $_[0]? shift : $Self);
    return $self->{sc};
}

sub have_sc {
    #my $self = shift;
    return 1 if (defined $ENV{SYSTEMC} || defined $ENV{SYSTEMC_INCLUDE});
    return 0;
}

sub have_cmake {
    return cmake_version() >= version->declare("3.8");
}

sub cmake_version {
    chomp(my $cmake_bin = `which cmake`);
    if (!$cmake_bin) {
        return undef;
    }
    my $cmake_version = `cmake --version`;
    if ($cmake_version !~ /cmake version (\d+)\.(\d+)/) {
        return undef;
    }
    $cmake_version = "$1.$2";
    return version->declare($cmake_version);
}

sub trace_filename {
    my $self = shift;
    return "$self->{obj_dir}/simx.fst" if $self->{trace_format} =~ /^fst/;
    return "$self->{obj_dir}/simx.vcd";
}

sub obj_dir {
    my $self = shift;
    return $self->{obj_dir};
}

sub get_default_vltmt_threads {
    return $Vltmt_threads;
}

sub pli_filename {
    my $self = (ref $_[0]? shift : $Self);
    $self->{pli_filename} = shift if defined $_[0];
    return $self->{pli_filename};
}

sub too_few_cores {
    my $threads = ::calc_threads($Vltmt_threads);
    return $threads < $Vltmt_threads;
}

sub skip_if_too_few_cores {
    my $self = (ref $_[0]? shift : $Self);
    if (too_few_cores()) {
        $self->skip("Skipping due to too few cores\n");
    }
}

sub wno_unopthreads_for_few_cores {
    if (too_few_cores()) {
        warn "Too few cores, using -Wno-UNOPTTHREADS\n";
        return "-Wno-UNOPTTHREADS";
    }
    return "";
}

sub VM_PREFIX {
    my $self = (ref $_[0]? shift : $Self);
    $self->{VM_PREFIX} = shift if defined $_[0];
    return $self->{VM_PREFIX};
}

#----------------------------------------------------------------------

sub run {
    my $self = (ref $_[0]? shift : $Self);
    $self->_run(@_);
}
sub _run {
    my $self = (ref $_[0]? shift : $Self);
    my %param = (tee => 1,
                 #entering =>  # Print entering directory information
                 @_);
    my $command = join(' ',@{$param{cmd}});
    $command = "time $command" if $opt_benchmark && $command !~ /^cd /;
    print "\t$command";
    print "   > $param{logfile}" if $param{logfile};
    print "\n";

    # Execute command redirecting output, keeping order between stderr and stdout.
    # Must do low-level IO so GCC interaction works (can't be line-based)
    my $status;
    {
        pipe(PARENTRD, CHILDWR) or die "%Error: Can't Pipe, stopped";
        autoflush PARENTRD 1;
        autoflush CHILDWR 1;
        my $logfh;
        if ($param{logfile}) {
            $logfh = IO::File->new(">$param{logfile}") or die "%Error: Can't open $param{logfile}";
        }
        my $pid=fork();
        if ($pid) {  # Parent
            close CHILDWR;
            print "driver: Entering directory '",
                File::Spec->rel2abs($param{entering}), "'\n" if $param{entering};
            while (1) {
                my $buf = '';
                my $got = sysread PARENTRD,$buf,10000;
                last if defined $got && $got==0;
                print $buf if $param{tee};
                print $logfh $buf if $logfh;
            }
            close PARENTRD;
            close $logfh if $logfh;
            print "driver: Leaving directory '",
                File::Spec->rel2abs($param{entering}), "'\n" if $param{entering};
        }
        else {  # Child
            close PARENTRD;
            close $logfh if $logfh;
            # Reset signals
            $SIG{ALRM} = 'DEFAULT';
            $SIG{CHLD} = 'DEFAULT';
            # Logging
            open(STDOUT, ">&CHILDWR") or croak "%Error: Can't redirect stdout, stopped";
            open(STDERR, ">&STDOUT") or croak "%Error: Can't dup stdout, stopped";
            autoflush STDOUT 1;
            autoflush STDERR 1;
            system "$command";
            my $status = $?;
            if (($status & 127) == 4  # SIGILL
                || ($status & 127) == 8  # SIGFPA
                || ($status & 127) == 11) {  # SIGSEGV
                $Self->error("Exec failed with core dump");
            }
            exit($? ? 10 : 0);  # $?>>8 misses coredumps
        }
        waitpid($pid,0);
        $status = $? || 0;
    }
    flush STDOUT;
    flush STDERR;

    if (!$param{fails} && $status) {
        my $firstline = "";
        if (my $fh = IO::File->new("<$param{logfile}")) {
            $firstline = $fh->getline || '';
            chomp $firstline;
        }
        $self->error("Exec of $param{cmd}[0] failed: $firstline\n");
    }
    if ($param{fails} && $status) {
        print "(Exec expected to fail, and did.)\n";
    }
    if ($param{fails} && !$status) {
        $self->error("Exec of $param{cmd}[0] ok, but expected to fail\n");
    }
    return if $self->errors || $self->skips || $self->unsupporteds;

    # Read the log file a couple of times to allow for NFS delays
    if ($param{check_finished} || $param{expect}) {
        for (my $try = $self->tries - 1; $try >= 0; $try--) {
            sleep 1 if ($try != $self->tries - 1);
            my $moretry = $try != 0;

            my $fh = IO::File->new("<$param{logfile}");
            next if !$fh && $moretry;
            local $/; undef $/;
            my $wholefile = <$fh>;
            $fh->close();

            # Finished?
            if ($param{check_finished} && $wholefile !~ /\*\-\* All Finished \*\-\*/) {
                next if $moretry;
                $self->error("Missing All Finished\n");
            }
            if ($param{expect}) {
                # Strip debugging comments
                # See also files_identical
                $wholefile =~ s/^- [^\n]+\n//mig;
                $wholefile =~ s/^- [a-z.0-9]+:\d+:[^\n]+\n//mig;
                $wholefile =~ s/^dot [^\n]+\n//mig;

                # Compare
                my $quoted = quotemeta($param{expect});
                my $ok = ($wholefile eq $param{expect}
                          || _try_regex($wholefile, $param{expect}) == 1
                          || $wholefile =~ /$quoted/ms);
                if (!$ok) {
                    #print "**BAD  $self->{name} $param{logfile} MT $moretry  $try\n";
                    next if $moretry;
                    $self->error("Mismatch in output from $param{cmd}[0]\n");
                    $self->error("Might be error in regexp format\n") if $ok<1;
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
    if ($param{expect_filename}) {
        files_identical($param{logfile}, $param{expect_filename}, 'logfile');
    }
}

#######################################################################
# Little utilities

sub _try_regex {
    # Try to eval a regexp
    # Returns:
    #  1 if $text ~= /$regex/ms
    #  0 if no match
    # -1 if $regex is invalid, doesn't compile
    my ($text, $regex) = @_;
    my $result;
    {
        local $@;
        eval {
            $result = ($text =~ /$regex/ms);
        };
        $result = -1 if $@;
    }
    return $result;
}

sub _make_main {
    my $self = shift;

    if ($self->vhdl) {
        $self->_read_inputs_vhdl();
    } else {
        $self->_read_inputs_v();
    }

    my $filename = $self->{main_filename};
    my $fh = IO::File->new(">$filename") or die "%Error: $! $filename,";

    print $fh "// Test defines\n";
    print $fh "#define VL_TIME_MULTIPLIER $self->{vl_time_multiplier}\n" if $self->{vl_time_multiplier};

    print $fh "// OS header\n";
    print $fh "#include \"verilatedos.h\"\n";

    print $fh "// Generated header\n";
    my $VM_PREFIX = $self->{VM_PREFIX};
    print $fh "#include \"$VM_PREFIX.h\"\n";

    print $fh "// General headers\n";
    print $fh "#include \"verilated.h\"\n";
    print $fh "#include \"systemc.h\"\n" if $self->sc;
    print $fh "#include \"verilated_fst_c.h\"\n" if $self->{trace} && $self->{trace_format} eq 'fst-c';
    print $fh "#include \"verilated_vcd_c.h\"\n" if $self->{trace} && $self->{trace_format} eq 'vcd-c';
    print $fh "#include \"verilated_vcd_sc.h\"\n" if $self->{trace} && $self->{trace_format} eq 'vcd-sc';
    print $fh "#include \"verilated_save.h\"\n" if $self->{savable};

    print $fh "$VM_PREFIX* topp;\n";
    if (!$self->sc) {
        print $fh "vluint64_t main_time = false;\n";
        print $fh "double sc_time_stamp() { return main_time; }\n";
    }

    if ($self->{savable}) {
        $fh->print("\n");
        $fh->print("void save_model(const char* filenamep) {\n");
        $fh->print("    VL_PRINTF(\"Saving model to '%s'\\n\", filenamep);\n");
        $fh->print("    VerilatedSave os;\n");
        $fh->print("    os.open(filenamep);\n");
        $fh->print("    os << main_time;\n");
        $fh->print("    os << *topp;\n");
        $fh->print("    os.close();\n");
        $fh->print("}\n");
        $fh->print("\n");
        $fh->print("void restore_model(const char* filenamep) {\n");
        $fh->print("    VL_PRINTF(\"Restoring model from '%s'\\n\", filenamep);\n");
        $fh->print("    VerilatedRestore os;\n");
        $fh->print("    os.open(filenamep);\n");
        $fh->print("    os >> main_time;\n");
        $fh->print("    os >> *topp;\n");
        $fh->print("    os.close();\n");
        $fh->print("}\n");
    }

    #### Main
    if ($self->sc) {
        print $fh "extern int sc_main(int argc, char** argv);\n";
        print $fh "int sc_main(int argc, char** argv) {\n";
        print $fh "    sc_signal<bool> fastclk;\n" if $self->{inputs}{fastclk};
        print $fh "    sc_signal<bool> clk;\n"  if $self->{inputs}{clk};
        print $fh "    sc_time sim_time($self->{sim_time}, SC_NS);\n";
    } else {
        print $fh "int main(int argc, char** argv, char** env) {\n";
        print $fh "    double sim_time = $self->{sim_time};\n";
    }
    print $fh "    Verilated::commandArgs(argc, argv);\n";
    print $fh "    Verilated::debug(".($self->{verilated_debug}?1:0).");\n";
    print $fh "    srand48(5);\n";  # Ensure determinism
    print $fh "    Verilated::randReset(".$self->{verilated_randReset}.");\n" if defined $self->{verilated_randReset};
    print $fh "    topp = new $VM_PREFIX(\"top\");\n";
    print $fh "    Verilated::internalsDump()\n;" if $self->{verilated_debug};

    my $set;
    if ($self->sc) {
        print $fh "    topp->fastclk(fastclk);\n" if $self->{inputs}{fastclk};
        print $fh "    topp->clk(clk);\n" if $self->{inputs}{clk};
        $set = "";
    } else {
        print $fh "    topp->eval();\n";
        $set = "topp->";
    }

    if ($self->{trace}) {
        $fh->print("\n");
        $fh->print("#if VM_TRACE\n");
        $fh->print("    Verilated::traceEverOn(true);\n");
        $fh->print("    VerilatedFstC* tfp = new VerilatedFstC;\n") if $self->{trace_format} eq 'fst-c';
        $fh->print("    VerilatedVcdC* tfp = new VerilatedVcdC;\n") if $self->{trace_format} eq 'vcd-c';
        $fh->print("    VerilatedVcdSc* tfp = new VerilatedVcdSc;\n") if $self->{trace_format} eq 'vcd-sc';
        $fh->print("    topp->trace(tfp, 99);\n");
        $fh->print("    tfp->open(\"".$self->trace_filename."\");\n");
        if ($self->{trace} && !$self->sc) {
            $fh->print("    if (tfp) tfp->dump(main_time);\n");
        }
        $fh->print("#endif\n");
    }

    if ($self->{savable}) {
        $fh->print("    const char* save_time_strp  = Verilated::commandArgsPlusMatch(\"save_time=\");\n");
        $fh->print("    unsigned int save_time = !save_time_strp[0] ? 0 : atoi(save_time_strp+strlen(\"+save_time=\"));\n");
        $fh->print("    const char* save_restore_strp = Verilated::commandArgsPlusMatch(\"save_restore=\");\n");
        $fh->print("    unsigned int save_restore = !save_restore_strp[0] ? 0 : 1;\n");
    }

    if ($self->{savable}) {
        $fh->print("    if (save_restore) {\n");
        $fh->print("        restore_model(\"$self->{obj_dir}/saved.vltsv\");\n");
        $fh->print("    } else {\n");
    } else {
        $fh->print("    {\n");
    }
    print $fh "        ${set}fastclk = false;\n" if $self->{inputs}{fastclk};
    print $fh "        ${set}clk = false;\n" if $self->{inputs}{clk};
    _print_advance_time($self, $fh, 10);
    print $fh "    }\n";

    print $fh "    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {\n";
    for (my $i=0; $i<5; $i++) {
        my $action = 0;
        if ($self->{inputs}{fastclk}) {
            print $fh "        ${set}fastclk = !${set}fastclk;\n";
            $action = 1;
        }
        if ($i==0 && $self->{inputs}{clk}) {
            print $fh "        ${set}clk = !${set}clk;\n";
            $action = 1;
        }
        if ($self->{savable}) {
            $fh->print("        if (sc_time_stamp() == save_time && save_time) {\n");
            $fh->print("            save_model(\"$self->{obj_dir}/saved.vltsv\");\n");
            $fh->print("            printf(\"Exiting after save_model\\n\");\n");
            $fh->print("            exit(0);\n");
            $fh->print("        }\n");
        }
        _print_advance_time($self, $fh, 1, $action);
    }
    print $fh "    }\n";
    print $fh "    if (!Verilated::gotFinish()) {\n";
    print $fh '        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");',"\n";
    print $fh "    }\n";
    print $fh "    topp->final();\n";

    if ($self->{coverage}) {
        $fh->print("#if VM_COVERAGE\n");
        $fh->print("    VerilatedCov::write(\"",$self->{coverage_filename},"\");\n");
        $fh->print("#endif  // VM_COVERAGE\n");
    }
    if ($self->{trace}) {
        $fh->print("#if VM_TRACE\n");
        $fh->print("    if (tfp) tfp->close();\n");
        $fh->print("#endif  // VM_TRACE\n");
    }
    $fh->print("\n");

    print $fh "    VL_DO_DANGLING(delete topp, topp);\n";
    print $fh "    exit(0L);\n";
    print $fh "}\n";
    $fh->close();
}

sub _print_advance_time {
    my $self = shift;
    my $fh = shift;
    my $time = shift;
    my $action = shift;

    my $set;
    if ($self->sc) { $set = ""; }
    else { $set = "topp->"; }

    if ($self->sc) {
        print $fh "#if (SYSTEMC_VERSION>=20070314)\n";
        print $fh "        sc_start(${time}, SC_NS);\n";
        print $fh "#else\n";
        print $fh "        sc_start(${time});\n";
        print $fh "#endif\n";
    } else {
        if ($action) {
            print $fh "        ${set}eval();\n";
            if ($self->{trace} && !$self->sc) {
                $fh->print("#if VM_TRACE\n");
                $fh->print("        if (tfp) tfp->dump(main_time);\n");
                $fh->print("#endif  // VM_TRACE\n");
            }
        }
        print $fh "        main_time += ${time};\n";
    }
}

#######################################################################

sub _make_top {
    my $self = shift;
    if ($self->vhdl) {
        $self->_make_top_vhdl;
    } else {
        $self->_make_top_v;
    }
}

sub _make_top_v {
    my $self = shift;

    $self->_read_inputs_v();

    my $fh = IO::File->new(">$self->{top_shell_filename}") or die "%Error: $! $self->{top_shell_filename},";
    print $fh "module top;\n";
    foreach my $inp (sort (keys %{$self->{inputs}})) {
        print $fh "    reg ${inp};\n";
    }
    # Inst
    print $fh "    t t (\n";
    my $comma="";
    foreach my $inp (sort (keys %{$self->{inputs}})) {
        print $fh "      ${comma}.${inp} (${inp})\n";
        $comma=",";
    }
    print $fh "    );\n";

    # Waves
    print $fh "\n";
    print $fh "`ifdef WAVES\n";
    print $fh "   initial begin\n";
    print $fh "      \$display(\"-Tracing Waves to Dumpfile: ".$self->trace_filename."\");\n";
    print $fh "      \$dumpfile(\"".$self->trace_filename."\");\n";
    print $fh "      \$dumpvars(0, top);\n";
    print $fh "   end\n";
    print $fh "`endif\n";

    # Test
    print $fh "\n";
    print $fh "    initial begin\n";
    print $fh "        fastclk = 0;\n" if $self->{inputs}{fastclk};
    print $fh "        clk = 0;\n" if $self->{inputs}{clk};
    print $fh "        #10;\n";
    print $fh "        fastclk = 1;\n" if $self->{inputs}{fastclk};
    print $fh "        clk = 1;\n" if $self->{inputs}{clk};
    print $fh "        while (\$time < $self->{sim_time}) begin\n";
    for (my $i=0; $i<5; $i++) {
        print $fh "          #1;\n";
        print $fh "          fastclk = !fastclk;\n" if $self->{inputs}{fastclk};
        print $fh "          clk = !clk;\n" if $i==4 && $self->{inputs}{clk};
    }
    print $fh "        end\n";
    print $fh "    end\n";

    print $fh "endmodule\n";
    $fh->close();
}

sub _make_top_vhdl {
    my $self = shift;

    $self->_read_inputs_vhdl();

    my $fh = IO::File->new(">$self->{top_shell_filename}") or die "%Error: $! $self->{top_shell_filename},";
    print $fh "library ieee;\n";

    my @ports = sort (keys %{$self->{inputs}});

    print $fh "entity t_ent is\n";
    if ($#ports >= 0) {
        print $fh "       port(\n";
        my $semi = "";
        foreach my $inp (@ports) {
            print $fh "        ${semi}${inp} : in std_logic\n";
            $semi=";";
        }
        print $fh "    );\n";
    }
    print $fh "end;\n";

    print $fh "entity top is\n";
    print $fh "end;\n";

    # Inst
    print $fh "architecture t_beh of t_ent is\n";
    if ($#ports >= 0) {
        foreach my $inp (@ports) {
            print $fh "      signal ${inp} : std_logic := '0';\n";
        }
    }
    print $fh "   begin\n";

    print $fh "    t : t_ent\n";
    if ($#ports >= 0) {
        print $fh "       port map(\n";
        my $comma="";
        foreach my $inp (@ports) {
            print $fh "\t${comma}${inp} => ${inp}\n";
            $comma=",";
        }
        print $fh "    )\n";
    }
    print $fh "   ;\n";

    print $fh "   end;\n";

    # Waves TBD
    # Test TBD

    print $fh "end;\n";
    $fh->close();
}

#######################################################################

sub _read_inputs_v {
    my $self = shift;
    my $filename = $self->top_filename;
    $filename = "$self->{t_dir}/$filename" if !-r $filename;
    my $fh = IO::File->new("<$filename") or die "%Error: $! $filename,";
    my $get_sigs=1;
    my %inputs;
    while (defined(my $line = $fh->getline)) {
        if ($get_sigs) {
            if ($line =~ /^\s*input\s*(\S+)\s*(\/[^\/]+\/|)\s*;/) {
                $inputs{$1} = $1;
            }
            if ($line =~ /^\s*(function|task|endmodule)/) {
                $get_sigs = 0;
            }
        }
        if ($line =~ /^\s*module\s+t\b/) {  # Ignore any earlier inputs; Module 't' has precedence
            %inputs = ();
            $get_sigs = 1;
        }
    }
    $self->{inputs}{$_} = $inputs{$_} foreach keys %inputs;
    $fh->close();
}

#######################################################################

sub _read_inputs_vhdl {
    my $self = shift;
    my $filename = $self->top_filename;
    $filename = "$self->{t_dir}/$filename" if !-r $filename;
    my $fh = IO::File->new("<$filename") or die "%Error: $! $filename,";
    while (defined(my $line = $fh->getline)) {
        # Only supports this form right now:
        # signal: in ...
        # signal: out ...
        if ($line =~ /^\s*(\S+)\s*:\s*(in)\b\s*/) {
            $self->{inputs}{$1} = $1;
        }
        if ($line =~ /^\s*(architecture)/) {
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
        my @args = ("perl", "$ENV{VERILATOR_ROOT}/bin/verilator", "--version");
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
    my $self = (ref $_[0]? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    my $fn1_is_logfile = shift;
    return 1 if $self->errors || $self->skips || $self->unsupporteds;

  try:
    for (my $try = $self->tries - 1; $try >= 0; $try--) {
        sleep 1 if ($try != $self->tries - 1);
        my $moretry = $try != 0;

        my $f1 = IO::File->new("<$fn1");
        my $f2 = IO::File->new("<$fn2");
        if (!$f1) {
            next try if $moretry;
            $self->error("Files_identical file does not exist $fn1\n");
            return 0;
        }
        if (!$f2 && !$ENV{HARNESS_UPDATE_GOLDEN}) {
            next try if $moretry;
            $self->error("Files_identical file does not exist $fn2\n");
            return 0;
        }
        my @l1 = $f1 && $f1->getlines();
        my @l2 = $f2 && $f2->getlines();
        if ($fn1_is_logfile) {
            @l1 = grep {
                !/^- [^\n]+\n/
                    && !/^- [a-z.0-9]+:\d+:[^\n]+\n/
                    && !/^-node:/
                    && !/^dot [^\n]+\n/
            } @l1;
            @l1 = map {
                s/(Internal Error: [^\n]+\.cpp):[0-9]+:/$1:#:/;
                s/^-V\{t[0-9]+,[0-9]+\}/-V{t#,#}/;  # --vlt vs --vltmt run differences
                $_;
            } @l1;
            for (my $l=0; $l<=$#l1; ++$l) {
                # Don't put control chars into our source repository
                $l1[$l] =~ s/\r/<#013>/mig;
                $l1[$l] =~ s/Command Failed[^\n]+/Command Failed/mig;
                $l1[$l] =~ s/Version: Verilator[^\n]+/Version: Verilator ###/mig;
                if ($l1[$l] =~ s/Exiting due to.*/Exiting due to/mig) {
                    splice @l1, $l+1;  # Trunc rest
                    last;
                }
            }
        }
        my $nl = $#l1;  $nl = $#l2 if ($#l2 > $nl);
        for (my $l=0; $l<=$nl; ++$l) {
            if (($l1[$l]||"") ne ($l2[$l]||"")) {
                next try if $moretry;
                $self->error("Line ".($l+1)." mismatches; $fn1 != $fn2");
                warn("F1: ".($l1[$l]||"*EOF*\n")
                     ."F2: ".($l2[$l]||"*EOF*\n"));
                if ($ENV{HARNESS_UPDATE_GOLDEN}) {  # Update golden files with current
                    warn "%Warning: HARNESS_UPDATE_GOLDEN set: cp $fn1 $fn2\n";
                    my $fhw = IO::File->new(">$fn2") or $self->error("Files_identical $! $fn2\n");
                    $fhw->print(join('',@l1));
                } else {
                    warn "To update reference: HARNESS_UPDATE_GOLDEN=1 {command} or --golden\n";
                }
                return 0;
            }
        }
        return 1;
    }
}

sub copy_if_golden {
    my $self = (ref $_[0]? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    if ($ENV{HARNESS_UPDATE_GOLDEN}) {  # Update golden files with current
        warn "%Warning: HARNESS_UPDATE_GOLDEN set: cp $fn1 $fn2\n";
        eval "use File::Copy;";
        File::Copy::copy($fn1, $fn2);
    }
}

sub vcd_identical {
    my $self = (ref $_[0]? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    return 0 if $self->errors || $self->skips || $self->unsupporteds;
    if (!-r $fn1) { $self->error("Vcd_identical file does not exist $fn1\n"); return 0; }
    if (!-r $fn2) { $self->error("Vcd_identical file does not exist $fn2\n"); return 0; }
    {
        # vcddiff to check transitions, if installed
        my $cmd = qq{vcddiff --help};
        print "\t$cmd\n" if $::Debug;
        my $out = `$cmd`;
        if (!$out || $out !~ /Usage:/) { $self->skip("No vcddiff installed\n"); return 1; }

        $cmd = qq{vcddiff "$fn1" "$fn2"};
        print "\t$cmd\n" if $::Debug;
        $out = `$cmd`;
        if ($out ne '') {
            print $out;
            $self->error("VCD miscompare $fn1 $fn2\n");
            $self->copy_if_golden($fn1, $fn2);
            return 0;
        }
    }
    {
        # vcddiff doesn't check module and variable scope, so check that
        # Also provides backup if vcddiff not installed
        my $h1 = $self->_vcd_read($fn1);
        my $h2 = $self->_vcd_read($fn2);
        $Data::Dumper::Sortkeys = 1;
        my $a = Dumper($h1);
        my $b = Dumper($h2);
        if ($a ne $b) {
            print "$a\n$b\n" if $::Debug;
            $self->error("VCD hier mismatch $fn1 $fn2\n");
            $self->copy_if_golden($fn1, $fn2);
            return 0;
        }
    }
    return 1;
}

sub fst2vcd {
    my $self = (ref $_[0]? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    if (!-r $fn1) { $self->error("File does not exist $fn1\n"); return 0; }
    my $cmd = qq{fst2vcd --help};
    print "\t$cmd\n" if $::Debug;
    my $out = `$cmd`;
    if (!$out || $out !~ /Usage:/) { $self->skip("No fst2vcd installed\n"); return 1; }

    $cmd = qq{fst2vcd -e "$fn1" -o "$fn2"};
    print "\t$cmd\n";  # Always print to help debug race cases
    $out = `$cmd`;
    return 1;
}

sub fst_identical {
    my $self = (ref $_[0]? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    my $tmp = $fn1.".vcd";
    fst2vcd($fn1, $tmp);
    return vcd_identical($tmp, $fn2);
}

sub _vcd_read {
    my $self = (ref $_[0]? shift : $Self);
    my $filename = shift;
    my $data = {};
    my $fh = IO::File->new("<$filename");
    if (!$fh) { warn "%Error: $! $filename\n"; return $data; }
    my @hier = ($data);
    my $lasthier;
    while (defined(my $line = $fh->getline)) {
        if ($line =~ /\$scope module\s+(\S+)/) {
            $hier[$#hier]->{$1} ||= {};
            push @hier, $hier[$#hier]->{$1};
            $lasthier = $hier[$#hier];
        } elsif ($line =~ /(\$var \S+\s+\d+\s+)\S+\s+(\S+)/) {
            $hier[$#hier]->{$1.$2} ||= {};
            $lasthier = $hier[$#hier];
        } elsif ($line =~ /(\$attrbegin .* \$end)/) {
            if ($lasthier) { $lasthier->{$1} ||= 1; }
        } elsif ($line =~ /\$enddefinitions/) {
            last;
        }
        while ($line =~ s/\$upscope//) {
            pop @hier;
            $lasthier = undef;
        }
    }
    return $data;
}

our $_Cxx_Version;
sub cxx_version {
    $_Cxx_Version ||= `make -C $ENV{VERILATOR_ROOT}/test_regress -f Makefile print-cxx-version`;
    return $_Cxx_Version;
}

our $_Cfg_With_Threaded;
sub cfg_with_threaded {
    $_Cfg_With_Threaded ||= `make -C $ENV{VERILATOR_ROOT} -f Makefile print-cfg-with-threaded`;
    return ($_Cfg_With_Threaded =~ /yes/i) ? 1:0;
}

sub tries {
    # Number of retries when reading logfiles, generally only need many
    # retries when system is busy running a lot of tests
    return 2 if !$::Fork->running;
    return 7 if (scalar($::Fork->running)) > 1;
    return 2;
}

sub file_grep_not {
    my $self = (ref $_[0]? shift : $Self);
    my $filename = shift;
    my $regexp = shift;
    my $expvalue = shift;
    return if $self->errors || $self->skips || $self->unsupporteds;
    !defined $expvalue or $self->error("file_grep_not: Unexpected 3rd argument: $expvalue");

    my $contents = $self->file_contents($filename);
    return if ($contents eq "_Already_Errored_");
    if ($contents =~ /$regexp/) {
        $self->error("File_grep_not: $filename: Regexp found: $regexp\n");
    }
}

sub file_grep {
    my $self = (ref $_[0]? shift : $Self);
    my $filename = shift;
    my $regexp = shift;
    my $expvalue = shift;
    return if $self->errors || $self->skips || $self->unsupporteds;

    my $contents = $self->file_contents($filename);
    return if ($contents eq "_Already_Errored_");
    if ($contents !~ /$regexp/) {
        $self->error("File_grep: $filename: Regexp not found: $regexp\n");
    } elsif ($expvalue && $expvalue ne $1) {
        $self->error("File_grep: $filename: Got='$1' Expected='$expvalue' in regexp: $regexp\n");
    }
}

my %_File_Contents_Cache;

sub file_contents {
    my $self = (ref $_[0]? shift : $Self);
    my $filename = shift;

    if (!$_File_Contents_Cache{$filename}) {
        my $fh = IO::File->new("<$filename");
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

sub write_wholefile {
    my $self = (ref $_[0]? shift : $Self);
    my $filename = shift;
    my $contents = shift;
    my $fh = IO::File->new(">$filename") or die "%Error: $! writing $filename,";
    print $fh $contents;
    $fh->close;
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

    if (my $pid = fork()) {  # Parent
        waitpid($pid, 0);
    } else {  # Child
        $params{run_on_start}->($self);
        exit(0);  # Don't close anything
    }
    $params{run_on_finish}->($self);
    return $self;
}
sub max_proc {}
sub sig_child {}
sub kill_tree_all {}
sub wait_all {}
sub ready {}
sub running {}
sub is_any_left { return 0; }

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

driver.pl invokes Verilator or another simulator on each test file.

The driver reports the number of tests which pass, fail, skipped (some
resource required by the test is not available, such as SystemC), or are
unsupported (buggy or require a feature change before will pass.)

There are hundreds of tests, and for faster completion you may want to run
the regression tests with OBJCACHE enabled and in parallel on a machine
with many cores.  See the -j option and OBJCACHE environment variable.

=head1 TEST CONFIGURATION

The Perl script (e.g. C<test_regres/t/t_EXAMPLE.pl>) controls how the test
will run by driver.pl. In general it includes a call to the C<compile>
subroutine to compile the test with Verilator (or an alternative
simulator), followed by a call to the C<execute> subroutine to run the
test. Compile-only tests omit the call to C<execute>.

If those complete, the script calls C<ok(1)> to increment the count of
successful tests and then returns 1 as its result.

Both C<compile> and C<execute> take an optional argument hash table to
control their behavior. For example:

  compile(
     verilator_flags2 => ["--lint-only"],
     fails => 1,
  );

indicates that when compiling this test, the C<--lint-only> flag should be
passed and that the test is expected to fail.

The full list of arguments can be found by looking at the C<driver.pl>
source code. Some commonly used arguments are:

=over 4

=item all_run_flags

A list of flags to be passed when running the simulator (Verilated model or
one of the other simulators).

=item check_finished

Set to 1 to indicate successful completion of the test is indicated by the
string C<*-* All Finished *-*> being printed on standard output. This is
the normal way for successful tests to finish.

=item expect

A quoted list of strings or regular expression to be matched in the
output. See </HINTS ON WRITING TESTS> for more detail on how this argument
should be used.

=item fails

Set to 1 to indicate this step (C<compile> or C<execute> or C<lint>) is
expected to fail.  Tests that are expected to fail generally have _bad in
their filename.

=item make_main

Set to 0 to disable the automatic creation of a C++ test wrapper (for
example when a hand-written test wrapper is provided using C<--exe>).

=item make_top_shell

Set to 0 to disable the automatic creation of a top level shell to run the
executable (for example when a hand-written test wrapper is provided using
C<--exe>).

=item ms_flags

=item ms_flags2

=item ms_run_flags

The equivalent of C<v_flags>, C<v_flags2> and C<all_run_flags>, but only
for use with the ModelSim simulator.

=item nc_flags

=item nc_flags2

=item nc_run_flags

The equivalent of C<v_flags>, C<v_flags2> and C<all_run_flags>, but only
for use with the Cadence NC simulator.

=item iv_flags

=item iv_flags2

=item iv_run_flags

The equivalent of C<v_flags>, C<v_flags2> and C<all_run_flags>, but only
for use with the Icarus Verilog simulator.

=item v_flags

A list of standard Verilog simulator flags to be passed to the simulator
compiler (Verilator or one of the other simulators).  This list is create
by the driver and rarely changed, use v_flags2 instead.

=item v_flags2

A list of standard Verilog simulator flags to be passed to the simulator
compiler (Verilator or one of the other simulators). Unlike v_flags, these
options may be overridden in some simulation files.

Similar sets of flags exist for atsim, GHDL, Cadence NC, Modelsim and
Synopsys VCS.

=item vcs_flags

=item vcs_flags2

=item vcs_run_flags

The equivalent of C<v_flags>, C<v_flags2> and C<all_run_flags>, but only
for use with the Synopsys VCS simulator.

=item verilator_flags

=item verilator_flags2

The equivalent of C<v_flags> and C<v_flags2>, but only for use with
Verilator.  If a flag is a standard flag (+incdir for example) v_flags2
should be used instead.

=item xsim_flags

=item xsim_flags2

=item xsim_run_flags

The equivalent of C<v_flags>, C<v_flags2> and C<all_run_flags>, but only
for use with the Xilinx XSim simulator.

=back

=head2 HINTS ON WRITING TESTS

There is generally no need for the test to create its own main program or
top level shell as the driver creates one automatically, however some tests
require their own C++ or SystemC test harness. This is commonly given the
same name as the test, but with .cpp as suffix
(C<test_regress/t/t_EXAMPLE.cpp>). This can be specified as follows:

  compile(
      make_top_shell   => 0,
      make_main        => 0,
      verilator_flags2 => ["--exe $Self->{t_dir}/$Self->{name}.cpp"], );

Tests should be self-checking, rather than producing lots of output. If a
test succeeds it should print C<*-* All Finished *-*> to standard output
and terminate (in Verilog C<$finish>), if not it should just stop (in
Verilog C<$stop>) as that signals an error.

If termination should be triggered from the C++ wrapper, the following code
can be used:

  vl_fatal(__FILE__, __LINE__, "dut", "<error message goes here>");
  exit(1);

This can be particularly useful if checking that the Verilator model has
not unexpectedly terminated.

  if (Verilated::gotFinish()) {
      vl_fatal(__FILE__, __LINE__, "dut", "<error message goes here>");
      exit(1);
  }

Where it might be useful for a test to produce output, it should qualify
this with C<TEST_VERBOSE>. For example in Verilog:

  `ifdef TEST_VERBOSE
        $write("Conditional generate if MASK [%1d] = %d\n", g, MASK[g]);
  `endif

Or in a hand-written C++ wrapper:

  #ifdef TEST_VERBOSE
      cout << "Read  a     = " << a << endl;
  #endif

The C<expect_filename> specifies a filename that should be used to check
the output results. This should not generally be used to decide if a test
has succeeded. However, in the case of tests that are designed to fail at
compile time, it is the only option. For example:

  compile(
      fails => 1,
      expect_filename => $Self->{golden_filename},
      );

Note expect_filename strips some debugging information from the logfile
when comparing.

The C<expect> argument specifies a regular expression which must match the
output.

=head1 DRIVER ARGUMENTS

=over 4

=item --benchmark [<cycles>]

Show execution times of each step.  If an optional number is given,
specifies the number of simulation cycles (for tests that support it).

=item --debug

Same as C<verilator --debug>: Use the debug version of Verilator which
enables additional assertions, debugging messages, and structure dump
files.

=item --debugi(-<srcfile>) <level>

Same as C<verilator --debugi level>: Set Verilator internal debugging level
globally to the specified debug level (1-10) or set the specified source
file to the specified level. Higher levels produce more detailed messages
(plain C<--debug> is equivalent to C<--debugi 4>).

=item --dump-tree

Same as C<verilator --dump-tree>: Enable Verilator writing .tree debug
files with dumping level 3, which dumps the standard critical stages.  For
details on the format see the Verilator Internals manual.

=item --gdb

Same as C<verilator --gdb>: Run Verilator under the debugger.

=item --gdbbt

Same as C<verilator --gdbbt>: Run Verilator under the debugger, only to
print backtrace information.  Requires --debug.

=item --gdbsim

Run Verilator generated executable under the debugger.

=item --golden

Update golden files, equivalent to setting HARNESS_UPDATE_GOLDEN=1.

=item --hashset I<set>/I<numsets>

Split tests based on a hash of the test names into I<numsets> and run only
tests in set number I<set> (0..I<numsets>-1).

=item --help

Displays this message and program version and exits.

=item --j #

Run number of parallel tests, or 0 to determine the count based on the
number of cores installed.  Requires Perl's Parallel::Forker package.

=item --optimize

Randomly turn on/off different optimizations.  With specific flags,
use those optimization settings

=item --quiet

Suppress all output except for failures and progress messages every 15
seconds.  Intended for use only in automated regressions.  See also
C<--rerun>, and C<--verbose> which is not the opposite of C<--quiet>.

=item --rerun

Rerun all tests that failed in this run. Reruns force the flags
C<--no-quiet --j 1>.

=item --rr

Same as C<verilator --rr>: Run Verilator and record with rr.

=item --rrsim

Run Verilator generated executable and record with rr.

=item --site

Run site specific tests also.

=item --stop

Stop on the first error.

=item --trace

Set the simulator specific flags to request waveform tracing.

=item --unsupported

Run tests even if marked as unsupported.

=item --verbose

Compile and run the test in verbose mode. This means C<TEST_VERBOSE> will
be defined for the test (Verilog and any C++/SystemC wrapper).

=back

=head1 SCENARIO ARGUMENTS

The following options control which simulator is used, and which tests are
run.  Multiple flags may be used to run multiple simulators/scenarios
simultaneously.

=over 4

=item --atsim

Run ATSIM simulator tests.

=item --dist

Run simulator-agnostic distribution tests.

=item --ghdl

Run GHDL simulator tests.

=item --iverilog

Run Icarus Verilog simulator tests.

=item --ms

Run ModelSim simulator tests.

=item --nc

Run Cadence NC-Verilog simulator tests.

=item --vcs

Run Synopsys VCS simulator tests.

=item --vlt

Run Verilator tests in single-threaded mode.  Default unless another scenario flag is provided.

=item --vltmt

Run Verilator tests in multithreaded mode.

=item --xsim

Run Xilinx XSim simulator tests.

=back

=head1 ENVIRONMENT

=over 4

=item SYSTEMC

Root directory name of SystemC kit.  Only used if SYSTEMC_INCLUDE not set.

=item SYSTEMC_INCLUDE

Directory name with systemc.h in it.

=item VERILATOR_GHDL

Command to use to invoke GHDL.

=item VERILATOR_IVERILOG

Command to use to invoke Icarus Verilog.

=item VERILATOR_MAKE

Command to use to rebuild Verilator and run single test.  Defaults to "make &&".

=item VERILATOR_MODELSIM

Command to use to invoke ModelSim.

=item VERILATOR_NCVERILOG

Command to use to invoke ncverilog.

=item VERILATOR_TESTS_SITE

Used with --site, a colon-separated list of directories with tests to be added to testlist.

=item VERILATOR_VCS

Command to use to invoke VCS.

=item VERILATOR_XELAB

Command to use to invoke XSim xelab

=item VERILATOR_XVLOG

Command to use to invoke XSim xvlog

=back

=head1 DISTRIBUTION

The latest version is available from L<https://verilator.org>.

Copyright 2003-2020 by Wilson Snyder. This program is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License
Version 2.0.

SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<verilator>

=cut

######################################################################
