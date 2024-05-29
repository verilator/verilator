#!/usr/bin/env perl
# See copyright, etc in below POD section.
######################################################################

require 5.006_001;
use warnings;
use Cwd;

BEGIN {
    if (!$ENV{VERILATOR_ROOT} && -x "../bin/verilator") {
        $ENV{VERILATOR_ROOT} = Cwd::getcwd() . "/..";
    }
    $ENV{MAKE} ||= "make";
    $ENV{CXX} ||= "c++";
    !defined $ENV{TEST_REGRESS} or die "TEST_REGRESS environment variable is already set";
    $ENV{TEST_REGRESS} = Cwd::getcwd();
}

use Getopt::Long;
use IO::File;
use Pod::Usage;
use Data::Dumper; $Data::Dumper::Sortkeys = 1;
use FindBin qw($RealBin);
use strict;
use vars qw($Debug %Vars $Driver $Fork);
use version;
use POSIX qw(strftime);
use lib ".";
use Time::HiRes qw(usleep);
use Digest::MD5 qw(md5);
use POSIX;

$::Driver = 1;
$::Have_Forker = 0;

eval "use Parallel::Forker; \$Fork=Parallel::Forker->new(use_sig_child=>1, poll_interval=>10*1000); \$::Have_Forker=1;";
$Fork = Forker->new(use_sig_child => 1) if !$Fork;
my $forker_Min_Version = 1.258;
if ($::Have_Forker && $Parallel::Forker::VERSION < $forker_Min_Version) {
    print STDERR "driver.pl: Parallel::Forker is older than $forker_Min_Version, suggest 'cpan install Parallel::Forker'\n";
    $::Have_Forker = 0;
}
$SIG{CHLD} = sub { $Fork->sig_child() if $Fork; };
$SIG{TERM} = sub { $Fork->kill_tree_all('TERM') if $Fork; die "Quitting...\n"; };

#======================================================================

# Map of all scenarios, with the names used to enable them
our %All_Scenarios
    = (dist  => [                                       "dist"],
       atsim => [          "simulator", "simulator_st", "atsim"],
       ghdl  => ["linter", "simulator", "simulator_st", "ghdl"],
       iv    => [          "simulator", "simulator_st", "iv"],
       ms    => ["linter", "simulator", "simulator_st", "ms"],
       nc    => ["linter", "simulator", "simulator_st", "nc"],
       vcs   => ["linter", "simulator", "simulator_st", "vcs"],
       xrun  => ["linter", "simulator", "simulator_st", "xrun"],
       xsim  => ["linter", "simulator", "simulator_st", "xsim"],
       vlt   => ["linter", "simulator", "simulator_st", "vlt_all", "vlt"],
       vltmt => [          "simulator",                 "vlt_all", "vltmt"],
    );

#======================================================================
# main

autoflush STDOUT 1;
autoflush STDERR 1;

our @Orig_ARGV = @ARGV;
our @Orig_ARGV_Sw; foreach (@Orig_ARGV) { push @Orig_ARGV_Sw, $_ if /^-/ && !/^-j/; }
our $Start = time();
our $Vltmt_threads = 3;

$Debug = 0;
my $opt_benchmark;
our $Opt_Fail_Max = 20;
my @opt_tests;
my $opt_dist;
my $opt_gdb;
my $opt_rr;
my $opt_gdbbt;
my $opt_gdbsim;
my $opt_hashset;
my $opt_jobs = 1;
my $opt_quiet;
my $opt_rerun;
my $opt_rrsim;
my $opt_sanitize;
my %opt_scenarios;
my $opt_site;
my $opt_stop;
my $opt_trace;
my $opt_verbose;
my $Opt_Verilated_Debug;
our $Opt_Verilation = 1;
our @Opt_Driver_Verilator_Flags;

Getopt::Long::config("pass_through");
if (! GetOptions(
          "benchmark:i" => sub { $opt_benchmark = $_[1] ? $_[1] : 1; },
          "debug"       => \&debug,
          #debugi          see parameter()
          "fail-max=i"  => \$Opt_Fail_Max,
          "gdb!"        => \$opt_gdb,
          "gdbbt!"      => \$opt_gdbbt,
          "gdbsim!"     => \$opt_gdbsim,
          "golden!"     => sub { $ENV{HARNESS_UPDATE_GOLDEN} = 1; },
          "hashset=s"   => \$opt_hashset,
          "help"        => \&usage,
          "j=i"         => \$opt_jobs,
          "quiet!"      => \$opt_quiet,
          "rerun!"      => \$opt_rerun,
          "rr!"         => \$opt_rr,
          "rrsim!"      => \$opt_rrsim,
          "sanitize!"   => \$opt_sanitize,
          "site!"       => \$opt_site,
          "stop!"       => \$opt_stop,
          "trace!"      => \$opt_trace,
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
          "xrun!"       => sub { $opt_scenarios{xrun} = $_[1]; },
          "xsim!"       => sub { $opt_scenarios{xsim} = $_[1]; },
          "<>"          => \&parameter,
    )) {
    die "%Error: Bad usage, try '$0 --help'\n";
}

$opt_jobs = calc_jobs() if defined $opt_jobs && $opt_jobs == 0;
$Fork->max_proc($opt_jobs);

my $interactive_debugger = $opt_gdb || $opt_gdbsim || $opt_rr || $opt_rrsim;
if ($opt_jobs > 1 && $interactive_debugger) {
   die "%Error: Unable to use -j > 1 with --gdb* and --rr* options"
}

if ((scalar keys %opt_scenarios) < 1) {
    $opt_scenarios{dist} = 1;
    $opt_scenarios{vlt} = 1;
}

our @Test_Dirs = "t";
push @Test_Dirs, split(/:/, $ENV{VERILATOR_TESTS_SITE})
    if (($#opt_tests < 0 ? $opt_site : 1) && $ENV{VERILATOR_TESTS_SITE});

if ($#opt_tests < 0) {  # Run everything
    my %uniq;
    foreach my $dir (@Test_Dirs) {
        my @stats = stat($dir);  # Uniquify by inode, so different paths to same place get combined
        next if !$stats[1] || $uniq{$stats[1]}++;
        push @opt_tests, sort(glob("${dir}/t_*.pl"));
    }
}
@opt_tests = _calc_hashset(@opt_tests) if $opt_hashset;

if ($#opt_tests >= 2 && $opt_jobs >= 2) {
    # Read supported into master process, so don't call every subprocess
    _have_coroutines();
    _have_sc();
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
    print("=" x 70, "\n");
    print("=" x 70, "\n");
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
        skip_cnt => $orig_runner->{skip_cnt});
    foreach my $test (@{$orig_runner->{fail_tests}}) {
        # Reschedule test
        $test->clean if $test->rerunnable;
        $runner->one_test(pl_filename => $test->{pl_filename},
                          $test->{scenario} => 1,
                          rerun_skipping => !$test->rerunnable);
    }
    $runner->wait_and_report;
}

exit(10) if $runner->fail_count;

#----------------------------------------------------------------------

sub usage {
    pod2usage(-verbose => 2, -exitval => 0, -output => \*STDOUT);
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
        $_Parameter_Next_Level = undef;
    }
    elsif ($param =~ /\.pl/) {
        push @opt_tests, $param;
    }
    elsif ($param =~ /^-?(-debugi|-dumpi)/) {
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

our $_Max_Procs;

sub max_procs {
    if (!defined $_Max_Procs) {
        $_Max_Procs = `python3 -c 'import multiprocessing\nprint(multiprocessing.cpu_count())'`;
        chomp $_Max_Procs;
        if ($_Max_Procs < 2) {
            $_Max_Procs = 2;
            warn "driver.pl: Python didn't find at least two CPUs\n";
        }
    }
    return $_Max_Procs;
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
    print "driver.pl: Found $ok cores, using -j ", $ok, "\n";
    return $ok;
}

sub _calc_hashset {
    my @in = @_;
    return @in if !$opt_hashset;
    $opt_hashset =~ m!^(\d+)/(\d+)$!
        or die "%Error: Need number/number format for --hashset: $opt_hashset\n";
    my ($set, $nsets) = ($1, $2);
    my @new;
    foreach my $t (@opt_tests) {
        my $checksum = unpack('L', substr(md5($t), 0, 4));
        if (($set % $nsets) == ($checksum % $nsets)) {
            push @new, $t;
        }
    }
    return @new;
}

#######################################################################
# Verilator utilities

our %_Verilator_Supported;
sub _verilator_get_supported {
    my $feature = shift;
    # Returns if given feature is supported
    if (!defined $_Verilator_Supported{$feature}) {
        my @args = ("perl", "$ENV{VERILATOR_ROOT}/bin/verilator", "-get-supported", $feature);
        my $args = join(' ', @args);
        my $out = `$args`;
        $out or die "couldn't run: $! " . join(' ', @args);
        chomp $out;
        $_Verilator_Supported{$feature} = ($out =~ /1/ ? 1 : 0);
    }
    return $_Verilator_Supported{$feature};
}

sub _have_coroutines {
    return 1 if _verilator_get_supported('COROUTINES');
    return 0;
}

sub _have_sc {
    return 1 if (defined $ENV{SYSTEMC} || defined $ENV{SYSTEMC_INCLUDE} || $ENV{CFG_HAVE_SYSTEMC});
    return 1 if _verilator_get_supported('SYSTEMC');
    return 0;
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
        # Arguments
        driver_log_filename => undef,
        quiet => 0,
        # Counts
        all_cnt => 0,
        left_cnt => 0,
        ok_cnt => 0,  # Argument passed when rerunning
        fail1_cnt => 0,  # Argument passed when rerunning
        fail_cnt => 0,
        skip_cnt => 0,  # Argument passed when rerunning
        skip_msgs => [],
        fail_msgs => [],
        fail_tests => [],
        # Per-task identifiers
        running_ids => {},
        @_  # All legal arguments shown immediately above
    };
    bless $self, $class;
    return $self;
}

sub fail_count { return $_[0]->{fail_cnt}; }

sub one_test {
    my $self = shift;
    my @params = (# Parameters:
                  # pl_filename =>
                  # rerun_skipping =>
                  # {scenario_name} => 1
                  @_);  # All legal arguments shown immediately above
    my %params = (@params);
    $self->{all_cnt}++;
    $self->{left_cnt}++;
    $::Fork->schedule
        (
         test_pl_filename => $params{pl_filename},
         run_pre_start => sub {
             my $process = shift;
             # Running in context of parent, before run_on_start
             # Make an identifier that is unique across all current running jobs
             my $i = 1; while (exists $self->{running_ids}{$i}) { ++$i; }
             $process->{running_id} = $i;
             if ($::Opt_Fail_Max && $::Opt_Fail_Max <= $self->fail_count) {
                 print STDERR "== Too many test failures; exceeded --fail-max\n"
                     if !$self->{_msg_fail_max_skip}++;
                 $process->{fail_max_skip} = 1;
             }
             $self->{running_ids}{$process->{running_id}} = 1;
         },
         run_on_start => sub {
             my $process = shift;
             # Running in context of child, so can't pass data to parent directly
             if ($self->{quiet}) {
                 open(STDOUT, ">/dev/null");
                 open(STDERR, ">&STDOUT");
             }
             print("=" x 70, "\n");
             my $test = VTest->new(@params,
                                   running_id => $process->{running_id});
             $test->oprint("=" x 50, "\n");
             $test->_prep;
             if ($params{rerun_skipping}) {
                 print "  ---------- Earlier logfiles below; test was rerunnable = 0\n";
                 system("cat $test->{obj_dir}/*.log");
                 print "  ---------- Earlier logfiles above; test was rerunnable = 0\n";
             } elsif ($process->{fail_max_skip}) {
                 $test->skip("Too many test failures; exceeded --fail-max");
             } else {
                 unlink $test->{status_filename};
                 $test->_read;
             }
             # Don't put anything other than _exit after _read,
             # as may call _exit via another path
             $test->_exit;
         },
         run_on_finish => sub {
             # Running in context of parent
             my $process = shift;
             my $test = VTest->new(@params,
                                   running_id => $process->{running_id});
             $test->_read_status;
             if ($test->ok) {
                 $self->{ok_cnt}++;
             } elsif ($test->scenario_off && !$test->errors) {
             } elsif ($test->skips && !$test->errors) {
                 push @{$self->{skip_msgs}},
                     ("\t#" . $test->soprint("-Skip:  $test->{skips}\n"));
                 $self->{skip_cnt}++;
             } else {
                 $test->oprint("FAILED: $test->{errors}\n");
                 my $j = ($opt_jobs > 1 ? " -j" : "");
                 my $makecmd = $ENV{VERILATOR_MAKE} || "$ENV{MAKE}$j &&";
                 my $upperdir = (Cwd::getcwd() =~ /test_regress/
                                 ? 'test_regress/' : '');
                 push @{$self->{fail_msgs}},
                     ("\t#" . $test->soprint("%Error: $test->{errors}\n")
                      . "\t\t$makecmd "
                      . $upperdir . $test->{pl_filename}
                      . " " . join(' ', _manual_args())
                      . " --" . $test->{scenario} . "\n");
                 push @{$self->{fail_tests}}, $test;
                 $self->{fail_cnt}++;
                 $self->report($self->{driver_log_filename});
                 my $other = "";
                 foreach my $proc ($::Fork->running) {
                     $other .= "  " . $proc->{test_pl_filename};
                 }
                 $test->oprint("Simultaneous running tests:", $other, "\n")
                     if $other && !$opt_quiet;
                 if ($opt_stop) { die "%Error: --stop and errors found\n"; }
             }
             $self->{left_cnt}--;
             $self->print_summary;
             delete $self->{running_ids}{$process->{running_id}} if $process->{running_id};
         },
         )->ready();
}

sub wait_and_report {
    my $self = shift;
    $self->print_summary(force => 1);
    # Wait for all children to finish
    while ($::Fork->is_any_left) {
        $::Fork->poll;
        if ((time() - ($self->{_last_summary_time} || 0) >= 30)
            && !$interactive_debugger) {  # Don't show for interactive gdb etc
            $self->print_summary(force => 1, show_running => 1);
        }
        Time::HiRes::usleep 100 * 1000;
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
    $fh->print("=" x 70, "\n");
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
    $fh->print("==TESTS DONE, $sum: " . $self->sprint_summary . "\n");
}

sub print_summary {
    my $self = shift;
    my %params = (force => 0, # Force printing
                  show_running => 0, # Show running processes
                  @_);  # All legal arguments shown immediately above
    if (!$self->{quiet} || $params{force}
        || ($self->{left_cnt} < 5)
        || (time() - ($self->{_last_summary_time} || 0) >= 15)) {
        $self->{_last_summary_time} = time();
        print STDERR ("==SUMMARY: " . $self->sprint_summary . "\n");
        if ($params{show_running}) {
            my $other;
            foreach my $proc ($::Fork->running) {
                $other .= "  " . $proc->{test_pl_filename};
            }
            print STDERR ("==STILL RUNNING: " . $other . "\n");
        }
    }
}

sub sprint_summary {
    my $self = shift;

    my $delta = time() - $::Start;
    my $leftmsg = $::Have_Forker ? $self->{left_cnt} : "NO-FORKER";
    my $pct = int(100 * ($self->{left_cnt} / ($self->{all_cnt} + 0.001)) + 0.999);
    # Fudge of 120% works out about right so ETA correctly predicts completion time
    my $eta = 1.2 * (($self->{all_cnt}
                      * ($delta / (($self->{all_cnt} - $self->{left_cnt})+0.001)))
                     - $delta);
    $eta = 0 if $delta < 10;
    my $out = "";
    $out .= "Left $leftmsg  " if $self->{left_cnt};
    $out .= "Passed $self->{ok_cnt}";
    # Ordered below most severe to least severe
    $out .= "  Failed $self->{fail_cnt}";
    $out .= "  Failed-First $self->{fail1_cnt}" if $self->{fail1_cnt};
    $out .= "  Skipped $self->{skip_cnt}" if $self->{skip_cnt};
    $out .= sprintf("  Eta %d:%02d", int($eta / 60), $eta % 60) if $self->{left_cnt} > 10 && $eta > 10;
    $out .= sprintf("  Time %d:%02d", int($delta / 60), $delta % 60);
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
    my $self = {@_};  # Supports arbitrary arguments

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
    $self->{scenario} ||= "xrun" if $self->{xrun};
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
        $self->{obj_dir} = "$scen_dir/$self->{name}";
    }

    my $define_opt = defineOpt($self->{xsim});

    $self = {
        name => undef,          # Set below, name of this test
        pl_filename => undef,   # Name of .pl file to get setup from
        make_top_shell => 1,    # Make a default __top.v file
        make_main => 1,         # Make __main.cpp
        make_pli => 0,          # need to compile pli
        sc_time_resolution => "SC_PS",  # Keep - PS is SystemC default
        sim_time => 1100,
        threads => -1,          # --threads (negative means auto based on scenario)
        context_threads => 0,   # Number of threads to allocate in the context
        benchmark => $opt_benchmark,
        verbose => $opt_verbose,
        rerunnable => 1,        # Rerun if fails
        run_env => '',
        # All compilers
        v_flags => [split(/\s+/,
                          (($self->{xsim} ? " -f input.xsim.vc " :
                            (-r 'input.vc' ? " -f input.vc " : ""))
                           .($self->{t_dir} !~ m!/test_regress!  # Don't include standard dir, only site's
                             ? " +incdir+$self->{t_dir} -y $self->{t_dir}" : "")
                           . " " . $define_opt . "TEST_OBJ_DIR=$self->{obj_dir}"
                           .($opt_verbose ? " " . $define_opt . "TEST_VERBOSE=1" : "")
                           .($opt_benchmark ? " " . $define_opt . "TEST_BENCHMARK=$opt_benchmark" : "")
                           .($opt_trace ? " " . $define_opt . "WAVES=1" : "")
                          ))],
        v_flags2 => [],  # Overridden in some sim files
        v_other_filenames => [],  # After the filename so we can spec multiple files
        all_run_flags => [],
        pli_flags => ["-I$ENV{VERILATOR_ROOT}/include/vltstd -fPIC -shared"
                      . (($^O eq "darwin" )
                         ? " -Wl,-undefined,dynamic_lookup"
                         : " -export-dynamic")
                      . ($opt_verbose ? " -DTEST_VERBOSE=1" : "")
                      . " -o $self->{obj_dir}/libvpi.so"],
        tool_c_flags => [],
        # ATSIM
        atsim => 0,
        atsim_define => 'ATSIM',
        atsim_flags => [split(/\s+/, "-c +sv +define+ATSIM"),
                        "+sv_dir+$self->{obj_dir}/.athdl_compile"],
        atsim_flags2 => [],  # Overridden in some sim files
        atsim_run_flags => [],
        # GHDL
        ghdl => 0,
        ghdl_define => 'GHDL',
        ghdl_work_dir => "$self->{obj_dir}/ghdl_compile",
        ghdl_flags => [($::Debug ? "-v" : ""),
                       "--workdir=$self->{obj_dir}/ghdl_compile", ],
        ghdl_flags2 => [],  # Overridden in some sim files
        ghdl_run_flags => [],
        # IV
        iv => 0,
        iv_define => 'IVERILOG',
        iv_flags => [split(/\s+/, "+define+IVERILOG -g2012 -o $self->{obj_dir}/simiv")],
        iv_flags2 => [],  # Overridden in some sim files
        iv_pli => 0,  # need to use pli
        iv_run_flags => [],
        # VCS
        vcs => 0,
        vcs_define => 'VCS',
        vcs_flags => [split(/\s+/, "+vcs+lic+wait +cli -debug_access +define+VCS+1 -q -sverilog -CFLAGS '-DVCS' ")],
        vcs_flags2 => [],  # Overridden in some sim files
        vcs_run_flags => [split(/\s+/, "+vcs+lic_wait")],
        # NC
        nc => 0,
        nc_define => 'NC',
        nc_flags => [split(/\s+/, ("+licqueue +nowarn+LIBNOU +define+NC=1 -q +assert +sv -c "
                                   . ($opt_trace ? " +access+r" : "")))],
        nc_flags2 => [],  # Overridden in some sim files
        nc_run_flags => [split(/\s+/, "+licqueue -q +assert +sv -R")],
        # ModelSim
        ms => 0,
        ms_define => 'MS',
        ms_flags => [split(/\s+/, ("-sv -work $self->{obj_dir}/work +define+MS=1 -ccflags \"-DMS=1\""))],
        ms_flags2 => [],  # Overridden in some sim files
        ms_pli => 1,  # need to use pli
        ms_run_flags => [split(/\s+/, "-lib $self->{obj_dir}/work -c -do 'run -all;quit' ")],
        # Xcelium (xrun)
        xrun => 0,
        xrun_define => 'XRUN',
        xrun_flags => [], # doesn't really have a compile step
        xrun_flags2 => [],  # Overridden in some sim files
        xrun_run_flags => [split(/\s+/, "-64 -access +rwc -newsv -sv -xmlibdirname $self->{obj_dir}/work -l $self->{obj_dir}/history -quiet -plinowarn ")],
        # XSim
        xsim => 0,
        xsim_define => 'XSIM',
        xsim_flags => [split(/\s+/, ("--nolog --sv --define XSIM --work $self->{name}=$self->{obj_dir}/xsim"))],
        xsim_flags2 => [],  # Overridden in some sim files
        xsim_run_flags => [split(/\s+/, ("--nolog --runall --lib $self->{name}=$self->{obj_dir}/xsim"
                                         .($opt_trace ? " --debug all" : "")))],
        xsim_run_flags2 => [],  # Overridden in some sim files
        # Verilator
        vlt => 0,
        vltmt => 0,
        verilator_define => 'VERILATOR',
        verilator_flags => ["-cc",
                            "-Mdir $self->{obj_dir}",
                            "--fdedup",  # As currently disabled unless -O3
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

    $self->{vm_prefix} ||= "V" . $self->{name};
    $self->{stats} ||= "$self->{obj_dir}/V" . $self->{name} . "__stats.txt";
    $self->{status_filename} ||= "$self->{obj_dir}/V" . $self->{name} . ".status";
    $self->{run_log_filename} ||= "$self->{obj_dir}/vlt_sim.log";
    $self->{coverage_filename} ||= "$self->{obj_dir}/coverage.dat";
    $self->{main_filename} ||= "$self->{obj_dir}/$self->{vm_prefix}__main.cpp";
    ($self->{top_filename} ||= $self->{pl_filename}) =~ s/\.pl$//;
    ($self->{golden_filename} ||= $self->{pl_filename}) =~ s/\.pl$/.out/;
    if (-e ($self->{top_filename} . ".vhd")) {  # If VHDL file exists
        $self->{vhdl} = 1;
        $self->{top_filename} .= ".vhd";
    } else {
        $self->{top_filename} .= ".v";
    }
    if (!$self->{make_top_shell}) {
        $self->{top_shell_filename} = $self->{top_filename};
    } else {
        $self->{top_shell_filename} = "$self->{obj_dir}/$self->{vm_prefix}__top.v";
    }
    $self->{pli_filename} ||= $self->{name} . ".cpp";

    return $self;
}

sub benchmarksim_filename {
    my $self = (ref $_[0] ? shift : $Self);
    return $self->{obj_dir} . "/$self->{name}_benchmarksim.csv";
}

sub init_benchmarksim {
    my $self = (ref $_[0] ? shift : $Self);
    # Simulations with benchmarksim enabled append to the same file between runs.
    # Test files must ensure a clean benchmark data file before executing tests.
    my $filename = $self->benchmarksim_filename();
    my $fh = IO::File->new(">" . $filename) or die "%Error: $! " . $filename;
    print $fh "# Verilator simulation benchmark data\n";
    print $fh "# Test name: " . $self->{name} . "\n";
    print $fh "# Top file: " . $self->{top_filename} . "\n";
    print $fh "evals, time[s]\n";
}

sub soprint {
    my $self = (ref $_[0] ? shift : $Self);
    my $str = "$self->{scenario}/$self->{name}: " . join('', @_);
    $str =~ s/\n\n+$/\n/s;
    return $str;
}

sub oprint {
    my $self = (ref $_[0] ? shift : $Self);
    print $self->soprint(@_);
}

sub error {
    my $self = (ref $_[0] ? shift : $Self);
    my $msg = join('', @_);
    # Called from tests as: error("Reason message"[, ...]);
    warn "%Warning: $self->{scenario}/$self->{name}: " . $msg . "\n";
    $self->{errors} ||= $msg;
}

sub error_keep_going {
    my $self = (ref $_[0] ? shift : $Self);
    my $msg = join('', @_);
    # Called from tests as: error_keep_going("Reason message"[, ...]);
    warn "%Warning: $self->{scenario}/$self->{name}: " . $msg . "\n";
    $self->{errors_keep_going} ||= $msg;
}

sub skip {
    my $self = (ref $_[0] ? shift : $Self);
    my $msg = join('', @_);
    # Called from tests as: skip("Reason message"[, ...]);
    warn "-Skip: $self->{scenario}/$self->{name}: " . $msg . "\n";
    $self->{skips} ||= "Skip: " . $msg;
}

sub scenarios {
    my $self = (ref $_[0] ? shift : $Self);
    my %params = (@_);  # Called from tests as: scenarios(...);
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
        $self->oprint("-Skip: $self->{skips}\n");
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

sub clean {
    my $self = (ref $_[0] ? shift : $Self);
    # Called on a rerun to cleanup files
    if ($self->{clean_command}) {
        system($self->{clean_command});
    }
    if (1) {
        # Prevents false-failures when switching compilers
        # Remove old results to force hard rebuild
        system("rm", "-rf", "$self->{obj_dir}__fail1");
        system("mv", "$self->{obj_dir}", "$self->{obj_dir}__fail1");
    }
}

sub clean_objs {
    my $self = (ref $_[0] ? shift : $Self);
    system("rm", "-rf", glob("$self->{obj_dir}/*"));
}

sub _checkflags {
    my $self = shift;
    my %param = (@_);
    my $checkflags = (' '.join(' ',
                               @{$param{v_flags}},
                               @{$param{v_flags2}},
                               @{$param{verilator_flags}},
                               @{$param{verilator_flags2}},
                               @{$param{verilator_flags3}})
                      .' ');
    return $checkflags;
}

sub compile_vlt_cmd {
    my $self = (ref $_[0] ? shift : $Self);
    my %param = (%{$self},  # Default arguments are from $self
                 @_);  # Supports arbitrary arguments
    return 1 if $self->errors || $self->skips;

    my @vlt_cmd = (
        "perl", "$ENV{VERILATOR_ROOT}/bin/verilator",
        $self->_compile_vlt_flags(%param),
        $param{top_filename},
        @{$param{v_other_filenames}},
        $param{stdout_filename} ? "> " . $param{stdout_filename} : ""
    );
    return @vlt_cmd;
}

sub _compile_vlt_flags {
    my $self = shift;
    my %param = (@_);  # Supports arbitrary arguments from compile_vlt_cmd
    return 1 if $self->errors || $self->skips;

    my $checkflags = $self->_checkflags(%param);
    die "%Error: specify threads via 'threads =>' argument, not as a command line option" unless ($checkflags !~ /(^|\s)-?-threads\s/);
    $self->{coverage} = 1 if ($checkflags =~ /-coverage\b/);
    $self->{savable} = 1 if ($checkflags =~ /-savable\b/);
    $self->{sc} = 1 if ($checkflags =~ /-sc\b/);
    $self->{timing} = 1 if ($checkflags =~ / -?-timing\b/ || $checkflags =~ / -?-binary\b/ );
    $self->{trace} = ($opt_trace || $checkflags =~ /-trace\b/
                      || $checkflags =~ /-trace-fst\b/);
    $self->{trace_format} = (($checkflags =~ /-trace-fst/ && $self->{sc} && 'fst-sc')
                             || ($checkflags =~ /-trace-fst/ && !$self->{sc} && 'fst-c')
                             || ($self->{sc} && 'vcd-sc')
                             || (!$self->{sc} && 'vcd-c'));
    $self->{sanitize} = $opt_sanitize unless exists($self->{sanitize});
    $self->{benchmarksim} = 1 if ($param{benchmarksim});

    my @verilator_flags = @{$param{verilator_flags}};
    unshift @verilator_flags, "--gdb" if $opt_gdb;
    unshift @verilator_flags, "--gdbbt" if $opt_gdbbt;
    unshift @verilator_flags, "--rr" if $opt_rr;
    unshift @verilator_flags, "--x-assign unique";  # More likely to be buggy
    unshift @verilator_flags, "--trace" if $opt_trace;
    unshift @verilator_flags, "--threads $param{threads}" if $param{threads} >= 0;
    unshift @verilator_flags, "--trace-threads 2" if $param{vltmt} && $checkflags =~ /-trace-fst /;
    unshift @verilator_flags, "--debug-partition" if $param{vltmt};
    unshift @verilator_flags, "-CFLAGS -ggdb -LDFLAGS -ggdb" if $opt_gdbsim || $opt_rrsim;
    unshift @verilator_flags, "-CFLAGS -fsanitize=address,undefined -LDFLAGS -fsanitize=address,undefined" if $param{sanitize};
    unshift @verilator_flags, "--make gmake" if $param{verilator_make_gmake};
    unshift @verilator_flags, "--make cmake" if $param{verilator_make_cmake};
    unshift @verilator_flags, "--exe" if
        $param{make_main} && $param{verilator_make_gmake};
    unshift @verilator_flags, "../" . $self->{main_filename} if
        $param{make_main} && $param{verilator_make_gmake};

    my @cmdargs = (
                   "--prefix " . $param{vm_prefix},
                   @verilator_flags,
                   @{$param{verilator_flags2}},
                   @{$param{verilator_flags3}},
                   @{$param{v_flags}},
                   @{$param{v_flags2}},
                   # Flags from driver cmdline override default flags and
                   # flags from the test itself
                   driver_verilator_flags(),
        );
    return @cmdargs;
}

sub driver_verilator_flags {
    # my $self = (ref $_[0] ? shift : $Self);
    return @Opt_Driver_Verilator_Flags;
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
                 @_);  # Supports arbitrary arguments
    $self->compile(%param);
}

sub compile {
    my $self = (ref $_[0] ? shift : $Self);
    my %param = (tee => 1,
                 %{$self},  # Default arguments are from $self
                 @_);  # Supports arbitrary arguments
    return 1 if $self->errors || $self->skips;
    $self->oprint("Compile\n") if $self->{verbose};

    die "%Error: 'threads =>' argument must be <= 1 for vlt scenario" if $param{vlt} && $param{threads} > 1;
    # Compute automatic parameter values
    my $checkflags = $self->_checkflags(%param);
    $param{threads} = ::calc_threads($Vltmt_threads) if $param{threads} < 0 && $param{vltmt};
    $param{context_threads} = $param{threads} >= 1 ? $param{threads} : 1 if !$param{context_threads};
    $param{make_main} = 0 if ($checkflags =~ / -?-main\b/ || $checkflags =~ / -?-binary\b/);
    if ($checkflags =~ / -?-build\b/ || $checkflags =~ / -?-binary\b/) {
        $param{verilator_make_cmake} = 0;
        $param{verilator_make_gmake} = 0;
    }

    $self->{threads} = $param{threads};
    $self->{context_threads} = $param{context_threads};

    $self->compile_vlt_cmd(%param);

    my $define_opt = defineOpt($self->{xsim});
    if (join(' ', @{$self->{v_flags}}) !~ /TEST_DUMPFILE/) {
        push @{$self->{v_flags}}, ($define_opt . "TEST_DUMPFILE=" . $self->trace_filename);
    }

    if (!$param{make_top_shell}) {
        $param{top_shell_filename}
        = $self->{top_shell_filename} = "";
    } else {
        $param{top_shell_filename}
        = $self->{top_shell_filename} = "$self->{obj_dir}/$self->{vm_prefix}__top." . $self->v_suffix;
    }

    if ($param{atsim}) {
        $param{tool_define} ||= $param{atsim_define};
        $self->_make_top() if $param{make_top_shell};
        $self->_run(logfile=>"$self->{obj_dir}/atsim_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_ATSIM} || "atsim"),
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
        $param{tool_define} ||= $param{ghdl_define};
        mkdir $self->{ghdl_work_dir};
        $self->_make_top() if $param{make_top_shell};
        $self->_run(logfile=>"$self->{obj_dir}/ghdl_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_GHDL} || "ghdl"),
                          # Add -c here, as having -c twice freaks it out
                          ((($ENV{VERILATOR_GHDL} || ' ') =~ / -c\b/) ? "" : "-c"),
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
        $param{tool_define} ||= $param{vcs_define};
        $self->_make_top() if $param{make_top_shell};
        $self->_run(logfile=>"$self->{obj_dir}/vcs_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_VCS} || "vcs"),
                          @{$param{vcs_flags}},
                          @{$param{vcs_flags2}},
                          ($opt_verbose ? " -CFLAGS -DTEST_VERBOSE=1" : ""),
                          @{$param{v_flags}},
                          @{$param{v_flags2}},
                          $param{top_filename},
                          $param{top_shell_filename},
                          @{$param{v_other_filenames}},
                          ]);
    }
    elsif ($param{nc}) {
        $param{tool_define} ||= $param{nc_define};
        $self->_make_top() if $param{make_top_shell};
        my @more_args;
        if ($self->vhdl) {
            ((my $ts = $param{top_shell_filename}) =~ s!\.v!!);
            $ts =~ s!.*/!!;
            push @more_args, "-vhdltop", $ts;
        }
        $self->_run(logfile=>"$self->{obj_dir}/nc_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_NCVERILOG} || "ncverilog"),
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
        $param{tool_define} ||= $param{ms_define};
        $self->_make_top() if $param{make_top_shell};
        $self->_run(logfile=>"$self->{obj_dir}/ms_compile.log",
                    fails=>$param{fails},
                    cmd=>[("vlib $self->{obj_dir}/work && "),
                          ($ENV{VERILATOR_MODELSIM} || "vlog"),
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
        $param{tool_define} ||= $param{iv_define};
        $self->_make_top() if $param{make_top_shell};
        my @cmd = (($ENV{VERILATOR_IVERILOG} || "iverilog"),
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
    elsif ($param{xrun}) {
        $param{tool_define} ||= $param{xrun_define};
        $self->_make_top() if $param{make_top_shell};
    }
    elsif ($param{xsim}) {
        $param{tool_define} ||= $param{xsim_define};
        $self->_make_top() if $param{make_top_shell};
        $self->_run(logfile=>"$self->{obj_dir}/xsim_compile.log",
                    fails=>$param{fails},
                    cmd=>[($ENV{VERILATOR_XVLOG} || "xvlog"),
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
        $param{tool_define} ||= $param{verilator_define};

        if ($self->sc && !$self->have_sc) {
            $self->skip("Test requires SystemC; ignore error since not installed\n");
            return 1;
        }
        if ($self->{timing} && !$self->have_coroutines) {
            $self->skip("Test requires Coroutines; ignore error since not available\n");
            return 1;
        }
        if ($param{verilator_make_cmake} && !$self->have_cmake) {
            $self->skip("Test requires CMake; ignore error since not available or version too old\n");
            return 1;
        }

        if (!$param{fails} && $param{make_main}) {
            $self->_make_main($param{timing_loop});
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
                        verilator_run => 1,
                        cmd => \@vlt_cmd) if $::Opt_Verilation;
            return 1 if $self->errors || $self->skips;
        }

        if ($param{verilator_make_cmake}) {
            my @vlt_args = $self->_compile_vlt_flags(%param);
            $self->oprint("Running cmake\n") if $self->{verbose};
            mkdir $self->{obj_dir};
            my @csources = ();
            unshift @csources, $self->{main_filename} if $param{make_main};
            $self->_run(logfile => "$self->{obj_dir}/vlt_cmake.log",
                        fails => $param{fails},
                        tee => $param{tee},
                        expect => $param{expect},
                        expect_filename => $param{expect_filename},
                        verilator_run => 1,
                        cmd => ["cd \"" . $self->{obj_dir} . "\" && cmake",
                                "\"" . $self->{t_dir} . "/..\"",
                                "-DTEST_VERILATOR_ROOT=$ENV{VERILATOR_ROOT}",
                                "-DTEST_NAME=$self->{name}",
                                "-DTEST_CSOURCES=\"@csources\"",
                                "-DTEST_VERILATOR_ARGS=\"@vlt_args\"",
                                "-DTEST_VERILATOR_SOURCES=\"$param{top_filename} @{$param{v_other_filenames}}\"",
                                "-DTEST_VERBOSE=\"" . ($self->{verbose} ? 1 : 0) . "\"",
                                "-DTEST_SYSTEMC=\""  . ($self->sc ? 1 : 0) . "\"",
                                "-DCMAKE_PREFIX_PATH=\"" . (($ENV{SYSTEMC_INCLUDE} || $ENV{SYSTEMC} || '') . "/..\""),
                                "-DTEST_OPT_FAST=\"" . ($param{benchmark} ? "-Os" : "-O0") . "\"",
                                "-DTEST_OPT_GLOBAL=\"" . ($param{benchmark} ? "-Os" : "-O0") . "\"",
                                "-DTEST_VERILATION=\"" . $::Opt_Verilation . "\"",
                        ]);
            return 1 if $self->errors || $self->skips;
        }

        if (!$param{fails} && $param{verilator_make_gmake}) {
            $self->oprint("Running make (gmake)\n") if $self->{verbose};
            $self->_run(logfile => "$self->{obj_dir}/vlt_gcc.log",
                        entering => "$self->{obj_dir}",
                        cmd => [$ENV{MAKE},
                                "-C " . $self->{obj_dir},
                                "-f " . $FindBin::RealBin . "/Makefile_obj",
                                ($self->{verbose} ? "" : "--no-print-directory"),
                                "VM_PREFIX=$self->{vm_prefix}",
                                "TEST_OBJ_DIR=$self->{obj_dir}",
                                "CPPFLAGS_DRIVER=-D" . uc($self->{name}),
                                ($self->{verbose} ? "CPPFLAGS_DRIVER2=-DTEST_VERBOSE=1" : ""),
                                ($param{benchmark} ? "" : "OPT_FAST=-O0"),
                                ($param{benchmark} ? "" : "OPT_GLOBAL=-O0"),
                                "$self->{vm_prefix}",  # bypass default rule, as we don't need archive
                                ($param{make_flags} || ""),
                        ]);
        }

        if (!$param{fails} && $param{verilator_make_cmake}) {
            $self->oprint("Running cmake --build\n") if $self->{verbose};
            $self->_run(logfile => "$self->{obj_dir}/vlt_cmake_build.log",
                        cmd => ["cmake",
                                "--build", $self->{obj_dir},
                                ($self->{verbose} ? "--verbose" : ""),
                        ]);
        }
    }
    else {
        $self->error("No compile step defined for '$self->{scenario}' scenario");
    }

    if ($param{make_pli}) {
        # if make_pli is a string and not one
        if ($param{make_pli} ne "1") {
            $self->{pli_filename} = $param{make_pli};
        }
        $self->oprint("Compile vpi\n") if $self->{verbose};
        my @cmd = ($ENV{CXX}, @{$param{pli_flags}},
                   "-D" . $param{tool_define},
                   "-DIS_VPI", ($ENV{CFLAGS} || ''),
                   "$self->{t_dir}/$self->{pli_filename}");

        $self->_run(logfile=>"$self->{obj_dir}/pli_compile.log",
                    fails=>$param{fails},
                    cmd=>\@cmd);
    }

    return 1;
}

sub execute {
    my $self = (ref $_[0] ? shift : $Self);
    return 1 if $self->errors || $self->skips;
    my %param = (%{$self},  # Default arguments are from $self
                 @_);  # Supports arbitrary arguments
    # params may be expect or {tool}_expect
    $self->oprint("Run\n") if $self->{verbose};

    delete $ENV{SYSTEMC_DISABLE_COPYRIGHT_MESSAGE};
    $ENV{SYSTEMC_DISABLE_COPYRIGHT_MESSAGE} = "DISABLE" if !$self->{verbose};

    my $run_env = $param{run_env};
    $run_env .= ' ' if $run_env;

    if ($param{atsim}) {
        $self->_run(logfile=>"$self->{obj_dir}/atsim_sim.log",
                    fails=>$param{fails},
                    cmd=>["echo q | " . $run_env . "$self->{obj_dir}/athdl_sv",
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
                    cmd=>[$run_env . "$self->{obj_dir}/simghdl",
                          @{$param{ghdl_run_flags}},
                          @{$param{all_run_flags}},
                          ],
                    %param,
                    expect=>$param{ghdl_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{ghdl_run_expect_filename},
                    );
    }
    elsif ($param{iv}) {
        my @cmd = ($run_env . "$self->{obj_dir}/simiv",
                   @{$param{iv_run_flags}},
                   @{$param{all_run_flags}},
                          );
        if ($param{use_libvpi}) {
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
        my @pli_opt = ();
        if ($param{use_libvpi}) {
            unshift @pli_opt, "-pli $self->{obj_dir}/libvpi.so";
        }
        $self->_run(logfile=>"$self->{obj_dir}/ms_sim.log",
                    fails=>$param{fails},
                    cmd=>["echo q | " . $run_env . ($ENV{VERILATOR_MODELSIM} || "vsim"),
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
                    cmd=>["echo q | " . $run_env . ($ENV{VERILATOR_NCVERILOG} || "ncverilog"),
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
                    cmd=>["echo q | " . $run_env . "./simv",
                          @{$param{vcs_run_flags}},
                          @{$param{all_run_flags}},
                          ],
                    %param,
                    expect=>$param{vcs_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{vcs_run_expect_filename},
                    );
    }
    elsif ($param{xrun}) {
        my @pli_opt = ();
        if ($param{use_libvpi}) {
            unshift @pli_opt, "-loadvpi $self->{obj_dir}/libvpi.so:vpi_compat_bootstrap";
        }
        $self->_run(logfile=>"$self->{obj_dir}/xrun_sim.log",
                    fails=>$param{fails},
                    cmd=>["echo q | " . $run_env . ($ENV{VERILATOR_XRUN} || "xrun "),
                          @{$param{xrun_run_flags}},
                          @{$param{xrun_flags2}},
                          @{$param{all_run_flags}},
                          @{pli_opt},
                            $param{top_filename},
                          ],
                    %param,
                    expect=>$param{xrun_run_expect},  # non-verilator expect isn't the same
                    expect_filename=>$param{xrun_run_expect_filename},
                    );
    }
    elsif ($param{xsim}) {
        $self->_run(logfile=>"$self->{obj_dir}/xsim_sim.log",
                    fails=>$param{fails},
                    cmd=>[$run_env.($ENV{VERILATOR_XELAB} || "xelab"),
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
        $param{executable} ||= "$self->{obj_dir}/$param{vm_prefix}";
        my $debugger = "";
        if ($opt_gdbsim) {
            $debugger = ($ENV{VERILATOR_GDB} || "gdb") . " ";
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

sub setenv {
    my $self = (ref $_[0] ? shift : $Self);
    my $var = shift;
    my $val = shift;
    print "\texport $var='$val'\n";
    $ENV{$var} = $val;
}

sub inline_checks {
    my $self = (ref $_[0] ? shift : $Self);
    return 1 if $self->errors || $self->skips;
    return 1 if !$self->{vlt_all};

    my $covfn = $Self->{coverage_filename};
    my $contents = $self->file_contents($covfn);

    $self->oprint("Extract checks\n") if $self->{verbose};
    my $fh = IO::File->new("<$self->{top_filename}");
    while (defined(my $line = $fh->getline)) {
        if ($line =~ /CHECK/) {
            if ($line =~ /CHECK_COVER *\( *([---0-9]+) *, *"([^"]+)" *, *("([^"]+)" *,|) *(\d+) *\)/) {
                my $lineno = ($. + $1); my $hier = $2; my $comment = $4; my $count = $5;
                my $regexp = "\001l\002" . $lineno;
                $regexp .= ".*\001o\002" . quotemeta($comment) if $comment;
                $regexp .= ".*\001h\002" . quotemeta($hier) if $hier;
                $regexp .= ".*' " . $count;
                if ($contents !~ /$regexp/) {
                    $self->error("CHECK_COVER: $covfn: Regexp not found: $regexp\n" .
                                 "From $self->{top_filename}:$.: $line");
                }
            }
            elsif ($line =~ /CHECK_COVER_MISSING *\( *([---0-9]+) *\)/) {
                my $lineno = ($. + $1);
                my $regexp = "\001l\002" . $lineno;
                if ($contents =~ /$regexp/) {
                    $self->error("CHECK_COVER_MISSING: $covfn: Regexp found: $regexp\n" .
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
    my $self = (ref $_[0] ? shift : $Self);
    $self->{ok} = $_[0] if defined $_[0];
    $self->{ok} = 0 if $self->{errors} || $self->{errors_keep_going} || $self->{skips};
    return $self->{ok};
}

sub continuing {
    my $self = (ref $_[0] ? shift : $Self);
    return !($self->errors || $self->skips);
}

sub errors {
    my $self = (ref $_[0] ? shift : $Self);
    return $self->{errors};
}

sub golden_filename {
    my $self = (ref $_[0] ? shift : $Self);
    $self->{golden_filename} = shift if defined $_[0];
    return $self->{golden_filename};
}

sub scenario_off {
    my $self = (ref $_[0] ? shift : $Self);
    return $self->{scenario_off};
}

sub skips {
    my $self = (ref $_[0] ? shift : $Self);
    return $self->{skips};
}

sub top_filename {
    my $self = (ref $_[0] ? shift : $Self);
    $self->{top_filename} = shift if defined $_[0];
    return $self->{top_filename};
}

sub vhdl {
    my $self = (ref $_[0] ? shift : $Self);
    $self->{vhdl} = shift if defined $_[0];
    if ($self->{vhdl}) {
        $self->{top_filename} =~ s/\.v$/\.vhdl/;
    }
    return $self->{vhdl};
}

sub v_suffix {
    my $self = (ref $_[0] ? shift : $Self);
    # Suffix for file type, e.g. .vhdl or .v
    return $self->{vhdl} ? "vhdl" : "v";
}

sub sc {
    my $self = (ref $_[0] ? shift : $Self);
    return $self->{sc};
}

sub have_sc {
    return ::_have_sc();
}

sub have_coroutines {
    return ::_have_coroutines();
}

sub make_version {
    my $ver = `$ENV{MAKE} --version`;
    if ($ver =~ /make ([0-9]+\.[0-9]+)/i) {
        return $1;
    } else {
        return -1;
    }
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

our $_have_solver = undef;
sub have_solver {
    if (!defined($_have_solver)) {
        my $ok = `(z3 --help || cvc5 --help || cvc4 --help) 2>/dev/null`;
        $ok ||= "";
        if ($ok =~ /usage/i) {
            $_have_solver = 1;
        } else {
            $_have_solver = 0;
        }
    }
    return $_have_solver;
}

our $_aslr_off = undef;
sub aslr_off {
    if (!defined($_aslr_off)) {
        my $ok = `setarch --addr-no-randomize echo ok 2>/dev/null` || "";
        if ($ok =~ /ok/) {
            $_aslr_off = "setarch --addr-no-randomize ";
        } else {
            $_aslr_off = "";
        }
    }
    return $_aslr_off;
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
    my $self = (ref $_[0] ? shift : $Self);
    $self->{pli_filename} = shift if defined $_[0];
    return $self->{pli_filename};
}

sub rerunnable {
    my $self = (ref $_[0] ? shift : $Self);
    $self->{rerunnable} = shift if defined $_[0];
    return $self->{rerunnable};
}

sub too_few_cores {
    my $threads = ::calc_threads($Vltmt_threads);
    return $threads < $Vltmt_threads;
}

sub skip_if_too_few_cores {
    my $self = (ref $_[0] ? shift : $Self);
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

sub vm_prefix {
    my $self = (ref $_[0] ? shift : $Self);
    $self->{vm_prefix} = shift if defined $_[0];
    return $self->{vm_prefix};
}

#----------------------------------------------------------------------

sub run {
    my $self = (ref $_[0] ? shift : $Self);
    $self->_run(@_);  # See _run() for arguments
}

sub _run {
    my $self = (ref $_[0] ? shift : $Self);
    my %param = (tee => 1,
                 # cmd => [...]
                 # aslr_off => # Disable address space layour randomization
                 # check_finished => 0  # Check for All Finished
                 # entering =>  # Print entering directory information
                 # expect =>  # Regexp to expect in output
                 # expect_filename =>  # Filename that should match logfile
                 # fails => 0  # Command should fail
                 # logfile =>  # Filename to write putput to
                 # verilator_run =>  # Move gcov data to parallel area
                 @_);  # All legal arguments shown immediately above

    my $command = join(' ', @{$param{cmd}});

    if ($param{aslr_off}) {
        if (my $prefix = aslr_off()) {
            $command = "$prefix $command";
        }
    }

    $command = "time $command" if $opt_benchmark && $command !~ /^cd /;

    if ($param{verilator_run}) {
        # Gcov fails when parallel jobs write same data file,
        # so we make sure .gcda output dir is unique across all running jobs.
        # We can't just put each one in an unique obj_dir as it uses too much disk.
        # Must use absolute path as some execute()s have different PWD
        $ENV{GCOV_PREFIX_STRIP} = 99;
        $ENV{GCOV_PREFIX} = File::Spec->rel2abs("$FindBin::RealBin/obj_dist/gcov_$self->{running_id}");
        mkdir $ENV{GCOV_PREFIX};
        print "export GCOV_PREFIX_STRIP=99 GCOV_PREFIX=$ENV{GCOV_PREFIX}\n" if $self->{verbose};
    } else {
        delete $ENV{GCOV_PREFIX_STRIP};
        delete $ENV{GCOV_PREFIX};
    }

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
        my $backup_fg_group = POSIX::tcgetpgrp(0);
        my $pid = fork();
        if ($pid) {  # Parent
            if ($interactive_debugger) {
                # Let gdb take care of signals send from keyboard
                POSIX::setpgid($pid, 0);  # Put child in separate process group
                POSIX::tcsetpgrp(0, $pid);  # Make this group a foreground one
            }
            close CHILDWR;
            print "driver: Entering directory '",
                File::Spec->rel2abs($param{entering}), "'\n" if $param{entering};
            while (1) {
                my $buf = '';
                my $got = sysread PARENTRD, $buf, 10000;
                last if defined $got && $got == 0;
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
            if (!$opt_gdb) {
                # Redirecting the stdout of GDB prevents output syntax colors
                # and the use of the TUI, so only redirect when not --gdb
                open(STDOUT, ">&CHILDWR") or croak "%Error: Can't redirect stdout, stopped";
                open(STDERR, ">&STDOUT") or croak "%Error: Can't dup stdout, stopped";
                autoflush STDOUT 1;
                autoflush STDERR 1;
            }
            system "$command";
            my $status = $?;
            if (($status & 127) == 4  # SIGILL
                || ($status & 127) == 8  # SIGFPA
                || ($status & 127) == 11) {  # SIGSEGV
                $Self->error("Exec failed with core dump");
            }
            exit($? ? 10 : 0);  # $?>>8 misses coredumps
        }
        waitpid($pid, 0);
        if ($interactive_debugger) {
            # Restore old foreground group
            local $SIG{TTOU} = 'IGNORE';  # Ignore SIGTTOU from modyfing terminal settings in bg proccess
            POSIX::tcsetpgrp(0, $backup_fg_group);
        }
        $status = $? || 0;
    }
    flush STDOUT;
    flush STDERR;

    if (!$param{fails} && $status) {
        my $firstline = "";
        if (my $fh = IO::File->new("<$param{logfile}")) {
            while (defined(my $line = $fh->getline)) {
                next if $line =~ /^- /;  # Debug message
                $firstline = $line;
                chomp $firstline;
                last;
            }
        }
        $self->error("Exec of $param{cmd}[0] failed: $firstline\n");
    }
    if ($param{fails} && $status) {
        print "(Exec expected to fail, and did.)\n";
    }
    if ($param{fails} && !$status) {
        $self->error("Exec of $param{cmd}[0] ok, but expected to fail\n");
    }
    return if $self->errors || $self->skips;

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
                $wholefile =~ s/^==[0-9]+== [^\n]+\n//mig; # valgrind

                # Compare
                my $quoted = quotemeta($param{expect});
                my $ok = ($wholefile eq $param{expect}
                          || _try_regex($wholefile, $param{expect}) == 1
                          || $wholefile =~ /$quoted/ms);
                if (!$ok) {
                    #print "**BAD  $self->{name} $param{logfile} MT $moretry  $try\n";
                    next if $moretry;
                    $self->error("Miscompares in output from $param{cmd}[0]\n");
                    $self->error("Might be error in regexp format\n") if $ok < 1;
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
    my $text = shift;
    my $regex = shift;
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
    my $timing_loop = shift;

    if ($timing_loop && $self->sc) {
        $self->error("Cannot use timing loop and SystemC together!\n");
    }

    if ($self->vhdl) {
        $self->_read_inputs_vhdl();
    } else {
        $self->_read_inputs_v();
    }

    my $filename = $self->{main_filename};
    my $fh = IO::File->new(">$filename") or die "%Error: $! $filename,";

    print $fh "// Test defines\n";
    print $fh "#define MAIN_TIME_MULTIPLIER " . ($self->{main_time_multiplier} || 1) . "\n";

    print $fh "#include <memory>\n";
    print $fh "#include <fstream>\n" if $self->{benchmarksim};
    print $fh "#include <chrono>\n" if $self->{benchmarksim};
    print $fh "#include <iomanip>\n" if $self->{benchmarksim};

    print $fh "// OS header\n";
    print $fh "#include \"verilatedos.h\"\n";

    print $fh "// Generated header\n";
    my $vm_prefix = $self->{vm_prefix};
    print $fh "#include \"${vm_prefix}.h\"\n";

    print $fh "// General headers\n";
    print $fh "#include \"verilated.h\"\n";
    print $fh "#include \"systemc.h\"\n" if $self->sc;
    print $fh "#include \"verilated_fst_c.h\"\n" if $self->{trace} && $self->{trace_format} eq 'fst-c';
    print $fh "#include \"verilated_fst_sc.h\"\n" if $self->{trace} && $self->{trace_format} eq 'fst-sc';
    print $fh "#include \"verilated_vcd_c.h\"\n" if $self->{trace} && $self->{trace_format} eq 'vcd-c';
    print $fh "#include \"verilated_vcd_sc.h\"\n" if $self->{trace} && $self->{trace_format} eq 'vcd-sc';
    print $fh "#include \"verilated_save.h\"\n" if $self->{savable};

    print $fh "std::unique_ptr<${vm_prefix}> topp;\n";

    if ($self->{savable}) {
        $fh->print("\n");
        $fh->print("void save_model(const char* filenamep) {\n");
        $fh->print("    VL_PRINTF(\"Saving model to '%s'\\n\", filenamep);\n");
        $fh->print("    VerilatedSave os;\n");
        $fh->print("    os.open(filenamep);\n");
        $fh->print("    os << *topp;\n");
        $fh->print("    os.close();\n");
        $fh->print("}\n");
        $fh->print("\n");
        $fh->print("void restore_model(const char* filenamep) {\n");
        $fh->print("    VL_PRINTF(\"Restoring model from '%s'\\n\", filenamep);\n");
        $fh->print("    VerilatedRestore os;\n");
        $fh->print("    os.open(filenamep);\n");
        $fh->print("    os >> *topp;\n");
        $fh->print("    os.close();\n");
        $fh->print("}\n");
    }

    #### Main
    if ($self->sc) {
        print $fh "extern int sc_main(int argc, char** argv);\n";
        print $fh "int sc_main(int argc, char** argv) {\n";
        print $fh "    sc_signal<bool> fastclk;\n" if $self->{inputs}{fastclk};
        print $fh "    sc_signal<bool> clk;\n" if $self->{inputs}{clk};
        print $fh "    sc_set_time_resolution(1, $Self->{sc_time_resolution});\n";
        print $fh "    sc_time sim_time($self->{sim_time}, $Self->{sc_time_resolution});\n";
    } else {
        print $fh "int main(int argc, char** argv) {\n";
        print $fh "    uint64_t sim_time = $self->{sim_time};\n";
    }

    print $fh "    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};\n";
    print $fh "    contextp->threads($self->{context_threads});\n";
    print $fh "    contextp->commandArgs(argc, argv);\n";
    print $fh "    contextp->debug(" . ($self->{verilated_debug} ? 1 : 0) . ");\n";
    print $fh "    srand48(5);\n";  # Ensure determinism
    print $fh "    contextp->randReset(" . $self->{verilated_randReset} . ");\n"
        if defined $self->{verilated_randReset};
    print $fh "    topp.reset(new ${vm_prefix}{\"top\"});\n";
    print $fh "    contextp->internalsDump()\n;" if $self->{verilated_debug};

    my $set;
    if ($self->sc) {
        print $fh "    topp->fastclk(fastclk);\n" if $self->{inputs}{fastclk};
        print $fh "    topp->clk(clk);\n" if $self->{inputs}{clk};
        $set = "";
    } else {
        print $fh "    topp->eval();\n";
        $set = "topp->";
    }

    if ($self->{benchmarksim}) {
        $fh->print("    std::chrono::time_point<std::chrono::steady_clock> starttime;\n");
        $fh->print("    bool warm = false;\n");
        $fh->print("    uint64_t n_evals = 0;\n");
    }

    if ($self->{trace}) {
        $fh->print("\n");
        $fh->print("#if VM_TRACE\n");
        $fh->print("    contextp->traceEverOn(true);\n");
        $fh->print("    std::unique_ptr<VerilatedFstC> tfp{new VerilatedFstC};\n") if $self->{trace_format} eq 'fst-c';
        $fh->print("    std::unique_ptr<VerilatedFstSc> tfp{new VerilatedFstSc};\n") if $self->{trace_format} eq 'fst-sc';
        $fh->print("    std::unique_ptr<VerilatedVcdC> tfp{new VerilatedVcdC};\n") if $self->{trace_format} eq 'vcd-c';
        $fh->print("    std::unique_ptr<VerilatedVcdSc> tfp{new VerilatedVcdSc};\n") if $self->{trace_format} eq 'vcd-sc';
        $fh->print("    sc_core::sc_start(sc_core::SC_ZERO_TIME);  // Finish elaboration before trace and open\n") if $self->sc;
        $fh->print("    topp->trace(tfp.get(), 99);\n");
        $fh->print("    tfp->open(\"" . $self->trace_filename . "\");\n");

        if ($self->{trace} && !$self->sc) {
            $fh->print("    if (tfp) tfp->dump(contextp->time());\n");
        }
        $fh->print("#endif\n");
    }

    if ($self->{savable}) {
        $fh->print("    const char* save_time_strp = contextp->commandArgsPlusMatch(\"save_time=\");\n");
        $fh->print("    unsigned int save_time = !save_time_strp[0] ? 0 : std::atoi(save_time_strp + std::strlen(\"+save_time=\"));\n");
        $fh->print("    const char* save_restore_strp = contextp->commandArgsPlusMatch(\"save_restore=\");\n");
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
    if (!$timing_loop) {
        _print_advance_time($self, $fh, 10);
    }
    print $fh "    }\n";

    my $time = $self->sc ? "sc_time_stamp()" : "contextp->time()";

    print $fh "    while (";
    if (!$timing_loop || $self->{inputs}{clk}) {
        print $fh "(${time} < sim_time * MAIN_TIME_MULTIPLIER) && ";
    }
    print $fh "!contextp->gotFinish()) {\n";

    if ($timing_loop) {
        print $fh "        topp->eval();\n";
        if ($self->{trace}) {
            $fh->print("#if VM_TRACE\n");
            $fh->print("        if (tfp) tfp->dump(contextp->time());\n");
            $fh->print("#endif  // VM_TRACE\n");
        }
        if ($self->{inputs}{clk}) {
            print $fh "        uint64_t cycles = contextp->time() / MAIN_TIME_MULTIPLIER;\n";
            print $fh "        uint64_t new_time = (cycles + 1) * MAIN_TIME_MULTIPLIER;\n";
            print $fh "        if (topp->eventsPending() &&\n";
            print $fh "            topp->nextTimeSlot() / MAIN_TIME_MULTIPLIER <= cycles) {\n";
            print $fh "            new_time = topp->nextTimeSlot();\n";
            print $fh "        } else {\n";
            print $fh "            ${set}clk = !${set}clk;\n";
            print $fh "        }\n";
            print $fh "        contextp->time(new_time);\n";
        } else {
            print $fh "        if (!topp->eventsPending()) break;\n";
            print $fh "        contextp->time(topp->nextTimeSlot());\n";
        }
    } else {
        for (my $i = 0; $i < 5; $i++) {
            my $action = 0;
            if ($self->{inputs}{fastclk}) {
                print $fh "        ${set}fastclk = !${set}fastclk;\n";
                $action = 1;
            }
            if ($i == 0 && $self->{inputs}{clk}) {
                print $fh "        ${set}clk = !${set}clk;\n";
                $action = 1;
            }
            if ($self->{savable}) {
                $fh->print("        if (save_time && ${time} == save_time) {\n");
                $fh->print("            save_model(\"$self->{obj_dir}/saved.vltsv\");\n");
                $fh->print("            printf(\"Exiting after save_model\\n\");\n");
                $fh->print("            topp.reset(nullptr);\n");
                $fh->print("            return 0;\n");
                $fh->print("        }\n");
            }
            _print_advance_time($self, $fh, 1, $action);
        }
    }
    if ($self->{benchmarksim}) {
        $fh->print("        if (VL_UNLIKELY(!warm)) {\n");
        $fh->print("            starttime = std::chrono::steady_clock::now();\n");
        $fh->print("            warm = true;\n");
        $fh->print("        } else {\n");
        $fh->print("            ++n_evals;\n");
        $fh->print("        }\n");
    }
    print $fh "    }\n";

    if ($self->{benchmarksim}) {
        $fh->print("    {\n");
        $fh->print("        const std::chrono::duration<double> exec_s =  std::chrono::steady_clock::now() - starttime;\n");
        $fh->print("        std::ofstream benchfile(\"" . $self->benchmarksim_filename() . "\", std::ofstream::out | std::ofstream::app);\n");
        $fh->print("        benchfile << std::fixed << std::setprecision(9) << n_evals << \",\" << exec_s.count() << std::endl;\n");
        $fh->print("        benchfile.close();\n");
        $fh->print("    }\n");
    }

    print $fh "    if (!contextp->gotFinish()) {\n";
    print $fh '        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");', "\n";
    print $fh "    }\n";
    print $fh "    topp->final();\n";

    if ($self->{coverage}) {
        $fh->print("#if VM_COVERAGE\n");
        $fh->print("    contextp->coveragep()->write(\"", $self->{coverage_filename}, "\");\n");
        $fh->print("#endif  // VM_COVERAGE\n");
    }
    if ($self->{trace}) {
        $fh->print("#if VM_TRACE\n");
        $fh->print("    if (tfp) tfp->close();\n");
        $fh->print("    tfp.reset();\n");
        $fh->print("#endif  // VM_TRACE\n");
    }
    $fh->print("\n");

    print $fh "    topp.reset();\n";
    print $fh "    return 0;\n";
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
        print $fh "        sc_start(${time} * MAIN_TIME_MULTIPLIER, $Self->{sc_time_resolution});\n";
    } else {
        if ($action) {
            print $fh "        ${set}eval();\n";
            if ($self->{trace} && !$self->sc) {
                $fh->print("#if VM_TRACE\n");
                $fh->print("        if (tfp) tfp->dump(contextp->time());\n");
                $fh->print("#endif  // VM_TRACE\n");
            }
        }
        print $fh "        contextp->timeInc(${time} * MAIN_TIME_MULTIPLIER);\n";
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

    my $fh = IO::File->new(">$self->{top_shell_filename}")
        or die "%Error: $! $self->{top_shell_filename},";
    print $fh "module top;\n";
    foreach my $inp (sort (keys %{$self->{inputs}})) {
        print $fh "    reg ${inp};\n";
    }
    # Inst
    print $fh "    t t (\n";
    my $comma = "";
    foreach my $inp (sort (keys %{$self->{inputs}})) {
        print $fh "      ${comma}.${inp} (${inp})\n";
        $comma = ",";
    }
    print $fh "    );\n";

    # Waves
    print $fh "\n";
    print $fh "`ifdef WAVES\n";
    print $fh "   initial begin\n";
    print $fh "      \$display(\"-Tracing Waves to Dumpfile: " . $self->trace_filename . "\");\n";
    print $fh "      \$dumpfile(\"" . $self->trace_filename . "\");\n";
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
    for (my $i = 0; $i < 5; $i++) {
        print $fh "          #1;\n";
        print $fh "          fastclk = !fastclk;\n" if $self->{inputs}{fastclk};
        print $fh "          clk = !clk;\n" if $i == 4 && $self->{inputs}{clk};
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
            $semi = ";";
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
        my $comma = "";
        foreach my $inp (@ports) {
            print $fh "\t${comma}${inp} => ${inp}\n";
            $comma = ",";
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
    my $get_sigs = 1;
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
# File utilities

sub files_identical {
    my $self = (ref $_[0] ? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    my $fn1_is_logfile = shift;
    return 1 if $self->errors || $self->skips;

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
                    && !/^In file: .*\/sc_.*:\d+/
                    && !/^libgcov.*/
                    && !/--- \/tmp\//  # t_difftree.pl
                    && !/\+\+\+ \/tmp\//  # t_difftree.pl
                    && !/^==[0-9]+== ?[^\n]*\n/  # valgrind
            } @l1;
            @l1 = map {
                while (s/(Internal Error: [^\n]+\.(cpp|h)):[0-9]+/$1:#/g) {}
                s/^-V\{t[0-9]+,[0-9]+\}/-V{t#,#}/;  # --vlt vs --vltmt run differences
                $_;
            } @l1;
            for (my $l = 0; $l <= $#l1; ++$l) {
                # Don't put control chars into our source repository
                $l1[$l] =~ s/\r/<#013>/mig;
                $l1[$l] =~ s/Command Failed[^\n]+/Command Failed/mig;
                $l1[$l] =~ s/Version: Verilator[^\n]+/Version: Verilator ###/mig;
                $l1[$l] =~ s/CPU Time: +[0-9.]+ seconds[^\n]+/CPU Time: ###/mig;
                $l1[$l] =~ s/\?v=[0-9.]+/?v=latest/mig;  # warning URL
                $l1[$l] =~ s/_h[0-9a-f]{8}_/_h########_/mg;
                $l1[$l] =~ s!%Error: \./!%Error: !mg; # clang gives ./ while GCC does not
                $l1[$l] =~ s/ \/[^ ]+\/verilated_std.sv/ verilated_std.sv/mg;
                if ($l1[$l] =~ s/Exiting due to.*/Exiting due to/mig) {
                    splice @l1, $l+1;  # Trunc rest
                    last;
                }
            }
        }
        my $nl = $#l1; $nl = $#l2 if ($#l2 > $nl);
        for (my $l=0; $l<=$nl; ++$l) {
            if (($l1[$l] || "") ne ($l2[$l] || "")) {
                next try if $moretry;
                $self->error_keep_going("Line " . ($l+1) . " miscompares; $fn1 != $fn2");
                warn("F1: " . ($l1[$l] || "*EOF*\n")
                     . "F2: " . ($l2[$l] || "*EOF*\n"));
                if ($ENV{HARNESS_UPDATE_GOLDEN}) {  # Update golden files with current
                    warn "%Warning: HARNESS_UPDATE_GOLDEN set: cp $fn1 $fn2\n";
                    my $fhw = IO::File->new(">$fn2") or $self->error("Files_identical $! $fn2\n");
                    $fhw->print(join('', @l1));
                } else {
                    warn "To update reference: HARNESS_UPDATE_GOLDEN=1 {command} or --golden\n";
                }
                return 0;
            }
        }
        return 1;
    }
}

sub files_identical_sorted {
    my $self = (ref $_[0] ? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    my $fn1_is_logfile = shift;
    return 1 if $self->errors || $self->skips;
    # Set LC_ALL as suggested in the sort manpage to avoid sort order
    # changes from the locale.
    setenv('LC_ALL', "C");
    my $fn1sort = "$fn1.sort";
    run(cmd => ["sort", "$fn1", "> $fn1sort"]);
    return $self->files_identical($fn1sort, $fn2, $fn1_is_logfile);
}

sub copy_if_golden {
    my $self = (ref $_[0] ? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    if ($ENV{HARNESS_UPDATE_GOLDEN}) {  # Update golden files with current
        warn "%Warning: HARNESS_UPDATE_GOLDEN set: cp $fn1 $fn2\n";
        eval "use File::Copy;";
        File::Copy::copy($fn1, $fn2);
    }
}

sub vcd_identical {
    my $self = (ref $_[0] ? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    return 0 if $self->errors || $self->skips;
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
        if ($? != 0 || $out ne '') {
            $cmd = qq{vcddiff "$fn2" "$fn1"};
            print "\t$cmd\n" if $::Debug;
            $out = `$cmd`;
            if ($? != 0 || $out ne '') {
                print $out;
                $self->error("VCD miscompares $fn2 $fn1\n");
                $self->copy_if_golden($fn1, $fn2);
                return 0;
            }
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
            $self->error("VCD hier miscompares $fn1 $fn2\n");
            $self->copy_if_golden($fn1, $fn2);
            return 0;
        }
    }
    return 1;
}

sub fst2vcd {
    my $self = (ref $_[0] ? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    if (!-r $fn1) { $self->error("File does not exist $fn1\n"); return 0; }
    my $cmd = qq{fst2vcd -h};
    print "\t$cmd\n" if $::Debug;
    my $out = `$cmd`;
    if (!$out || $out !~ /Usage:/) { $self->skip("No fst2vcd installed\n"); return 1; }

    $cmd = qq{fst2vcd -e -f "$fn1" -o "$fn2"};
    print "\t$cmd\n";  # Always print to help debug race cases
    $out = `$cmd`;
    return 1;
}

sub fst_identical {
    my $self = (ref $_[0] ? shift : $Self);
    my $fn1 = shift;
    my $fn2 = shift;
    return 0 if $self->errors || $self->skips;
    my $tmp = $fn1 . ".vcd";
    fst2vcd($fn1, $tmp);
    return vcd_identical($tmp, $fn2);
}

sub _vcd_read {
    my $self = (ref $_[0] ? shift : $Self);
    my $filename = shift;
    my $data = {};
    my $fh = IO::File->new("<$filename");
    if (!$fh) { warn "%Error: $! $filename\n"; return $data; }
    my @hier = ($data);
    my $lasthier;
    while (defined(my $line = $fh->getline)) {
        if ($line =~ /\$scope (module|struct|interface)\s+(\S+)/) {
            $hier[$#hier]->{$1} ||= {};
            push @hier, $hier[$#hier]->{$1};
            $lasthier = $hier[$#hier];
        } elsif ($line =~ /(\$var \S+\s+\d+\s+)\S+\s+(\S+)/) {
            $hier[$#hier]->{$1 . $2} ||= {};
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
    $_Cxx_Version ||= `$ENV{MAKE} -C $ENV{TEST_REGRESS} -f Makefile print-cxx-version`;
    return $_Cxx_Version;
}

our $_Cfg_with_ccache;

sub cfg_with_ccache {
    $_Cfg_with_ccache ||= `grep "OBJCACHE \?= ccache" "$ENV{VERILATOR_ROOT}/include/verilated.mk"` ne "";
    return $_Cfg_with_ccache;
}

sub tries {
    # Number of retries when reading logfiles, generally only need many
    # retries when system is busy running a lot of tests
    return 2 if !$::Fork->running;
    return 7 if (scalar($::Fork->running)) > 1;
    return 2;
}

sub glob_all {
    my $self = (ref $_[0] ? shift : $Self);
    my $pattern = shift;

    return glob($pattern);
}

sub glob_one {
    my $self = (ref $_[0] ? shift : $Self);
    my $pattern = shift;
    return if $self->errors || $self->skips;

    my @files = glob($pattern);
    my $n = scalar @files;
    if ($n == 0) {
        $self->error("glob_one: pattern '$pattern' does not match any files\n");
    } elsif ($n != 1) {
        my $msg = "glob_one: pattern '$pattern' matches multiple files:\n";
        foreach my $file (@files) {
            $msg .= $file . "\n";
        }
        $self->error($msg);
    } else {
        return $files[0];
    }
}

sub file_grep_not {
    my $self = (ref $_[0] ? shift : $Self);
    my $filename = shift;
    my $regexp = shift;
    my $expvalue = shift;
    return if $self->errors || $self->skips;
    !defined $expvalue or $self->error("file_grep_not: Unexpected 3rd argument: $expvalue");

    my $contents = $self->file_contents($filename);
    return if ($contents eq "_Already_Errored_");
    if ($contents =~ /$regexp/) {
        $self->error("File_grep_not: $filename: Regexp found: $regexp\n");
    }
}

sub file_grep {
    my $self = (ref $_[0] ? shift : $Self);
    my $filename = shift;
    my $regexp = shift;
    my $expvalue = shift;
    return if $self->errors || $self->skips;

    my $contents = $self->file_contents($filename);
    return if ($contents eq "_Already_Errored_");
    if ($contents !~ /$regexp/) {
        $self->error("File_grep: $filename: Regexp not found: $regexp\n");
    } elsif (defined($expvalue) && $expvalue ne $1) {
        $self->error("File_grep: $filename: Got='$1' Expected='$expvalue' in regexp: $regexp\n");
    }
    return @{^CAPTURE};
}

sub file_grep_count {
    my $self = (ref $_[0] ? shift : $Self);
    my $filename = shift;
    my $regexp = shift;
    my $expcount = shift;
    return if $self->errors || $self->skips;

    my $contents = $self->file_contents($filename);
    my $count = () = $contents =~ /$regexp/g;
    if ($count != $expcount) {
        $self->error("file_grep_count: $filename: Got='$count' Expected='$expcount' for regexp: $regexp\n");
    }
}

sub file_grep_any {
    my $self = $Self;
    my @filenames = @{$_[0]}; shift;
    my $regexp = shift;
    my $expvalue = shift;
    return if $self->errors || $self->skips;

    foreach my $filename (@filenames) {
        my $contents = $self->file_contents($filename);
        return if ($contents eq "_Already_Errored_");
        if ($contents =~ /$regexp/) {
            if ($expvalue && $expvalue ne $1) {
                $self->error("file_grep: $filename: Got='$1' Expected='$expvalue' in regexp: $regexp\n");
            }
            return;
        }
    }
    my $msg = "file_grep_any: Regexp '$regexp' not found in any of the following files:\n";
    foreach my $filename (@filenames) {
        $msg .= $filename . "\n";
    }
    $self->error($msg);
}

my %_File_Contents_Cache;

sub file_contents {
    my $self = (ref $_[0] ? shift : $Self);
    my $filename = shift;

    if (!$_File_Contents_Cache{$filename}) {
        my $fh = IO::File->new("<$filename");
        if (!$fh) {
            $_File_Contents_Cache{$filename} = "_Already_Errored_";
            $self->error("File_contents file not found: " . $filename . "\n");
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
    my $self = (ref $_[0] ? shift : $Self);
    my $filename = shift;
    my $contents = shift;
    my $fh = IO::File->new(">$filename") or die "%Error: $! writing $filename,";
    print $fh $contents;
    $fh->close;
    delete $_File_Contents_Cache{$filename};
}

sub file_sed {
    my $self = (ref $_[0] ? shift : $Self);
    my $infilename = shift;
    my $outfilename = shift;
    my $editcb = shift;
    my $contents = $self->file_contents($infilename);
    {
        $_ = $contents;
        $editcb->($contents);
        $contents = $_;
    }
    $self->write_wholefile($outfilename, $contents);
}

sub extract {
    my $self = (ref $_[0] ? shift : $Self);
    my %param = (#in =>,
                 #out =>
                 regexp => qr/.*/,
                 lineno_adjust => -9999,
                 lines => undef,  #'#, #-#',
                 @_);  # All legal arguments shown immediately above

    my $temp_fn = $param{out};
    $temp_fn =~ s!.*/!!g;
    $temp_fn = $self->{obj_dir} . "/" . $temp_fn;

    my @out;
    my $emph = "";
    my $lineno = 0;
    my $lineno_out = 0;
    {
        my $fh = IO::File->new("<$param{in}") or die "%Error: $! $param{in},";
        while (defined(my $line = $fh->getline)) {
            ++$lineno;
            if ($line =~ /$param{regexp}/
                && _lineno_match($lineno, $param{lines})) {
                if ($line =~ m!t/[A-Za-z0-9_]+.v:(\d+):(\d+):!) {
                    my $lineno = $1;
                    my $col = $2;
                    $lineno += $param{lineno_adjust};
                    $lineno = 1 if $lineno < 1;
                    $line =~ s!t/[A-Za-z0-9_]+.v:(\d+):(\d+):!example.v:${lineno}:${col}!;
                }
                push @out, "   " . $line;
                ++$lineno_out;
                if ($line =~ /<--/) {
                    $emph .= "," if $emph;
                    $emph .= $lineno_out;
                }
            }
        }
    }
    {
        my $fhw = IO::File->new(">$temp_fn") or die "%Error: $! $temp_fn,";
        my $lang = "";
        $lang = " sv" if $param{in} =~ /\.s?vh?$/;
        $fhw->print(".. comment: generated by " . $self->{name} . "\n");
        $fhw->print(".. code-block::${lang}\n");
        $fhw->print("   :linenos:\n") if $lang && $#out > 0;
        $fhw->print("   :emphasize-lines: ${emph}\n") if $emph;
        $fhw->print("\n");

        foreach my $line (@out) {
            $fhw->print($line);
        }
    }

    $self->files_identical($temp_fn, $param{out});
}

sub _lineno_match {
    my $lineno = shift;
    my $lines = shift;
    return 1 if !defined $lines;
    foreach my $lc (split /,/, $lines) {
        if ($lc =~ /^(\d+)$/) {
            return 1 if $1 == $lineno;
        } elsif ($lc =~ /^(\d+)-(\d+)$/) {
            return 1 if $1 <= $lineno && $2 >= $lineno;
        }
    }
    return 0;
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

    $params{run_pre_start}->($self);
    if (my $pid = fork()) {  # Parent
        waitpid($pid, 0);
    } else {  # Child
        $params{run_on_start}->($self);
        exit(0);  # Don't close anything
    }
    $params{run_on_finish}->($self);
    return $self;
}
sub max_proc { }
sub sig_child { }
sub kill_tree_all { }
sub wait_all { }
sub ready { }
sub running { }
sub is_any_left { return 0; }

#######################################################################
1;

package main;
__END__

=pod

=head1 NAME

driver.pl - Run regression tests

=head1 SYNOPSIS

  make test    # In Verilator directory
  ./driver.pl  # Or, to run directly

=head1 DESCRIPTION

driver.pl invokes Verilator or another simulator on each test file.
See docs/internals.rst in the distribution for more information.

=head1 DISTRIBUTION

The latest version is available from L<https://verilator.org>.

Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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
