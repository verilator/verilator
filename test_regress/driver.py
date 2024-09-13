#!/usr/bin/env python3
# pylint: disable=C0103,C0114,C0115,C0116,C0209,C0302,R0902,R0903,R0904,R0912,R0913,R0914,R0915,R0916,W0212,W0511,W0603,W1201
######################################################################

import argparse
import collections
import glob
import hashlib
import json
import logging
import multiprocessing
import os
import pickle
import platform
import re
import runpy
import shutil
import signal
import subprocess
import sys
import time

from functools import lru_cache  # Eventually use python 3.9's cache
from pprint import pformat, pprint
from packaging import version

if False:  # pylint: disable=using-constant-test
    pprint(pformat("Ignored"))  # Prevent unused warning

# Map of all scenarios, with the names used to enable them
All_Scenarios = {
    # yapf: disable
    'dist': ['dist'],
    'atsim': ['simulator', 'simulator_st', 'atsim'],
    'ghdl': ['linter', 'simulator', 'simulator_st', 'ghdl'],
    'iv': ['simulator', 'simulator_st', 'iv'],
    'ms': ['linter', 'simulator', 'simulator_st', 'ms'],
    'nc': ['linter', 'simulator', 'simulator_st', 'nc'],
    'vcs': ['linter', 'simulator', 'simulator_st', 'vcs'],
    'xrun': ['linter', 'simulator', 'simulator_st', 'xrun'],
    'xsim': ['linter', 'simulator', 'simulator_st', 'xsim'],
    'vlt': ['linter', 'simulator', 'simulator_st', 'vlt_all', 'vlt'],
    'vltmt': ['simulator', 'vlt_all', 'vltmt'],
    # yapf: enable
}

# Globals
test = None
Arg_Tests = []
Arg_Driver_Verilator_Flags = []

# So an 'import vltest_bootstrap' inside test files will do nothing
sys.modules['vltest_bootstrap'] = {}

#######################################################################
#######################################################################
# Decorators


class staticproperty(property):

    def __get__(self, owner_self, owner_cls):
        return self.fget()


#######################################################################
#######################################################################
# VtOs -- OS extensions


class VtOs:

    @staticmethod
    def delenv(var: str) -> None:
        """Delete environment variable, if exists"""
        if var in os.environ:
            del os.environ[var]

    @staticmethod
    def getenv_def(var: str, default=None) -> str:
        """Return environment variable, returning default if does not exist"""
        if var in os.environ:
            return os.environ[var]
        return default

    @staticmethod
    def mkdir_ok(path: str) -> None:
        """Make directory, no error if exists"""
        try:
            os.mkdir(path)
        except FileExistsError:
            pass

    @staticmethod
    def run_capture(command: str, check=True) -> str:
        """Run a command and return results"""
        proc = subprocess.run([command], capture_output=True, text=True, shell=True, check=False)
        if check and proc.returncode:
            sys.exit("%Error: command failed '" + command + "':\n" + proc.stderr + proc.stdout)
        return str(proc.stdout)

    @staticmethod
    def unlink_ok(filename: str) -> None:
        """Unlink a file, no error if fails"""
        try:
            os.unlink(filename)
        except OSError:
            pass


#######################################################################
#######################################################################
# Capabilities -- What OS/Verilator is built to support


class Capabilities:

    # @lru_cache(maxsize=1024) broken with @staticmethod on older pythons we use
    _cached_cmake_version = None
    _cached_cxx_version = None
    _cached_have_coroutines = None
    _cached_have_gdb = None
    _cached_have_sc = None
    _cached_have_solver = None
    _cached_make_version = None

    @staticproperty
    def cmake_version() -> str:  # pylint: disable=no-method-argument
        if Capabilities._cached_cmake_version is None:
            out = VtOs.run_capture('cmake --version', check=False)
            match = re.search(r'cmake version (\d+)\.(\d+)', out, re.IGNORECASE)
            if match:
                Capabilities._cached_cmake_version = match.group(1) + "." + match.group(2)
            else:
                Capabilities._cached_cmake_version = 0
        return Capabilities._cached_cmake_version

    @staticproperty
    def cxx_version() -> str:  # pylint: disable=no-method-argument
        if Capabilities._cached_cxx_version is None:
            Capabilities._cached_cxx_version = VtOs.run_capture(os.environ['MAKE'] + " -C " +
                                                                os.environ['TEST_REGRESS'] +
                                                                " -f Makefile print-cxx-version",
                                                                check=False)

        return Capabilities._cached_cxx_version

    @staticproperty
    def have_coroutines() -> bool:  # pylint: disable=no-method-argument
        if Capabilities._cached_have_coroutines is None:
            Capabilities._cached_have_coroutines = bool(
                Capabilities._verilator_get_supported('COROUTINES'))
        return Capabilities._cached_have_coroutines

    @staticproperty
    def have_gdb() -> bool:  # pylint: disable=no-method-argument
        if Capabilities._cached_have_gdb is None:
            out = VtOs.run_capture('gdb --version 2>/dev/null', check=False)
            Capabilities._cached_have_gdb = bool('Copyright' in out)
        return Capabilities._cached_have_gdb

    @staticproperty
    def have_sc() -> bool:  # pylint: disable=no-method-argument
        if Capabilities._cached_have_sc is None:
            if 'SYSTEMC' in os.environ:
                Capabilities._cached_have_sc = True
            elif 'SYSTEMC_INCLUDE' in os.environ:
                Capabilities._cached_have_sc = True
            elif 'CFG_HAVE_SYSTEMC' in os.environ:
                Capabilities._cached_have_sc = True
            else:
                Capabilities._cached_have_sc = bool(
                    Capabilities._verilator_get_supported('SYSTEMC'))
        return Capabilities._cached_have_sc

    @staticproperty
    def have_solver() -> bool:  # pylint: disable=no-method-argument
        if Capabilities._cached_have_solver is None:
            out = VtOs.run_capture('(z3 --help || cvc5 --help || cvc4 --help) 2>/dev/null',
                                   check=False)
            Capabilities._cached_have_solver = bool('Usage' in out)
        return Capabilities._cached_have_solver

    @staticproperty
    @lru_cache(maxsize=1024)
    def make_version() -> str:  # pylint: disable=no-method-argument
        if Capabilities._cached_make_version is None:
            out = VtOs.run_capture(os.environ['MAKE'] + ' --version', check=False)
            match = re.search(r'make ([0-9]+\.[0-9]+)', out, flags=re.IGNORECASE)
            if match:
                Capabilities._cached_make_version = match.group(1)
            else:
                Capabilities._cached_make_version = -1
        return Capabilities._cached_make_version

    # Fetch
    @staticmethod
    def warmup_cache() -> None:
        _ignore = Capabilities.have_coroutines
        _ignore = Capabilities.have_gdb
        _ignore = Capabilities.have_sc
        _ignore = Capabilities.have_solver

    # Internals

    @staticmethod
    def _verilator_get_supported(feature) -> str:
        # Returns if given feature is supported
        cmd = "perl " + os.environ['VERILATOR_ROOT'] + "/bin/verilator -get-supported " + feature
        out = VtOs.run_capture(cmd, check=False).strip()
        if out == '1':
            return True
        if out in ('', '0'):
            return False
        sys.exit("%Error: couldn't verilator_get_supported: " + cmd + "\n" + out)


#######################################################################
#######################################################################
# Forker class - run multprocess pool of processes
# Similar interface to Perl's Parallel::Forker.


class Forker:

    class Process:

        def __init__(self, _id, name, scenario, rerun_skipping, run_pre_start, run_on_start,
                     run_on_finish):
            self.fail_max_skip = False
            self.id = _id
            self.name = name
            self.scenario = scenario
            self.rerun_skipping = rerun_skipping
            self.run_pre_start = run_pre_start
            self.run_on_start = run_on_start
            self.run_on_finish = run_on_finish
            self.mprocess = None  # Set once call run()

        @property
        def pid(self) -> int:
            return self.mprocess.pid

        @property
        def exitcode(self) -> int:
            return self.mprocess.exitcode

    def __init__(self, max_processes):
        self._max_processes = max_processes
        self._id_next = 0
        self._left = collections.deque()  # deque of Process
        self._running = {}  # key of pid, value of Process

    def is_any_left(self) -> bool:
        return self.num_running() > 0 or (len(self._left) > 0 and not Quitting)

    def max_proc(self, n: int) -> None:
        self._max_processes = n

    def poll(self) -> None:
        # We don't use SIGCHLD as conflicted with other handler, instead just poll
        completed = []  # Need two passes to avoid changing the list we are iterating
        nrunning = 0
        for process in self._running.values():
            if process.exitcode is not None:
                completed.append(process)
            else:
                nrunning += 1
        for process in completed:
            self._finished(process)
        while len(self._left) and nrunning < self._max_processes and not Quitting:
            process = self._left.popleft()
            self._run(process)
            nrunning += 1

    def running(self) -> list:
        return self._running.values()

    def num_running(self) -> int:
        return len(self._running)

    def schedule(self, name, scenario, rerun_skipping, run_pre_start, run_on_start, run_on_finish):
        # print("-Forker::schedule: [" + name + "]")
        process = Forker.Process(self._id_next,
                                 name=name,
                                 scenario=scenario,
                                 rerun_skipping=rerun_skipping,
                                 run_pre_start=run_pre_start,
                                 run_on_start=run_on_start,
                                 run_on_finish=run_on_finish)
        self._id_next += 1
        self._left.append(process)

    def kill_tree_all(self) -> None:
        # print("-Forker: kill_tree_all")
        for process in self._running.values():
            process.mprocess.kill()

    def _run(self, process) -> None:
        # print("-Forker: [" + process.name + "] run_pre_start")
        process.run_pre_start(process)

        ctx = multiprocessing.get_context('fork')
        process.mprocess = ctx.Process(target=lambda: self.child_start(process))
        process.mprocess.start()

        # print("-Forker: [" + process.name + "] RUNNING pid=" + str(process.pid))
        self._running[process.pid] = process

    @staticmethod
    def child_start(process) -> None:
        # Runs in context of child
        # print("-Forker: [" + process.name + "] run_on_start")
        process.run_on_start(process)
        # print("-Forker: [" + process.name + "] FINISHED run_on_start")
        sys.exit(0)
        # Don't close anything

    def _finished(self, process) -> None:
        del self._running[process.pid]
        # print("-Forker: [" + process.name + "] run_on_finish exitcode=" + str(process.exitcode))
        process.run_on_finish(process)
        process.mprocess.close()


#######################################################################
#######################################################################
# Runner class


class Runner:

    def __init__(self, driver_log_filename, quiet, ok_cnt=0, fail1_cnt=0, skip_cnt=0):
        self.driver_log_filename = driver_log_filename
        self.quiet = quiet
        # Counts
        self.all_cnt = 0
        self.left_cnt = 0
        self.ok_cnt = ok_cnt
        self.fail1_cnt = fail1_cnt
        self.fail_cnt = 0
        self.skip_cnt = skip_cnt
        self.skip_msgs = []
        self.fail_msgs = []
        self.fail_tests = []
        self._last_proc_finish_time = 0
        self._last_summary_time = 0
        self._last_summary_left = 0
        self._running_ids = {}
        self._msg_fail_max_skip = False
        Runner.runner = self

    def one_test(self, py_filename: str, scenario: str, rerun_skipping=False) -> None:
        self.all_cnt += 1
        self.left_cnt += 1
        forker.schedule(name=py_filename,
                        scenario=scenario,
                        rerun_skipping=rerun_skipping,
                        run_pre_start=self._run_pre_start_static,
                        run_on_start=self._run_on_start_static,
                        run_on_finish=self._run_on_finish_static)

    @staticmethod
    def _run_pre_start_static(process) -> None:
        Runner.runner._run_pre_start(process)  # pylint: disable=protected-access

    def _run_pre_start(self, process) -> None:
        # Running in context of parent, before run_on_start
        # Make an identifier that is unique across all current running jobs
        i = 1
        while i in self._running_ids:
            i += 1
        process.running_id = i
        self._running_ids[process.running_id] = 1
        if Args.fail_max and Args.fail_max <= self.fail_cnt:
            if not self._msg_fail_max_skip:
                self._msg_fail_max_skip = True
                print("== Too many test failures; exceeded --fail-max\n", file=sys.stderr)
            process.fail_max_skip = 1

    @staticmethod
    def _run_on_start_static(process) -> None:
        Runner.runner._run_on_start(process)  # pylint: disable=protected-access

    def _run_on_start(self, process) -> None:
        # Running in context of child, so can't pass data to parent directly
        if self.quiet:
            sys.stdout = open(os.devnull, 'w')  # pylint: disable=R1732,unspecified-encoding
            sys.stderr = open(os.devnull, 'w')  # pylint: disable=R1732,unspecified-encoding

        print("=" * 70)
        global test
        test = VlTest(py_filename=process.name,
                      scenario=process.scenario,
                      running_id=process.running_id)
        test.oprint("=" * 50)
        test._prep()
        if process.rerun_skipping:
            print("  ---------- Earlier logfiles below; test was rerunnable = 0\n")
            os.system("cat $test->{obj_dir}/*.log")
            print("  ---------- Earlier logfiles above; test was rerunnable = 0\n")
        elif process.fail_max_skip:
            test.skip("Too many test failures; exceeded --fail-max")
        else:
            VtOs.unlink_ok(test._status_filename)
            test._read()
        # Don't put anything other than _exit after _read,
        # as may call _exit via another path
        test._exit()

    @staticmethod
    def _run_on_finish_static(process) -> None:
        Runner.runner._run_on_finish(process)  # pylint: disable=protected-access

    def _run_on_finish(self, process) -> None:
        # Running in context of parent
        global test
        test = VlTest(py_filename=process.name,
                      scenario=process.scenario,
                      running_id=process.running_id)
        test._quit = Quitting
        test._read_status()
        if test.ok:
            self.ok_cnt += 1
        elif test._quit:
            pass
        elif test._scenario_off and not test.errors:
            pass
        elif test._skips and not test.errors and not test.errors_keep_going:
            self.skip_msgs.append("\t#" + test.soprint("-Skip:  " + test._skips))
            self.skip_cnt += 1
        else:
            error_msg = test.errors if test.errors else test.errors_keep_going
            test.oprint("FAILED: " + error_msg)
            j = " -j" if Args.jobs else ""
            makecmd = VtOs.getenv_def('VERILATOR_MAKE', os.environ['MAKE']) + j + " &&"
            upperdir = 'test_regress/' if re.search(r'test_regress', os.getcwd()) else ''
            self.fail_msgs.append("\t#" + test.soprint("%Error: " + error_msg) + "\t\t" + makecmd +
                                  " " + upperdir + test.py_filename +
                                  ' '.join(self._manual_args()) + " --" + test.scenario + "\n")
            self.fail_tests.append(test)
            self.fail_cnt += 1
            self.report(self.driver_log_filename)
            other = ""
            for proc in forker.running():
                other += "  " + proc.name
            if other != "" and not Args.quiet:
                test.oprint("Simultaneous running tests:" + other)
            if Args.stop:
                sys.exit("%Error: --stop and errors found\n")

        self.left_cnt -= 1
        self._last_proc_finish_time = time.time()
        if process.running_id:
            del self._running_ids[process.running_id]

    def wait_and_report(self) -> None:
        self.print_summary(force=True)
        # Wait for all children to finish
        while forker.is_any_left():
            forker.poll()
            if not interactive_debugger:
                self.print_summary(force=False)
            time.sleep(0.1)
        self.report(None)
        self.report(self.driver_log_filename)

    def report(self, filename: str) -> None:
        if filename:
            with open(filename, "w", encoding="utf8") as fh:
                self._report_fh(fh)
        else:
            self._report_fh(sys.stdout)

    def _report_fh(self, fh) -> None:
        fh.write("\n")
        fh.write('=' * 70 + "\n")
        for f in sorted(self.fail_msgs):
            fh.write(f.strip() + "\n")
        for f in sorted(self.skip_msgs):
            fh.write(f.strip() + "\n")
        if self.fail_cnt:
            sumtxt = 'FAILED'
        elif self.skip_cnt:
            sumtxt = 'PASSED w/SKIPS'
        else:
            sumtxt = 'PASSED'
        fh.write("==TESTS DONE, " + sumtxt + ": " + self.sprint_summary() + "\n")

    def print_summary(self, force=False):
        change = self._last_summary_left != self.left_cnt
        if (force or ((time.time() - self._last_summary_time) >= 15)
                or (not self.quiet and change)):
            self._last_summary_left = self.left_cnt
            self._last_summary_time = time.time()
            print("==SUMMARY: " + self.sprint_summary(), file=sys.stderr)

            if (self._last_proc_finish_time != 0
                    and ((time.time() - self._last_proc_finish_time) > 15)):
                self._last_proc_finish_time = time.time()
                other = ""
                for proc in forker.running():
                    other += "  " + proc.name
                print("==STILL RUNNING:" + other, file=sys.stderr)

    @staticmethod
    def _py_filename_adjust(py_filename: str,
                            tdir_def: str) -> list:  # Return (py_filename, t_dir)
        for tdir in Test_Dirs:  # pylint: disable=redefined-outer-name
            # t_dir used both absolutely and under obj_dir
            try_py_filename = tdir + "/" + os.path.basename(py_filename)
            if os.path.exists(try_py_filename):
                # Note most tests require error messages of the form t/x.v
                # Therefore py_filename must be t/ for local tests
                # t_dir must be absolute - used under t or under obj_dir
                tdir_abs = os.path.abspath(tdir)
                return (try_py_filename, tdir_abs)
        return (py_filename, os.path.abspath(tdir_def))

    def sprint_summary(self) -> str:
        delta = time.time() - Start
        # Fudge of 120% works out about right so ETA correctly predicts completion time
        eta = 1.2 * ((self.all_cnt * (delta / ((self.all_cnt - self.left_cnt) + 0.001))) - delta)
        if delta < 10:
            eta = 0
        out = ""
        if self.left_cnt:
            out += "Left " + str(self.left_cnt) + "  "
        out += "Passed " + str(self.ok_cnt)
        # Ordered below most severe to least severe
        out += "  Failed " + str(self.fail_cnt)
        if self.fail1_cnt:
            out += "  Failed-First " + str(self.fail1_cnt)
        if self.skip_cnt:
            out += "  Skipped " + str(self.skip_cnt)
        if forker.num_running():
            out += "  Running " + str(forker.num_running())
        if self.left_cnt > 10 and eta > 10:
            out += "  Eta %d:%02d" % (int(eta / 60), eta % 60)
        out += "  Time %d:%02d" % (int(delta / 60), delta % 60)
        return out

    def _manual_args(self) -> str:
        # Return command line with scenarios stripped
        out = []
        for oarg in Orig_ARGV_Sw:
            showarg = True
            for val in All_Scenarios.values():
                for allscarg in val:
                    if oarg == "--" + allscarg:
                        showarg = False
            # Also strip certain flags that per-test debugging won't want
            if showarg and oarg != '--rerun' and oarg != '--quiet':
                out.append(oarg)
        return out


#######################################################################
#######################################################################
# Test exceptions


class VtSkipException(Exception):
    pass


class VtErrorException(Exception):
    pass


#######################################################################
#######################################################################
# Test class


class VlTest:

    _file_contents_cache = {}

    # @lru_cache(maxsize=1024) broken with @staticmethod on older pythons we use
    _cached_aslr_off = None
    _cached_cfg_with_ccache = None

    def __init__(self, py_filename, scenario, running_id):
        self.py_filename = py_filename  # Name of .py file to get setup from
        self.running_id = running_id
        self.scenario = scenario

        self._have_solver_called = False
        self._inputs = {}
        self._ok = False
        self._quit = False
        self._scenario_off = False  # scenarios() didn't match running scenario
        self._skips = None

        match = re.match(r'^(.*/)?([^/]*)\.py', self.py_filename)
        self.name = match.group(2)  # Name of this test

        self.benchmark = Args.benchmark
        self.benchmarksim = False
        self.clean_command = None
        self.context_threads = 0  # Number of threads to allocate in the context
        self.errors = None
        self.errors_keep_going = None
        self.main_time_multiplier = 1
        self.make_main = 1  # Make __main.cpp
        self.make_pli = 0  # need to compile pli
        self.make_top_shell = 1  # Make a default __top.v file
        self.rerunnable = True  # Rerun if fails
        self.sc_time_resolution = "SC_PS"  # Keep - PS is SystemC default
        self.sim_time = 1100  # simulation time units for main wrapper
        self.threads = -1  # --threads (negative means auto based on scenario)
        self.verbose = Args.verbose
        self.verilated_randReset = ""
        self.vm_prefix = "V" + self.name

        # Make e.g. self.vlt, self.vltmt etc
        self.vlt = False  # Set below also
        self.vltmt = False  # Set below also
        self.xsim = False  # Set below also
        for ascenario in All_Scenarios:
            self.__dict__[ascenario] = False
        self.__dict__[scenario] = True
        self.vlt_all = self.vlt or self.vltmt  # Any Verilator scenario

        (self.py_filename, self.t_dir) = Runner._py_filename_adjust(self.py_filename, ".")
        for tdir in Test_Dirs:  # pylint: disable=redefined-outer-name
            # t_dir used both absolutely and under obj_dir
            self.t_dir = None
            if os.path.exists(tdir + "/" + self.name + ".py"):
                # Note most tests require error messages of the form t/x.v
                # Therefore py_filename must be t/ for local tests
                self.py_filename = os.path.relpath(tdir + "/" + self.name + ".py")
                # t_dir must be absolute - used under t or under obj_dir
                self.t_dir = os.path.abspath(tdir)
                break

        if not self.t_dir:
            sys.exit("%Error: Can't locate dir for " + self.name)

        scen_dir = os.path.relpath(self.t_dir + "/../obj_" + self.scenario)
        # Simplify filenames on local runs
        scen_dir = re.sub(r'^t/\.\./', '', scen_dir)
        # Not mkpath so error if try to build somewhere odd
        VtOs.mkdir_ok(scen_dir)
        self.obj_dir = scen_dir + "/" + self.name

        define_opt = self._define_opt_calc()

        # All compilers
        self.v_flags = []
        if self.xsim:
            self.v_flags += ["-f input.xsim.vc"]
        elif os.path.exists('input.vc'):
            self.v_flags += ["-f input.vc"]
        if not re.search(r'/test_regress', self.t_dir):  # Don't include standard dir, only site's
            self.v_flags += ["+incdir+" + self.t_dir + " -y " + self.t_dir]
        self.v_flags += [define_opt + "TEST_OBJ_DIR=" + self.obj_dir]
        if Args.verbose:
            self.v_flags += [define_opt + "TEST_VERBOSE=1"]
        if Args.benchmark:
            self.v_flags += [define_opt + "TEST_BENCHMARK=Args.benchmark"]
        if Args.trace:
            self.v_flags += [define_opt + "WAVES=1"]

        self.v_flags2 = []  # Overridden in some sim files
        self.v_other_filenames = []
        self.all_run_flags = []

        self.pli_flags = [
            "-I" + os.environ['VERILATOR_ROOT'] + "/include/vltstd", "-fPIC", "-shared"
        ]
        if platform.system() == 'Darwin':
            self.pli_flags += ["-Wl,-undefined,dynamic_lookup"]
        else:
            self.pli_flags += ["-rdynamic"]
        if Args.verbose:
            self.pli_flags += ["-DTEST_VERBOSE=1"]
        self.pli_flags += ["-o", self.obj_dir + "/libvpi.so"]

        self.tool_c_flags = []
        # ATSIM
        self.atsim_define = 'ATSIM'
        self.atsim_flags = [
            "-c", "+sv", "+define+ATSIM", ("+sv_dir+" + self.obj_dir + "/.athdl_compile")
        ]
        self.atsim_flags2 = []  # Overridden in some sim files
        self.atsim_run_flags = []
        # GHDL
        self.ghdl_define = 'GHDL'
        self.ghdl_work_dir = self.obj_dir + "/ghdl_compile"
        self.ghdl_flags = [("-v" if Args.debug else ""),
                           ("--workdir=" + self.obj_dir + "/ghdl_compile")]
        self.ghdl_flags2 = []  # Overridden in some sim files
        self.ghdl_run_flags = []
        # IV
        self.iv_define = 'IVERILOG'
        self.iv_flags = ["+define+IVERILOG", "-g2012", ("-o" + self.obj_dir + "/simiv")]
        self.iv_flags2 = []  # Overridden in some sim files
        self.iv_run_flags = []
        # VCS
        self.vcs_define = 'VCS'
        self.vcs_flags = [
            "+vcs+lic+wait", "+cli", "-debug_access", "+define+VCS+1", "-q", "-sverilog",
            "-CFLAGS", "'-DVCS'"
        ]
        self.vcs_flags2 = []  # Overridden in some sim files
        self.vcs_run_flags = ["+vcs+lic_wait"]
        # NC
        self.nc_define = 'NC'
        self.nc_flags = [
            "+licqueue", "+nowarn+LIBNOU", "+define+NC=1", "-q", "+assert", "+sv", "-c",
            ("+access+r" if Args.trace else "")
        ]
        self.nc_flags2 = []  # Overridden in some sim files
        self.nc_run_flags = ["+licqueue", "-q", "+assert", "+sv", "-R"]
        # ModelSim
        self.ms_define = 'MS'
        self.ms_flags = [
            "-sv", "-work", (self.obj_dir + "/work"), "+define+MS=1", "-ccflags", '\"-DMS=1\"'
        ]
        self.ms_flags2 = []  # Overridden in some sim files
        self.ms_run_flags = ["-lib", self.obj_dir + "/work", "-c", "-do", "'run -all;quit'"]
        # XSim
        self.xsim_define = 'XSIM'
        self.xsim_flags = [
            "--nolog", "--sv", "--define", "XSIM", "--work",
            (self.name + "=" + self.obj_dir + "/xsim")
        ]
        self.xsim_flags2 = []  # Overridden in some sim files
        self.xsim_run_flags = [
            "--nolog", "--runall", "--lib", (self.name + "=" + self.obj_dir + "/xsim"),
            (" --debug all" if Args.trace else "")
        ]
        self.xsim_run_flags2 = []  # Overridden in some sim files
        # Xcelium (xrun)
        self.xrun = 0
        self.xrun_define = 'XRUN'
        self.xrun_flags = []  # Doesn't really have a compile step
        self.xrun_flags2 = []  # Overridden in some sim files
        self.xrun_run_flags = [
            "-64", "-access", "+rwc", "-newsv", "-sv", "-xmlibdirname", self.obj_dir + "/work",
            "-l", self.obj_dir + "/history", "-quiet", "-plinowarn"
        ]
        # Verilator
        self.verilator_define = 'VERILATOR'
        self.verilator_flags = [
            "-cc",
            "-Mdir",
            self.obj_dir,
            "--fdedup",  # As currently disabled unless -O3
            "--debug-check",
            "--comp-limit-members",
            "10"
        ]
        self.verilator_flags2 = []
        self.verilator_flags3 = ["--clk clk"]
        self.verilator_make_gmake = True
        self.verilator_make_cmake = False
        self.verilated_debug = Args.verilated_debug

        self._status_filename = self.obj_dir + "/V" + self.name + ".status"
        self.coverage_filename = self.obj_dir + "/coverage.dat"
        self.golden_filename = re.sub(r'\.py$', '.out', self.py_filename)
        self.main_filename = self.obj_dir + "/" + self.vm_prefix + "__main.cpp"
        self.run_log_filename = self.obj_dir + "/vlt_sim.log"
        self.stats = self.obj_dir + "/V" + self.name + "__stats.txt"
        self.top_filename = re.sub(r'\.py$', '', self.py_filename) + '.' + self.v_suffix
        self.pli_filename = re.sub(r'\.py$', '', self.py_filename) + '.cpp'
        self.top_shell_filename = self.obj_dir + "/" + self.vm_prefix + "__top.v"

    def _define_opt_calc(self) -> str:
        return "--define " if self.xsim else "+define+"

    def init_benchmarksim(self) -> None:
        # Simulations with benchmarksim enabled append to the same file between runs.
        # Test files must ensure a clean benchmark data file before executing tests.
        filename = self.benchmarksim_filename
        with open(filename, 'w', encoding="utf8") as fh:
            fh.write("# Verilator simulation benchmark data\n")
            fh.write("# Test name: " + self.name + "\n")
            fh.write("# Top file: " + self.top_filename + "\n")
            fh.write("evals, time[s]\n")

    def soprint(self, message: str) -> str:
        message = message.rstrip() + "\n"
        message = self.scenario + "/" + self.name + ": " + message
        return message

    def oprint(self, message: str) -> None:
        message = message.rstrip() + "\n"
        print(self.soprint(message), end="")

    def error(self, message: str) -> None:
        """Called from tests as: error("Reason message")
        Newline is optional. Only first line is passed to summaries
        Throws a VtErrorException, so rest of testing is not executed"""
        message = message.rstrip() + "\n"
        print("%Warning: " + self.scenario + "/" + self.name + ": " + message,
              file=sys.stderr,
              end="")
        if not self.errors:
            message = re.sub(r'\n.*', '\n', message)
            self.errors = message
            raise VtErrorException

    def error_keep_going(self, message: str) -> None:
        """Called from tests as: error_keep_going("Reason message")
        Newline is optional. Only first line is passed to summaries"""
        if self._quit:
            return
        message = message.rstrip() + "\n"
        print("%Warning: " + self.scenario + "/" + self.name + ": " + message,
              file=sys.stderr,
              end="")
        if not self.errors_keep_going:
            message = re.sub(r'\n.*', '\n', message)
            self.errors_keep_going = message

    def skip(self, message: str) -> None:
        """Called from tests as: skip("Reason message"[, ...])
        Newline is optional. Only first line is passed to summaries.
        Throws a VtSkipException, so rest of testing is not executed"""
        message = message.rstrip() + "\n"
        print("-Skip: " + self.scenario + "/" + self.name + ": " + message,
              file=sys.stderr,
              end="")
        if not self._skips:
            message = re.sub(r'\n.*', '\n', message)
            self._skips = message
            raise VtSkipException

    def scenarios(self, *scenario_list) -> None:
        """Called from tests as: scenarios(<list_of_scenarios>) to
        specify which scenarios this test runs under.  Where ... is
        one cases listed in  All_Scenarios.
        All scenarios must be on one line; this is parsed outside Python."""
        enabled_scenarios = {}
        for param in scenario_list:
            hit = False
            for allsc, allscs in All_Scenarios.items():
                for allscarg in allscs:
                    if param == allscarg:
                        hit = True
                        enabled_scenarios[allsc] = True
            if not hit:
                self.error("scenarios(...) has unknown scenario '" + param + "'")

        if not enabled_scenarios.get(self.scenario, None):
            self._scenario_off = True
            self.skip("scenario '" + self.scenario + "' not enabled for test")
            # self._exit() implied by skip's exception

    @staticmethod
    def _prefilter_scenario(py_filename: str, scenario: str) -> bool:
        """Read a python file to see if scenarios require it to be run.
        Much faster than parsing the file for a runtime check."""
        (py_filename, _) = Runner._py_filename_adjust(py_filename, ".")
        with open(py_filename, 'r', encoding="utf-8") as fh:
            for line in fh:
                m = re.search(r'^\s*test.scenarios\((.*?)\)', line)
                if m:
                    for param in re.findall(r"""["']([^,]*)["']""", m.group(1)):
                        for allscarg in All_Scenarios[scenario]:
                            if param == allscarg:
                                return True
        return False

    def _prep(self) -> None:
        VtOs.mkdir_ok(self.obj_dir)  # Ok if already exists

    def _read(self) -> None:
        if not os.path.exists(self.py_filename):
            self.error("Can't open " + self.py_filename)
            return
        global test
        test = self
        sys.path.append(self.t_dir)  # To find vltest_bootstrap.py
        # print("_read/exec py_filename=" + self.py_filename)
        # print("_read/exec dir=", ' '.join(dir()))
        # print("_read/exec vars=", ' '.join(vars().keys()))
        # print("_read/exec globals=", ' '.join(globals().keys()))
        # print("_read/exec locals=", ' '.join(locals().keys()))
        try:
            runpy.run_path(self.py_filename, globals())
        except (VtErrorException, VtSkipException):
            pass

    def _exit(self):
        if self.ok:
            self.oprint("Self PASSED")
        elif self._skips and not self.errors:
            self.oprint("-Skip: " + self._skips)
        else:
            # If no worse errors, promote errors_keep_going to normal errors
            if not self.errors and self.errors_keep_going:
                self.errors = self.errors_keep_going
            if not self.errors:
                self.error("Missing ok")
            self.oprint("%Error: " + self.errors)
        self._write_status()
        sys.exit(0)

    def _write_status(self) -> None:
        with open(self._status_filename, "wb") as fh:
            pass_to_driver = {
                '_ok': self._ok,
                '_scenario_off': self._scenario_off,
                '_skips': self._skips,
                'errors': self.errors,
            }
            pickle.dump(pass_to_driver, fh)

    def _read_status(self) -> None:
        filename = self._status_filename
        if not os.path.isfile(filename):
            self.error_keep_going("Child test did not return status (test has Python error?): " +
                                  self.py_filename)
            return
        with open(filename, "rb") as fh:
            dic = pickle.load(fh)
            for k in dic.keys():
                # print("_read_status " + filename + ".test['" + k + "]=" + pformat(dic[k]))
                setattr(self, k, dic[k])

    #----------------------------------------------------------------------
    # Methods invoked by tests

    def clean(self) -> None:
        """Called on a rerun to cleanup files."""
        if self.clean_command:
            os.system(self.clean_command)
        # Prevents false-failures when switching compilers
        # Remove old results to force hard rebuild
        os.system('/bin/rm -rf ' + self.obj_dir + '__fail1')
        os.system('/bin/mv ' + self.obj_dir + ' ' + self.obj_dir + '__fail1')

    def clean_objs(self) -> None:
        os.system("/bin/rm -rf " + ' '.join(glob.glob(self.obj_dir + "/*")))

    def _checkflags(self, param):
        checkflags = (
            ' ' + ' '.join(param['v_flags']) +  #
            ' ' + ' '.join(param['v_flags2']) +  #
            ' ' + ' '.join(param['verilator_flags']) +  #
            ' ' + ' '.join(param['verilator_flags2']) +  #
            ' ' + ' '.join(param['verilator_flags3']) + ' ')
        return checkflags

    def compile_vlt_cmd(self, **kwargs) -> list:
        """Return default command list to run verilator"""
        param = {'stdout_filename': None}
        param.update(vars(self))
        param.update(kwargs)
        vlt_cmd = [
            "perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator",
            *self._compile_vlt_flags(**param), param['top_filename'], *param['v_other_filenames']
        ]
        if param['stdout_filename']:
            vlt_cmd += ["> " + param['stdout_filename']]
        return vlt_cmd

    def _compile_vlt_flags(self, **param) -> list:
        checkflags = self._checkflags(param)
        d_verilator_flags = ' ' + ' '.join(self.driver_verilator_flags) + ' '

        self.pins_sc_uint_bool = (  # pylint: disable=attribute-defined-outside-init
            bool(
                re.search(r'-pins-sc-uint-bool\b', checkflags)
                or re.search(r'-pins-sc-uint-bool\b', d_verilator_flags)))
        self.savable = (  # pylint: disable=attribute-defined-outside-init
            bool(re.search(r'-savable\b', checkflags)))
        self.coverage = (  # pylint: disable=attribute-defined-outside-init
            bool(re.search(r'-coverage\b', checkflags)))
        self.sanitize = param.get('sanitize', None)  # pylint: disable=attribute-defined-outside-init
        self.sc = (  # pylint: disable=attribute-defined-outside-init
            bool(re.search(r'-sc\b', checkflags)))
        self.timing = (  # pylint: disable=attribute-defined-outside-init
            bool(re.search(r'( -?-timing\b| -?-binary\b)', checkflags)))
        self.trace = (  # pylint: disable=attribute-defined-outside-init
            bool(Args.trace or re.search(r'-trace\b|-trace-fst\b', checkflags)))

        if re.search(r'-trace-fst', checkflags):
            if self.sc:
                self.trace_format = 'fst-sc'  # pylint: disable=attribute-defined-outside-init
            else:
                self.trace_format = 'fst-c'  # pylint: disable=attribute-defined-outside-init
        elif self.sc:
            self.trace_format = 'vcd-sc'  # pylint: disable=attribute-defined-outside-init
        else:
            self.trace_format = 'vcd-c'  # pylint: disable=attribute-defined-outside-init

        if param.get('benchmarksim', None):
            self.benchmarksim = True  # pylint: disable=attribute-defined-outside-init

        verilator_flags = [*param.get('verilator_flags', "")]
        if Args.gdb:
            verilator_flags += ["--gdb"]
        if Args.gdbbt:
            verilator_flags += ["--gdbbt"]
        if Args.rr:
            verilator_flags += ["--rr"]
        if Args.trace:
            verilator_flags += ["--trace"]
        if Args.gdbsim or Args.rrsim:
            verilator_flags += ["-CFLAGS -ggdb -LDFLAGS -ggdb"]
        verilator_flags += ["--x-assign unique"]  # More likely to be buggy

        if param['vltmt']:
            verilator_flags += ["--debug-partition"]
        if param['threads'] >= 0:
            verilator_flags += ["--threads", str(param['threads'])]
        if param['vltmt'] and re.search(r'-trace-fst ', checkflags):
            verilator_flags += ["--trace-threads 2"]
        if self.sanitize:
            verilator_flags += [
                "-CFLAGS -fsanitize=address,undefined -LDFLAGS -fsanitize=address,undefined"
            ]
        if param['verilator_make_cmake']:
            verilator_flags += ["--make cmake"]
        if param['verilator_make_gmake']:
            verilator_flags += ["--make gmake"]
        if param['make_main'] and param['verilator_make_gmake']:
            verilator_flags += ["--exe"]
        if param['make_main'] and param['verilator_make_gmake']:
            verilator_flags += ["../" + self.main_filename]

        cmdargs = [
            "--prefix",
            param['vm_prefix'],
            *verilator_flags,
            *param['verilator_flags2'],
            *param['verilator_flags3'],
            *param['v_flags'],
            *param['v_flags2'],
            # Flags from driver cmdline override default flags and
            # flags from the test itself
            *self.driver_verilator_flags,
        ]
        return cmdargs

    def lint(self, **kwargs) -> None:
        """Run a linter. Arguments similar to run(); default arguments are from self"""
        param = {}
        param.update(vars(self))
        param.update({  # Lint-specific default overrides
            'make_main': False,
            'make_top_shell': False,
            'verilator_flags2': ["--lint-only"],
            'verilator_make_gmake': False
        })
        param.update(kwargs)
        self.compile(**param)

    def compile(self, **kwargs) -> None:
        """Run simulation compiler.  Arguments similar to run(); default arguments are from self"""
        param = {
            'expect': None,
            'expect_filename': None,
            'fails': False,
            'make_flags': [],
            'tee': True,
            'timing_loop': False,
        }
        param.update(vars(self))
        param.update(kwargs)

        if self.verbose:
            self.oprint("Compile")

        if param['vlt'] and param['threads'] > 1:
            self.error("'threads =' argument must be <= 1 for vlt scenario")
        # Compute automatic parameter values
        checkflags = self._checkflags(param)
        if re.search(r'(^|\s)-?-threads\s', checkflags):
            self.error("Specify threads via 'threads=' argument, not as a command line option")

        if param['threads'] < 0 and param['vltmt']:
            param['threads'] = calc_threads(Vltmt_Threads)
        if not param['context_threads']:
            param['context_threads'] = param['threads'] if (param['threads'] >= 1) else 1
        if re.search(r'( -?-main\b| -?-binary\b)', checkflags):
            param['make_main'] = False
        if re.search(r'( -?-build\b| -?-binary\b)', checkflags):
            param['verilator_make_cmake'] = False
            param['verilator_make_gmake'] = False
        self.threads = param['threads']
        self.context_threads = param['context_threads']

        self.compile_vlt_cmd(**param)

        if not re.search(r'TEST_DUMPFILE', ' '.join(self.v_flags)):
            self.v_flags += [self._define_opt_calc() + "TEST_DUMPFILE=" + self.trace_filename]

        if not param['make_top_shell']:
            self.top_shell_filename = ""
        else:
            self.top_shell_filename = self.obj_dir + "/" + self.vm_prefix + "__top." + self.v_suffix
        param['top_shell_filename'] = self.top_shell_filename

        if param['atsim']:
            tool_define = param['atsim_define']
            self._make_top(param['make_top_shell'])
            self.run(logfile=self.obj_dir + "/atsim_compile.log",
                     fails=param['fails'],
                     cmd=[
                         VtOs.getenv_def('VERILATOR_ATSIM', "atsim"),
                         ' '.join(param['atsim_flags']),
                         ' '.join(param['atsim_flags2']),
                         ' '.join(param['v_flags']),
                         ' '.join(param['v_flags2']),
                         param['top_filename'],
                         param['top_shell_filename'],
                         ' '.join(param['v_other_filenames']),
                     ])
        elif param['ghdl']:
            tool_define = param['ghdl_define']
            VtOs.mkdir_ok(self.ghdl_work_dir)
            self._make_top(param['make_top_shell'])
            tool_exe = VtOs.getenv_def('VERILATOR_GHDL', "ghdl")
            self.run(
                logfile=self.obj_dir + "/ghdl_compile.log",
                fails=param['fails'],
                cmd=[
                    tool_exe,
                    # Add -c here, as having -c twice freaks it out
                    ("" if re.search(r' -c\b', tool_exe) else "-c"),
                    ' '.join(param['ghdl_flags']),
                    ' '.join(param['ghdl_flags2']),
                    #' '.join(param['v_flags']),  # Not supported
                    #' '.join(param['v_flags2']),  # Not supported
                    param['top_filename'],
                    param['top_shell_filename'],
                    ' '.join(param['v_other_filenames']),
                    "-e t",
                ])
        elif param['vcs']:
            tool_define = param['vcs_define']
            self._make_top(param['make_top_shell'])
            self.run(logfile=self.obj_dir + "/vcs_compile.log",
                     fails=param['fails'],
                     cmd=[
                         VtOs.getenv_def('VERILATOR_VCS', "vcs"),
                         ' '.join(param['vcs_flags']),
                         ' '.join(param['vcs_flags2']),
                         ("-CFLAGS -DTEST_VERBOSE=1" if Args.verbose else ""),
                         ' '.join(param['v_flags']),
                         ' '.join(param['v_flags2']),
                         param['top_filename'],
                         param['top_shell_filename'],
                         ' '.join(param['v_other_filenames']),
                     ])
        elif param['nc']:
            tool_define = param['nc_define']
            self._make_top(param['make_top_shell'])
            self.run(logfile=self.obj_dir + "/nc_compile.log",
                     fails=param['fails'],
                     cmd=[
                         VtOs.getenv_def('VERILATOR_NCVERILOG', "ncverilog"),
                         ' '.join(param['nc_flags']),
                         ' '.join(param['nc_flags2']),
                         ' '.join(param['v_flags']),
                         ' '.join(param['v_flags2']),
                         param['top_filename'],
                         param['top_shell_filename'],
                         ' '.join(param['v_other_filenames']),
                     ])
        elif param['ms']:
            tool_define = param['ms_define']
            self._make_top(param['make_top_shell'])
            self.run(logfile=self.obj_dir + "/ms_compile.log",
                     fails=param['fails'],
                     cmd=[
                         ("vlib " + self.obj_dir + "/work && "),
                         VtOs.getenv_def('VERILATOR_MODELSIM', "vlog"),
                         ' '.join(param['ms_flags']),
                         ' '.join(param['ms_flags2']),
                         ' '.join(param['v_flags']),
                         ' '.join(param['v_flags2']),
                         param['top_filename'],
                         param['top_shell_filename'],
                     ])
        elif param['iv']:
            tool_define = param['iv_define']
            self._make_top(param['make_top_shell'])
            cmd = (VtOs.getenv_def('VERILATOR_IVERILOG', "iverilog"), ' '.join(param['iv_flags']),
                   ' '.join(param['iv_flags2']), ' '.join(param['v_flags']),
                   ' '.join(param['v_flags2']), param['top_filename'], param['top_shell_filename'],
                   ' '.join(param['v_other_filenames']))
            cmd = list(map(lambda str: re.sub(r'\+define\+', '-D ', str), cmd))
            self.run(logfile=self.obj_dir + "/iv_compile.log", fails=param['fails'], cmd=cmd)
        elif param['xrun']:
            tool_define = param['xrun_define']
            self._make_top(param['make_top_shell'])
        elif param['xsim']:
            tool_define = param['xsim_define']
            self._make_top(param['make_top_shell'])
            self.run(logfile=self.obj_dir + "/xsim_compile.log",
                     fails=param['fails'],
                     cmd=[
                         VtOs.getenv_def('VERILATOR_XVLOG', "xvlog"),
                         ' '.join(param['xsim_flags']),
                         ' '.join(param['xsim_flags2']),
                         ' '.join(param['v_flags']),
                         ' '.join(param['v_flags2']),
                         param['top_filename'],
                         param['top_shell_filename'],
                     ])
        elif param['vlt_all']:
            tool_define = param['verilator_define']

            if self.sc and not self.have_sc:
                self.skip("Test requires SystemC; ignore error since not installed\n")
                return

            if self.timing and not self.have_coroutines:
                self.skip("Test requires Coroutines; ignore error since not available\n")
                return

            if param['verilator_make_cmake'] and not self.have_cmake:
                self.skip(
                    "Test requires CMake; ignore error since not available or version too old\n")
                return

            if not param['fails'] and param['make_main']:
                self._make_main(param['timing_loop'])

            if (param['verilator_make_gmake']
                    or (not param['verilator_make_gmake'] and not param['verilator_make_cmake'])):
                vlt_cmd = self.compile_vlt_cmd(**param)
                if self.verbose:
                    self.oprint("Running Verilator (gmake)")
                if Args.verilation:
                    self.run(logfile=self.obj_dir + "/vlt_compile.log",
                             fails=param['fails'],
                             tee=param['tee'],
                             expect=param['expect'],
                             expect_filename=param['expect_filename'],
                             verilator_run=True,
                             cmd=vlt_cmd)

            if param['verilator_make_cmake']:
                vlt_args = self._compile_vlt_flags(**param)
                if self.verbose:
                    self.oprint("Running cmake")
                VtOs.mkdir_ok(self.obj_dir)
                csources = []
                if param['make_main']:
                    csources.append(self.main_filename)
                self.run(
                    logfile=self.obj_dir + "/vlt_cmake.log",
                    fails=param['fails'],
                    tee=param['tee'],
                    expect=param['expect'],
                    expect_filename=param['expect_filename'],
                    verilator_run=True,
                    cmd=[
                        "cd \"" + self.obj_dir + "\" && cmake",
                        "\"" + self.t_dir + "/..\"",
                        "-DTEST_VERILATOR_ROOT=" + os.environ['VERILATOR_ROOT'],
                        "-DTEST_NAME=" + self.name,
                        "-DTEST_CSOURCES=\"" + ' '.join(csources) + "\"",
                        "-DTEST_VERILATOR_ARGS=\"" + ' '.join(vlt_args) + "\"",
                        "-DTEST_VERILATOR_SOURCES=\"" + param['top_filename'] + ' ' +
                        ' '.join(param['v_other_filenames']) + "\"",
                        "-DTEST_VERBOSE=\"" + ("1" if self.verbose else "0") + "\"",
                        "-DTEST_SYSTEMC=\"" + ("1" if self.sc else "0") + "\"",
                        "-DCMAKE_PREFIX_PATH=\"" +
                        (VtOs.getenv_def('SYSTEMC_INCLUDE', VtOs.getenv_def('SYSTEMC', '')) +
                         "/..\""),
                        "-DTEST_OPT_FAST=\"" + ("-Os" if param['benchmark'] else "-O0") + "\"",
                        "-DTEST_OPT_GLOBAL=\"" + ("-Os" if param['benchmark'] else "-O0") + "\"",
                        "-DTEST_VERILATION=\"" + ("1" if Args.verilation else "0") + "\"",
                    ])

            if not param['fails'] and param['verilator_make_gmake']:
                if self.verbose:
                    self.oprint("Running make (gmake)")
                self.run(
                    logfile=self.obj_dir + "/vlt_gcc.log",
                    entering=self.obj_dir,
                    cmd=[
                        os.environ['MAKE'],
                        "-C " + self.obj_dir,
                        "-f " + os.path.abspath(os.path.dirname(__file__)) + "/Makefile_obj",
                        ("" if self.verbose else "--no-print-directory"),
                        "VM_PREFIX=" + self.vm_prefix,
                        "TEST_OBJ_DIR=" + self.obj_dir,
                        "CPPFLAGS_DRIVER=-D" + self.name.upper(),
                        ("CPPFLAGS_DRIVER2=-DTEST_VERBOSE=1" if self.verbose else ""),
                        ("" if param['benchmark'] else "OPT_FAST=-O0"),
                        ("" if param['benchmark'] else "OPT_GLOBAL=-O0"),
                        self.vm_prefix,  # bypass default rule, as we don't need archive
                        *param['make_flags'],
                    ])

            if not param['fails'] and param['verilator_make_cmake']:
                if self.verbose:
                    self.oprint("Running cmake --build")
                self.run(logfile=self.obj_dir + "/vlt_cmake_build.log",
                         cmd=[
                             "cmake",
                             "--build",
                             self.obj_dir,
                             ("--verbose" if self.verbose else ""),
                         ])
        else:
            self.error("No compile step defined for '%s' scenario" % self.scenario())

        if param['make_pli']:
            if self.verbose:
                self.oprint("Compile vpi")
            cmd = [
                os.environ['CXX'], *param['pli_flags'], "-D" + tool_define, "-DIS_VPI",
                VtOs.getenv_def('CFLAGS', ''), self.pli_filename
            ]
            self.run(logfile=self.obj_dir + "/pli_compile.log", fails=param['fails'], cmd=cmd)

    def execute(self, **kwargs) -> None:
        """Run simulation executable.
        Arguments similar to run(); default arguments are from self"""
        # Default arguments are from self
        # params may be expect or {tool}_expect
        param = {
            'aslr_off': False,
            'entering': False,
            'check_finished': False,
            'executable': None,
            'expect': None,
            'expect_filename': None,
            'fails': False,
            'run_env': '',
            'tee': False,
        }
        param.update(vars(self))
        param.update(kwargs)

        if self.verbose:
            self.oprint("Run")

        if not self.verbose:
            os.environ['SYSTEMC_DISABLE_COPYRIGHT_MESSAGE'] = 'DISABLE'
        else:
            VtOs.delenv('SYSTEMC_DISABLE_COPYRIGHT_MESSAGE')

        if not self._have_solver_called:
            os.environ['VERILATOR_SOLVER'] = "test.py-file-needs-have_solver()-call"

        if param['check_finished'] is None and not param['fails']:
            param['check_finished'] = 1

        run_env = param['run_env']
        if run_env:
            run_env = run_env + ' '

        if param['atsim']:
            self.run(
                logfile=self.obj_dir + "/atsim_sim.log",
                fails=param['fails'],
                cmd=[
                    "echo q | " + run_env + self.obj_dir + "/athdl_sv",
                    ' '.join(param['atsim_run_flags']),
                    ' '.join(param['all_run_flags']),
                ],
                *param,
                expect=param['atsim_run_expect'],  # non-verilator expect isn't the same
                expect_filename=param['atsim_run_expect_filename'],
            )
        elif param['ghdl']:
            self.run(
                logfile=self.obj_dir + "/ghdl_sim.log",
                fails=param['fails'],
                cmd=[
                    run_env + self.obj_dir + "/simghdl",
                    ' '.join(param['ghdl_run_flags']),
                    ' '.join(param['all_run_flags']),
                ],
                *param,
                expect=param['ghdl_run_expect'],  # non-verilator expect isn't the same
                expect_filename=param['ghdl_run_expect_filename'],
            )
        elif param['iv']:
            cmd = [
                run_env + self.obj_dir + "/simiv",
                ' '.join(param['iv_run_flags']),
                ' '.join(param['all_run_flags']),
            ]
            if param['use_libvpi']:
                # Don't enter command line on $stop, include vpi
                cmd += ["vvp -n -m " + self.obj_dir + "/libvpi.so"]
            self.run(
                logfile=self.obj_dir + "/iv_sim.log",
                fails=param['fails'],
                cmd=cmd,
                *param,
                expect=param['iv_run_expect'],  # non-verilator expect isn't the same
                expect_filename=param['iv_run_expect_filename'],
            )
        elif param['ms']:
            pli_opt = ""
            if param['use_libvpi']:
                pli_opt = "-pli " + self.obj_dir + "/libvpi.so"
            self.run(
                logfile=self.obj_dir + "/ms_sim.log",
                fails=param['fails'],
                cmd=[
                    "echo q | " + run_env + VtOs.getenv_def('VERILATOR_MODELSIM', "vsim"),
                    ' '.join(param['ms_run_flags']), ' '.join(param['all_run_flags']), pli_opt,
                    (" top")
                ],
                *param,
                expect=param['ms_run_expect'],  # non-verilator expect isn't the same
                expect_filename=param['ms_expect_filename'],
            )
        elif param['nc']:
            self.run(
                logfile=self.obj_dir + "/nc_sim.log",
                fails=param['fails'],
                cmd=[
                    "echo q | " + run_env + VtOs.getenv_def('VERILATOR_NCVERILOG', "ncverilog"),
                    ' '.join(param['nc_run_flags']),
                    ' '.join(param['all_run_flags']),
                ],
                *param,
                expect=param['nc_run_expect'],  # non-verilator expect isn't the same
                expect_filename=param['nc_run_expect_filename'],
            )
        elif param['vcs']:
            # my $fh = IO::File->new(">simv.key") or die "%Error: $! simv.key,"
            # fh.print("quit\n"); fh.close()
            self.run(
                logfile=self.obj_dir + "/vcs_sim.log",
                cmd=[
                    "echo q | " + run_env + "./simv",
                    ' '.join(param['vcs_run_flags']),
                    ' '.join(param['all_run_flags']),
                ],
                *param,
                expect=param['vcs_run_expect'],  # non-verilator expect isn't the same
                expect_filename=param['vcs_run_expect_filename'],
            )
        elif param['xrun']:
            pli_opt = ""
            if param['use_libvpi']:
                pli_opt = "-loadvpi " + self.obj_dir + "/libvpi.so:vpi_compat_bootstrap"
            self.run(
                logfile=self.obj_dir + "/xrun_sim.log",
                fails=param['fails'],
                cmd=[
                    "echo q | " + run_env + VtOs.getenv_def('VERILATOR_XRUN', "xrun"),
                    ' '.join(param['xrun_run_flags']),
                    ' '.join(param['xrun_flags2']),
                    ' '.join(param['all_run_flags']),
                    pli_opt,
                    param['top_filename'],
                ],
                *param,
                expect=param['xrun_run_expect'],  # non-verilator expect isn't the same
                expect_filename=param['xrun_run_expect_filename'],
            )
        elif param['xsim']:
            self.run(
                logfile=self.obj_dir + "/xsim_sim.log",
                fails=param['fails'],
                cmd=[
                    run_env + VtOs.getenv_def('VERILATOR_XELAB', "xelab"),
                    ' '.join(param['xsim_run_flags']), ' '.join(param['xsim_run_flags2']),
                    ' '.join(param['all_run_flags']), (" " + self.name + ".top")
                ],
                *param,
                expect=param['xsim_run_expect'],  # non-verilator expect isn't the same
                expect_filename=param['xsim_expect_filename'],
            )
        elif param['vlt_all']:
            if not param['executable']:
                param['executable'] = self.obj_dir + "/" + param['vm_prefix']
            debugger = ""
            if Args.gdbsim:
                debugger = VtOs.getenv_def('VERILATOR_GDB', "gdb") + " "
            elif Args.rrsim:
                debugger = "rr record "
            self.run(
                cmd=[
                    (run_env + debugger + param['executable'] +
                     (" -ex 'run " if Args.gdbsim else "")),
                    *param['all_run_flags'],
                    ("'" if Args.gdbsim else ""),
                ],
                aslr_off=param['aslr_off'],  # Disable address space layour randomization
                check_finished=param['check_finished'],  # Check for All Finished
                entering=param['entering'],  # Print entering directory information
                expect=param['expect'],
                expect_filename=param['expect_filename'],
                fails=param['fails'],
                logfile=param.get('logfile', self.obj_dir + "/vlt_sim.log"),
                tee=param['tee'],
                verilator_run=True,
            )
        else:
            self.error("No execute step for this simulator")

    #---------------------------------------------------------------
    # Accessors

    @property
    def aslr_off(self) -> str:
        if VlTest._cached_aslr_off is None:
            out = VtOs.run_capture('setarch --addr-no-randomize echo OK 2>/dev/null`', check=False)
            if re.search(r'OK', out):
                VlTest._cached_aslr_off = "setarch --addr-no-randomize "
            else:
                VlTest._cached_aslr_off = ""
        return VlTest._cached_aslr_off

    @property
    def benchmarksim_filename(self) -> str:
        return self.obj_dir + "/" + self.name + "_benchmarksim.csv"

    @property
    def driver_verilator_flags(self) -> list:
        return Arg_Driver_Verilator_Flags

    @property
    def get_default_vltmt_threads(self) -> int:
        return Vltmt_Threads

    @property
    def ok(self) -> bool:
        if self.errors or self.errors_keep_going or self._skips:
            self._ok = False
        return self._ok

    def passes(self, is_ok=True):
        if not self.errors:
            self._ok = is_ok

    @property
    def too_few_cores(self) -> bool:
        return calc_threads(Vltmt_Threads) < Vltmt_Threads

    @property
    def trace_filename(self) -> str:
        if re.match(r'^fst', self.trace_format):
            return self.obj_dir + "/simx.fst"
        return self.obj_dir + "/simx.vcd"

    def skip_if_too_few_cores(self) -> None:
        if self.too_few_cores:
            self.skip("Skipping due to too few cores")

    @property
    def v_suffix(self) -> str:
        return "v"

    @property
    def wno_unopthreads_for_few_cores(self) -> str:
        if self.too_few_cores:
            print("Too few cores, using -Wno-UNOPTTHREADS")
            return "-Wno-UNOPTTHREADS"
        return ""

    #---------------------------------------------------------------
    # Capabilities

    @property
    def cmake_version(self) -> str:
        return Capabilities.cmake_version

    @property
    def cxx_version(self) -> str:
        return Capabilities.cxx_version

    @property
    def have_cmake(self) -> bool:
        ver = Capabilities.cmake_version
        return ver and version.parse(ver) >= version.parse("3.8")

    @property
    def have_coroutines(self) -> bool:
        return Capabilities.have_coroutines

    @property
    def have_gdb(self) -> bool:
        return Capabilities.have_gdb

    @property
    def have_sc(self) -> bool:
        return Capabilities.have_sc

    @property
    def have_solver(self) -> bool:
        self._have_solver_called = True
        return Capabilities.have_solver

    @property
    def make_version(self) -> str:
        return Capabilities.make_version

    #---------------------------------------------------------------
    # OS functions

    def getenv_def(self, var: str, default=None) -> str:
        """Return environment variable, returning default if does not exist"""
        return VtOs.getenv_def(var, default)

    def mkdir_ok(self, filename) -> None:
        """Make directory, no error if exists"""
        if test.verbose:
            print("\tmkdir " + filename)
        VtOs.mkdir_ok(filename)

    def run_capture(self, cmd: str, check=True) -> str:
        """Run a command and return results"""
        if test.verbose:
            print("\t" + cmd)
        return VtOs.run_capture(cmd, check=check)

    def setenv(self, var: str, val: str) -> None:
        """Set enviornment variable"""
        print("\texport %s='%s'" % (var, val))
        os.environ[var] = val

    def unlink_ok(self, filename) -> None:
        """Unlink a file, no error if fails"""
        if test.verbose:
            print("\trm " + filename)
        VtOs.unlink_ok(filename)

    #----------------------------------------------------------------------

    def run(
            self,  #
            cmd: list,
            aslr_off=False,  # Disable address space layour randomization
            check_finished=False,  # Check for All Finished
            entering=None,  # Print entering directory information
            expect=None,  # Regexp to expect in output
            expect_filename=None,  # Filename that should match logfile
            fails=False,  # Command should fail
            logfile=None,  # Filename to write putput to
            tee=True,
            verilator_run=False) -> str:  # Move gcov data to parallel area

        try:
            command = ' '.join(cmd)
        except TypeError:
            print('run(cmd=' + pformat(cmd))
        command = ' '.join(cmd)

        if aslr_off and aslr_off != "":
            prefix = self.aslr_off
            if prefix:
                command = prefix + " " + command

        if Args.benchmark and re.match(r'^cd ', command):
            command = "time " + command

        if verilator_run:
            # Gcov fails when parallel jobs write same data file,
            # so we make sure .gcda output dir is unique across all running jobs.
            # We can't just put each one in an unique obj_dir as it uses too much disk.
            # Must use absolute path as some execute()s have different PWD
            self.setenv('GCOV_PREFIX_STRIP', '99')
            self.setenv('GCOV_PREFIX',
                        os.path.abspath(__file__ + "/../obj_dist/gcov_" + str(self.running_id)))
            os.makedirs(os.environ['GCOV_PREFIX'], exist_ok=True)
        else:
            VtOs.delenv('GCOV_PREFIX_STRIP')
            VtOs.delenv('GCOV_PREFIX')

        print("\t" + command + (("   > " + logfile) if logfile else ""))

        if entering:
            print("driver: Entering directory '" + os.path.abspath(entering) + "'")

        # Execute command redirecting output, keeping order between stderr and stdout.
        # Must do low-level IO so GCC interaction works (can't be line-based)
        status = None
        if True:  # process_caller_block  # pylint: disable=using-constant-test

            logfh = None
            if logfile:
                logfh = open(logfile, 'wb')  # pylint: disable=consider-using-with

            with subprocess.Popen(command,
                                  shell=True,
                                  bufsize=0,
                                  stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT) as proc:

                rawbuf = bytearray(2048)

                while proc.poll() is None:
                    got = proc.stdout.readinto(rawbuf)
                    if got:
                        data = rawbuf[0:got]
                        if tee:
                            sys.stdout.write(data.decode())
                            if interactive_debugger:
                                sys.stdout.flush()
                        if logfh:
                            logfh.write(data)

                if logfh:
                    logfh.close()

                rc = proc.returncode  # Negative if killed by signal
                if (rc in (
                        -4,  # SIGILL
                        -8,  # SIGFPA
                        -11)):  # SIGSEGV
                    self.error("Exec failed with core dump")
                    status = 10
                elif rc:
                    status = 10
                else:
                    status = 0

        sys.stdout.flush()
        sys.stderr.flush()

        if entering:
            print("driver: Leaving directory '" + os.path.abspath(entering) + "'")

        if not fails and status:
            firstline = ""
            if logfile:
                with open(logfile, 'r', encoding="utf8") as fh:
                    firstline = fh.read()
                firstline = firstline.strip()
                firstline = re.sub(r'(^|\n)- [^\n]+', '\1', firstline)  # Debug message
            self.error("Exec of " + cmd[0] + " failed: " + firstline)
        if fails and status:
            print("(Exec expected to fail, and did.)")
        if fails and not status:
            self.error("Exec of " + cmd[0] + " ok, but expected to fail")
        if self.errors or self._skips:
            return False

        # Read the log file a couple of times to allow for NFS delays
        if check_finished or expect:
            for tryn in range(self.tries() - 1, -1, -1):
                if tryn != self.tries() - 1:
                    time.sleep(1)
                moretry = tryn != 0
                if self._run_log_try(cmd, logfile, check_finished, moretry, expect):
                    break
        if expect_filename:
            self.files_identical(logfile, expect_filename, is_logfile=True)
            return False

        return True

    def _run_log_try(self, cmd: str, logfile: str, check_finished: bool, moretry: bool,
                     expect) -> None:
        with open(logfile, 'r', encoding='latin-1', newline='\n') as fh:
            if not fh and moretry:
                return True
            wholefile = str(fh.read())

        # Finished?
        if check_finished and not re.search(r'\*\-\* All Finished \*\-\*', wholefile):
            if moretry:
                return True
            self.error("Missing '*-* All Finished *-*'")
        if expect:
            # Strip debugging comments
            # See also files_identical
            wholefile = re.sub(r'^- [^\n]+\n', '', wholefile)
            wholefile = re.sub(r'^- [a-z.0-9]+:\d+:[^\n]+\n', '', wholefile)
            wholefile = re.sub(r'^dot [^\n]+\n', '', wholefile)
            wholefile = re.sub(r'^==[0-9]+== [^\n]+\n', '', wholefile)  # Valgrind
            # Compare
            quoted = (re.escape(expect) or self._try_regex(wholefile, expect) == 1
                      or re.search(expect, wholefile))
            ok = (wholefile == expect or self._try_regex(wholefile, expect) == 1
                  or re.search(quoted, wholefile))
            if not ok:
                #print("**BAD  " + self.name + " " + logfile + " MT " + moretry + "  " + try)
                if moretry:
                    return True
                self.error("Miscompares in output from " + cmd[0])
                if ok < 1:
                    self.error("Might be error in regexp format")
                print("GOT:")
                print(wholefile)
                print("ENDGOT")
                print("EXPECT:")
                print(expect)
                print("ENDEXPECT")

        return False

    #######################################################################
    # Little utilities

    @staticmethod
    def _try_regex(text: str, regex) -> None:
        # Try to eval a regexp
        # Returns:
        #  1 if $text ~= /$regex/ms
        #  0 if no match
        # -1 if $regex is invalid, doesn't compile
        try:
            m = re.search(regex, text)
            return 1 if m else 0
        except re.error:
            return -1

    def _make_main(self, timing_loop: bool) -> None:
        if timing_loop and self.sc:
            self.error("Cannot use timing loop and SystemC together!")

        self._read_inputs_v()

        filename = self.main_filename
        with open(filename, "w", encoding="utf8") as fh:

            fh.write("// Test defines\n")
            fh.write("#define MAIN_TIME_MULTIPLIER " +
                     str(int(round(self.main_time_multiplier, 0))) + "\n")

            fh.write("#include <memory>\n")
            if self.benchmarksim:
                fh.write("#include <fstream>\n")
                fh.write("#include <chrono>\n")
                fh.write("#include <iomanip>\n")

            fh.write("// OS header\n")
            fh.write('#include "verilatedos.h"' + "\n")

            fh.write("// Generated header\n")
            fh.write('#include "' + self.vm_prefix + '.h"' + "\n")

            fh.write("// General headers\n")
            fh.write('#include "verilated.h"' + "\n")
            if self.sc:
                fh.write('#include "systemc.h"' + "\n")
            if self.trace and self.trace_format == 'fst-c':
                fh.write("#include \"verilated_fst_c.h\"\n")
            if self.trace and self.trace_format == 'fst-sc':
                fh.write("#include \"verilated_fst_sc.h\"\n")
            if self.trace and self.trace_format == 'vcd-c':
                fh.write("#include \"verilated_vcd_c.h\"\n")
            if self.trace and self.trace_format == 'vcd-sc':
                fh.write("#include \"verilated_vcd_sc.h\"\n")
            if self.savable:
                fh.write("#include \"verilated_save.h\"\n")

            fh.write("std::unique_ptr<" + self.vm_prefix + "> topp;\n")

            if self.savable:
                fh.write("\n")
                fh.write("void save_model(const char* filenamep) {\n")
                fh.write("    VL_PRINTF(\"Saving model to '%s'\\n\", filenamep);\n")
                fh.write("    VerilatedSave os;\n")
                fh.write("    os.open(filenamep);\n")
                fh.write("    os << *topp;\n")
                fh.write("    os.close();\n")
                fh.write("}\n")
                fh.write("\n")
                fh.write("void restore_model(const char* filenamep) {\n")
                fh.write("    VL_PRINTF(\"Restoring model from '%s'\\n\", filenamep);\n")
                fh.write("    VerilatedRestore os;\n")
                fh.write("    os.open(filenamep);\n")
                fh.write("    os >> *topp;\n")
                fh.write("    os.close();\n")
                fh.write("}\n")

            #### Main
            if self.sc:
                fh.write("extern int sc_main(int argc, char** argv);\n")
                fh.write("int sc_main(int argc, char** argv) {\n")
                if 'fastclk' in self._inputs:
                    if self.pins_sc_uint_bool:
                        fh.write("    sc_signal<sc_dt::sc_uint<1>> fastclk;\n")
                    else:
                        fh.write("    sc_signal<bool> fastclk;\n")
                if 'clk' in self._inputs:
                    if self.pins_sc_uint_bool:
                        fh.write("    sc_signal<sc_dt::sc_uint<1>> clk;\n")
                    else:
                        fh.write("    sc_signal<bool> clk;\n")
                fh.write("    sc_set_time_resolution(1, " + self.sc_time_resolution + ");\n")
                fh.write("    sc_time sim_time(" + str(self.sim_time) + ", " +
                         self.sc_time_resolution + ");\n")
            else:
                fh.write("int main(int argc, char** argv) {\n")
                fh.write("    uint64_t sim_time = " + str(self.sim_time) + ";\n")

            fh.write(
                "    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};\n")
            fh.write("    contextp->threads(" + str(self.context_threads) + ");\n")
            fh.write("    contextp->commandArgs(argc, argv);\n")
            fh.write("    contextp->debug(" + ('1' if self.verilated_debug else '0') + ");\n")
            fh.write("    srand48(5);\n")  # Ensure determinism
            if self.verilated_randReset is not None and self.verilated_randReset != "":
                fh.write("    contextp->randReset(" + str(self.verilated_randReset) + ");\n")
            fh.write("    topp.reset(new " + self.vm_prefix + "{\"top\"});\n")
            if self.verilated_debug:
                fh.write("    contextp->internalsDump()\n;")

            if self.sc:
                if 'fastclk' in self._inputs:
                    fh.write("    topp->fastclk(fastclk);\n")
                if 'clk' in self._inputs:
                    fh.write("    topp->clk(clk);\n")
                setp = ""
            else:
                fh.write("    topp->eval();\n")
                setp = "topp->"

            if self.benchmarksim:
                fh.write("    std::chrono::time_point<std::chrono::steady_clock> starttime;\n")
                fh.write("    bool warm = false;\n")
                fh.write("    uint64_t n_evals = 0;\n")

            if self.trace:
                fh.write("\n")
                fh.write("#if VM_TRACE\n")
                fh.write("    contextp->traceEverOn(true);\n")
                if self.trace_format == 'fst-c':
                    fh.write("    std::unique_ptr<VerilatedFstC> tfp{new VerilatedFstC};\n")
                if self.trace_format == 'fst-sc':
                    fh.write("    std::unique_ptr<VerilatedFstSc> tfp{new VerilatedFstSc};\n")
                if self.trace_format == 'vcd-c':
                    fh.write("    std::unique_ptr<VerilatedVcdC> tfp{new VerilatedVcdC};\n")
                if self.trace_format == 'vcd-sc':
                    fh.write("    std::unique_ptr<VerilatedVcdSc> tfp{new VerilatedVcdSc};\n")
                if self.sc:
                    fh.write("    sc_core::sc_start(sc_core::SC_ZERO_TIME);" +
                             "  // Finish elaboration before trace and open\n")
                fh.write("    topp->trace(tfp.get(), 99);\n")
                fh.write("    tfp->open(\"" + self.trace_filename + "\");\n")

                if self.trace and not self.sc:
                    fh.write("    if (tfp) tfp->dump(contextp->time());\n")
                fh.write("#endif\n")

            if self.savable:
                fh.write("    const char* save_time_strp"
                         " = contextp->commandArgsPlusMatch(\"save_time=\");\n")
                fh.write("    unsigned int save_time = !save_time_strp[0]"
                         " ? 0 : std::atoi(save_time_strp + std::strlen(\"+save_time=\"));\n")
                fh.write("    const char* save_restore_strp"
                         " = contextp->commandArgsPlusMatch(\"save_restore=\");\n")
                fh.write("    unsigned int save_restore = !save_restore_strp[0] ? 0 : 1;\n")

            if self.savable:
                fh.write("    if (save_restore) {\n")
                fh.write("        restore_model(\"" + self.obj_dir + "/saved.vltsv\");\n")
                fh.write("    } else {\n")
            else:
                fh.write("    {\n")

            if 'fastclk' in self._inputs:
                fh.write("        " + setp + "fastclk = false;\n")
            if 'clk' in self._inputs:
                fh.write("        " + setp + "clk = false;\n")
            if not timing_loop:
                self._print_advance_time(fh, 10, None)
            fh.write("    }\n")

            timestamp = "sc_time_stamp()" if self.sc else "contextp->time()"

            fh.write("    while (")
            if not timing_loop or 'clk' in self._inputs:
                fh.write("(" + timestamp + " < sim_time * MAIN_TIME_MULTIPLIER) && ")
            fh.write("!contextp->gotFinish()) {\n")

            if timing_loop:
                fh.write("        topp->eval();\n")
                if self.trace:
                    fh.write("#if VM_TRACE\n")
                    fh.write("        if (tfp) tfp->dump(contextp->time());\n")
                    fh.write("#endif  // VM_TRACE\n")
                if 'clk' in self._inputs:
                    fh.write("        const uint64_t cycles"
                             " = contextp->time() / MAIN_TIME_MULTIPLIER;\n")
                    fh.write("        uint64_t new_time = (cycles + 1) * MAIN_TIME_MULTIPLIER;\n")
                    fh.write("        if (topp->eventsPending() &&\n")
                    fh.write("            topp->nextTimeSlot()"
                             " / MAIN_TIME_MULTIPLIER <= cycles) {\n")
                    fh.write("            new_time = topp->nextTimeSlot();\n")
                    fh.write("        } else {\n")
                    if self.pins_sc_uint_bool:
                        fh.write("            " + setp + "clk.write(!" + setp + "clk.read());\n")
                    else:
                        fh.write("            " + setp + "clk = !" + setp + "clk;\n")
                    fh.write("        }\n")
                    fh.write("        contextp->time(new_time);\n")
                else:
                    fh.write("        if (!topp->eventsPending()) break;\n")
                    fh.write("        contextp->time(topp->nextTimeSlot());\n")
            else:
                for i in range(5):
                    action = False
                    if 'fastclk' in self._inputs:
                        if self.pins_sc_uint_bool:
                            fh.write("        " + setp + "fastclk.write(!" + setp +
                                     "fastclk.read());\n")
                        else:
                            fh.write("        " + setp + "fastclk = !" + setp + "fastclk;\n")
                        action = True
                    if i == 0 and 'clk' in self._inputs:
                        if self.pins_sc_uint_bool:
                            fh.write("        " + setp + "clk.write(!" + setp + "clk.read());\n")
                        else:
                            fh.write("        " + setp + "clk = !" + setp + "clk;\n")
                        action = True
                    if self.savable:
                        fh.write("        if (save_time && " + timestamp + " == save_time) {\n")
                        fh.write("            save_model(\"" + self.obj_dir + "/saved.vltsv\");\n")
                        fh.write("            printf(\"Exiting after save_model\\n\");\n")
                        fh.write("            topp.reset(nullptr);\n")
                        fh.write("            return 0;\n")
                        fh.write("        }\n")
                    self._print_advance_time(fh, 1, action)
            if self.benchmarksim:
                fh.write("        if (VL_UNLIKELY(!warm)) {\n")
                fh.write("            starttime = std::chrono::steady_clock::now();\n")
                fh.write("            warm = true;\n")
                fh.write("        } else {\n")
                fh.write("            ++n_evals;\n")
                fh.write("        }\n")

            fh.write("    }\n")

            if self.benchmarksim:
                fh.write("    {\n")
                fh.write("        const std::chrono::duration<double> exec_s"
                         " = std::chrono::steady_clock::now() - starttime;\n")
                fh.write("        std::ofstream benchfile(\"" + self.benchmarksim_filename +
                         "\", std::ofstream::out | std::ofstream::app);\n")
                fh.write("        benchfile << std::fixed << std::setprecision(9)"
                         " << n_evals << \",\" << exec_s.count() << std::endl;\n")
                fh.write("        benchfile.close();\n")
                fh.write("    }\n")

            fh.write("    if (!contextp->gotFinish()) {\n")
            fh.write('        vl_fatal(__FILE__, __LINE__, "main",' +
                     ' "%Error: Timeout; never got a $finish");' + "\n")
            fh.write("    }\n")
            fh.write("    topp->final();\n")
            fh.write("\n")

            if self.coverage:
                fh.write("#if VM_COVERAGE\n")
                fh.write("    contextp->coveragep()->write(\"" + self.coverage_filename + "\");\n")
                fh.write("#endif  // VM_COVERAGE\n")

            if self.trace:
                fh.write("#if VM_TRACE\n")
                fh.write("    if (tfp) tfp->close();\n")
                fh.write("    tfp.reset();\n")
                fh.write("#endif  // VM_TRACE\n")

            fh.write("    topp.reset();\n")
            fh.write("    return 0;\n")
            fh.write("}\n")

    def _print_advance_time(self, fh, timeinc: str, action: bool) -> None:
        setp = "" if self.sc else "topp->"
        if self.sc:
            fh.write("        sc_start(" + str(timeinc) + " * MAIN_TIME_MULTIPLIER, " +
                     self.sc_time_resolution + ");\n")
        else:
            if action:
                fh.write("        " + setp + "eval();\n")
                if self.trace and not self.sc:
                    fh.write("#if VM_TRACE\n")
                    fh.write("        if (tfp) tfp->dump(contextp->time());\n")
                    fh.write("#endif  // VM_TRACE\n")
            fh.write("        contextp->timeInc(" + str(timeinc) + " * MAIN_TIME_MULTIPLIER);\n")

    #######################################################################

    def _make_top(self, needed=True) -> None:
        if not needed:
            return
        self._make_top_v()

    def _make_top_v(self) -> None:
        self._read_inputs_v()

        with open(self.top_shell_filename(), 'w', encoding="utf8") as fh:
            fh.write("module top;\n")
            for inp in sorted(self._inputs.keys()):
                fh.write("    reg " + inp + ";\n")
            # Inst
            fh.write("    t t (\n")
            comma = ""
            for inp in sorted(self._inputs.keys()):
                fh.write("      " + comma + "." + inp + " (" + inp + ")\n")
                comma = ","
            fh.write("    );\n")

            # Waves
            fh.write("\n")
            fh.write("`ifdef WAVES\n")
            fh.write("   initial begin\n")
            fh.write("      $display(\"-Tracing Waves to Dumpfile: " + self.trace_filename +
                     "\");\n")
            fh.write("      $dumpfile(\"" + self.trace_filename + "\");\n")
            fh.write("      $dumpvars(0, top);\n")
            fh.write("   end\n")
            fh.write("`endif\n")

            # Test
            fh.write("\n")
            fh.write("    initial begin\n")
            if 'fastclk' in self._inputs:
                fh.write("        fastclk = 0;\n")
            if 'clk' in self._inputs:
                fh.write("        clk = 0;\n")
            fh.write("        #10;\n")
            if 'fastclk' in self._inputs:
                fh.write("        fastclk = 1;\n")
            if 'clk' in self._inputs:
                fh.write("        clk = 1;\n")
            fh.write("        while (" + time + " < " + self.sim_time + ") begin\n")
            for i in range(6):
                fh.write("          #1;\n")
                if 'fastclk' in self._inputs:
                    fh.write("          fastclk = !fastclk;\n")
                if i == 4 and 'clk' in self._inputs:
                    fh.write("          clk = !clk;\n")
            fh.write("        end\n")
            fh.write("    end\n")

            fh.write("endmodule\n")

    #######################################################################

    def _read_inputs_v(self) -> None:
        filename = self.top_filename
        if not os.path.exists(filename):
            filename = self.t_dir + '/' + filename
        with open(filename, 'r', encoding="utf8") as fh:
            get_sigs = True
            inputs = {}
            for line in fh:
                if get_sigs:
                    m = re.match(r'^\s*input\s*(\S+)\s*(\/[^\/]+\/|)\s*;', line)
                    if m:
                        inputs[m.group(1)] = m.group(1)
                    if re.match(r'^\s*(function|task|endmodule)', line):
                        get_sigs = False
                # Ignore any earlier inputs; Module 't' has precedence
                if re.match(r'^\s*module\s+t\b', line):
                    inputs = {}
                    get_sigs = True
            for sig, val in inputs.items():
                self._inputs[sig] = val

    #######################################################################
    # File utilities

    def files_identical(self, fn1: str, fn2: str, is_logfile=False) -> None:
        """Test if two files have identical contents"""
        for tryn in range(self.tries() - 1, -1, -1):
            if tryn != self.tries() - 1:
                time.sleep(1)
            moretry = tryn != 0
            if not self._files_identical_try(
                    fn1=fn1, fn2=fn2, is_logfile=is_logfile, moretry=moretry):
                break

    def _files_identical_try(self, fn1: str, fn2: str, is_logfile: bool, moretry: bool) -> bool:
        try:
            f1 = open(  # pylint: disable=consider-using-with
                fn1, 'r', encoding='latin-1', newline='\n')
        except FileNotFoundError:
            f1 = None
            if not moretry:
                self.error("Files_identical file does not exist: " + fn1)
            return True
        try:
            f2 = open(  # pylint: disable=consider-using-with
                fn2, 'r', encoding='latin-1', newline='\n')
        except FileNotFoundError:
            f2 = None
            if not moretry:
                self.copy_if_golden(fn1, fn2)
                self.error("Files_identical file does not exist: " + fn2)
            return True
        ok = self._files_identical_reader(f1,
                                          f2,
                                          fn1=fn1,
                                          fn2=fn2,
                                          is_logfile=is_logfile,
                                          moretry=moretry)
        if f1:
            f1.close()
        if f2:
            f2.close()
        return ok

    def _files_identical_reader(self, f1, f2, fn1: str, fn2: str, is_logfile: bool,
                                moretry: bool) -> None:
        l1s = f1.readlines()
        l2s = f2.readlines() if f2 else []
        # print(" rawGOT="+pformat(l1s)+"\n rawEXP="+pformat(l2s))
        if is_logfile:
            l1o = []
            for line in l1s:
                if (re.match(r'^- [^\n]+\n', line)  #
                        or re.match(r'^- [a-z.0-9]+:\d+:[^\n]+\n', line)
                        or re.match(r'^-node:', line)  #
                        or re.match(r'^dot [^\n]+\n', line)  #
                        or re.match(r'^Aborted', line)  #
                        or re.match(r'^In file: .*\/sc_.*:\d+', line)  #
                        or re.match(r'^libgcov.*', line)  #
                        or re.match(r'--- \/tmp\/', line)  # t_difftree.py
                        or re.match(r'\+\+\+ \/tmp\/', line)  # t_difftree.py
                        or re.match(r'^==[0-9]+== ?[^\n]*\n', line)):  # valgrind
                    continue
                # Don't put control chars or unstable lines into source repository
                while True:
                    (line, didn) = re.subn(r'(Internal Error: [^\n]+?\.(cpp|h)):[0-9]+', r'\1:#',
                                           line)
                    if not didn:
                        break
                # --vlt vs --vltmt run differences
                line = re.sub(r'^-V\{t[0-9]+,[0-9]+\}', '-V{t#,#}', line)
                line = re.sub(r'\r', '<#013>', line)
                line = re.sub(r'Command Failed[^\n]+', 'Command Failed', line)
                line = re.sub(r'Version: Verilator[^\n]+', 'Version: Verilator ###', line)
                line = re.sub(r'CPU Time: +[0-9.]+ seconds[^\n]+', 'CPU Time: ###', line)
                line = re.sub(r'\?v=[0-9.]+', '?v=latest', line)  # warning URL
                line = re.sub(r'_h[0-9a-f]{8}_', '_h########_', line)
                line = re.sub(r'%Error: /[^: ]+/([^/:])', r'%Error: .../\1',
                              line)  # Avoid absolute paths
                line = re.sub(r' \/[^ ]+\/verilated_std.sv', ' verilated_std.sv', line)
                #
                (line, n) = re.subn(r'Exiting due to.*', r"Exiting due to", line)
                if n:
                    l1o.append(line)
                    break  # Trunc rest
                l1o.append(line)
            #
            l1s = l1o

        for lineno_m1 in range(0, max(len(l1s), len(l2s))):
            l1 = l1s[lineno_m1] if lineno_m1 < len(l1s) else "*EOF*\n"
            l2 = l2s[lineno_m1] if lineno_m1 < len(l2s) else "*EOF*\n"
            if l1 != l2:
                # print(" clnGOT="+pformat(l1s)+"\n clnEXP="+pformat(l2s))
                if moretry:
                    return True
                self.error_keep_going("Line " + str(lineno_m1) + " miscompares; " + fn1 + " != " +
                                      fn2)
                for c in range(min(len(l1), len(l2))):
                    if ord(l1[c]) != ord(l2[c]):
                        print("Miscompare starts at column " + str(c) +
                              (" w/ F1(got)=0x%02x F2(exp)=0x%02x" % (ord(l1[c]), ord(l2[c]))),
                              file=sys.stderr)
                        break
                print("F1(got): " + l1 + "F2(exp): " + l2, file=sys.stderr)
                if 'HARNESS_UPDATE_GOLDEN' in os.environ:  # Update golden files with current
                    print("%Warning: HARNESS_UPDATE_GOLDEN set: cp " + fn1 + " " + fn2,
                          file=sys.stderr)
                    with open(fn2, 'w', encoding="utf8") as fhw:
                        fhw.write(''.join(l1s))
                else:
                    print("To update reference: HARNESS_UPDATE_GOLDEN=1 {command} or --golden",
                          file=sys.stderr)
                return False

        return True

    def files_identical_sorted(self, fn1: str, fn2: str, is_logfile=False) -> None:
        """Test if two files, after sorting both, have identical contents"""
        # Set LC_ALL as suggested in the sort manpage to avoid sort order
        # changes from the locale.
        os.environ['LC_ALL'] = 'C'
        fn1sort = fn1 + '.sort'
        self.run(cmd=['sort', fn1, "> " + fn1sort])
        self.files_identical(fn1sort, fn2, is_logfile)

    def copy_if_golden(self, fn1: str, fn2: str) -> None:
        """Copy a file if updating golden .out files"""
        if 'HARNESS_UPDATE_GOLDEN' in os.environ:  # Update golden files with current
            print("%Warning: HARNESS_UPDATE_GOLDEN set: cp " + fn1 + " " + fn2, file=sys.stderr)
            shutil.copy(fn1, fn2)

    def vcd_identical(self, fn1: str, fn2: str) -> None:
        """Test if two VCD files have logically-identical contents"""
        # vcddiff to check transitions, if installed
        cmd = "vcddiff --help"
        out = test.run_capture(cmd, check=True)
        cmd = 'vcddiff ' + fn1 + ' ' + fn2
        out = test.run_capture(cmd, check=True)
        if out != "":
            cmd = 'vcddiff ' + fn2 + " " + fn1  # Reversed arguments
            out = VtOs.run_capture(cmd, check=False)
            if out != "":
                print(out)
                self.copy_if_golden(fn1, fn2)
                self.error("VCD miscompares " + fn2 + " " + fn1)

        # vcddiff doesn't check module and variable scope, so check that
        # Also provides backup if vcddiff not installed
        h1 = self._vcd_read(fn1)
        h2 = self._vcd_read(fn2)
        a = json.dumps(h1, sort_keys=True, indent=1)
        b = json.dumps(h2, sort_keys=True, indent=1)
        if a != b:
            self.copy_if_golden(fn1, fn2)
            self.error("VCD hier miscompares " + fn1 + " " + fn2 + "\nGOT=" + a + "\nEXP=" + b +
                       "\n")

    def fst2vcd(self, fn1: str, fn2: str) -> None:
        cmd = "fst2vcd -h"
        out = VtOs.run_capture(cmd, check=False)
        if out == "" or not re.search(r'Usage:', out):
            self.skip("No fst2vcd installed")
            return

        cmd = 'fst2vcd -e -f "' + fn1 + '" -o "' + fn2 + '"'
        print("\t " + cmd + "\n")  # Always print to help debug race cases
        out = VtOs.run_capture(cmd, check=False)
        print(out)

    def fst_identical(self, fn1: str, fn2: str) -> None:
        """Test if two FST files have logically-identical contents"""
        tmp = fn1 + ".vcd"
        self.fst2vcd(fn1, tmp)
        self.vcd_identical(tmp, fn2)

    def _vcd_read(self, filename: str) -> str:
        data = {}
        with open(filename, 'r', encoding='latin-1') as fh:
            hier_stack = ["TOP"]
            var = []
            for line in fh:
                match1 = re.search(r'\$scope (module|struct|interface)\s+(\S+)', line)
                match2 = re.search(r'(\$var (\S+)\s+\d+\s+)\S+\s+(\S+)', line)
                match3 = re.search(r'(\$attrbegin .* \$end)', line)
                line = line.rstrip()
                # print("VR"+ ' '*len(hier_stack) +" L " + line)
                if match1:  # $scope
                    name = match1.group(2)
                    # print("VR"+ ' '*len(hier_stack) +" scope " + line)
                    hier_stack += [name]
                    scope = '.'.join(hier_stack)
                    data[scope] = match1.group(1) + " " + name
                elif match2:  # $var
                    # print("VR"+ ' '*len(hier_stack) +" var " + line)
                    scope = '.'.join(hier_stack)
                    var = match2.group(2)
                    data[scope + "." + var] = match2.group(1) + match2.group(3)
                elif match3:  # $attrbegin
                    # print("VR"+ ' '*len(hier_stack) +" attr " + line)
                    if var:
                        scope = '.'.join(hier_stack)
                        data[scope + "." + var + "#"] = match3.group(1)
                elif re.search(r'\$enddefinitions', line):
                    break
                n = len(re.findall(r'\$upscope', line))
                if n:
                    for i in range(0, n):  # pylint: disable=unused-variable
                        # print("VR"+ ' '*len(hier_stack) +" upscope " + line)
                        hier_stack.pop()
        return data

    def inline_checks(self) -> None:
        covfn = self.coverage_filename
        contents = self.file_contents(covfn)

        if self.verbose:
            self.oprint("Extract checks")
        with open(self.top_filename, 'r', encoding="utf8") as fh:
            flineno = 0
            for line in fh:
                flineno += 1
                if re.search(r'CHECK', line):
                    match1 = re.search(
                        r'CHECK_COVER *\( *((-|[0-9])+) *,'
                        r'*"([^"]+)" *, *("([^"]+)" *,|) *(\d+) *\)', line)
                    match2 = re.search(r'CHECK_COVER_MISSING *\( *((-|[0-9])+) *\)', line)
                    if match1:
                        lineno = flineno + int(match1.group(1))
                        hier = match1.group(3)
                        comment = match1.group(5)
                        count = match1.group(6)
                        regexp = "\001l\002" + str(lineno)
                        if comment:
                            regexp += ".*\001o\002" + re.escape(comment)
                        if hier:
                            regexp += ".*\001h\002" + re.escape(hier)
                        regexp += ".*' " + str(count)
                        if not re.search(regexp, contents):
                            self.error("CHECK_COVER: " + covfn + ":" + str(flineno) +
                                       ": Regexp not found: " + regexp + "\n" + "From " +
                                       self.top_filename + ": " + line)
                    elif match2:
                        lineno = flineno + int(match2.group(1))
                        regexp = "\001l\002" + str(lineno)
                        if re.search(regexp, contents):
                            self.error("CHECK_COVER_MISSING: " + covfn + ":" + str(flineno) +
                                       ": Regexp found: " + regexp + "\n" + "From " +
                                       self.top_filename + ": " + line)
                    else:
                        self.error(self.top_filename + ":" + str(flineno) +
                                   ": Unknown CHECK request: " + line)

    @staticmethod
    def cfg_with_ccache() -> bool:
        if VlTest._cached_cfg_with_ccache is None:
            mkf = VlTest._file_contents_static(os.environ['VERILATOR_ROOT'] +
                                               "/include/verilated.mk")
            VlTest._cached_cfg_with_ccache = bool(re.match(r'OBJCACHE \?= ccache', mkf))
        return VlTest._cached_cfg_with_ccache

    @staticmethod
    def tries() -> int:
        # Number of retries when reading logfiles, generally only need many
        # retries when system is busy running a lot of tests
        if not forker.running:
            return 2
        if len(Arg_Tests) > 3:
            return 7
        return 2

    def glob_some(self, pattern: str) -> list:
        """Return list of filenames matching a glob, with at least one match required."""
        files = glob.glob(pattern)
        # print("glob_some('" + pattern + "') files =\n  " + pformat(files))
        if not files:
            self.error("glob_one: pattern '" + pattern + "' does not match any files")
            return ['No_file_found']
        return sorted(files)

    def glob_one(self, pattern: str) -> str:
        """Return a filename matching a glob, with exactly one match required."""
        files = self.glob_some(pattern)
        if files and len(files) > 1:
            msg = "glob_one: pattern '" + pattern + "' matches multiple files:\n"
            for file in files:
                msg += file + "\n"
            self.error(msg)
            return 'Multiple_files_found'
        return files[0]

    def file_grep_not(self, filename: str, regexp) -> None:
        contents = self.file_contents(filename)
        if contents == "_Already_Errored_":
            return
        if re.search(regexp, contents, re.MULTILINE):
            self.error("File_grep_not: " + filename + ": Regexp found: '" + regexp + "'")

    def file_grep(self, filename: str, regexp, expvalue=None) -> list:
        contents = self.file_contents(filename)
        if contents == "_Already_Errored_":
            return None
        match = re.search(regexp, contents, re.MULTILINE)
        if not match:
            self.error("File_grep: " + filename + ": Regexp not found: " + regexp)
            return None
        if expvalue and str(expvalue) != match.group(1):
            self.error("File_grep: " + filename + ": Got='" + match.group(1) + "' Expected='" +
                       str(expvalue) + "' in regexp: '" + regexp + "'")
            return None
        return [match.groups()]

    def file_grep_count(self, filename: str, regexp, expcount: int) -> None:
        contents = self.file_contents(filename)
        if contents == "_Already_Errored_":
            return
        count = len(re.findall(regexp, contents))
        if expcount != count:
            self.error("File_grep_count: " + filename + ": Got='" + count + "' Expected='" +
                       expcount + "' in regexp: '" + regexp + "'")

    def file_grep_any(self, filenames: list, regexp, expvalue=None) -> None:
        for filename in filenames:
            contents = self.file_contents(filename)
            if contents == "_Already_Errored_":
                return
            match = re.search(regexp, contents)
            if match:
                if expvalue and str(expvalue) != match.group(1):
                    self.error("file_grep: " + filename + ": Got='" + match.group(1) +
                               "' Expected='" + str(expvalue) + "' in regexp: " + regexp)
                return
        msg = "file_grep_any: Regexp '" + regexp + "' not found in any of the following files:\n"
        for filename in filenames:
            msg += filename + "\n"
        self.error(msg)

    def file_contents(self, filename: str) -> str:
        if filename not in self._file_contents_cache:
            if not os.path.exists(filename):
                self._file_contents_cache[filename] = "_Already_Errored_"
                self.error("File_contents file not found: " + filename)
            else:
                with open(filename, 'r', encoding='latin-1') as fh:
                    self._file_contents_cache[filename] = str(fh.read())
        return self._file_contents_cache[filename]

    @staticmethod
    def _file_contents_static(filename: str) -> str:
        if filename not in VlTest._file_contents_cache:
            if not os.path.exists(filename):
                VlTest._file_contents_cache[filename] = "_Already_Errored_"
                sys.exit("_file_contents_static file not found: " + filename)
            else:
                with open(filename, 'r', encoding='latin-1') as fh:
                    VlTest._file_contents_cache[filename] = str(fh.read())
        return VlTest._file_contents_cache[filename]

    def write_wholefile(self, filename: str, contents: str) -> None:
        with open(filename, 'wb') as fh:
            fh.write(contents.encode('latin-1'))
        if filename in self._file_contents_cache:
            del self._file_contents_cache[filename]

    def file_sed(self, in_filename: str, out_filename, edit_lambda) -> None:
        contents = self.file_contents(in_filename)
        contents = edit_lambda(contents)
        self.write_wholefile(out_filename, contents)

    def extract(
            self,
            in_filename: str,
            out_filename: str,
            regexp=r'.*',
            lineno_adjust=-9999,  #
            lines=None) -> None:  #'#, #-#'
        temp_fn = out_filename
        temp_fn = re.sub(r'.*/', '', temp_fn)
        temp_fn = self.obj_dir + "/" + temp_fn

        out = []
        emph = ""
        lineno = 0
        lineno_out = 0
        with open(in_filename, 'r', encoding="latin-1") as fh:
            for line in fh:
                lineno += 1
                if re.search(regexp, line) and self._lineno_match(lineno, lines):
                    match = re.search(r't/[A-Za-z0-9_]+.v:(\d+):(\d+):', line)
                    if match:
                        mlineno = int(match.group(1)) + lineno_adjust
                        col = int(match.group(2))
                        mlineno = max(1, mlineno)
                        line = re.sub(r't/[A-Za-z0-9_]+.v:(\d+):(\d+):',
                                      'example.v:' + str(mlineno) + ':' + str(col), line)
                    out.append("   " + line)
                    lineno_out += 1
                    if '<--' in line:
                        if emph:
                            emph += ","
                        emph += str(lineno_out)

        with open(temp_fn, 'w', encoding="latin-1") as fhw:
            lang = " sv" if re.search(r'\.s?vh?$', in_filename) else ""
            fhw.write(".. comment: generated by " + self.name + "\n")
            fhw.write(".. code-block::" + lang + "\n")
            if lang != "" and len(out) > 1:
                fhw.write("   :linenos:\n")
            if emph:
                fhw.write("   :emphasize-lines: " + emph + "\n")
            fhw.write("\n")
            for line in out:
                fhw.write(line)

        self.files_identical(temp_fn, out_filename)

    @staticmethod
    def _lineno_match(lineno: int, lines: str) -> bool:
        if not lines:
            return True
        for lc in lines.split(','):
            match1 = re.match(r'^(\d+)$', lc)
            match2 = re.match(r'^(\d+)-(\d+)$', lc)
            if match1 and int(match1.group(1)) == lineno:
                return True
            if match2 and int(match2.group(1)) <= lineno <= int(match2.group(2)):
                return True
        return False


######################################################################
######################################################################
# Global Functions


def calc_jobs() -> int:
    ok_threads = max_procs()
    print("driver.py: Found %d cores, using -j %d" % (ok_threads, ok_threads))
    return ok_threads


def calc_threads(default_threads) -> int:
    ok_threads = max_procs()
    return ok_threads if (ok_threads < default_threads) else default_threads


def _calc_hashset() -> list:
    match = re.match(r'^(\d+)/(\d+)$', Args.hashset)
    if not match:
        sys.exit("%Error: Need number/number format for --hashset: " + Args.hashset)
    setn = int(match.group(1))
    nsets = int(match.group(2))
    new = []
    global Arg_Tests
    for t in Arg_Tests:
        checksum = int(hashlib.sha256(t.encode("utf-8")).hexdigest()[0:4], 16)
        if (setn % nsets) == (checksum % nsets):
            new.append(t)
    Arg_Tests = new


#######################################################################
#######################################################################
# Verilator utilities


@lru_cache(maxsize=1)
def max_procs() -> int:
    procs = multiprocessing.cpu_count()
    if procs < 2:
        print("driver.py: Python didn't find at least two CPUs")
    return procs


def _parameter(param: str) -> None:
    global _Parameter_Next_Level
    if _Parameter_Next_Level:
        if not re.match(r'^(\d+)$', _Parameter_Next_Level):
            sys.exit("%Error: Expected number following " + _Parameter_Next_Level + ": " + param)
        Arg_Driver_Verilator_Flags.append(param)
        _Parameter_Next_Level = None
    elif re.search(r'\.py', param):
        Arg_Tests.append(param)
    elif re.match(r'^-?(-debugi|-dumpi)', param):
        Arg_Driver_Verilator_Flags.append(param)
        _Parameter_Next_Level = param
    elif re.match(r'^-?(-W||-debug-check)', param):
        Arg_Driver_Verilator_Flags.append(param)
    else:
        sys.exit("%Error: Unknown parameter: " + param)


def run_them() -> None:
    VtOs.mkdir_ok("obj_dist")
    timestart = time.strftime("%Y%m%d_%H%M%S")

    runner = Runner(driver_log_filename="obj_dist/driver_" + timestart + ".log", quiet=Args.quiet)
    for test_py in Arg_Tests:
        for scenario in sorted(set(Args.scenarios)):
            if VlTest._prefilter_scenario(test_py, scenario):
                runner.one_test(py_filename=test_py, scenario=scenario)
    runner.wait_and_report()

    if Args.rerun and runner.fail_cnt and not Quitting:
        print('=' * 70)
        print('=' * 70)
        print("RERUN  ==\n")

        # Avoid parallel run to ensure that isn't causing problems
        # If > 10 failures something more wrong and get results quickly
        if runner.fail_cnt < 10:
            forker.max_proc(1)

        orig_runner = runner
        runner = Runner(driver_log_filename="obj_dist/driver_" + timestart + "_rerun.log",
                        quiet=False,
                        fail1_cnt=orig_runner.fail_cnt,
                        ok_cnt=orig_runner.ok_cnt,
                        skip_cnt=orig_runner.skip_cnt)
        for ftest in orig_runner.fail_tests:
            # Reschedule test
            if ftest.rerunnable:
                ftest.clean()
            runner.one_test(py_filename=ftest.py_filename,
                            scenario=ftest.scenario,
                            rerun_skipping=not ftest.rerunnable)

        runner.wait_and_report()

    if runner.fail_cnt:
        sys.exit(10)


######################################################################
######################################################################
# Globals

os.environ['PYTHONUNBUFFERED'] = "1"

if ('VERILATOR_ROOT' not in os.environ) and os.path.isfile('../bin/verilator'):
    os.environ['VERILATOR_ROOT'] = os.getcwd() + "/.."
if 'MAKE' not in os.environ:
    os.environ['MAKE'] = "make"
if 'CXX' not in os.environ:
    os.environ['CXX'] = "c++"
if 'TEST_REGRESS' in os.environ:
    sys.exit("%Error: TEST_REGRESS environment variable is already set")
os.environ['TEST_REGRESS'] = os.getcwd()

forker = None
Start = time.time()
Vltmt_Threads = 3
_Parameter_Next_Level = None
Quitting = False


def sig_int(signum, env) -> None:  # pylint: disable=unused-argument
    global Quitting
    if Quitting:
        sys.exit("\nQuitting (immediately)...")
    print("\nQuitting... (send another interrupt signal for immediate quit)")
    Quitting = True
    if forker:
        forker.kill_tree_all()


signal.signal(signal.SIGINT, sig_int)

Orig_ARGV_Sw = []
for arg in sys.argv:
    if re.match(r'^-', arg) and not re.match(r'^-j', arg):
        Orig_ARGV_Sw.append(arg)

#---------------------------------------------------------------------

parser = argparse.ArgumentParser(
    allow_abbrev=False,
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""Run Verilator regression tests""",
    epilog="""driver.py invokes Verilator or another simulator on each test file.
See docs/internals.rst in the distribution for more information.

Copyright 2024-2024 by Wilson Snyder. This program is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License
Version 2.0.

SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0""")

parser.add_argument('--benchmark', action='store', help='enable benchmarking')
parser.add_argument('--debug', action='store_const', const=9, help='enable debug')
# --debugi: see _parameter()
parser.add_argument('--fail-max',
                    action='store',
                    default=None,
                    help='run Verilator executable with gdb')
parser.add_argument('--gdb', action='store_true', help='run Verilator executable with gdb')
parser.add_argument('--gdbbt',
                    action='store_true',
                    help='run Verilated executable with gdb and backtrace')
parser.add_argument('--gdbsim', action='store_true', help='run Verilated executable with gdb')
parser.add_argument('--golden', '--gold', action='store_true', help='update golden .out files')
parser.add_argument('--hashset', action='store', help='split tests based on <set>/<numsets>')
parser.add_argument('--jobs',
                    '-j',
                    action='store',
                    default=0,
                    type=int,
                    help='parallel job count (0=cpu count)')
parser.add_argument('--quiet',
                    action='store_true',
                    help='suppress output except failures and progress')
parser.add_argument('--rerun', action='store_true', help='rerun all tests that fail')
parser.add_argument('--rr', action='store_true', help='run Verilator executable with rr')
parser.add_argument('--rrsim', action='store_true', help='run Verilated executable with rr')
parser.add_argument('--sanitize', action='store_true', help='run address sanitizer')
parser.add_argument('--site', action='store_true', help='include VERILATOR_TEST_SITE test list')
parser.add_argument('--stop', action='store_true', help='stop on the first error')
parser.add_argument('--trace', action='store_true', help='enable simulator waveform tracing')
parser.add_argument('--verbose', action='store_true', help='compile and run test in verbose mode')
parser.add_argument(
    '--verilation',  # -no-verilation undocumented debugging
    action='store_true',
    default=True,
    help="don't run verilator compile() phase")
parser.add_argument('--verilated-debug',
                    action='store_true',
                    help='enable Verilated executable debug')
## Scenarios
for scen, v in All_Scenarios.items():
    parser.add_argument('--' + scen,
                        dest='scenarios',
                        action='append_const',
                        const=scen,
                        help='scenario-enable ' + scen)

(Args, rest) = parser.parse_known_intermixed_args()

for arg in rest:
    _parameter(arg)

if Args.debug:
    Arg_Driver_Verilator_Flags.append("--debug --no-skip-identical")
    logging.basicConfig(level=logging.DEBUG)
    logging.info("In driver.py, ARGV=" + pformat(sys.argv))

if Args.golden:
    os.environ['HARNESS_UPDATE_GOLDEN'] = '1'
if Args.jobs == 0:
    Args.jobs = calc_jobs()
if not Args.scenarios:
    Args.scenarios = []
    Args.scenarios.append('dist')
    Args.scenarios.append('vlt')

interactive_debugger = Args.gdb or Args.gdbsim or Args.rr or Args.rrsim
if Args.jobs > 1 and interactive_debugger:
    sys.exit("%Error: Unable to use -j > 1 with --gdb* and --rr* options")

forker = Forker(Args.jobs)

Test_Dirs = ["t"]
if 'VERILATOR_TESTS_SITE' in os.environ:
    if Args.site or len(Arg_Tests) >= 1:
        for tdir in os.environ['VERILATOR_TESTS_SITE'].split(':'):
            Test_Dirs.append(tdir)

if not Arg_Tests:  # Run everything
    uniq = {}
    for tdir in Test_Dirs:
        # Uniquify by inode, so different paths to same place get combined
        stats = os.stat(tdir)
        if stats.st_ino not in uniq:
            uniq[stats.st_ino] = 1
            Arg_Tests += sorted(glob.glob(tdir + "/t_*.py"))
if Args.hashset:
    _calc_hashset()

if len(Arg_Tests) >= 2 and Args.jobs >= 2:
    # Read supported into master process, so don't call every subprocess
    Capabilities.warmup_cache()
    # Without this tests such as t_debug_sigsegv_bt_bad.py will occasionally
    # block on input and cause a SIGSTOP, then a "fg" was needed to resume testing.
    print("== Many jobs; redirecting STDIN", file=sys.stderr)
    #
    sys.stdin = open("/dev/null", 'r', encoding="utf8")  # pylint: disable=consider-using-with

run_them()
