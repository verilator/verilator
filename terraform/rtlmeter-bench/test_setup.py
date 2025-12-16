#!/usr/bin/env python3
"""
Pre-flight tests to validate RTLMeter benchmark setup before running expensive tests.
Run via: pytest test_setup.py -v
"""

import subprocess
import os
import re
import pytest

BENCHMARK_DIR = "/home/ubuntu/benchmark"
BASELINE_DIR = f"{BENCHMARK_DIR}/verilator-install-baseline"
PR_DIR = f"{BENCHMARK_DIR}/verilator-install-pr"
RTLMETER_DIR = f"{BENCHMARK_DIR}/rtlmeter"
VERILATOR_SRC = f"{BENCHMARK_DIR}/verilator"


class TestDirectoryStructure:
    """Verify all required directories exist."""

    def test_benchmark_dir_exists(self):
        assert os.path.isdir(BENCHMARK_DIR), f"{BENCHMARK_DIR} does not exist"

    def test_baseline_install_exists(self):
        assert os.path.isdir(BASELINE_DIR), f"{BASELINE_DIR} does not exist"

    def test_pr_install_exists(self):
        assert os.path.isdir(PR_DIR), f"{PR_DIR} does not exist"

    def test_rtlmeter_exists(self):
        assert os.path.isdir(RTLMETER_DIR), f"{RTLMETER_DIR} does not exist"

    def test_verilator_source_exists(self):
        assert os.path.isdir(VERILATOR_SRC), f"{VERILATOR_SRC} does not exist"


class TestVerilatorBinaries:
    """Verify Verilator binaries are present and executable."""

    def test_baseline_verilator_exists(self):
        binary = f"{BASELINE_DIR}/bin/verilator"
        assert os.path.isfile(binary), f"{binary} does not exist"
        assert os.access(binary, os.X_OK), f"{binary} is not executable"

    def test_pr_verilator_exists(self):
        binary = f"{PR_DIR}/bin/verilator"
        assert os.path.isfile(binary), f"{binary} does not exist"
        assert os.access(binary, os.X_OK), f"{binary} is not executable"

    def test_baseline_verilator_runs(self):
        result = subprocess.run(
            [f"{BASELINE_DIR}/bin/verilator", "--version"],
            capture_output=True, text=True
        )
        assert result.returncode == 0, f"Baseline verilator failed: {result.stderr}"
        assert "Verilator" in result.stdout

    def test_pr_verilator_runs(self):
        result = subprocess.run(
            [f"{PR_DIR}/bin/verilator", "--version"],
            capture_output=True, text=True
        )
        assert result.returncode == 0, f"PR verilator failed: {result.stderr}"
        assert "Verilator" in result.stdout


class TestVerilatorVersions:
    """Verify Verilator versions are different (baseline vs PR)."""

    def get_version(self, verilator_path):
        result = subprocess.run(
            [verilator_path, "--version"],
            capture_output=True, text=True
        )
        return result.stdout.strip()

    def test_versions_are_different(self):
        baseline_ver = self.get_version(f"{BASELINE_DIR}/bin/verilator")
        pr_ver = self.get_version(f"{PR_DIR}/bin/verilator")
        assert baseline_ver != pr_ver, \
            f"Baseline and PR versions should differ:\n  Baseline: {baseline_ver}\n  PR: {pr_ver}"

    def test_baseline_is_upstream(self):
        """Baseline should be from upstream (no fork commits)."""
        baseline_ver = self.get_version(f"{BASELINE_DIR}/bin/verilator")
        # PR version has commits like "Add Jose Drowne to CONTRIBUTORS"
        assert "db5876f" not in baseline_ver, \
            f"Baseline appears to be PR version: {baseline_ver}"


class TestPRCodeChanges:
    """Verify PR has the V3ThreadPool optimization changes."""

    def test_pr_has_lambda_wait(self):
        """PR should use lambda form of condition_variable wait."""
        result = subprocess.run(
            ["grep", "-c", "m_completionCV.wait(m_mutex, \\[",
             f"{VERILATOR_SRC}/src/V3ThreadPool.cpp"],
            capture_output=True, text=True
        )
        # Check if the PR branch has the lambda form
        subprocess.run(
            ["git", "-C", VERILATOR_SRC, "checkout", "fork/optimize-threadpool-wait-cv"],
            capture_output=True
        )
        result = subprocess.run(
            ["grep", "m_completionCV.wait(m_mutex,",
             f"{VERILATOR_SRC}/src/V3ThreadPool.cpp"],
            capture_output=True, text=True
        )
        assert "lambda" in result.stdout or "[&]" in result.stdout or result.returncode == 0, \
            "PR should have lambda form of wait()"

    def test_pr_has_memory_order_release(self):
        """PR should use memory_order_release (not acq_rel)."""
        subprocess.run(
            ["git", "-C", VERILATOR_SRC, "checkout", "fork/optimize-threadpool-wait-cv"],
            capture_output=True
        )
        with open(f"{VERILATOR_SRC}/src/V3ThreadPool.cpp") as f:
            content = f.read()
        assert "memory_order_release" in content, \
            "PR should have memory_order_release in fetch_sub"
        # The acq_rel should NOT be present in the notification code
        assert content.count("memory_order_acq_rel") == 0 or \
               "fetch_sub(1, std::memory_order_release)" in content, \
            "PR should use memory_order_release, not acq_rel"


class TestRTLMeter:
    """Verify RTLMeter is set up correctly."""

    def test_rtlmeter_script_exists(self):
        script = f"{RTLMETER_DIR}/rtlmeter"
        assert os.path.isfile(script), f"{script} does not exist"

    def test_rtlmeter_venv_exists(self):
        venv = f"{RTLMETER_DIR}/venv"
        assert os.path.isdir(venv), f"{venv} does not exist - run 'make venv'"

    def test_rtlmeter_runs(self):
        result = subprocess.run(
            [f"{RTLMETER_DIR}/rtlmeter", "--help"],
            capture_output=True, text=True,
            cwd=RTLMETER_DIR
        )
        assert result.returncode == 0, f"RTLMeter failed: {result.stderr}"
        assert "RTLMeter" in result.stdout or "benchmark" in result.stdout.lower()

    def test_rtlmeter_can_list_cases(self):
        result = subprocess.run(
            [f"{RTLMETER_DIR}/rtlmeter", "show", "--cases"],
            capture_output=True, text=True,
            cwd=RTLMETER_DIR
        )
        assert result.returncode == 0, f"RTLMeter show --cases failed: {result.stderr}"
        assert "Caliptra" in result.stdout, "Expected Caliptra cases in RTLMeter"


class TestSystemResources:
    """Verify system has adequate resources."""

    def test_cpu_count(self):
        cpu_count = os.cpu_count()
        assert cpu_count is not None
        assert cpu_count >= 16, f"Expected at least 16 CPUs, got {cpu_count}"

    def test_memory_available(self):
        """Check at least 32GB RAM available."""
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemTotal:"):
                    # Value is in kB
                    mem_kb = int(line.split()[1])
                    mem_gb = mem_kb / (1024 * 1024)
                    assert mem_gb >= 32, f"Expected at least 32GB RAM, got {mem_gb:.1f}GB"
                    return
        pytest.fail("Could not read memory info")

    def test_disk_space(self):
        """Check at least 50GB free disk space."""
        stat = os.statvfs(BENCHMARK_DIR)
        free_gb = (stat.f_bavail * stat.f_frsize) / (1024**3)
        assert free_gb >= 50, f"Expected at least 50GB free, got {free_gb:.1f}GB"


class TestParallelCompilation:
    """Verify parallel compilation works with -j flag."""

    def test_verilator_accepts_j_flag(self):
        """Both verilators should accept -j flag."""
        for name, path in [("baseline", BASELINE_DIR), ("pr", PR_DIR)]:
            result = subprocess.run(
                [f"{path}/bin/verilator", "--help"],
                capture_output=True, text=True
            )
            assert "-j" in result.stdout or "--threads" in result.stdout, \
                f"{name} verilator should support -j flag"


class TestQuickVerilation:
    """Quick smoke test that verilation works."""

    @pytest.fixture
    def temp_dir(self, tmp_path):
        return tmp_path

    def test_baseline_can_verilate_simple(self, temp_dir):
        """Baseline can verilate a simple module."""
        # Create simple test module
        sv_file = temp_dir / "test.sv"
        sv_file.write_text("module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule")

        result = subprocess.run(
            [f"{BASELINE_DIR}/bin/verilator", "--cc", str(sv_file)],
            capture_output=True, text=True,
            cwd=temp_dir
        )
        assert result.returncode == 0, f"Baseline verilate failed: {result.stderr}"

    def test_pr_can_verilate_simple(self, temp_dir):
        """PR can verilate a simple module."""
        sv_file = temp_dir / "test.sv"
        sv_file.write_text("module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule")

        result = subprocess.run(
            [f"{PR_DIR}/bin/verilator", "--cc", str(sv_file)],
            capture_output=True, text=True,
            cwd=temp_dir
        )
        assert result.returncode == 0, f"PR verilate failed: {result.stderr}"

    def test_pr_can_verilate_with_j_flag(self, temp_dir):
        """PR can verilate with -j flag (uses thread pool)."""
        sv_file = temp_dir / "test.sv"
        sv_file.write_text("module test(input clk, output reg q); always @(posedge clk) q <= ~q; endmodule")

        result = subprocess.run(
            [f"{PR_DIR}/bin/verilator", "--cc", "-j", "4", str(sv_file)],
            capture_output=True, text=True,
            cwd=temp_dir
        )
        assert result.returncode == 0, f"PR verilate with -j failed: {result.stderr}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
