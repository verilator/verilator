#!/usr/bin/env python3
"""
RTLMeter benchmark runner using AWS SSM.
Compares baseline (upstream master) vs PR changes for V3ThreadPool wait() optimization.
"""

import subprocess
import json
import time
import sys
from pathlib import Path


def run_cmd(cmd: list[str], check: bool = True) -> subprocess.CompletedProcess:
    """Run a local command and return result."""
    print(f"$ {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True)
    if check and result.returncode != 0:
        print(f"STDERR: {result.stderr}")
        raise RuntimeError(f"Command failed: {' '.join(cmd)}")
    return result


def get_instance_id() -> str:
    """Get instance ID from Terraform output."""
    result = run_cmd(["terraform", "output", "-raw", "instance_id"])
    return result.stdout.strip()


def wait_for_ssm(instance_id: str, timeout: int = 300) -> None:
    """Wait for SSM agent to be ready on the instance."""
    print(f"Waiting for SSM agent on {instance_id}...")
    start = time.time()
    while time.time() - start < timeout:
        result = run_cmd([
            "aws", "ssm", "describe-instance-information",
            "--filters", f"Key=InstanceIds,Values={instance_id}",
            "--query", "InstanceInformationList[0].PingStatus",
            "--output", "text"
        ], check=False)
        if result.stdout.strip() == "Online":
            print("SSM agent is online!")
            return
        print(".", end="", flush=True)
        time.sleep(10)
    raise TimeoutError("SSM agent did not come online in time")


def ssm_run(instance_id: str, commands: list[str], timeout: int = 3600) -> str:
    """Run commands on instance via SSM and return output."""
    # Join commands with && for sequential execution
    command_str = " && ".join(commands)

    # Send command
    result = run_cmd([
        "aws", "ssm", "send-command",
        "--instance-ids", instance_id,
        "--document-name", "AWS-RunShellScript",
        "--parameters", json.dumps({"commands": [command_str]}),
        "--timeout-seconds", str(timeout),
        "--output", "json"
    ])

    cmd_data = json.loads(result.stdout)
    command_id = cmd_data["Command"]["CommandId"]
    print(f"SSM command {command_id} sent, waiting for completion...")

    # Wait for completion
    while True:
        time.sleep(5)
        result = run_cmd([
            "aws", "ssm", "get-command-invocation",
            "--command-id", command_id,
            "--instance-id", instance_id,
            "--output", "json"
        ], check=False)

        if result.returncode != 0:
            continue

        invocation = json.loads(result.stdout)
        status = invocation["Status"]

        if status == "Success":
            print("Command completed successfully")
            return invocation.get("StandardOutputContent", "")
        elif status in ("Failed", "Cancelled", "TimedOut"):
            print(f"Command {status}")
            print(f"STDOUT: {invocation.get('StandardOutputContent', '')}")
            print(f"STDERR: {invocation.get('StandardErrorContent', '')}")
            raise RuntimeError(f"SSM command {status}")

        print(f"Status: {status}...")


def setup_instance(instance_id: str) -> None:
    """Install all dependencies on the instance."""
    print("\n=== Setting up instance ===")

    setup_commands = [
        # Update system
        "sudo apt-get update",
        "sudo DEBIAN_FRONTEND=noninteractive apt-get upgrade -y",

        # Install Verilator build dependencies
        "sudo DEBIAN_FRONTEND=noninteractive apt-get install -y "
        "git perl python3 python3-pip make autoconf g++ flex bison ccache "
        "libgoogle-perftools-dev numactl perl-doc libfl2 libfl-dev zlib1g zlib1g-dev "
        "help2man",

        # Install RTLMeter dependencies
        "pip3 install --user pyyaml tabulate scipy",

        # Create work directory
        "mkdir -p /home/ubuntu/benchmark",

        # Clone verilator
        "cd /home/ubuntu/benchmark && git clone https://github.com/verilator/verilator.git",

        # Clone RTLMeter
        "cd /home/ubuntu/benchmark && git clone https://github.com/verilator/rtlmeter.git",
    ]

    ssm_run(instance_id, setup_commands, timeout=1800)
    print("Instance setup complete!")


def build_verilator(instance_id: str, label: str, git_ref: str = "master",
                    remote: str = "origin", apply_patch: bool = False) -> None:
    """Build Verilator at specified git ref."""
    print(f"\n=== Building Verilator ({label}) ===")

    build_commands = [
        "cd /home/ubuntu/benchmark/verilator",
        f"git fetch {remote}",
        f"git checkout {git_ref}",
        "git clean -fdx",
        "autoconf",
        "./configure --prefix=/home/ubuntu/benchmark/verilator-install",
        "make -j$(nproc)",
        "make install",
    ]

    ssm_run(instance_id, build_commands, timeout=1800)
    print(f"Verilator ({label}) built successfully!")


def run_rtlmeter(instance_id: str, label: str, threads: int = 4) -> str:
    """Run RTLMeter benchmarks and return results."""
    print(f"\n=== Running RTLMeter ({label}, threads={threads}) ===")

    # Use a smaller subset of benchmarks for faster results
    # Focus on multi-threaded designs that will show the improvement
    benchmark_commands = [
        "cd /home/ubuntu/benchmark/rtlmeter",
        f"export PATH=/home/ubuntu/benchmark/verilator-install/bin:$PATH",
        f"export VERILATOR_ROOT=/home/ubuntu/benchmark/verilator-install",
        # Run a subset of benchmarks - VeeR is good for quick testing
        f"python3 rtlmeter.py --verilator-root /home/ubuntu/benchmark/verilator-install "
        f"--threads {threads} --cases VeeR-EH1:default --runs 3 "
        f"--output /home/ubuntu/benchmark/results_{label}_t{threads}.json",
        f"cat /home/ubuntu/benchmark/results_{label}_t{threads}.json",
    ]

    output = ssm_run(instance_id, benchmark_commands, timeout=3600)
    return output


def main():
    # Change to terraform directory
    tf_dir = Path(__file__).parent
    import os
    os.chdir(tf_dir)

    print("=== RTLMeter Benchmark Runner ===\n")

    # Check if instance exists
    result = run_cmd(["terraform", "output", "-raw", "instance_id"], check=False)
    if result.returncode != 0 or not result.stdout.strip():
        print("No instance found. Run 'terraform apply' first.")
        sys.exit(1)

    instance_id = result.stdout.strip()
    print(f"Using instance: {instance_id}")

    # Wait for SSM
    wait_for_ssm(instance_id)

    # Setup
    setup_instance(instance_id)

    # Build baseline (upstream master)
    build_verilator(instance_id, "baseline", git_ref="master")

    # Run baseline benchmarks
    baseline_results = run_rtlmeter(instance_id, "baseline", threads=4)
    print(f"\nBaseline results:\n{baseline_results}")

    # Add our fork as remote and build with PR changes
    add_remote_commands = [
        "cd /home/ubuntu/benchmark/verilator",
        "git remote add fork https://github.com/10U-Labs-LLC/verilator.git || true",
        "git fetch fork optimize-threadpool-wait-cv",
    ]
    ssm_run(instance_id, add_remote_commands)

    build_verilator(instance_id, "pr", git_ref="fork/optimize-threadpool-wait-cv")

    # Run PR benchmarks
    pr_results = run_rtlmeter(instance_id, "pr", threads=4)
    print(f"\nPR results:\n{pr_results}")

    print("\n=== Benchmark Complete ===")
    print("Run 'terraform destroy' to clean up the instance.")


if __name__ == "__main__":
    main()
