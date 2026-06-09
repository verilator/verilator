#!/usr/bin/env python3
# DESCRIPTION: Verilator: RTLMeter cases to run in the rtlmeter.yml CI workflow
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

###############################################################################
# Defines the RTLMeter cases to run in CI. This is consumed by the 'start' job
# in rtlmeter.yml, which captures the printed JSON and feeds it to the run job
# matrices.
###############################################################################

import argparse
import json

# Cases to run for scheduled runs, keyyed by the 'run tag' used in rtlmeter.yml
# The associated priority is roughly the number of minutes it takes to run the
# job, the emitted job matrix will try to start longest jobs first.

# Cases to run for non-PR jobs (e.g.: nightly schedule)
# fmt: off
CASES = {
    "gcc": [
        ("BlackParrot:1x1:*",                    5),
        ("BlackParrot:2x2:*",                    14),
        ("BlackParrot:4x4:*",                    25),
        ("Caliptra:default:*",                   19),
        ("NVDLA:*",                              29),
        ("OpenPiton:1x1:*",                      4),
        ("OpenPiton:2x2:*",                      7),
        ("OpenPiton:4x4:*",                      10),
        ("OpenTitan:*",                          16),
        ("Servant:qerv:*",                       2),
        ("Servant:serv:*",                       2),
        ("VeeR-EH1:asic:*",                      4),
        ("VeeR-EH1:default:*",                   6),
        ("VeeR-EH1:hiperf:*",                    5),
        ("VeeR-EH2:asic:*",                      13),
        ("VeeR-EH2:default:*",                   6),
        ("VeeR-EH2:hiperf:*",                    12),
        ("VeeR-EL2:asic:*",                      4),
        ("VeeR-EL2:default:*",                   4),
        ("VeeR-EL2:hiperf:*",                    4),
        ("Vortex:mini:*",                        3),
        ("Vortex:sane:*",                        6),
        ("XiangShan:default-chisel3:* !*:linux", 31),
        ("XiangShan:default-chisel6:* !*:linux", 28),
        ("XiangShan:mini-chisel3:* !*:linux",    13),
        ("XiangShan:mini-chisel6:* !*:linux",    15),
        ("XuanTie-C906:*",                       5),
        ("XuanTie-C910:*",                       9),
        ("XuanTie-E902:*",                       5),
        ("XuanTie-E906:*",                       6),
    ],
    "clang": [
        ("BlackParrot:1x1:*",                    5),
        ("BlackParrot:2x2:*",                    9),
        ("BlackParrot:4x4:*",                    12),
        ("Caliptra:default:*",                   16),
        ("NVDLA:*",                              28),
        ("OpenPiton:1x1:*",                      5),
        ("OpenPiton:2x2:*",                      6),
        ("OpenPiton:4x4:*",                      8),
        ("OpenTitan:*",                          10),
        ("Servant:qerv:*",                       17),
        ("Servant:serv:*",                       15),
        ("VeeR-EH1:asic:*",                      6),
        ("VeeR-EH1:default:*",                   8),
        ("VeeR-EH1:hiperf:*",                    5),
        ("VeeR-EH2:asic:*",                      9),
        ("VeeR-EH2:default:*",                   8),
        ("VeeR-EH2:hiperf:*",                    7),
        ("VeeR-EL2:asic:*",                      4),
        ("VeeR-EL2:default:*",                   5),
        ("VeeR-EL2:hiperf:*",                    5),
        ("Vortex:mini:*",                        3),
        ("Vortex:sane:*",                        5),
        ("XiangShan:default-chisel3:* !*:linux", 21),
        ("XiangShan:default-chisel6:* !*:linux", 19),
        ("XiangShan:mini-chisel3:* !*:linux",    8),
        ("XiangShan:mini-chisel6:* !*:linux",    8),
        ("XuanTie-C906:*",                       3),
        ("XuanTie-C910:*",                       7),
        ("XuanTie-E902:*",                       7),
        ("XuanTie-E906:*",                       7),
    ],
    "gcc-hier": [
        ("BlackParrot:1x1:*",    4),
        ("BlackParrot:2x2:*",    16),
        ("BlackParrot:4x4:*",    25),
        ("NVDLA:*",              25),
        ("OpenPiton:16x16:dhry", 16),
        ("OpenPiton:1x1:*",      4),
        ("OpenPiton:2x2:*",      4),
        ("OpenPiton:4x4:*",      4),
        ("OpenPiton:8x8:*",      6),
        ("XuanTie-C910:*",       7),
    ],
}
# fmt: on

# Cases to run for PR jobs
# fmt: off
CASES_PR = {
    "gcc": [
        ("BlackParrot:1x1:*",                    5),
        ("BlackParrot:4x4:*",                    25),
        ("Caliptra:default:*",                   19),
        ("NVDLA:*",                              29),
        ("OpenPiton:1x1:*",                      4),
        ("OpenPiton:4x4:*",                      10),
        ("OpenTitan:*",                          16),
        ("Servant:qerv:*",                       2),
        ("Servant:serv:*",                       2),
        ("VeeR-EH1:asic:*",                      4),
        ("VeeR-EH1:default:*",                   6),
        ("VeeR-EH1:hiperf:*",                    5),
        ("VeeR-EH2:asic:*",                      13),
        ("VeeR-EH2:default:*",                   6),
        ("VeeR-EH2:hiperf:*",                    12),
        ("VeeR-EL2:asic:*",                      4),
        ("VeeR-EL2:default:*",                   4),
        ("VeeR-EL2:hiperf:*",                    4),
        ("Vortex:mini:*",                        3),
        ("Vortex:sane:*",                        6),
        ("XiangShan:default-chisel3:* !*:linux", 31),
        ("XiangShan:default-chisel6:* !*:linux", 28),
        ("XiangShan:mini-chisel3:* !*:linux",    13),
        ("XiangShan:mini-chisel6:* !*:linux",    15),
        ("XuanTie-C906:*",                       5),
        ("XuanTie-C910:*",                       9),
        ("XuanTie-E902:*",                       5),
        ("XuanTie-E906:*",                       6),
    ],
    "clang": [
        ("BlackParrot:1x1:*",                    5),
        ("BlackParrot:4x4:*",                    12),
        ("Caliptra:default:*",                   16),
        ("NVDLA:*",                              28),
        ("OpenPiton:1x1:*",                      5),
        ("OpenPiton:4x4:*",                      8),
        ("OpenTitan:*",                          10),
        ("Servant:qerv:*",                       17),
        ("Servant:serv:*",                       15),
        ("VeeR-EH1:asic:*",                      6),
        ("VeeR-EH1:default:*",                   8),
        ("VeeR-EH1:hiperf:*",                    5),
        ("VeeR-EH2:asic:*",                      9),
        ("VeeR-EH2:default:*",                   8),
        ("VeeR-EH2:hiperf:*",                    7),
        ("VeeR-EL2:asic:*",                      4),
        ("VeeR-EL2:default:*",                   5),
        ("VeeR-EL2:hiperf:*",                    5),
        ("Vortex:mini:*",                        3),
        ("Vortex:sane:*",                        5),
        ("XiangShan:default-chisel3:* !*:linux", 21),
        ("XiangShan:default-chisel6:* !*:linux", 19),
        ("XiangShan:mini-chisel3:* !*:linux",    8),
        ("XiangShan:mini-chisel6:* !*:linux",    8),
        ("XuanTie-C906:*",                       3),
        ("XuanTie-C910:*",                       7),
        ("XuanTie-E902:*",                       7),
        ("XuanTie-E906:*",                       7),
    ],
    "gcc-hier": [
        ("BlackParrot:1x1:*",    4),
        ("BlackParrot:4x4:*",    25),
        ("NVDLA:*",              25),
        ("OpenPiton:16x16:dhry", 16),
        ("OpenPiton:1x1:*",      4),
        ("OpenPiton:4x4:*",      4),
        ("OpenPiton:8x8:*",      6),
        ("XuanTie-C910:*",       7),
    ],
}
# fmt: on

parser = argparse.ArgumentParser(
    description="Print the RTLMeter CI cases as JSON, keyed by run tag")
parser.add_argument("--event-name",
                    required=True,
                    help="GitHub event name that triggered the workflow")
parser.add_argument(
    "--ci-testing",
    action="store_true",
    help="Print only the shortest (lowest priority) case per tag, to reduce CI testing time")
args = parser.parse_args()

# Pull requests use the reduced 'CASES_PR' set, other events (e.g.: the nightly
# schedule) use the full 'CASES' set.
is_pr = args.event_name == "pull_request"
selected = CASES_PR if is_pr else CASES

cases = {}
for tag, entries in selected.items():
    # Highest priority (longest) first
    ordered = sorted(entries, key=lambda cp: cp[1], reverse=True)
    # While tweaking the CI, keep only the shortest (lowest priority) case to minimise churn time
    if args.ci_testing:
        ordered = ordered[-1:]
    # Case filters appended to every case for this tag/event
    suffix = ""
    # Filters out the non-hierarchical case variants for the hierarchical job
    if tag == "gcc-hier":
        suffix += " !-hier"
    # Filter out hello tests on pull requests, these just add measurement noise
    if is_pr:
        suffix += " !*:hello"
    cases[tag] = [case + suffix for case, _ in ordered]
print(json.dumps(cases, separators=(",", ":")))
