#!/usr/bin/env python3
# pylint: disable=C0103,C0114,C0116
# DESCRIPTION: Verilator: CI script to apply the grade of a pull request
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

###############################################################################
# For the 'pr-event' job of 'pr-automation.yml': label a newly opened pull
# request with the grade Claude gave it in the 'grade' job, by the rules in
# '.github/pr-grade.md', and write the part of the opening comment about it.
# The grade is only data: the labels are fixed here, the rules that the
# changed files decide set the lowest risk, and the reasons are shown as inert
# text, whatever the pull request makes Claude return.
# GitHub is reached with 'gh', which takes the token from GH_TOKEN.
###############################################################################

import argparse
import html
import json
import re
import subprocess
import textwrap

RISKS = ("low", "medium", "high")

RTLMETER_LABELS = {"perf": "pr: rtlmeter-perf", "test": "pr: rtlmeter-test", "none": None}


def gh(*command):
    return subprocess.run(["gh", *command],
                          stdout=subprocess.PIPE,
                          encoding="utf-8",
                          errors="replace",
                          check=True).stdout


def parse_grade():
    # None unless Claude returned a valid grade, so that a broken one labels nothing
    try:
        grade = json.loads(ARGS.grade)
        if (grade["risk"] in RISKS and grade["rtlmeter"] in RTLMETER_LABELS
                and isinstance(grade["reason"], str)):
            return grade
    except (KeyError, TypeError, ValueError):
        pass
    return None


def lowest_risk():
    # The rules of '.github/pr-grade.md' that the changed files decide
    pages = json.loads(
        gh("api", "--paginate", "--slurp", f"repos/{ARGS.repo}/pulls/{ARGS.pr}/files"))
    files = [f for page in pages for f in page]
    if len(files) >= 100:
        return "medium"
    for f in files:
        if f["status"] == "added" and re.fullmatch(r"(src|include)/.*\.(cpp|h)", f["filename"]):
            return "medium"
        if f["filename"] in ("bin/verilator", "bin/verilator_coverage"):
            return "medium"
    return "low"


def apply():
    grade = parse_grade()
    if grade is None:
        print("::warning::No grade from Claude")
        return

    risk = max(grade["risk"], lowest_risk(), key=RISKS.index)
    # The reasons as JSON, so that no line of them can pass for a workflow command
    print(f"Risk: {risk} (Claude: {grade['risk']})")
    print(f"RTLMeter: {grade['rtlmeter']}")
    print(f"Reason: {json.dumps(grade['reason'])}")

    labels = [f"pr-risk: {risk}"]
    # Never a test run over a perf run, or the same run again, as adding the
    # label would restart the run in progress
    rtlmeter = RTLMETER_LABELS[grade["rtlmeter"]]
    current = gh("pr", "view", ARGS.pr, "--repo", ARGS.repo, "--json", "labels", "--jq",
                 ".labels[].name").splitlines()
    if rtlmeter and RTLMETER_LABELS["perf"] not in current and rtlmeter not in current:
        labels.append(rtlmeter)
    gh("pr", "edit", ARGS.pr, "--repo", ARGS.repo, "--add-label", ",".join(labels))

    # The pull request can make Claude write anything as the reasons, so they
    # are cut short, escaped, and in '<pre>', where GitHub renders no Markdown,
    # mention or link. No blank line, which would end the HTML block.
    reason = textwrap.fill(textwrap.shorten(grade["reason"], 1000), 80)
    if risk != grade["risk"]:
        reason += f"\n(Raised from {grade['risk']} risk by the files changed.)"
    with open(ARGS.comment, "w", encoding="utf-8") as fd:
        fd.write(f"<details>\n<summary>PR appears {risk} risk.</summary>\n"
                 f"<pre>\n{html.escape(reason)}\n</pre>\n</details>\n")


######################################################################
# main

parser = argparse.ArgumentParser(allow_abbrev=False,
                                 description="Apply the grade of a pull request")
parser.add_argument("--repo", required=True, help="repository, as owner/name")
parser.add_argument("--pr", required=True, help="number of the pull request")
parser.add_argument("--grade", required=True, help="structured output of Claude")
parser.add_argument("--comment", required=True, help="file to write the comment on the grade to")
ARGS = parser.parse_args()

apply()
