#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI script for Claude to post its 'claude-review.yml' review
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Claude runs this script to post its review of the pull request the workflow
# was started on, as a single pull request review, so that it sends one
# notification. This is the only command Claude may run that writes to GitHub,
# so the pull request and the COMMENT verdict are fixed here, whatever the pull
# request under review makes Claude ask for.

set -eo pipefail

# Input: the review comments written by Claude, the only file it may write, as a
# JSON array of the 'comments' objects of
# https://docs.github.com/en/rest/pulls/reviews#create-a-review-for-a-pull-request
# They are not passed on the command line, as Claude Code does not allow
# commands containing JSON.
COMMENTS_FILE="${RUNNER_TEMP}/claude-review.json"

PR_NUMBER=$(jq -r .issue.number "${GITHUB_EVENT_PATH}")

jq '{event: "COMMENT", comments: .}
    + if . == [] then {body: "No issues found."} else {} end' "${COMMENTS_FILE}" \
  | gh api --method POST "repos/${GITHUB_REPOSITORY}/pulls/${PR_NUMBER}/reviews" --input -
