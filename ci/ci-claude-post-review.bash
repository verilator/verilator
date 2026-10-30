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

# Delete any pending review of Claude's left by a failed earlier attempt, as
# GitHub allows only one per user and pull request, and that would make posting
# fail
gh api --paginate "repos/${GITHUB_REPOSITORY}/pulls/${PR_NUMBER}/reviews" \
  --jq '.[] | select(.state == "PENDING" and .user.login == "claude[bot]") | .id' \
  | while read -r REVIEW_ID; do
    gh api --method DELETE \
      "repos/${GITHUB_REPOSITORY}/pulls/${PR_NUMBER}/reviews/${REVIEW_ID}" > /dev/null
  done

if [ "$(jq length "${COMMENTS_FILE}")" -eq 0 ]; then
  # Nothing to say, so post nothing and mark the pull request as passing
  gh pr edit "${PR_NUMBER}" --add-label "pr: claude-pass"
else
  # Clear any mark left by an earlier review
  gh pr edit "${PR_NUMBER}" --remove-label "pr: claude-pass"
  jq '{event: "COMMENT", comments: .}' "${COMMENTS_FILE}" \
    | gh api --method POST "repos/${GITHUB_REPOSITORY}/pulls/${PR_NUMBER}/reviews" --input -
fi

# Tell the workflow the review is done, as only Claude sees how this script ends
touch "${RUNNER_TEMP}/claude-review-done"
