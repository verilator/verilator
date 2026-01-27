#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI script for 'pages.yml', notifies PRs
#
# SPDX-FileCopyrightText: 2025 Geza Lore
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Notify PRs via comment that their coverage reports are available

# Get the current repo URL - might differ on a fork
readonly REPO_URL=$(gh repo view --json url --jq .url)

# Create artifacts root directory
ARTIFACTS_ROOT=artifacts
mkdir -p ${ARTIFACTS_ROOT}

for RUN_ID in ${COVERAGE_PR_RUN_IDS//,/ }; do
  echo "@@@ Processing run ${RUN_ID}"

  # Create workflow artifacts directory
  ARTIFACTS_DIR=${ARTIFACTS_ROOT}/${RUN_ID}
  mkdir -p ${ARTIFACTS_DIR}

  # Download artifact of this run, if exists
  gh run download ${RUN_ID} --name coverage-pr-notification --dir ${ARTIFACTS_DIR} || true
  ls -lsha ${ARTIFACTS_DIR}

  # Move on if no notification is required
  if [ ! -f ${ARTIFACTS_DIR}/pr-number.txt ]; then
    echo "No notification found"
    continue
  fi
  echo "Posting notification found"

  cat ${ARTIFACTS_DIR}/body.txt
  gh pr comment $(cat ${ARTIFACTS_DIR}/pr-number.txt) --body-file ${ARTIFACTS_DIR}/body.txt

  # Get the artifact ID
  ARTIFACT_ID=$(gh api "repos/{owner}/{repo}/actions/runs/${RUN_ID}/artifacts" --jq '.artifacts[] | select(.name == "coverage-pr-notification") | .id')

  # Delete it, so we only notify once
  gh api --method DELETE "repos/{owner}/{repo}/actions/artifacts/${ARTIFACT_ID}"
done
