#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI script for 'pages.yml', builds the GitHub Pages
#
# Copyright 2025 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# This scipt build the content of the GitHub Pages for the repository.
# Currently this only hosts code coverage reports, but it would be possible to
# add any other contents to the page in parallel here.

# Developer note: You should be able to run this script in your local checkout
# if you have GitHub CLI (command 'gh') setup, authenticated ('gh auth login'),
# and have set a default repository ('gh repo set-default').

# Create pages root directory. The contents of this directory will be deployed
# and served via GitHubPages
readonly PAGES_ROOT=pages
mkdir -p ${PAGES_ROOT}

# Get the current repo URL - might differ on a fork
readonly REPO_URL=$(gh repo view --json url --jq .url)

# Set GITHUB_OUTPUT when run locally for testing
if [[ -z "$GITHUB_OUTPUT" ]]; then
  GITHUB_OUTPUT=github-output.txt
fi

# Populates ${PAGES_ROOT}/coverage-reports
compile_coverage_reports() {
  # We will process all runs up to and including this date. This is chosen to be
  # slightly less than the artifact retention period for simplicity.
  local OLDEST=$(date --date="28 days ago" --iso-8601=date)

  # Gather all coverage workflow runs within the time window
  gh run list -w coverage.yml --limit 1000 --created ">=${OLDEST}" --json "databaseId,event,status,conclusion,createdAt,number" > recentRuns.json
  echo @@@ Recent runs:
  jq "." recentRuns.json

  # Select completd runs that were not cancelled or skipped, sort by descending run number
  jq 'sort_by(-.number) | map(select(.status == "completed" and (.conclusion == "success" or .conclusion == "failure")))' recentRuns.json > completedRuns.json
  echo @@@ Completed with success or failure:
  jq "." completedRuns.json

  # Create artifacts root directory
  local ARTIFACTS_ROOT=artifacts
  mkdir -p ${ARTIFACTS_ROOT}

  # Create coverage reports root directory
  local COVERAGE_ROOT=${PAGES_ROOT}/coverage-reports
  mkdir -p ${COVERAGE_ROOT}

  # Create index page contents fragment
  local CONTENTS=contents.tmp
  echo > ${CONTENTS}

  # Run IDs of PR jobs processed
  local PR_RUN_IDS=""

  # Iterate over all unique event types that triggered the workflows
  for EVENT in $(jq -r 'map(.event) | sort | unique | .[]' completedRuns.json); do
    echo "@@@ Processing '${EVENT}' runs"

    # Emit section header if a report exists with this event type
    EMIT_SECTION_HEADER=1

    # For each worfklow run that was triggered by this event type
    for RUN_ID in $(jq ".[] | select(.event == \"${EVENT}\") |.databaseId" completedRuns.json); do
      echo "@@@ Processing run ${RUN_ID}"

      # Extract the info of this run
      jq ".[] | select(.databaseId == $RUN_ID)" completedRuns.json > workflow.json
      jq "." workflow.json

      # Record run ID of PR job
      if [[ $EVENT == "pull_request" ]]; then
        if [[ -z "$PR_RUN_IDS" ]]; then
          PR_RUN_IDS="$RUN_ID"
        else
          PR_RUN_IDS="$PR_RUN_IDS,$RUN_ID"
        fi
      fi

      # Create workflow artifacts directory
      local ARTIFACTS_DIR=${ARTIFACTS_ROOT}/${RUN_ID}
      mkdir -p ${ARTIFACTS_DIR}

      # Download artifacts of this run, if exists
      gh run download ${RUN_ID} --name coverage-report --dir ${ARTIFACTS_DIR} || true
      ls -lsha ${ARTIFACTS_DIR}

      # Move on if no coverage report is available
      if [ ! -d ${ARTIFACTS_DIR}/report ]; then
        echo "No coverage report found"
        continue
      fi
      echo "Coverage report found"

      # Emit section header
      if [[ -n $EMIT_SECTION_HEADER ]]; then
        unset EMIT_SECTION_HEADER
        if [[ $EVENT == "pull_request" ]]; then
          echo "<h4>Patch coverage reports for '${EVENT}' runs:</h4>" >> ${CONTENTS}
        else
          echo "<h4>Code coverage reports for '${EVENT}' runs:</h4>" >> ${CONTENTS}
        fi
      fi

      # Create pages subdirectory
      mv ${ARTIFACTS_DIR}/report ${COVERAGE_ROOT}/${RUN_ID}

      # Add index page content
      local WORKFLOW_CREATED=$(jq -r '.createdAt' workflow.json)
      local WOFKRLOW_NUMBER=$(jq -r '.number' workflow.json)
      cat >> ${CONTENTS} <<CONTENTS_TEMPLATE
        Run <a href="${RUN_ID}/index.html">#${WOFKRLOW_NUMBER}</a>
        | GitHub: <a href="${REPO_URL}/actions/runs/${RUN_ID}">${RUN_ID}</a>
        | started at: ${WORKFLOW_CREATED}
CONTENTS_TEMPLATE
      if [ -e ${ARTIFACTS_DIR}/pr-number.txt ]; then
        local PRNUMBER=$(cat ${ARTIFACTS_DIR}/pr-number.txt)
        echo " | Pull request: <a href=\"${REPO_URL}/pull/${PRNUMBER}\">#${PRNUMBER}</a>" >> ${CONTENTS}
      fi
      echo "<br>" >> ${CONTENTS}
    done

    # Section break
    if [[ -z "$EMIT_SECTION_HEADER" ]]; then
      echo "<hr>" >> ${CONTENTS}
    fi
  done

  # Write coverage report index.html
  cat > ${COVERAGE_ROOT}/index.html  <<INDEX_TEMPLATE
  <html>

  <head>
    <title>Verilator CI coverage reports</title>
    <style>
    body {
      font-family: courier, serif;
      background-color: #f3f3f3;
      a {
        color: #008fd7;
      }
    }
    </style>
  </head>

  <body>
  $(cat ${CONTENTS})
  <h4>Assembled $(date --iso-8601=minutes --utc)</h1>
  <body>

  </html>
INDEX_TEMPLATE

  # Report size
  du -shc ${COVERAGE_ROOT}/*

  # Set output
  echo "coverage-pr-run-ids=${PR_RUN_IDS}" >> $GITHUB_OUTPUT
}

# Compilie coverage reports
compile_coverage_reports;

# You can build any other content here to be put under ${PAGES_ROOT}
