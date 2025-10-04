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
  local CONTENTSS=contents.tmp
  echo > ${CONTENTSS}

  # Iterate over all unique event types that triggered the workflows
  for EVENT in $(jq -r 'map(.event) | sort | unique | .[]' completedRuns.json); do
    echo "@@@ Processing '${EVENT}' runs"

    # Emit section header if a report exists with this event type
    EMIT_SECTION_HEADER=1

    # For each worfklow run that was triggered by this event type
    for WORKFLOW_ID in $(jq ".[] | select(.event == \"${EVENT}\") |.databaseId" completedRuns.json); do
      echo "@@@ Processing run ${WORKFLOW_ID}"

      # Extract the info of this run
      jq ".[] | select(.databaseId == $WORKFLOW_ID)" completedRuns.json > workflow.json
      jq "." workflow.json

      # Create workflow artifacts directory
      local ARTIFACTS_DIR=${ARTIFACTS_ROOT}/${WORKFLOW_ID}
      mkdir -p ${ARTIFACTS_DIR}

      # Download artifacts of this run, if exists
      gh run download ${WORKFLOW_ID} --name coverage-report --dir ${ARTIFACTS_DIR} || true
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
        echo "<h4>Coverage reports for '${EVENT}' runs:</h4>" >> ${CONTENTSS}
      fi

      #Create pages subdirectory
      mv ${ARTIFACTS_DIR}/report ${COVERAGE_ROOT}/${WORKFLOW_ID}

      # Add index page content
      local WORKFLOW_CREATED=$(jq -r '.createdAt' workflow.json)
      local WOFKRLOW_NUMBER=$(jq -r '.number' workflow.json)
      cat >> ${CONTENTSS} <<CONTENTS_TEMPLATE
        Run <a href="${WORKFLOW_ID}/index.html">#${WOFKRLOW_NUMBER}</a>
        | GitHub: <a href="${REPO_URL}/actions/runs/${WORKFLOW_ID}">${WORKFLOW_ID}</a>
        | started at: ${WORKFLOW_CREATED}
        <br>
CONTENTS_TEMPLATE
    done

    # Section break
    if [[ -z $EMIT_SECTION_HEADER ]]; then
      echo "<hr>" >> ${CONTENTSS}
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
      background-color: #dddddd;
      a {
        color: #008fd7;
      }
    }
    </style>
  </head>

  <body>
  $(cat ${CONTENTSS})
  <h4>Assembled $(date --iso-8601=minutes --utc)</h1>
  <body>

  </html>
INDEX_TEMPLATE
}

# Compilie coverage reports
compile_coverage_reports;

# You can build any other content here to be put under ${PAGES_ROOT}
