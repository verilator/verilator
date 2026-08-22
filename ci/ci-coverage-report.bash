#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI script for 'coverage.yml' results
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# This script combines the code coverage data gathered by the test jobs into
# the HTML report published on GitHub Pages, and for a pull request, builds the
# content of the response comment posted on it.

# Developer note: You should be able to run this script in your local checkout
# if you have GitHub CLI (command 'gh') setup, authenticated ('gh auth login'),
# and have set a default repository ('gh repo set-default').

set -eo pipefail

# Trace when running in the CI
[ "$GITHUB_ACTIONS" != "true" ] || set -x

# Arguments:
#  1. run ID
#  2. number of the pull request, or empty for a non-pull-request run
#  3. base SHA of the pull request (pull requests only)
#  4. head SHA of the pull request (pull requests only)
RUN_ID=$1
PR_NUMBER=$2
PR_BASE_SHA=$3
PR_HEAD_SHA=$4

# Coverage data and report directory, uploaded as the 'coverage-report' artifact
COVERAGE_DIR=obj_coverage
ls -lsha ${COVERAGE_DIR}

# Combine the reports from the test jobs
nodist/fastcov.py -C ${COVERAGE_DIR}/verilator-*.info --lcov -o ${COVERAGE_DIR}/verilator.info

# Create the report. For a pull request, report patch coverage against the
# merge-base between the head of the pull request and the target branch. The
# summary quoted in the notification below is only in the log of 'make'.
MAKE_LOG=make-coverage-report.log
if [ -n "${PR_NUMBER}" ]; then
  COVERAGE_BASE=$(git rev-parse --short $(git merge-base ${PR_BASE_SHA} ${PR_HEAD_SHA}))
  make coverage-report COVERAGE_BASE=${COVERAGE_BASE} |& tee ${MAKE_LOG}
else
  make coverage-report
fi

# Remove the data files, only the HTML report is published
rm -f ${COVERAGE_DIR}/verilator*.info

# The rest is for pull requests only
if [ -z "${PR_NUMBER}" ]; then
  exit 0
fi

# Get some metadata about the run
RUN_NUM=$(gh run view ${RUN_ID} --json number --jq ".number")
RUN_URL=$(gh run view ${RUN_ID} --json url    --jq ".url")

# Repository owner and name of the default repository, used to build the
# GitHub Pages URL of the report. The owner is lowercased, as required for the
# '<owner>.github.io' Pages domain.
PAGES_OWNER=$(gh repo view --json owner --jq '.owner.login' | tr '[:upper:]' '[:lower:]')
PAGES_NAME=$(gh repo view --json name --jq '.name')

REPORT_URL=https://${PAGES_OWNER}.github.io/${PAGES_NAME}/coverage-reports/${RUN_ID}/index.html

###############################################################################
# Create the PR notification
###############################################################################

NOTIFICATION_DIR=notification
mkdir -p ${NOTIFICATION_DIR}

cat > ${NOTIFICATION_DIR}/body.txt <<NOTIFICATION_TEMPLATE
Patch coverage from PR workflow [#${RUN_NUM}](${RUN_URL}) (code coverage of lines changed relative to ${COVERAGE_BASE}):
NOTIFICATION_TEMPLATE

if [ -f ${COVERAGE_DIR}/empty-patch ]; then
  # Patch is empty
  cat >> ${NOTIFICATION_DIR}/body.txt <<SUMMARY_TEMPLATE
Patch contains no code changes
SUMMARY_TEMPLATE

  echo "Workflow [#${RUN_NUM}](${RUN_URL}): patch contains no code changes" > ${NOTIFICATION_DIR}/hist.txt

else
  # Patch contains code changes

  cat >> ${NOTIFICATION_DIR}/body.txt <<SUMMARY_TEMPLATE
<pre>
$(grep -E "(lines|branches)\.*:" ${MAKE_LOG} | sed "s/\.*:/:/" || true)
</pre>
Report: [${RUN_ID}](${REPORT_URL})

Please get to 100% line coverage, and understand all branches; see the [developer docs](https://github.com/verilator/verilator/blob/master/docs/internals.rst#code-coverage-results)
SUMMARY_TEMPLATE

  echo "Workflow [#${RUN_NUM}](${RUN_URL}) report: [${RUN_ID}](${REPORT_URL})" > ${NOTIFICATION_DIR}/hist.txt
fi
