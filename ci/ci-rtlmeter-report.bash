#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI script for 'rtlmeter.yml' PR results
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# This script builds the content of the response comment posted on PRs
# at the end of RTLMeter runs.

# Developer note: You should be able to run this script in your local checkout
# if you have GitHub CLI (command 'gh') setup, authenticated ('gh auth login'),
# and have set a default repository ('gh repo set-default').

# Trace when running in the CI
[ "$GITHUB_ACTIONS" != "true" ] || set -x

# Arguments:
#  1. run ID
#  2. SHA of the event that triggered the run (for a PR, the test merge commit)
#  rest: run tags
RUN_ID=$1; shift
RUN_SHA=$1; shift
RUNS="$@"

# $VERILATOR_CHECKOUT/ci directory
SCRIPT_DIR=$(readlink -f $(dirname ${BASH_SOURCE[0]}))

# Move into a temporary directory
rm -rf rtlmeter-report
mkdir rtlmeter-report
pushd rtlmeter-report &> /dev/null
TMP_DIR=$(readlink -f .)

# Download the combined results. 'combine-results' uploads a single artifact
# for each version, holding the per-tag JSON files (e.g. all-results-gcc.json):
#  - 'all-results'   for the new version
#  - 'all-reference' for the old reference version
mkdir new ref
NEW_DIR=$(readlink -f new)
REF_DIR=$(readlink -f ref)
gh run download ${RUN_ID} --name all-results   --dir $NEW_DIR
gh run download ${RUN_ID} --name all-reference --dir $REF_DIR

# Get Some metadata about the runs
RUN_URL=$(gh run view $RUN_ID --json url --jq ".url")
RUN_NUM=$(gh run view $RUN_ID --json number --jq ".number")

# Repository owner and name of the default repository, used to build the
# GitHub Pages URL of the detailed report. The owner is lowercased, as required
# for the '<owner>.github.io' Pages domain. Resolved here, while still in the
# default repository's git context (before the 'cd rtlmeter' below).
PAGES_OWNER=$(gh repo view --json owner --jq '.owner.login' | tr '[:upper:]' '[:lower:]')
PAGES_NAME=$(gh repo view --json name --jq '.name')

# The 'old' reference was built from the target branch base commit, which is
# the first parent of the triggering merge commit (same as the 'start' job in
# rtlmeter.yml). Resolved here, while still in the default repository's git
# context (before the 'cd rtlmeter' below).
REF_SHA=$(gh api "repos/{owner}/{repo}/commits/$RUN_SHA" --jq '.parents[0].sha')

# Go back to root directory
popd &> /dev/null
# Go to RTLMeter directory
cd rtlmeter

# Compare results
SUMMARY_ARGS=()
for r in $RUNS; do
  CMP_JSON=$TMP_DIR/cmp-$r.json
  # Gather args for summary script
  SUMMARY_ARGS+=($NEW_DIR/all-results-$r.json $CMP_JSON)
  # Create JSON
  ./rtlmeter compare --format json --steps "*" --metrics "*" \
    $REF_DIR/all-reference-$r.json $NEW_DIR/all-results-$r.json > $CMP_JSON
  # Also create detailed tables
  ./rtlmeter compare --format ascii --steps 'verilate' --metrics '*' $REF_DIR/all-reference-$r.json $NEW_DIR/all-results-$r.json > $TMP_DIR/verilate-$r.txt
  ./rtlmeter compare --format ascii --steps 'cppbuild' --metrics '*' $REF_DIR/all-reference-$r.json $NEW_DIR/all-results-$r.json > $TMP_DIR/cppbuild-$r.txt
  ./rtlmeter compare --format ascii --steps 'execute'  --metrics '*' $REF_DIR/all-reference-$r.json $NEW_DIR/all-results-$r.json > $TMP_DIR/execute-$r.txt
  # Chop them at new lines, into one table per file
  awk -v RS= -v prefix=$TMP_DIR/$r-frag '{print > sprintf("%s-verilate-%02d.txt",prefix,NR)}' $TMP_DIR/verilate-$r.txt
  awk -v RS= -v prefix=$TMP_DIR/$r-frag '{print > sprintf("%s-cppbuild-%02d.txt",prefix,NR)}' $TMP_DIR/cppbuild-$r.txt
  awk -v RS= -v prefix=$TMP_DIR/$r-frag '{print > sprintf("%s-execute-%02d.txt" ,prefix,NR)}' $TMP_DIR/execute-$r.txt
done

# Create summary, suppress failure, but save the status reported to pass back.
STATUS=0
venv/bin/python3 $SCRIPT_DIR/ci-rtlmeter-report.py ${SUMMARY_ARGS[@]} > $TMP_DIR/summary.txt || STATUS=$?
# Print it
cat $TMP_DIR/summary.txt

# Create notification comment content
NOTIFICATION=$TMP_DIR/notification.txt
cat > $NOTIFICATION <<NOTIFICATION_TEMPLATE
Performance metrics for PR workflow [#$RUN_NUM]($RUN_URL), comparing:
- target branch commit [${REF_SHA:0:9}](https://github.com/${PAGES_OWNER}/${PAGES_NAME}/commit/${REF_SHA}) (A)
- with PR merge commit [${RUN_SHA:0:9}](https://github.com/${PAGES_OWNER}/${PAGES_NAME}/commit/${RUN_SHA}) (B)

<details open>
  <summary>Summary of all runs</summary>
  <pre>
$(cat $TMP_DIR/summary.txt)
  </pre>
</details>

The reported numbers are the geometric means of the ratios of the metrics over all cases,
less than 1 is a regression, greater than 1 is an improvement.
The jobs run on variable and noisy runners, so some variance is expected between runs.

Detailed report: [${RUN_ID}](https://${PAGES_OWNER}.github.io/${PAGES_NAME}/rtlmeter-reports/${RUN_ID}/index.html)
NOTIFICATION_TEMPLATE

# Create detailed report
REPORT=$TMP_DIR/body.html
cat > $REPORT <<SUMMARY_TEMPLATE
<h3>Summary of all runs</h3>
<pre>
$(cat $TMP_DIR/summary.txt)
</pre>
SUMMARY_TEMPLATE
echo "<h3>Detailed results</h3>" >> $REPORT
for r in $RUNS; do
  RUN_NAME=$(jq -rj ".[0].runName" $NEW_DIR/all-results-$r.json)
  echo "<h4>$RUN_NAME</h4>" >> $REPORT
  for f in $(ls -1 $TMP_DIR/$r-frag-verilate-*.txt | sort) \
           $(ls -1 $TMP_DIR/$r-frag-cppbuild-*.txt | sort) \
           $(ls -1 $TMP_DIR/$r-frag-execute-*.txt | sort); do
    cat >> $REPORT <<DETAIL_TAMPLATE
    <details>
      <summary>$(head -n 1 $f | tr -d '\n')</summary>
      <pre>
$(tail -n +2 $f)
      </pre>
    </details>
DETAIL_TAMPLATE
  done
done

# Turn the report into a proper HTML page
mkdir -p ${TMP_DIR}/report
cat > ${TMP_DIR}/report/index.html <<INDEX_TEMPLATE
<html>

  <head>
    <title>Verilator RTLMeter report #${RUN_NUM}</title>
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
$(cat ${TMP_DIR}/body.html)
  </body>

</html>
INDEX_TEMPLATE

exit $STATUS
