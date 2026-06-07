#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI script for 'rtlmeter.yml' PR results
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# This scipt builds the content of the response comment posten on PRs
# at the end of RTLMeter runs.

# Developer note: You should be able to run this script in your local checkout
# if you have GitHub CLI (command 'gh') setup, authenticated ('gh auth login'),
# and have set a default repository ('gh repo set-default').

# Trace when running in the CI
[ "$GITHUB_ACTIONS" != "true" ] || set -x

# Arguments:
#  1. reference run ID
#  2. new run ID
#  rest: run tags
REF_ID=$1; shift
NEW_ID=$1; shift
RUNS="$@"

# $VERILATOR_CHECKOUT/ci directory
SCRIPT_DIR=$(readlink -f $(dirname ${BASH_SOURCE[0]}))

# Move into a temporary directory
rm -rf rtlmeter-report
mkdir rtlmeter-report
pushd rtlmeter-report &> /dev/null
TMP_DIR=$(readlink -f .)

# Artifacts to download
DOWNLOAD_ARTIFACTS=""
for r in $RUNS; do
  DOWNLOAD_ARTIFACTS="$DOWNLOAD_ARTIFACTS --name all-results-$r"
done

# Download reference run results
mkdir ref
REF_DIR=$(readlink -f ref)
gh run download ${REF_ID} $DOWNLOAD_ARTIFACTS --dir $REF_DIR
mv $REF_DIR/*/*.json $REF_DIR/
find $REF_DIR -mindepth 1 -type d -delete

# Download current run results
mkdir new
NEW_DIR=$(readlink -f new)
gh run download ${NEW_ID} $DOWNLOAD_ARTIFACTS --dir $NEW_DIR
mv $NEW_DIR/*/*.json $NEW_DIR/
find $NEW_DIR -mindepth 1 -type d -delete

# Get Some metadata about the runs
REF_URL=$(gh run view $REF_ID --json url --jq ".url")
REF_NUM=$(gh run view $REF_ID --json number --jq ".number")
REF_DATE=$(gh run view $REF_ID --json createdAt --jq ".createdAt")
NEW_URL=$(gh run view $NEW_ID --json url --jq ".url")
NEW_NUM=$(gh run view $NEW_ID --json number --jq ".number")

# Go back to root directory
popd &> /dev/null
# Go to RTLMeter directory
cd rtlmeter

# Compare results
SUMMARY_ARGS=()
for r in $RUNS; do
  CMP_JSON=$TMP_DIR/cmp-$r.json
  # Gather args for summary script
  SUMMARY_ARGS+=($REF_DIR/all-results-$r.json $CMP_JSON)
  # Create JSON
  ./rtlmeter compare --format json --steps "*" --metrics "*" \
    $REF_DIR/all-results-$r.json $NEW_DIR/all-results-$r.json > $CMP_JSON
  # Also create detailed tables
  ./rtlmeter compare --format ascii --steps 'verilate' --metrics '* !system !user' $REF_DIR/all-results-$r.json $NEW_DIR/all-results-$r.json > $TMP_DIR/verilate-$r.txt
  ./rtlmeter compare --format ascii --steps 'cppbuild' --metrics '* !system !user' $REF_DIR/all-results-$r.json $NEW_DIR/all-results-$r.json > $TMP_DIR/cppbuild-$r.txt
  ./rtlmeter compare --format ascii --steps 'execute'  --metrics '* !system !user' $REF_DIR/all-results-$r.json $NEW_DIR/all-results-$r.json > $TMP_DIR/execute-$r.txt
  # Chop them at new lines, into one table per file
  awk -v RS= -v prefix=$TMP_DIR/$r-frag '{print > sprintf("%s-verilate-%02d.txt",prefix,NR)}' $TMP_DIR/verilate-$r.txt
  awk -v RS= -v prefix=$TMP_DIR/$r-frag '{print > sprintf("%s-cppbuild-%02d.txt",prefix,NR)}' $TMP_DIR/cppbuild-$r.txt
  awk -v RS= -v prefix=$TMP_DIR/$r-frag '{print > sprintf("%s-execute-%02d.txt" ,prefix,NR)}' $TMP_DIR/execute-$r.txt
done

# Create summary
venv/bin/python3 $SCRIPT_DIR/ci-rtlmeter-report.py ${SUMMARY_ARGS[@]} > $TMP_DIR/summary.txt
# Print it
cat $TMP_DIR/summary.txt

# Create notification comment content
NOTIFICATION=$TMP_DIR/notification.txt
cat > $NOTIFICATION <<NOTIFICATION_TEMPLATE
Performance metrics for PR workflow [#$NEW_NUM]($NEW_URL) (B)
compared to scheduled run [#$REF_NUM]($REF_URL) (A) from $REF_DATE
<details open>
  <summary><strong>Summary of all runs</strong></summary>
  <pre>
$(cat $TMP_DIR/summary.txt)
  </pre>
</details>
Blah Blah Blah
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
  RUN_NAME=$(jq -rj ".[0].runName" $REF_DIR/all-results-$r.json)
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
    <title>Verilator RTLMeter report #${NEW_NUM}</title>
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
