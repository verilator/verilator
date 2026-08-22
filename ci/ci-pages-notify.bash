#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI script for 'pages.yml', notifies PRs
#
# SPDX-FileCopyrightText: 2025 Geza Lore
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Notify PRs via comment that their workflow reports are available

# Note this deliberately does not 'set -e'. A run that cannot be notified, say
# because its pull request was locked, must not hold up the notification of all
# the others, so each failure below moves on to the next run instead. Its
# artifact is then left in place, so it is retried on the next run of 'pages.yml'.

# The account we post as, which is how we tell our own earlier notifications
# from anybody else's comments. 'pages.yml' sets this to the slug of the app the
# token belongs to. Set it to your own login when running this by hand. The 'jq'
# filter below picks it up from the environment.
if [ -z "${GH_AUTHOR:-}" ]; then
  echo "GH_AUTHOR must hold the account we post as" >&2
  exit 1
fi
echo "Posting as '${GH_AUTHOR}'"

# Marker line separating the report from the history of the older reports
readonly HISTORY_MARKER='<!-- Verilator CI notification history -->'
# Opening line of the HTML comment stashing the history entry of the report
# itself. It is not shown in its own history, only inherited by the ones
# superseding it, hence it is kept out of sight until then.
readonly NEXTHIST_MARKER='<!-- Verilator CI notification entry'

# Create artifacts root directory
ARTIFACTS_ROOT=artifacts
mkdir -p ${ARTIFACTS_ROOT}

for RUN_ID in ${PR_RUN_IDS//,/ }; do
  # Create workflow artifacts directory
  ARTIFACTS_DIR=${ARTIFACTS_ROOT}/${RUN_ID}
  mkdir -p ${ARTIFACTS_DIR}

  # Download artifact of this run, if exists
  gh run download ${RUN_ID} --name pr-notification --dir ${ARTIFACTS_DIR} &> /dev/null || true

  # Move on if no notification is required
  if [ ! -f ${ARTIFACTS_DIR}/pr-number.txt ]; then
    continue
  fi

  PR_NUMBER=$(cat ${ARTIFACTS_DIR}/pr-number.txt)
  echo "@@@ Run ${RUN_ID}: notifying PR #${PR_NUMBER}"

  # Everything below is created and validated by the 'upload-pr-notification'
  # action. Move on if this artifact was not made by it, e.g. it is left over
  # from an earlier version of the CI, so it does not hold up the other runs.
  for f in body.txt key.txt hist.txt; do
    if [ ! -f ${ARTIFACTS_DIR}/${f} ]; then
      echo "Notification has no '${f}'" >&2
      continue 2  # Note: continues the enclosing 'RUN_ID' loop
    fi
  done

  # 'key.txt' holds the key naming the source of the notification. It goes on the
  # first line of the comment as an HTML comment, so it is invisible when
  # rendered, and is used below to find the stale notifications with the same
  # key, which are then superseded by the new one and deleted.
  COMMENT_MARKER="<!-- Verilator CI notification: $(cat ${ARTIFACTS_DIR}/key.txt) -->"

  # Find the stale notifications from the same source on this PR. That is, our
  # own comments with the same marker on their first line. Oldest first, as
  # returned by the API. An app posts as '<slug>[bot]', so drop that suffix to
  # compare against the slug. Move on if they cannot be listed, as without them
  # we would post a duplicate instead of superseding them.
  if ! COMMENT_MARKER="${COMMENT_MARKER}" \
      gh api --paginate "repos/{owner}/{repo}/issues/${PR_NUMBER}/comments" \
        --jq '.[]
              | select((.user.login | rtrimstr("[bot]")) == env.GH_AUTHOR)
              | select((.body | split("\n") | .[0] | rtrimstr("\r")) == env.COMMENT_MARKER)
              | {id, body}' > ${ARTIFACTS_DIR}/stale.json; then
    echo "Failed to list the comments of PR #${PR_NUMBER}" >&2
    continue
  fi

  # Inherit the history of the newest stale notification. There should only ever
  # be one, and it holds the whole history anyway, as each notification inherits
  # the history of the one it superseded. Any older ones are only deleted below.
  STALE_COUNT=$(wc -l < ${ARTIFACTS_DIR}/stale.json)
  if [ ${STALE_COUNT} -gt 1 ]; then
    echo "Found ${STALE_COUNT} stale notifications, only the newest is inherited from"
  fi

  HISTORY=${ARTIFACTS_DIR}/history.txt
  touch ${HISTORY}
  if [ ${STALE_COUNT} -gt 0 ]; then
    tail -n 1 ${ARTIFACTS_DIR}/stale.json | jq -r '.body' | tr -d '\r' > ${ARTIFACTS_DIR}/stale-body.txt
    # Its own entry, stashed in an HTML comment
    awk -v marker="${NEXTHIST_MARKER}" '
      $0 == marker { inside = 1; next }
      !inside { next }
      $0 == "-->" { exit }
      NF { print }
    ' ${ARTIFACTS_DIR}/stale-body.txt >> ${HISTORY}
    # Followed by its history, without the enclosing '<details>' markup
    awk -v marker="${HISTORY_MARKER}" '
      $0 == marker { inside = 1; next }
      !inside { next }
      $0 == "<details>" || /^<summary>/ { next }
      $0 == "</details>" { exit }
      NF { print }
    ' ${ARTIFACTS_DIR}/stale-body.txt >> ${HISTORY}
  fi

  # Assemble the comment. Starts with the marker and the report.
  COMMENT=${ARTIFACTS_DIR}/comment.txt
  cat > ${COMMENT} <<COMMENT_TEMPLATE
${COMMENT_MARKER}
$(cat ${ARTIFACTS_DIR}/body.txt)
COMMENT_TEMPLATE

  # Then the history inherited from the notifications this one supersedes, so
  # the older reports remain reachable from the only remaining comment.
  if [ -s ${HISTORY} ]; then
    echo "History holds $(wc -l < ${HISTORY}) entries"
    cat >> ${COMMENT} <<HISTORY_TEMPLATE
${HISTORY_MARKER}
<details>
<summary>PR history</summary>

$(cat ${HISTORY})
</details>
HISTORY_TEMPLATE
  fi

  # Finally this report's own history entry, stashed out of sight until a later
  # notification inherits it.
  cat >> ${COMMENT} <<NEXTHIST_TEMPLATE
${NEXTHIST_MARKER}
$(cat ${ARTIFACTS_DIR}/hist.txt)
-->
NEXTHIST_TEMPLATE

  # Post it. Move on if this failed, without deleting anything below, otherwise
  # the history held by the stale notifications would be lost.
  if ! jq -Rs '{body: .}' ${COMMENT} \
      | gh api --method POST "repos/{owner}/{repo}/issues/${PR_NUMBER}/comments" \
          --input - > ${ARTIFACTS_DIR}/posted.json; then
    echo "Failed to post this notification on PR #${PR_NUMBER}:" >&2
    cat ${COMMENT} >&2
    continue
  fi
  echo "Posted $(jq -r '.html_url' ${ARTIFACTS_DIR}/posted.json)"

  # Delete the stale notifications, so only the new one remains
  for COMMENT_ID in $(jq -r '.id' ${ARTIFACTS_DIR}/stale.json); do
    echo "Deleting stale comment ${COMMENT_ID}"
    gh api --method DELETE "repos/{owner}/{repo}/issues/comments/${COMMENT_ID}"
  done

  # Get the artifact IDs. Note there can be more than one artifact named
  # 'pr-notification' for a single run, as the artifacts endpoint lists
  # artifacts across all run attempts, and a re-run uploads a new one while
  # keeping the previous attempt's artifact.
  ARTIFACT_IDS=$(gh api "repos/{owner}/{repo}/actions/runs/${RUN_ID}/artifacts" --jq '.artifacts[] | select(.name == "pr-notification") | .id')

  # Delete them all, so we only notify once
  for ARTIFACT_ID in ${ARTIFACT_IDS}; do
    gh api --method DELETE "repos/{owner}/{repo}/actions/artifacts/${ARTIFACT_ID}"
  done
done
