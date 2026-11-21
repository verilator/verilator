#!/usr/bin/env python3
# pylint: disable=C0103,C0114,C0115,C0116
# DESCRIPTION: Verilator: CI script for the jobs of 'claude-review.yml'
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

###############################################################################
# The parts of Claude's review of a pull request that talk to GitHub:
#   fetch: for the 'review' job, add the pull request contents in '.pr', for
#          Claude to read, and print the commit at its head
#   post:  for the 'post' job, post Claude's review
# GitHub is reached with 'gh', which takes the token from GH_TOKEN.
###############################################################################

import argparse
import json
import os
import re
import subprocess
import sys
from typing import NamedTuple

# The CI app, which posts the reviews
BOT = "verilator-bot[bot]"

# Marks a pull request Claude had nothing to say about
PASS_LABEL = "pr-pass: claude"

PREAMBLE = """\
Consider the following AI review, which may be inaccurate. \
Click "Resolve conversation" on each item in GitHub and avoid commentary that \
only describes how it was resolved. \
When you think the pull request is ready to merge, and all tests are passing, \
make a comment to "Request a human review or merge"."""

# GraphQL, as REST does not tell whether a thread is resolved
THREADS_QUERY = """
query($owner: String!, $repo: String!, $number: Int!, $endCursor: String) {
  repository(owner: $owner, name: $repo) {
    pullRequest(number: $number) {
      reviewThreads(first: 100, after: $endCursor) {
        pageInfo { hasNextPage endCursor }
        nodes {
          isResolved
          isOutdated
          path
          line
          originalLine
          comments(first: 100) {
            nodes { author { __typename login } authorAssociation body }
          }
        }
      }
    }
  }
}"""


def gh(*command, stdin=None):
    return subprocess.run(["gh", *command],
                          input=stdin,
                          stdout=subprocess.PIPE,
                          encoding="utf-8",
                          errors="replace",
                          check=True).stdout


def gh_pages(*command):
    return json.loads(gh("api", "--paginate", "--slurp", *command))


def compare(head_sha):
    # The diff of the pull request at 'head_sha', whatever is pushed to it later
    return gh("api", "-H", "Accept: application/vnd.github.diff",
              f"repos/{ARGS.repo}/compare/{ARGS.base_ref}...{head_sha}")


######################################################################
# fetch


def is_member(association):
    return association in ("OWNER", "MEMBER", "COLLABORATOR")


def fetch_comments(pr_author):
    # The discussion, and the texts of the reviews
    found = gh_pages(f"repos/{ARGS.repo}/issues/{ARGS.pr}/comments")
    found += gh_pages(f"repos/{ARGS.repo}/pulls/{ARGS.pr}/reviews")
    comments = []
    for comment in sorted((c for page in found for c in page),
                          key=lambda c: c.get("created_at") or c.get("submitted_at") or ""):
        author = (comment["user"] or {}).get("login")
        is_bot_review = author == BOT and "submitted_at" in comment
        if not comment["body"]:
            continue
        if author == pr_author or is_member(comment["author_association"]) or is_bot_review:
            comments.append({"author": author, "body": comment["body"]})
    return comments


def fetch_threads(pr_author):
    # The review threads, each on a line of a file, Claude's earlier reviews among them
    owner, repo = ARGS.repo.split("/")
    pages = gh_pages("graphql", "-F", f"owner={owner}", "-F", f"repo={repo}", "-F",
                     f"number={ARGS.pr}", "-f", f"query={THREADS_QUERY}")
    threads = []
    for page in pages:
        for thread in page["data"]["repository"]["pullRequest"]["reviewThreads"]["nodes"]:
            comments = []
            for comment in thread["comments"]["nodes"]:
                author = comment["author"] or {}
                name = author.get("login")
                # Bots have no '[bot]' suffix here, so a user could have the same login
                if author.get("__typename") == "Bot":
                    name += "[bot]"
                if name in (pr_author, BOT) or is_member(comment["authorAssociation"]):
                    comments.append({"author": name, "body": comment["body"]})
                elif not comments:
                    break  # A thread started by someone else
            if comments:
                threads.append({
                    "path": thread["path"],
                    "line": thread["line"] or thread["originalLine"],
                    "outdated": thread["isOutdated"],
                    "resolved": thread["isResolved"],
                    "comments": comments
                })
    return threads


def fetch():
    pr = json.loads(gh("api", f"repos/{ARGS.repo}/pulls/{ARGS.pr}"))
    pr_author = pr["user"]["login"]
    head_sha = pr["head"]["sha"]

    # The pull request contents for Claude, as it cannot run commands. Only that
    # of the author, of members and of Claude's earlier reviews, so that others
    # cannot steer the review. The comments are JSON, so that the text of one
    # cannot pass for another, or for someone else's.
    contents = {
        "description.md": f"# {pr['title']}\n\n{pr['body'] or ''}\n",
        "diff.patch": compare(head_sha),
        "comments.json": json.dumps(fetch_comments(pr_author), indent=2, ensure_ascii=False),
        "threads.json": json.dumps(fetch_threads(pr_author), indent=2, ensure_ascii=False),
    }
    os.mkdir(".pr")
    for name, text in contents.items():
        with open(os.path.join(".pr", name), "w", encoding="utf-8") as fd:
            fd.write(text)

    # The head of the diff reviewed, for the 'post' job
    print(head_sha)


######################################################################
# post


class Line(NamedTuple):
    # A line of the diff that GitHub accepts a comment on
    path: str
    start: int  # The first line of the new version in the '@@' header of its hunk
    side: str  # "RIGHT" if added or unchanged, "LEFT" if removed
    line: int  # In the new version of the file on "RIGHT", in the old on "LEFT"


def diff_lines(diff):
    lines = []
    path = None
    in_hunk = False
    old = new = start = 0
    for text in diff.split("\n"):
        hunk = re.match(r"@@ -(\d+)\S* \+(\d+)", text)
        if text.startswith("diff --git "):
            path = None
            in_hunk = False
        elif hunk:
            old, new = int(hunk[1]), int(hunk[2])
            start = new
            in_hunk = True
        elif not in_hunk:
            # A removed file has only the old name
            if text.startswith("+++ b/") or (text.startswith("--- a/") and not path):
                path = text[6:]
        elif text.startswith("-"):
            lines.append(Line(path, start, "LEFT", old))
            old += 1
        elif text.startswith("+"):
            lines.append(Line(path, start, "RIGHT", new))
            new += 1
        elif text.startswith(" "):
            lines.append(Line(path, start, "RIGHT", new))
            new += 1
            old += 1
    return lines


def place(comment, lines):
    # A comment not on one of 'lines' goes on the nearest line of the hunk
    # Claude says it is about, or else of any hunk of its file, on the side
    # Claude says if the file has lines there, or else on the first line of the
    # diff, starting with where it belongs
    path, side, line = comment["path"], comment["side"], comment["line"]
    near = [x for x in lines if x.path == path]
    near = [x for x in near if x.side == side] or near
    if not any(x.line == line for x in near):
        named = re.search(r"\+(\d+)", comment["hunk"])
        near = [x for x in near if named and x.start == int(named[1])] or near
    at = min(near, key=lambda x: abs(x.line - line)) if near else lines[0]
    body = comment["body"]
    if (at.path, at.side, at.line) != (path, side, line):
        body = f"`{path}:{line}`: {body}"
    return {"path": at.path, "side": at.side, "line": at.line, "body": body}


def review_comments():
    # The comments of Claude's structured output that say something. None unless
    # there is a list of comments, so that a broken review cannot pass.
    try:
        comments = json.loads(ARGS.review)["comments"]
        if not isinstance(comments, list):
            return None
        return [c for c in comments if c["body"].strip()]
    except (KeyError, TypeError, ValueError, AttributeError):
        return None


def post():
    comments = review_comments()

    if comments == []:
        # Nothing to say, so post nothing and mark the pull request as passing
        gh("pr", "edit", ARGS.pr, "--repo", ARGS.repo, "--add-label", PASS_LABEL)
        return

    # Clear any mark left by an earlier review
    gh("pr", "edit", ARGS.pr, "--repo", ARGS.repo, "--remove-label", PASS_LABEL)
    if comments is None:
        sys.exit("::error::No review from Claude")

    lines = diff_lines(compare(ARGS.head_sha))
    if not lines:
        sys.exit("::error::No lines to comment on in the diff")

    # A single review, so that it sends one notification, of comments on files,
    # not on the review as a whole. The review is only data: the pull request,
    # the commit and the COMMENT verdict are fixed here, whatever the pull
    # request under review makes Claude return.
    placed = [place(comment, lines) for comment in comments]
    placed[0]["body"] = PREAMBLE + "\n\n" + placed[0]["body"]
    request = {"event": "COMMENT", "commit_id": ARGS.head_sha, "comments": placed}
    gh("api",
       "--method",
       "POST",
       f"repos/{ARGS.repo}/pulls/{ARGS.pr}/reviews",
       "--input",
       "-",
       stdin=json.dumps(request))


######################################################################
# main

parser = argparse.ArgumentParser(
    allow_abbrev=False,
    description="Fetch a pull request for, or post, the review of claude-review.yml")
commands = parser.add_subparsers(dest="command", required=True)
fetch_parser = commands.add_parser("fetch")
post_parser = commands.add_parser("post")
for subparser in (fetch_parser, post_parser):
    subparser.add_argument("--repo", required=True, help="repository, as owner/name")
    subparser.add_argument("--pr", required=True, help="number of the pull request")
    subparser.add_argument("--base-ref", required=True, help="base branch of the pull request")
post_parser.add_argument("--head-sha", required=True, help="commit that 'fetch' printed")
post_parser.add_argument("--review", required=True, help="structured output of Claude")
ARGS = parser.parse_args()

if ARGS.command == "fetch":
    fetch()
else:
    post()
