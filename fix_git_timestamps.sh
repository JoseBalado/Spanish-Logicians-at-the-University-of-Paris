#!/usr/bin/env bash
set -euo pipefail

# Rewrite commit timestamps while preserving each commit's original UTC date.
# This changes commit hashes. Make a backup before running it.

if ! git filter-repo --version >/dev/null 2>&1; then
    printf '%s\n' "Error: git-filter-repo is not installed." >&2
    printf '%s\n' "Install it with your system package manager, then rerun this script." >&2
    exit 1
fi

repo_root=$(git rev-parse --show-toplevel 2>/dev/null) || {
    printf '%s\n' "Error: run this script inside a Git repository." >&2
    exit 1
}
cd "$repo_root"

if [[ -n "$(git status --porcelain)" ]]; then
    printf '%s\n' "Error: the working tree is not clean. Commit or stash changes first." >&2
    exit 1
fi

printf '%s\n' "This will rewrite every commit in: $repo_root"
printf '%s\n' "All commit hashes will change. A backup is strongly recommended."
read -r -p "Continue? [y/N] " answer
if [[ "$answer" != "y" && "$answer" != "Y" ]]; then
    printf '%s\n' "Aborted."
    exit 0
fi

git filter-repo --force --commit-callback '
import datetime

# These values persist across callback invocations during this rewrite.
if "_shared_last_day" not in globals():
    globals()["_shared_last_day"] = None
    globals()["_shared_min_counter"] = 0

# Preserve the original UTC calendar day.
orig_timestamp = int(commit.author_date.split(b" ")[0])
orig_datetime = datetime.datetime.fromtimestamp(
    orig_timestamp, datetime.timezone.utc
)
current_day = orig_datetime.strftime("%Y-%m-%d")

# Restart the minute sequence when the calendar date changes.
if current_day != globals()["_shared_last_day"]:
    globals()["_shared_min_counter"] = 0
    globals()["_shared_last_day"] = current_day

# Place each commit at 18:00 UTC, one minute after the previous commit
# encountered on the same original calendar day.
new_datetime = orig_datetime.replace(
    hour=18,
    minute=0,
    second=0,
    microsecond=0,
) + datetime.timedelta(minutes=globals()["_shared_min_counter"])
new_epoch = str(int(new_datetime.timestamp())).encode("utf-8") + b" +0000"

# Keep author and committer timestamps aligned.
commit.author_date = new_epoch
commit.committer_date = new_epoch
globals()["_shared_min_counter"] += 1
'

printf '%s\n' "Timestamp rewrite completed. Review the history before pushing."
