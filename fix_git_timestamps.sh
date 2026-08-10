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

# git-filter-repo deliberately removes the `origin` remote after a rewrite so
# that an accidental force-push cannot overwrite the server. Save the remote
# configuration and the current branch's upstream, then restore them after the
# rewrite. Restoring the configuration does not push anything automatically.
origin_fetch_url=$(git remote get-url origin 2>/dev/null || true)
origin_push_url=$(git remote get-url --push origin 2>/dev/null || true)
current_branch=$(git symbolic-ref --quiet --short HEAD 2>/dev/null || true)
upstream_remote=""
upstream_merge=""
if [[ -n "$current_branch" ]]; then
    upstream_remote=$(git config --get "branch.$current_branch.remote" || true)
    upstream_merge=$(git config --get "branch.$current_branch.merge" || true)
fi

restore_remote_configuration() {
    if [[ -n "$origin_fetch_url" ]]; then
        if git remote get-url origin >/dev/null 2>&1; then
            git remote set-url origin "$origin_fetch_url"
        else
            git remote add origin "$origin_fetch_url"
        fi

        if [[ -n "$origin_push_url" && "$origin_push_url" != "$origin_fetch_url" ]]; then
            git remote set-url --push origin "$origin_push_url"
        fi
    fi

    if [[ -n "$current_branch" && -n "$upstream_remote" && -n "$upstream_merge" ]]; then
        git config "branch.$current_branch.remote" "$upstream_remote"
        git config "branch.$current_branch.merge" "$upstream_merge"
    fi
}

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

filter_status=0
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
' || filter_status=$?

restore_remote_configuration

if [[ "$filter_status" -ne 0 ]]; then
    printf '%s\n' "Timestamp rewrite failed; the saved remote configuration was restored." >&2
    exit "$filter_status"
fi

printf '%s\n' "Timestamp rewrite completed. Review the history before pushing."
printf '%s\n' "Use git push --force-with-lease origin $current_branch after verifying the history."
