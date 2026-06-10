# Install filter-repo:
sudo apt update && sudo apt install git-filter-repo


# Correcting the time for commits:

git filter-repo --force --commit-callback '
import datetime

# 1. Initialize our persistent counters on the global scope if missing
if "_shared_last_day" not in globals():
    globals()["_shared_last_day"] = None
    globals()["_shared_min_counter"] = 0

# 2. Parse original Unix epoch timestamp into a Python datetime object safely using [0]
orig_timestamp = int(commit.author_date.split(b" ")[0])
orig_datetime = datetime.datetime.fromtimestamp(orig_timestamp, datetime.timezone.utc)
current_day = orig_datetime.strftime("%Y-%m-%d")

# 3. Reset the minute sequence when the calendar date shifts
if current_day != globals()["_shared_last_day"]:
    globals()["_shared_min_counter"] = 0
    globals()["_shared_last_day"] = current_day

# 4. Build a brand new timestamp locking the day, setting hour to 18 GMT, and incrementing minutes
new_datetime = orig_datetime.replace(hour=18, minute=globals()["_shared_min_counter"], second=0)
new_epoch = str(int(new_datetime.timestamp())).encode("utf-8") + b" +0000"

# 5. Overwrite both fields to maintain perfect alignment
commit.author_date = new_epoch
commit.committer_date = new_epoch

# 6. Increment the counter correctly inside the script block
globals()["_shared_min_counter"] += 1
'



# Correcting the email:

git filter-repo --force --email-callback 'return b"7026031+JoseBalado@users.noreply.github.com"'

git push origin --force
