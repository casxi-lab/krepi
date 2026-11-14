# Runs the main command of a step under a deadline and passes a stop signal
# of the runner on to it:
#
#   exec bash .github/scripts/deadline.sh [--stop-commands] [--status FILE] DURATION KILL_AFTER COMMAND [ARGUMENT...]
#
# The command runs under `timeout --signal=TERM --kill-after=KILL_AFTER
# DURATION`, which stops it with SIGTERM at the deadline, and with SIGKILL
# KILL_AFTER later if it has not ended. `timeout` runs the command in a
# process group of its own, so a signal that reaches only the process of the
# step does not reach the command. When a run is cancelled, the runner sends
# SIGINT to the process of each running step, SIGTERM some seconds later and
# then kills what is left. A step therefore starts this script with `exec`,
# as its last command, so that the script is the process of the step: it
# passes SIGINT and SIGTERM on to `timeout`, which passes them on to the
# command and its group, and it does not end before the command has ended.
# The command can thus write its receipt or report before the step ends, and
# the steps after it that run always upload what it wrote.
#
# The script exits with the status of `timeout`: the status of the command,
# such as 130 or 143 for a command that ends on SIGINT or SIGTERM with 128
# plus the signal, 128 plus the number of a signal that ended it, and 124
# when the deadline stopped it. `timeout` exits with 137 when it had to kill
# the command with SIGKILL after the deadline; the script exits with 124 then
# as well, so that 124 means a command stopped at its deadline. DURATION is a
# whole number of seconds, minutes, hours or days, such as `13m`. With
# --stop-commands, the script turns workflow commands off with a random token
# before the command starts and on again once it has ended, so that its
# output cannot act as a workflow command. With --status, it writes the
# status with which it exits to FILE, followed by a line feed, once the
# command has ended, so that a later step can read it.

set -u

usage="usage: deadline.sh [--stop-commands] [--status FILE] DURATION KILL_AFTER COMMAND [ARGUMENT...]"
stop_commands=
status_file=
if [ "${1-}" = --stop-commands ]; then
  stop_commands=1
  shift
fi
if [ "${1-}" = --status ]; then
  if [ "$#" -lt 2 ]; then
    echo "$usage" >&2
    exit 2
  fi
  status_file=$2
  shift 2
fi
if [ "$#" -lt 3 ]; then
  echo "$usage" >&2
  exit 2
fi
duration=$1
kill_after=$2
shift 2
case $duration in
  '' | *[!0-9smhd]* | [!0-9]* | *[smhd]?*)
    echo "deadline.sh: the duration $duration is not a whole number with s, m, h or d" >&2
    exit 2
    ;;
  *s) limit=${duration%s} ;;
  *m) limit=$((${duration%m} * 60)) ;;
  *h) limit=$((${duration%h} * 3600)) ;;
  *d) limit=$((${duration%d} * 86400)) ;;
  *) limit=$duration ;;
esac

token=
if [ -n "$stop_commands" ]; then
  token=$(openssl rand -hex 16) || exit 2
  echo "::stop-commands::$token"
fi

# Bash starts a command in the background with SIGINT and SIGQUIT ignored,
# and `timeout` keeps a signal ignored that was ignored when it started, so
# GNU `env` gives the two signals their default action before it runs
# `timeout`. A signal that arrives before the script knows the process ID of
# `env` is passed on as soon as it does. A SIGINT that reaches the new
# process before `env` has reset it is lost, and the command starts; the
# SIGTERM that the runner sends after it is passed on.
pending=
trap 'pending=INT' INT
trap 'pending=TERM' TERM
SECONDS=0
env --default-signal=INT,QUIT timeout --signal=TERM --kill-after="$kill_after" "$duration" "$@" &
pid=$!

signalled=
forward() {
  signalled=1
  kill -s "$1" "$pid" 2> /dev/null || true
}
trap 'forward INT' INT
trap 'forward TERM' TERM
if [ -n "$pending" ]; then
  forward "$pending"
fi

# A signal with a trap ends `wait` early, with a status above 128, and then
# runs the trap, so after a signal the script waits again until the command
# has ended. When the signal came right after the command ended, the second
# wait finds no command and fails with 127, and the status of the first wait
# stands.
signalled=
wait "$pid" 2> /dev/null
status=$?
while [ -n "$signalled" ]; do
  signalled=
  wait "$pid" 2> /dev/null
  next=$?
  if [ "$next" -ne 127 ]; then
    status=$next
  fi
done
if [ "$status" -eq 137 ] && [ "$SECONDS" -ge "$limit" ]; then
  status=124
fi
if [ -n "$status_file" ]; then
  echo "$status" > "$status_file"
fi

if [ -n "$token" ]; then
  echo "::$token::"
fi
exit "$status"
