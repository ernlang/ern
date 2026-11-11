#!/bin/sh
# Run every litmus test under the RC11 reference model (rc11.cat) and keep the raw herd7 output
# in results/. LB+rlx is run a second time with the no-thin-air check skipped. The lock tests B1 to
# B5 and the group D tests are also run with RMW checks skipped, one result file per run.
# Set HERD7 to the herd7 binary if it is not on PATH.
set -u
HERD7=${HERD7:-herd7}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$here/results"
cd "$here/litmus" || exit 1
status=0

# run <result name> <herd7 arguments...>
run() {
  out="$here/results/$1.txt"
  shift
  "$HERD7" "$@" > "$out" 2>&1
  if ! grep -q '^Observation' "$out"; then
    echo "error: no Observation line in results/$(basename "$out")" >&2
    status=1
  fi
}

# skip <test> <checks>: run <test> under rc11.cat with the comma-separated <checks> skipped
skip() {
  run "$1+skip-$(echo "$2" | tr ',' '-')" -model rc11.cat -skipchecks "$2" "$1.litmus"
}

for t in *.litmus; do
  run "${t%.litmus}" -model rc11.cat "$t"
done
run "LB+rlx+skip-no-thin-air" -model rc11.cat -skipcheck no-thin-air LB+rlx.litmus

# Exclusive acquisition in the lock tests (LOCK3+xchg-acq+rel is left out: one run takes minutes)
for c in atomicity coherencermw atomicity,coherencermw; do
  skip LOCK+xchg-acq+rel "$c"
  skip LOCK+cas-acq+rel "$c"
done
skip LOCK+xchg-acq+rlx atomicity,coherencermw
skip LOCK+xchg-rlx+rel atomicity,coherencermw
skip LOCK+sc+sc atomicity,coherencermw
skip LOCK+sc+sc atomicity,coherencermw,SC

# Group D
for c in atomicity coherencermw atomicity,coherencermw; do
  skip XCHG+acq "$c"
  skip XCHG+rlx "$c"
  skip XCHG+sc "$c"
done
skip XCHG+sc atomicity,coherencermw,SC

exit $status
