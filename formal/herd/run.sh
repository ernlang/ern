#!/bin/sh
# Run every litmus test under the RC11 reference model (rc11.cat) and keep the raw herd7 output
# in results/. LB+rlx is run a second time with the no-thin-air check skipped, and
# LOCK+xchg-acq+norel with the atomicity and coherencermw checks skipped.
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

for t in *.litmus; do
  run "${t%.litmus}" -model rc11.cat "$t"
done
run "LB+rlx+skip-no-thin-air" -model rc11.cat -skipcheck no-thin-air LB+rlx.litmus
run "LOCK+xchg-acq+norel+skip-rmw" -model rc11.cat -skipchecks atomicity,coherencermw \
  LOCK+xchg-acq+norel.litmus

exit $status
