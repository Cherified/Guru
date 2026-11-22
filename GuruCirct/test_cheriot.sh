#!/bin/bash
# Copyright 2026 Google LLC
#
# SPDX-License-Identifier: MIT

# Builds CIRCT-based Verilator simulators of the CHERIoT designs and runs the CHERIoT test
# suite on them, as Agents/run_parallel.sh does for the simulators of Guru's PrettyPrinter:
#   cheriot    the specification of ../../cheriot (simulation mode, cheriot/SimTb.sv)
#   Fwd        the forwarding implementation, cheriot/Impl/Fwd (simulation mode, SimTb.sv)
#   Impl       the pipelined implementation, cheriot/Impl (RTL mode, cheriot/Impl/Tb.sv)
#   SimpleSim  simpleSpec of ../../SpecCheriot (simulation mode, SimTb.sv)
#   NondetSim  nondetSpec of ../../SpecCheriot (simulation mode, SimTb.sv)
# The extracted Compile.hs of each must exist (make -C ../../cheriot and ../../SpecCheriot).
#
# Usage: ./test_cheriot.sh [names...]     (default: all five)
# Environment: CIRCT_OPT (default circt-opt), JOBS (default 8)

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
CHERIOT="$(cd "$HERE/../../cheriot" && pwd)"
SPEC_CHERIOT="$(cd "$HERE/../../SpecCheriot" && pwd)"
JOBS="${JOBS:-8}"
NAMES=("$@")
[ ${#NAMES[@]} -eq 0 ] && NAMES=(cheriot Fwd Impl SimpleSim NondetSim)

cd "$HERE"

SIM_DIRS=()
RTL_DIRS=()
for n in "${NAMES[@]}"; do
  case "$n" in
    cheriot) SIM_DIRS+=("$CHERIOT/") ;;
    Fwd) SIM_DIRS+=("$CHERIOT/Impl/Fwd/") ;;
    SimpleSim|NondetSim) SIM_DIRS+=("$SPEC_CHERIOT/$n/") ;;
    Impl) RTL_DIRS+=("$CHERIOT/Impl/") ;;
    *) echo "unknown design: $n"; exit 1 ;;
  esac
done

if [ ${#SIM_DIRS[@]} -gt 0 ]; then
  make -j"$JOBS" DESIGNS="${SIM_DIRS[*]}" RTL_DESIGNS= SIM_TB="$CHERIOT/SimTb.sv" TB_TOP=Tb \
    TB_INC="-I$CHERIOT" sim || exit 1
fi
if [ ${#RTL_DIRS[@]} -gt 0 ]; then
  make -j"$JOBS" DESIGNS= RTL_DESIGNS="${RTL_DIRS[*]}" RTL_TB="$CHERIOT/Impl/Tb.sv" TB_TOP=Tb \
    TB_INC="-I$CHERIOT -I$CHERIOT/Impl" rtl || exit 1
fi

LOG_DIR="$HERE/build/test_logs"
rm -rf "$LOG_DIR"
mkdir -p "$LOG_DIR/tmp"
export TMPDIR="$LOG_DIR/tmp"

PIDS=()
for n in "${NAMES[@]}"; do
  if [ "$n" = Impl ]; then sim="$HERE/build/$n/obj_dir/VTb"; else sim="$HERE/build/$n/sim_obj_dir/VTb"; fi
  (cd "$CHERIOT" && ./run_all_tests.sh "$sim" > "$LOG_DIR/$n.log" 2>&1) &
  PIDS+=($!)
done

RC=0
for i in "${!NAMES[@]}"; do
  wait "${PIDS[$i]}" || RC=1
done

for n in "${NAMES[@]}"; do
  echo "=== $n ==="
  sed -n '/Running test: test-suite/,$p' "$LOG_DIR/$n.log" | grep '^\[Cycle ' | tail -n 1
  grep -E 'All tests finished in [0-9]+ cycles|TEST FAILED|Simulation timed out|^Summary:|^Failed tests:' "$LOG_DIR/$n.log"
done
exit $RC
