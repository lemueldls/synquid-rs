#!/usr/bin/env bash
# Run the full pldi16 benchmark suite with timings and reference comparison.
#
# Usage:
#   tests/run_pldi16.sh [--memoize] [--timeout SECS] [--no-compare] [--variants]
#
# For each specs/test/pldi16/*.sq:
#   - runs target/release/synquid (or the binary in $SYNQUID_BIN) with
#     `--print-stats --memoize <per-benchmark flags>` (the flag table mirrors
#     `specs/test/pldi16/run_all.py`'s ALL_BENCHMARKS, the source of truth)
#   - prints exit code, wall time, and SAME/DIFF vs
#     crates/synquid/tests/snapshots/pldi16/<Name>.out
#
# Exit status: 0 iff every benchmark matches its reference snapshot (or is a
# timed-out reference-slow benchmark). `--variants` additionally runs the
# run_all.py variant loop (def/nrt/ncc/nmus) checking only exit codes.

set -u
cd "$(dirname "$0")/../../.."

BIN="${SYNQUID_BIN:-target/release/synquid}"
TIMEOUT="${TIMEOUT:-25}"
MEMOIZE=0
COMPARE=1
VARIANTS=0
for arg in "$@"; do
  case "$arg" in
    --memoize) MEMOIZE=1 ;;
    --no-compare) COMPARE=0 ;;
    --variants) VARIANTS=1 ;;
    --timeout=*) TIMEOUT="${arg#--timeout=}" ;;
  esac
done

if [ ! -x "$BIN" ]; then
  echo "build first: cargo build --release" >&2
  exit 1
fi

mkdir -p /tmp/opencode/bench

# Per-benchmark options (run_all.py ALL_BENCHMARKS; group defaults in
# GROUP_FLAGS, used by the `def` variant).
declare -A BENCH_FLAGS=(
  [List-Append]="-m=1" [List-Fold-Length]="-m=0" [List-Fold-Append]="-m=0"
  [StrictIncList-Intersect]="-f=AllArguments"
  [List-Fold-Sort]="-m=1 -a=2 -e" [List-ExtractMin]="-a=2 -m 3" [List-Split]="-m=3"
  [IncList-Merge]="-f=AllArguments" [List-MergeSort]="-a=2 -m=3" [List-QuickSort]="-a=2"
  [BST-Delete]="-e" [AVL-RotateL]="-a 2 -u" [AVL-RotateR]="-a 2 -u"
  [AVL-Balance]="-a 2 -e" [AVL-Insert]="-a 2" [AVL-ExtractMin]="-a 2"
  [AVL-Delete]="-a 2 -m 1" [RBT-BalanceL]="-m=1 -a=2" [RBT-BalanceR]="-m=1 -a=2"
  [RBT-Insert]="-m=1 -a=2" [AddressBook-Make]="-a=2" [AddressBook-Merge]="-a=2"
)
declare -A GROUP_FLAGS=(
  [List]="" [Unique list]="" [Strictly sorted list]="-f=AllArguments"
  [Sorting]="-a=2 -m=3 -f=AllArguments" [Tree]="" [BST]="" [Binary Heap]=""
  [AVL]="-a=2" [RBT]="-m=1 -a=2" [User]=""
)
declare -A BENCH_GROUP=(
  [List-Null]=List [List-Elem]=List [List-Stutter]=List [List-Replicate]=List
  [List-Append]=List [List-Concat]=List [List-Take]=List [List-Drop]=List
  [List-Delete]=List [List-Map]=List [List-Zip]=List [List-ZipWith]=List
  [List-Product]=List [List-Ith]=List [List-ElemIndex]=List [List-Snoc]=List
  [List-Reverse]=List [List-Foldr]=List [List-Fold-Length]=List
  [List-Fold-Append]=List
  [UniqueList-Insert]="Unique list" [UniqueList-Delete]="Unique list"
  [List-Nub]="Unique list" [List-Compress]="Unique list"
  [UniqueList-Range]="Unique list"
  [StrictIncList-Insert]="Strictly sorted list"
  [StrictIncList-Delete]="Strictly sorted list"
  [StrictIncList-Intersect]="Strictly sorted list"
  [IncList-Insert]=Sorting [List-InsertSort]=Sorting [List-Fold-Sort]=Sorting
  [List-ExtractMin]=Sorting [List-SelectSort]=Sorting [List-Split]=Sorting
  [IncList-Merge]=Sorting [List-MergeSort]=Sorting [List-Partition]=Sorting
  [IncList-PivotAppend]=Sorting [List-QuickSort]=Sorting
  [Tree-Elem]=Tree [Tree-Count]=Tree [Tree-ToList]=Tree
  [Tree-BalancedReplicate]=Tree
  [BST-Member]=BST [BST-Insert]=BST [BST-Delete]=BST [BST-Sort]=BST
  [BinHeap-Member]="Binary Heap" [BinHeap-Insert]="Binary Heap"
  [BinHeap-Singleton]="Binary Heap" [BinHeap-Doubleton]="Binary Heap"
  [BinHeap-Tripleton]="Binary Heap"
  [AVL-RotateL]=AVL [AVL-RotateR]=AVL [AVL-Balance]=AVL [AVL-Insert]=AVL
  [AVL-ExtractMin]=AVL [AVL-Delete]=AVL
  [RBT-BalanceL]=RBT [RBT-BalanceR]=RBT [RBT-Insert]=RBT
  [Evaluator]=User [AddressBook-Make]=User [AddressBook-Merge]=User
)

normalize() {
  sed 's/\x1b\[[0-9;]*m//g' | grep -v '^$' | grep -vE '^\((Goals|Measures|Spec size|Solution size):'
}

same=0; timeout_n=0; mismatch=0; total=0
declare -a slowest=()
declare -a details=()

for f in specs/test/pldi16/*.sq; do
  n="$(basename "$f" .sq)"
  total=$((total + 1))
  flags="${BENCH_FLAGS[$n]:-}"
  start=$(date +%s%N)
  timeout "$TIMEOUT" "$BIN" --print-stats --memoize $flags "$f" > "/tmp/opencode/bench/$n.out" 2>&1
  code=$?
  end=$(date +%s%N)
  secs=$(awk "BEGIN { printf \"%.1f\", ($end - $start) / 1e9 }")
  slowest+=("$secs $n")

  if [ "$code" = 124 ]; then
    timeout_n=$((timeout_n + 1)); status="TIMEOUT"
  elif [ "$COMPARE" = 1 ]; then
    normalize < "/tmp/opencode/bench/$n.out" > "/tmp/opencode/bench/$n.clean"
    if diff -q "/tmp/opencode/bench/$n.clean" "crates/synquid/tests/snapshots/pldi16/$n.out" > /dev/null 2>&1; then
      same=$((same + 1)); status="SAME"
    else
      mismatch=$((mismatch + 1)); status="DIFF"
    fi
  else
    if [ "$code" = 0 ]; then
      same=$((same + 1)); status="exit0"
    else
      mismatch=$((mismatch + 1)); status="exit$code"
    fi
  fi
  details+=("$status $secs $n")
done

echo "=== summary: same=$same timeout=$timeout_n mismatch=$mismatch total=$total"
echo "=== slowest:"
printf '%s\n' "${slowest[@]}" | sort -t' ' -k1 -rn | head -10 | while read -r secs n; do
  printf '  %6ss  %s\n' "$secs" "$n"
done
if [ "$mismatch" = 0 ]; then
  result=0
else
  echo "=== mismatches (DIFF):"
  printf '%s\n' "${details[@]}" | grep '^DIFF\|^exit'
  result=1
fi

if [ "$VARIANTS" = 1 ]; then
  echo "=== variants (def/nrt/ncc/nmus, exit-code check only):"
  vfail=0
  for variant in def nrt ncc nmus; do
    vtimeout=0
    for f in specs/test/pldi16/*.sq; do
      n="$(basename "$f" .sq)"
      case "$variant" in
        def) vflags="${GROUP_FLAGS[${BENCH_GROUP[$n]}]:-}" ;;
        nrt) vflags="${GROUP_FLAGS[${BENCH_GROUP[$n]}]:-} --incremental=0" ;;
        ncc) vflags="${GROUP_FLAGS[${BENCH_GROUP[$n]}]:-} --consistency=0" ;;
        nmus) vflags="${GROUP_FLAGS[${BENCH_GROUP[$n]}]:-} --bfs-solver" ;;
      esac
      timeout 120 "$BIN" --print-stats --memoize $vflags "$f" > /dev/null 2>&1
      code=$?
      if [ "$code" != 0 ]; then
        vtimeout=$((vtimeout + 1)); echo "  $variant FAIL $n (exit $code)"
      fi
    done
    echo "  $variant: $((64 - vtimeout))/64 exit 0"
    [ "$vtimeout" -gt 0 ] && vfail=1
  done
  [ "$vfail" = 0 ] || result=1
fi

exit "$result"
