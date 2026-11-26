#!/bin/bash
# Parallel scorer over a corpus.tsv-shaped list.
#
# Serial is too slow here: the unresolved tasks each burn the full 900 s
# timeout and they dominate wall time, so the 3148-pair corpus would take days.
# Workers are capped well under the core count so a task's runtime -- and so
# which tasks time out, and so the score -- stays close to what it is alone.
#
# One directory per worker is not optional: the wrapper writes fixed temp
# filenames (deagle_tmp_output and friends), so two runs sharing a directory
# read each other's output and report each other's verdicts.
#
#   correct true +2 | correct false +1 | wrong true -32 | wrong false -16
set -u

CUR=/home/gennaro/iekke-sms-eval/benchexec/lazypo-mono-cur
P=/home/gennaro/iekke-sms-eval/sv-benchmarks/c/properties
LIST=${LIST:-/home/gennaro/corpus.tsv}
BASE=${BASE:-/home/gennaro/par-run}
OUT=${OUT:-/home/gennaro/par_score.tsv}
TO=${TO:-900}
W=${W:-8}
WRAPPER=${WRAPPER:-$CUR/deagle}

rm -rf "$BASE"; mkdir -p "$BASE"

worker() { # id
  # Two statements, not one: bash expands every word of a `local` before it
  # performs any of the assignments, so `local id=$1 d="$BASE/w$id"` reads an
  # unset `id` and, under `set -u`, kills the worker before it runs a thing.
  local id=$1
  local d="$BASE/w$id"
  local prop prog exp dm b arch s e v k pts
  mkdir -p "$d"
  cp -p "$WRAPPER" "$d/deagle"
  cp -p "$CUR/output_unwind_rounds.csv" "$CUR/iekke_exe" "$d/"
  chmod +x "$d/deagle"

  awk -v id="$id" -v w="$W" 'NR % w == id' "$LIST" | \
  while IFS=$'\t' read -r prop prog exp dm; do
    [ -f "$prog" ] || continue
    b=$(basename "$prog"); b=${b%.*}
    arch=--32; [ "$dm" = LP64 ] && arch=--64

    s=$(date +%s%N)
    v=$(cd "$d" && timeout -k 5 "$TO" ./deagle "$P/$prop.prp" "$prog" "$arch" 2>&1 | tail -1)
    e=$(date +%s%N)

    if   [ "$v" = SUCCESSFUL ] && [ "$exp" = true  ]; then k=T;           pts=2
    elif [ "$v" = FAILED     ] && [ "$exp" = false ]; then k=T;           pts=1
    elif [ "$v" = SUCCESSFUL ] && [ "$exp" = false ]; then k=WRONG_TRUE;  pts=-32
    elif [ "$v" = FAILED     ] && [ "$exp" = true  ]; then k=WRONG_FALSE; pts=-16
    else                                                   k=U;           pts=0
    fi

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$prop" "$b" "$exp" "${v:-none}" "$k" "$pts" "$(( (e-s)/1000000 ))" \
      >> "$BASE/part.$id"
  done
}

for i in $(seq 0 $((W-1))); do worker "$i" & done
wait

printf 'property\tbenchmark\texpected\tverdict\tclass\tpoints\tms\n' > "$OUT"
cat "$BASE"/part.* >> "$OUT"

awk -F'\t' 'NR>1{n++; c[$5]++; pts+=$6; if($5 ~ /^WRONG/) lost -= $6}
  END{
    printf "  %d task-property pairs\n", n
    printf "  correct %d   wrong-true %d   wrong-false %d   unknown %d\n", c["T"]+0, c["WRONG_TRUE"]+0, c["WRONG_FALSE"]+0, c["U"]+0
    printf "  SCORE %d   (thrown away by wrong answers: %d)\n", pts, lost+0
  }' "$OUT"
echo "  --- losses, worst first ---"
awk -F'\t' 'NR>1 && $5 ~ /^WRONG/{printf "  %6d  %-16s %-46s expected=%-6s got=%s\n", $6, $1, $2, $3, $4}' "$OUT" | sort -n
echo PAR_RUN_DONE
