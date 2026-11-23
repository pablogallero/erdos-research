#!/bin/sh
# Entrypoint of the ω = 6 search image (notes/omega6-job.md). Two modes:
#
#   run-root.sh run E   search the root 3^E (START3=E STOP3=E) on the shared checkpoint in the volume.
#                       Exit 0 = the root has an outcome (DONE, FOUND or CLOSED), written to
#                       $OWF_DATA/omega6-roots.txt and to the pod's termination message.
#                       Exit != 0 = crash or unexpected output: the Job restarts the container
#                       (restartPolicy OnFailure) and owf resumes from the checkpoint.
#   run-root.sh export  read-only dump of the progress for `scripts/owf-queue.sh export`.
#   run-root.sh worker  long-running queue worker (one per StatefulSet pod, at most 2): claims the next
#                       root under flock, runs it, records the outcome, takes the next one. No Kubernetes
#                       API needed: claims and outcomes live in the volume (claims.txt, omega6-roots.txt).
#                       Stops taking roots after a FOUND, CLOSED or ERROR outcome until a person looks.
#
# Volume layout ($OWF_DATA/$OWF_GEN, default /data/v2):
#   Generation v2 (2026-11-23) = search with the star-loop parity fix, started from an EMPTY checkpoint at 3^1.
#   The files of generation 1 (top level of $OWF_DATA: omega6.ck, omega6-roots.txt, claims.txt, logs/) were made
#   by the buggy code: they are left untouched there, marked "con fallo" in notes/omega6-invalidated.md, and
#   are never read by this script.
#   omega6.ck          plain checkpoint shared by all roots (append-only; one line per subtree decided True)
#   omega6-roots.txt   one line per finished root: "E OUTCOME UTC-date stats"
#   logs/root-E.log    owf stdout+stderr of every attempt
#   .lock              flock for seeding and for omega6-roots.txt
set -u
DATA=${OWF_DATA:-/data}/${OWF_GEN:-v2}
OWF=${OWF_BIN:-/usr/local/bin/owf}
K=${OWF_K:-6}
FROZEN=0       # no seed since generation v2: the whole checkpoint is the tail
CK=$DATA/omega6.ck
ROOTS=$DATA/omega6-roots.txt
LOCK=$DATA/.lock
TERM_MSG=${OWF_TERM_MSG:-/dev/termination-log}

die() { echo "run-root: $*" >&2; exit "${2:-64}"; }

seed() {
  # No seed (generation v2): the checkpoint starts empty; afterwards the volume is the source of truth.
  # The old seed (notes/data/omega6.ck.gz + omega6-2.ck.gz) came from the buggy code and was removed.
  mkdir -p "$DATA/logs" || die "cannot write $DATA" 65
  (
    flock 9 || exit 65
    if [ ! -e "$CK" ]; then
      : > "$CK" || exit 65
      echo "run-root: started an empty checkpoint $CK" >&2
    fi
    touch "$ROOTS"
  ) 9>>"$LOCK" || die "seeding failed" 65
}

record() { # E OUTCOME STATS
  ( flock 9; echo "$1 $2 $(date -u +%Y-%m-%dT%H:%M:%SZ) $3" >> "$ROOTS" ) 9>>"$LOCK"
  printf '%s %s' "$2" "$1" > "$TERM_MSG" 2>/dev/null || true
}

run() {
  E=$1
  case "$E" in ''|*[!0-9]*) die "root exponent must be a positive integer, got '$E'" ;; esac
  [ "$E" -ge 1 ] || die "root exponent must be >= 1"
  seed
  # Idempotent: a root that already has an outcome is not searched again (e.g. a Job recreated by hand).
  prev=$(awk -v e="$E" '$1 == e { print $2; exit }' "$ROOTS")
  if [ -n "$prev" ]; then
    echo "run-root: root 3^$E already recorded as $prev" >&2
    printf '%s %s' "$prev" "$E" > "$TERM_MSG" 2>/dev/null || true
    exit 0
  fi
  LOG=$DATA/logs/root-$E.log
  OUT=$(mktemp)
  echo "=== attempt $(date -u +%Y-%m-%dT%H:%M:%SZ) START3=$E STOP3=$E" >> "$LOG"
  # stderr (progress lines) goes to the log in the volume and to the container log (kubectl logs);
  # stdout is kept to classify the outcome.
  FIFO=$(mktemp -u)
  mkfifo "$FIFO" || die "mkfifo failed" 65
  tee -a "$LOG" < "$FIFO" >&2 &
  TEE=$!
  START3=$E STOP3=$E nice -n 19 "$OWF" "$K" "$CK" > "$OUT" 2> "$FIFO"
  rc=$?
  wait "$TEE"
  rm -f "$FIFO"
  cat "$OUT" >> "$LOG"
  cat "$OUT"
  if [ "$rc" -ne 0 ]; then
    echo "run-root: owf exited $rc; the Job restarts it and it resumes from the checkpoint" >&2
    rm -f "$OUT"; exit "$rc"
  fi
  first=$(head -n 1 "$OUT")
  case "$first" in
    "STOP3 reached: 3^$E done "*)
      record "$E" DONE "$(printf '%s' "$first" | sed 's/^STOP3 reached: 3^[0-9]* done //')" ;;
    "$K False "*)
      # owf returned False: some family was left undecided (nostruct/star) or a candidate was found.
      # Not retried (it would give the same answer); the queue stops until a person looks at the log.
      record "$E" FOUND "$(printf '%s' "$first" | sed "s/^$K False //") failures:$(tail -n +2 "$OUT" | tr '\n' ';')" ;;
    "$K True "*)
      # The region subtree of 3^E closed the loop over powers of 3 and the rest of the search was True:
      # no further root is needed. The queue stops so that a person checks it.
      record "$E" CLOSED "$(printf '%s' "$first" | sed "s/^$K True //")" ;;
    *)
      echo "run-root: unexpected owf output: $first" >&2
      rm -f "$OUT"; exit 70 ;;
  esac
  rm -f "$OUT"
  exit 0
}

worker() {
  # Queue worker (pgal deploy/owf.yaml: StatefulSet owf, 2 replicas). OWF_WORKER is the pod name, stable
  # across restarts, so a restarted worker resumes its own unfinished root first.
  ME=${OWF_WORKER:-$(hostname)}
  FIRST=${OWF_FIRST:-1}
  MAXFAIL=${OWF_MAXFAIL:-5}
  CLAIMS=$DATA/claims.txt
  seed
  while :; do
    if awk '$2 == "FOUND" || $2 == "CLOSED" || $2 == "ERROR" { f = 1 } END { exit !f }' "$ROOTS"; then
      echo "run-root: queue stopped (FOUND/CLOSED/ERROR in $ROOTS); waiting for a person" >&2
      sleep 3600; continue
    fi
    E=$( (
      flock 9 || exit 65
      touch "$CLAIMS"
      for e in $(awk -v me="$ME" '$2 == me { print $1 }' "$CLAIMS"); do
        awk -v e="$e" '$1 == e { f = 1 } END { exit !f }' "$ROOTS" || { echo "$e"; exit 0; }
      done
      e=$FIRST
      while awk -v e="$e" '$1 == e { f = 1 } END { exit !f }' "$ROOTS" "$CLAIMS"; do e=$((e + 1)); done
      echo "$e $ME" >> "$CLAIMS"
      echo "$e"
    ) 9>>"$LOCK" ) || die "claiming a root failed" 65
    fails=0
    while :; do
      ( run "$E" ) && break
      fails=$((fails + 1))
      if [ "$fails" -ge "$MAXFAIL" ]; then
        record "$E" ERROR "owf failed $fails times in a row; see logs/root-$E.log"
        break
      fi
      echo "run-root: root 3^$E failed ($fails/$MAXFAIL); retrying in 60 s from the checkpoint" >&2
      sleep 60
    done
  done
}

export_dump() {
  # Read-only. Prints the frozen-prefix hash, the roots file and the tail (complete lines only) as gzip+base64.
  [ -e "$CK" ] || die "no checkpoint at $CK" 66
  echo "OWF-EXPORT 1"
  echo "lines $(wc -l < "$CK")"
  echo "frozen-sha256 $(head -n "$FROZEN" "$CK" | sha256sum | cut -d' ' -f1)"
  echo "BEGIN-ROOTS"
  cat "$ROOTS" 2>/dev/null
  echo "END-ROOTS"
  echo "BEGIN-TAIL"
  # A writer may be in the middle of a line: `wc -l` counts only newline-terminated lines, and
  # `head -n` stops there, so a half-written last line is never exported.
  n=$(wc -l < "$CK")
  head -n "$n" "$CK" | tail -n +"$((FROZEN + 1))" | gzip -9 -c | base64
  echo "END-TAIL"
}

case "${1:-}" in
  run) run "${2:-${OWF_ROOT:-}}" ;;
  export) export_dump ;;
  worker) worker ;;
  *) die "usage: run-root.sh run E | run-root.sh export | run-root.sh worker" ;;
esac
