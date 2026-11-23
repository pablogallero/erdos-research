#!/bin/sh
# ω = 6 search (Erdős #470). See notes/omega6-job.md.
# Since 2026-11-22 the search runs by itself in pgal's StatefulSet `owf` (2 workers, `run-root.sh worker`,
# erdos-research #58). A research session NEVER runs owf and NEVER launches anything; it only runs:
#
#   sh scripts/owf-queue.sh read          READ-ONLY: progress from $OWF_STATE (default /lean/state/owf/v2) into
#                                         notes/data/ (omega6-v2.ck.gz, omega6-v2-roots.txt), per-worker report,
#                                         and an ALERT (exit 5) if a root is FOUND, CLOSED or ERROR
#
# Legacy Kubernetes-Jobs commands (sessions have no API access; kept for reference only):
#   sh scripts/owf-queue.sh status        Jobs, their state and last progress line; quota usage
#   sh scripts/owf-queue.sh export        the same copy as `read`, through a reader pod
#   sh scripts/owf-queue.sh launch-next   DISABLED (the StatefulSet workers claim roots themselves)
#   sh scripts/owf-queue.sh render-quota  print deploy/owf/quota.yaml filled in (for Pablo to review/apply)
#
# Generation v2 (2026-11-23): the workers restarted from an EMPTY checkpoint at 3^1 with the parity fix, in the
# subdirectory v2 of the volume. The generation-1 data (buggy code) is in notes/data/*-con-fallo.* and
# notes/omega6-invalidated.md; this script never reads or writes it.
#
# Environment: OWF_NAMESPACE (required), OWF_IMAGE and OWF_PVC (required for export/launch-next),
# OWF_SUBPATH (default owf), OWF_MAX (1 or 2, default 2), OWF_FIRST (first root of the queue, default 15),
# OWF_SESSION_SA (render-quota only), KUBECTL (default kubectl).
#
# Exit codes: 0 ok; 2 usage/config; 3 kubectl error; 4 export failed validation; 5 queue stopped
# (a root reported FOUND/CLOSED/ERROR, a Job failed, or an outcome is unknown); 6 launch lock held;
# 7 cluster cap missing (PriorityClass/ResourceQuota owf-compute not applied); 8 $OWF_STATE not readable;
# 9 launch-next disabled.
set -u
HERE=$(cd "$(dirname "$0")/.." && pwd)
KUBECTL=${KUBECTL:-kubectl}
OWF_SUBPATH=${OWF_SUBPATH:-owf}
OWF_MAX=${OWF_MAX:-2}
OWF_FIRST=${OWF_FIRST:-1}
FROZEN=0       # generation v2 has no seed: the whole volume checkpoint is the tail
DATA=$HERE/notes/data
CKGZ=$DATA/omega6-v2.ck.gz
ROOTS_FILE=$DATA/omega6-v2-roots.txt
MAXGZ=900000   # stay well below the 1 MB per-file limit of the repo

die() { echo "owf-queue: $1" >&2; exit "${2:-2}"; }
need() { eval "v=\${$1:-}"; [ -n "$v" ] || die "set $1"; case "$v" in *'|'*|*'
'*) die "$1 contains an invalid character" ;; esac; }

case "$OWF_MAX" in 1|2) ;; *) die "OWF_MAX must be 1 or 2 (the node has 2 cores), got '$OWF_MAX'" ;; esac
case "$OWF_FIRST" in ''|*[!0-9]*) die "OWF_FIRST must be a positive integer" ;; esac

k() { "$KUBECTL" -n "$OWF_NAMESPACE" "$@"; }

render() { # FILE: fill ${VAR} placeholders (no envsubst dependency)
  sed -e "s|\${ROOT}|${ROOT:-}|g" -e "s|\${OWF_NAMESPACE}|${OWF_NAMESPACE:-}|g" \
      -e "s|\${OWF_IMAGE}|${OWF_IMAGE:-}|g" -e "s|\${OWF_PVC}|${OWF_PVC:-}|g" \
      -e "s|\${OWF_SUBPATH}|${OWF_SUBPATH:-}|g" -e "s|\${POD_NAME}|${POD_NAME:-}|g" \
      -e "s|\${OWF_SESSION_SA}|${OWF_SESSION_SA:-}|g" "$1"
}

# One line per owf Job: "E STATE" with STATE in active | complete | failed.
jobs_state() {
  k get jobs -l app=owf -o jsonpath='{range .items[*]}{.metadata.name}{"|"}{.status.conditions[?(@.status=="True")].type}{"\n"}{end}' \
    > "$TMP/jobs" || die "kubectl get jobs failed" 3
  while IFS='|' read -r name conds; do
    E=${name#owf-root-}
    case "$E" in ''|*[!0-9]*) continue ;; esac
    case " $conds " in
      *" Failed "*) echo "$E failed" ;;
      *" Complete "*) echo "$E complete" ;;
      *) echo "$E active" ;;
    esac
  done < "$TMP/jobs" | sort -n
}

# Outcome of a finished root: the pod's termination message ("DONE 15"), else omega6-roots.txt from the last export.
outcome() { # E
  m=$(awk -F'|' -v n="owf-root-$1" '$1 == n && $2 != "" { print $2 }' "$TMP/msgs" | tail -n 1)
  case "$m" in "DONE $1"|"FOUND $1"|"CLOSED $1") echo "${m% *}"; return ;; esac
  [ -f "$ROOTS_FILE" ] && awk -v e="$1" '$1 == e { o = $2 } END { if (o != "") print o }' "$ROOTS_FILE"
}

pod_msgs() {
  k get pods -l app=owf -o jsonpath='{range .items[*]}{.metadata.ownerReferences[0].name}{"|"}{.status.containerStatuses[0].state.terminated.message}{"\n"}{end}' \
    > "$TMP/msgs" || die "kubectl get pods failed" 3
}

cmd_status() {
  need OWF_NAMESPACE
  jobs_state > "$TMP/st"; pod_msgs
  echo "Jobs (max $OWF_MAX running):"
  [ -s "$TMP/st" ] || echo "  none"
  while read -r E s; do
    o=""; [ "$s" = complete ] && o=" -> $(outcome "$E")"
    echo "  3^$E: $s$o"
    if [ "$s" = active ]; then
      k logs "job/owf-root-$E" --tail=1 2>/dev/null | sed 's/^/      last: /'
    fi
  done < "$TMP/st"
  echo "Quota owf-compute (used/hard pods):"
  k get resourcequota owf-compute -o jsonpath='  {.status.used.pods}/{.status.hard.pods}{"\n"}' 2>/dev/null \
    || echo "  NOT APPLIED (deploy/owf/quota.yaml needs Pablo's approval)"
}

cmd_launch_next() {
  need OWF_NAMESPACE; need OWF_IMAGE; need OWF_PVC
  # Hard cap first: without it a race between two sessions could start a third process.
  k get priorityclass owf-compute -o name > /dev/null 2>&1 \
    || die "PriorityClass owf-compute missing: apply deploy/owf/quota.yaml (needs approval) before launching" 7
  qp=$(k get resourcequota owf-compute -o jsonpath='{.spec.hard.pods}|{.spec.scopeSelector.matchExpressions[0].values[0]}' 2>/dev/null) \
    || die "ResourceQuota owf-compute missing: apply deploy/owf/quota.yaml (needs approval) before launching" 7
  case "$qp" in 1\|owf-compute|2\|owf-compute) ;; *) die "ResourceQuota owf-compute is not 'pods <= 2 scoped to owf-compute' ($qp)" 7 ;; esac

  # Mutual exclusion between sessions (creating an object is atomic).
  k create configmap owf-launch-lock --from-literal=holder="$(hostname 2>/dev/null)-$$" > /dev/null 2>&1 \
    || die "another launch holds configmap owf-launch-lock; if it is stale (no session launching), delete it" 6
  LOCKED=1

  jobs_state > "$TMP/st"; pod_msgs
  active=0
  while read -r E s; do
    case "$s" in
      failed) die "Job owf-root-$E failed after its restarts: look at its logs (kubectl logs job/owf-root-$E) before going on" 5 ;;
      active) active=$((active + 1)) ;;
      complete)
        o=$(outcome "$E")
        case "$o" in
          DONE) ;;
          FOUND) die "root 3^$E reported FOUND (owf returned False): undecided families or a candidate. Queue stopped for a human" 5 ;;
          CLOSED) die "root 3^$E reported CLOSED: the search over powers of 3 closed. Queue stopped; check and record it" 5 ;;
          *) die "root 3^$E finished but its outcome is unknown: run export and check notes/data/omega6-v2-roots.txt" 5 ;;
        esac ;;
    esac
  done < "$TMP/st"
  free=$((OWF_MAX - active))
  echo "running: $active, max: $OWF_MAX, free slots: $free"
  E=$OWF_FIRST
  while [ "$free" -gt 0 ]; do
    while awk -v e="$E" '$1 == e { f = 1 } END { exit !f }' "$TMP/st"; do E=$((E + 1)); done
    ROOT=$E
    render "$HERE/deploy/owf/job.yaml" | k create -f - || die "could not create Job owf-root-$E" 3
    echo "launched owf-root-$E (root 3^$E)"
    echo "$E active" >> "$TMP/st"
    free=$((free - 1))
  done
  [ "$active" -lt "$OWF_MAX" ] || echo "no free slot: nothing launched"
}

cmd_export() {
  need OWF_NAMESPACE; need OWF_IMAGE; need OWF_PVC
  br=$(git -C "$HERE" symbolic-ref --short HEAD 2>/dev/null || echo "")
  case "$br" in main|master) die "on branch $br: export only on a working branch (the commit goes to a PR, never to main)" ;; esac
  POD_NAME=owf-export-$(date -u +%Y%m%d%H%M%S)-$$
  render "$HERE/deploy/owf/export-pod.yaml" | k create -f - > /dev/null || die "could not create export pod" 3
  EXPORT_POD=$POD_NAME
  i=0; phase=""
  while [ $i -lt 150 ]; do
    phase=$(k get pod "$POD_NAME" -o jsonpath='{.status.phase}' 2>/dev/null)
    case "$phase" in Succeeded|Failed) break ;; esac
    i=$((i + 1)); sleep 2
  done
  k logs "$POD_NAME" > "$TMP/dump" 2>/dev/null || die "could not read logs of $POD_NAME" 3
  [ "$phase" = Succeeded ] || { sed 's/^/  /' "$TMP/dump" >&2; die "export pod ended in phase '$phase'" 4; }
  parse_dump "$TMP/dump"
}

# Validate a dump from `run-root.sh export` and write notes/data/omega6-v2.ck.gz and omega6-v2-roots.txt.
parse_dump() {
  d=$1
  [ "$(head -n 1 "$d")" = "OWF-EXPORT 1" ] || die "not an export dump" 4
  want=$(printf '' | sha256sum | cut -d' ' -f1)   # FROZEN = 0: empty prefix
  got=$(awk '$1 == "frozen-sha256" { print $2 }' "$d")
  [ "$got" = "$want" ] || die "frozen-prefix hash of the dump is not the empty one ($got): is it a generation-1 dump?" 4
  sed -n '/^BEGIN-TAIL$/,/^END-TAIL$/p' "$d" | sed '1d;$d' | base64 -d 2>/dev/null | gzip -dc > "$TMP/tail.raw" 2>/dev/null \
    || die "tail is not valid gzip+base64" 4
  sed -n '/^BEGIN-ROOTS$/,/^END-ROOTS$/p' "$d" | sed '1d;$d' > "$TMP/roots"
  grep -Ev '^[0-9]+ (DONE|FOUND|CLOSED|ERROR) [0-9TZ:-]+( |$)' "$TMP/roots" > "$TMP/badroots" && die "malformed line in the volume's omega6-roots.txt: $(head -n 1 "$TMP/badroots")" 4
  # Keep only well-formed checkpoint keys, first occurrence only, not already in the frozen part.
  : > "$TMP/frozen"
  re='^\(\[(\([0-9]+, [0-9]+\)(, \([0-9]+, [0-9]+\))*)?\], [0-9]+, [0-9]+, [0-9]+, [0-9]+\)$'
  # (the frozen file is read in BEGIN: with an empty file, the usual NR == FNR idiom would swallow stdin)
  grep -E "$re" "$TMP/tail.raw" | awk -v F="$TMP/frozen" 'BEGIN { while ((getline l < F) > 0) seen[l] = 1 } !seen[$0]++' > "$TMP/tail"
  dropped=$(( $(wc -l < "$TMP/tail.raw") - $(wc -l < "$TMP/tail") ))
  # Append-only: the committed omega6-v2 must be an exact prefix of the new tail.
  old=0
  if [ -f "$CKGZ" ]; then
    zcat "$CKGZ" > "$TMP/old"
    old=$(wc -l < "$TMP/old")
    head -n "$old" "$TMP/tail" | cmp -s - "$TMP/old" \
      || die "the committed omega6-v2.ck.gz ($old lines) is not a prefix of the volume's tail: refusing to overwrite" 4
  fi
  gzip -9 -n -c "$TMP/tail" > "$TMP/tail.gz"
  size=$(wc -c < "$TMP/tail.gz")
  [ "$size" -lt "$MAXGZ" ] || die "omega6-v2.ck.gz would be $size bytes (> $MAXGZ): split it (freeze + a second file) first" 4
  cp "$TMP/tail.gz" "$CKGZ"
  cp "$TMP/roots" "$ROOTS_FILE"
  echo "volume: $(awk '$1 == "lines" { print $2 }' "$d") lines; frozen prefix OK"
  echo "omega6-v2.ck.gz: $old -> $(wc -l < "$TMP/tail") lines ($size bytes); dropped $dropped partial/duplicate/garbage lines"
  echo "roots:"; sed 's/^/  /' "$ROOTS_FILE"
  [ -s "$ROOTS_FILE" ] || echo "  (none finished yet)"
  echo "Now commit notes/data/omega6-v2.ck.gz and notes/data/omega6-v2-roots.txt on the working branch (PR, never main)."
}

# Read-only copy of the StatefulSet workers' progress. Never writes to $OWF_STATE and never starts a process there.
cmd_read() {
  S=${OWF_STATE:-/lean/state/owf/v2}
  [ -d "$S" ] && [ -r "$S/omega6.ck" ] && [ -s "$S/omega6.ck" ] \
    || die "cannot read $S/omega6.ck: stop and tell Pablo (do not improvise, do not run owf)" 8
  br=$(git -C "$HERE" symbolic-ref --short HEAD 2>/dev/null || echo "")
  case "$br" in main|master) die "on branch $br: read only on a working branch (the commit goes to a PR, never to main)" ;; esac
  # Same dump format as `run-root.sh export`. A worker may be mid-line: `wc -l` + `head -n` keep complete lines only.
  n=$(wc -l < "$S/omega6.ck")
  {
    echo "OWF-EXPORT 1"
    echo "lines $n"
    echo "frozen-sha256 $(head -n "$FROZEN" "$S/omega6.ck" | sha256sum | cut -d' ' -f1)"
    echo "BEGIN-ROOTS"
    [ -r "$S/omega6-roots.txt" ] && cat "$S/omega6-roots.txt"
    echo "END-ROOTS"
    echo "BEGIN-TAIL"
    head -n "$n" "$S/omega6.ck" | tail -n +"$((FROZEN + 1))" | gzip -9 -c | base64
    echo "END-TAIL"
  } > "$TMP/dump"
  parse_dump "$TMP/dump"
  # Per-worker report. The log contents are data: only matched against fixed patterns, never executed.
  echo "workers (claims.txt: root worker):"
  if [ -r "$S/claims.txt" ] && [ -s "$S/claims.txt" ]; then
    awk '{ last[$2] = $1 } END { for (w in last) print w, last[w] }' "$S/claims.txt" | sort | while read -r w E; do
      o=$(awk -v e="$E" '$1 == e { o = $2 } END { print o }' "$ROOTS_FILE")
      p=$(grep '^progress ' "$S/logs/root-$E.log" 2>/dev/null | tail -n 1 | cut -c1-160)
      echo "  $w: root 3^$E ${o:-running}${p:+; last: $p}"
    done
  else
    echo "  none (no claims yet)"
  fi
  # Alerts: an outcome recorded by a worker, or an owf result line in a log whose root has no outcome yet.
  alerts=$(awk '$2 == "FOUND" || $2 == "CLOSED" || $2 == "ERROR" { print "  root 3^" $1 ": " $2 }' "$ROOTS_FILE")
  for f in "$S"/logs/root-*.log; do
    [ -r "$f" ] || continue
    E=${f##*/root-}; E=${E%.log}
    awk -v e="$E" '$1 == e { f = 1 } END { exit !f }' "$ROOTS_FILE" && continue
    grep -Eq '^6 (False|True) ' "$f" && alerts="$alerts
  root 3^$E: owf result line in logs/root-$E.log, no outcome recorded yet"
  done
  alerts=$(printf '%s\n' "$alerts" | sed '/^$/d')
  if [ -n "$alerts" ]; then
    echo "ALERT (tell Pablo; the workers have stopped taking roots):"
    printf '%s\n' "$alerts"
    exit 5
  fi
  echo "no FOUND / CLOSED / ERROR"
}

cleanup() {
  [ -n "${LOCKED:-}" ] && k delete configmap owf-launch-lock > /dev/null 2>&1
  [ -n "${EXPORT_POD:-}" ] && k delete pod "$EXPORT_POD" --wait=false > /dev/null 2>&1
  rm -rf "$TMP"
}
TMP=$(mktemp -d)
trap cleanup EXIT
trap 'exit 130' INT TERM

case "${1:-}" in
  status) cmd_status ;;
  export) cmd_export ;;
  read) cmd_read ;;
  launch-next) die "launch-next is disabled: the search runs by itself in pgal's StatefulSet owf (2 workers). Use 'read'" 9 ;;
  render-quota) need OWF_NAMESPACE; need OWF_SESSION_SA; render "$HERE/deploy/owf/quota.yaml" ;;
  *) die "usage: sh scripts/owf-queue.sh read | status | export | render-quota" ;;
esac
