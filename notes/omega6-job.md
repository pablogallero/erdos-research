# ω = 6 search as Kubernetes Jobs (since 2026-11-22)

The long search for Erdős #470 (odd weird numbers with ω = 6, `scripts/odd_weird_family.c`) no longer
runs inside research sessions. Each root 3^E runs as its own Kubernetes Job, continuously, with its
checkpoint in the persistent volume. There are **never more than 2** search processes at once,
because the node has 2 cores and 12 GB.

**A session never runs `owf`, `odd_weird_family.py`, `START3=…`, `STOP3=…` or `ROOTTEST=…`.**
Every older "resume START3=… under timeout" line in `notes/erdos-470.md` and in the session notes is
history only.

## Pieces

| File | What it is |
|---|---|
| `deploy/owf/Dockerfile` | Image: the C binary (built and smoke-tested with K = 4), `run-root.sh`, and the checkpoint seed (`omega6.ck.gz` + `omega6-2.ck.gz`). Build from the repo root, for linux/arm64. |
| `deploy/owf/run-root.sh` | Entrypoint. `run E` searches root 3^E on the shared checkpoint in the volume; `export` prints a read-only dump. |
| `deploy/owf/job.yaml` | Job template, one per root: name `owf-root-E` (deterministic, so a root cannot be launched twice), `restartPolicy: OnFailure`, `backoffLimit: 10`, PriorityClass `owf-compute`, PVC mounted at `/data` (subPath `owf`). |
| `deploy/owf/export-pod.yaml` | Short-lived pod that mounts the volume **read-only** and prints the dump. It works when no Job is running, and needs no `kubectl exec`. |
| `deploy/owf/quota.yaml` | **Prepared, not applied (needs Pablo's approval).** PriorityClass `owf-compute`, ResourceQuota `owf-compute` (`pods: 2`, scoped to that class), Role/RoleBinding for the session's ServiceAccount, and read access to the PriorityClass. |
| `scripts/owf-queue.sh` | The only thing a session runs: `status`, `export`, `launch-next` (plus `render-quota` for Pablo). |
| `notes/data/omega6-roots.txt` | Written by `export`: one line per finished root (`E OUTCOME date stats`). |

## Volume layout (`/data` in the pod)

- `omega6.ck`: the plain checkpoint, shared by all roots. It is append-only, with one line per subtree decided True. The first
  Job seeds it from the image under `flock`, and only if it is empty. From then on the volume is the source of truth.
  Two Jobs append to it concurrently, which is how two workers have always shared it: `owf` reloads it at depth ≤ 2,
  and every line is a separate flushed `O_APPEND` write.
- `omega6-roots.txt`: the outcome of each root. `logs/root-E.log`: `owf` output of every attempt, including progress lines.

## Outcome of a root (`run-root.sh run E`)

| `owf` result | Recorded as | Job | Queue |
|---|---|---|---|
| `STOP3 reached: 3^E done` | DONE | Complete | continues |
| `6 False …`: some family left undecided (`nostruct`/`star`) or a candidate. `owf` exits 0 here | FOUND (with the failure lines) | Complete, **no retry** (it would give the same answer) | **stops** until a person looks |
| `6 True …` without STOP3: the region subtree of 3^E closed the loop over powers of 3, so the whole search finished | CLOSED | Complete | **stops**, so the result gets checked and written up |
| crash, OOM, `exit(2)` (internal assertion), node restart | — | container restarted (≤ 10 times), resumes from the checkpoint | waits |
| any other output | — (exit 70) | restarted like a crash | waits |

The outcome also goes to the pod's termination message (`DONE 15`), which is how `launch-next` reads it.
If the pod is gone, `launch-next` falls back to `notes/data/omega6-roots.txt` from the last export.

## What a research session does (and only this)

```sh
export OWF_NAMESPACE=… OWF_IMAGE=… OWF_PVC=…     # values on board card #143
sh scripts/owf-queue.sh status        # 1. report: Jobs, state, last progress line, quota use
sh scripts/owf-queue.sh export        # 2. progress -> notes/data/omega6-2.ck.gz + omega6-roots.txt
#    then commit those two files on the working branch (PGAL opens the PR; never main)
sh scripts/owf-queue.sh launch-next   # 3. next root(s), only into free slots
```

- `export` checks that the volume's first 36729 lines hash to the frozen `omega6.ck.gz`. It keeps only complete,
  well-formed, first-occurrence keys, requires the committed `omega6-2.ck.gz` to be an exact prefix of the new one
  (append-only), refuses a `.gz` ≥ 900 KB (then freeze `omega6-2` and add `omega6-3`, which is a code change), and refuses to run on
  `main`/`master`.
- `launch-next` refuses to launch (exit 7) unless both the PriorityClass and the ResourceQuota `owf-compute` exist with
  `pods ≤ 2`. It stops the queue (exit 5) on FOUND, CLOSED, a Failed Job or an unknown outcome. It takes a lock
  (ConfigMap `owf-launch-lock`, whose creation is atomic) so that two sessions cannot launch at the same time. It counts Jobs
  that are not Complete or Failed and fills only `OWF_MAX − active` slots (`OWF_MAX` is 1 or 2, default 2). The next
  root is the smallest E ≥ `OWF_FIRST` (default 15) that has no Job yet.
- **The limit of 2 is enforced at three levels:** the script's count, the launch lock, and the ResourceQuota. The quota is the hard
  cap: the API server rejects a third `owf-compute` pod. The export pod is not in that class, takes no compute slot and
  lives a few seconds.
- A Failed Job is never relaunched automatically. A person reads `kubectl logs job/owf-root-E` and the volume log, then
  deletes the Job (`kubectl delete job owf-root-E`, which the Role allows) for it to be relaunched. `run-root.sh` skips a
  root that already has an outcome, so a relaunch is harmless.

## Resources

`owf` is single-threaded. Its measured peak RSS (session 51, root 3^15, full checkpoint loaded) was ≈ 31–37 MB,
mostly the hash set of checkpoint keys, which grows by well under 1 MB per root. The Job therefore asks for
`requests 500m / 256Mi` and gets `limits 1 CPU / 2Gi`. The task suggested ~5 GiB per process. 2 Gi is still ~50×
the measured peak, and two processes at 5 GiB would reserve 10 of the 12 GB, which would starve Lean builds (5.2 GB
peak, session 10) on the same node. If a pod is ever OOM-killed, the restart resumes from the checkpoint, and the limit can be raised.

## Deployment (Pablo; nothing has been applied to the cluster)

1. Build and push the image for arm64, from the repo root: `docker buildx build --platform linux/arm64 -f deploy/owf/Dockerfile
   -t <registry>/erdos-owf:<sha> --push .`
2. Choose the namespace, the existing PVC and the session's ServiceAccount, then review and apply the cap:
   `OWF_NAMESPACE=… OWF_SESSION_SA=… sh scripts/owf-queue.sh render-quota | kubectl apply -f -`.
3. Then the next session runs `launch-next`, which starts 3^15 and 3^16 (`OWF_FIRST=15`; roots 1..14 are finished).

## Starting state

- Roots v_3 ∈ {1..14} are finished (sessions 13–48).
- 3^15 has 5^b done for b ≤ 24, and 3^16 has b ≤ 25 (session 50; those lines are in `notes/data/omega6-2.ck.gz`, so the seed
  carries them and nothing is redone).
- `roottest50.ck.gz` (ROOTTEST=50) stays parked. It is not part of the queue.
