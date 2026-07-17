# Lattice pipeline — agent notes

Context an agent won't get from the code or git history. Current as of 2026-07-17.

## Where the work runs
- **lovelace** (128 physical cores × 2 threads, 2 TB RAM) runs the census; **hensel** (128 cores, 1 TB) is usually busy with someone else's work.
- SSH to both is flaky: use script files + `setsid`, and `ssh -o ServerAliveInterval=5`. Don't kill the user's own long-running Magma/sage sessions — only processes you started.
- The census: `run_all.py -r 1 -R 32 -D 32768 -j 96 --skip-enumerate-genera --skip-embeddings ...`. Progress is in `~/census.log` on lovelace; the progress bar uses `\r`, so `tr '\r' '\n' < ~/census.log | grep -oE '[0-9.]+% \([0-9]+/[0-9]+\)' | tail -1`.

## Pipeline shape (what produces a "representative")
- The **listing** stage (`genus.py:create_genus_entry`, calls `genus_symbol.representative()` at ~`genus.py:623`) is where a single lattice is built from a genus symbol and stored as `rep`. This is Sage, and it's a major cost (~per-genus dominated).
- The **fill/enumerate** stages enumerate the *entire* genus (all `h` classes) via Magma's `GenusRepresentativesOrth` (orbit method, `genus_reps.m`), seeded from the stored `rep`. This is NOT single-representative production — don't benchmark Sage `representative()` against Magma `GenusRepresentatives` as if they're the same task.

## Magma gotchas (each cost real debugging time)
- **`Alarm()` is an uncatchable SIGALRM** (exit 142) and never fires inside uninterruptible C builtins (`ShortVectors`, `AutomorphismGroupFaster`, canonical forms, genus enumeration). Bounding those needs the **`TimeoutCall(... : HardKill := true)`** watchdog (forks a second child that SIGKILLs the compute child). It's in the `Parallel.magma` submodule. Do NOT drop `HardKill` in a refactor — without it a stuck child hangs the parent forever (this looked like ~112-minute fill batches reporting `failed=0`).
- **Polymorphic return = "bad syntax":** a Magma function whose return *type* varies by argument makes any intrinsic that calls it twice fail to compile. See [magma-polymorphic-return].
- `pkill -f run_fill_genus.m` fails on ~800-char cmdlines (pattern past pkill's match window) — match an early token like `masslimit:=1000`. `pgrep -fc` self-matches; use `ps -eo cmd | grep "[m]asslimit"`.

## Coverage / data-integrity facts
- Overrunning a genus's `enum-timelimit` **discards ALL its lattices** (`fill_genus.m`, `lats := []`), by design — a partial set would contradict the stored `class_number`. So `enum-timelimit` is a coverage switch, not a speed knob; calibrated to 900s at C=256.
- `--enum-per-lattice-timeout` is a **per-operation** cap (canonical form, aut group, primal+dual theta each independently), so ~4× per lattice; the aggregate guard is the per-genus `--enum-timelimit`, not that option.
- A dropped/timed-out genus is a **MISSING `genera_advanced` file**, not a `\N` — null-scanning cannot see it. Audit timeouts vs crashes accordingly. See [lattice-pipeline-coverage-diagnostics].
- Mass is a terrible work proxy: high-rank genera have huge Aut → tiny mass despite large `h`. `run_all.py` uses a work-aware batch metric (`genus_work`, `--batch-work-target`) instead.

## Open follow-ups
- **`fill_genus.m` aut/gram basis mismatch (unfixed):** on a `CanonicalForm` timeout, the stored gram is in the LLL basis (`:345`) but `aut_group` is computed in `gram0`'s basis (`Lcanon := L` at `:354`). connect feeds both to consumers that assume one basis (Voronoi, shortest, t-design, and — new in PR #73 — `RepresentsLattice` orbit-collapse, where it can mint a false `proved=true`). Fix: gate on `gram_is_canonical`, or transport the aut group to the stored-gram basis. See [fill-genus-aut-gram-basis-mismatch].
- **`hanke_full.py`** `maximal_overlattice_2` is a verified drop-in for Sage's `maximal_overlattice` (184/184 small-prime sweep + deterministic large-prime isotropic search). ~1.64× on `representative()` in isolation but only ~1.15× on the real listing stage (Sage pre-warms caches it shares). It's an opt-in monkey-patch, NOT wired into the pipeline. Extend the regression set to large primes before any wiring.

## Open PRs (as of 2026-07-17, both awaiting David Roe)
- **#74** (ours): Hanke maximal-lattice + fill-stage docs. David's review fixed in `d5ec272`.
- **#73** (roed-math): universality/regularity columns + embedding engine + Oscar groundwork. Reviewed; the one blocker is the aut/gram mismatch above.
