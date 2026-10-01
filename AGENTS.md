# PrimeTensor-NS Codex Instructions

## Mission
Continue PrimeTensor-NS as a neutral, exhaustive Lean/Navier–Stokes research program. Lean and the repository are ground truth.

Do not turn a theorem proved under hypothetical nonextension into a claim that blowup exists. Do not turn a conditional continuation criterion into a claim of global regularity.

Prefer checkpoints that close a real logical/analytic gap, remove vacuity, connect the obstruction to standard hypotheses, or simplify the frontier. Avoid theorem-count busywork.

Read `.agent/PROJECT_STATE.md` before choosing work. Update it before proposing a checkpoint.

## User interaction
The user may interrupt at any time. Address the interruption before continuing. If a real decision is needed, end with:

<PT_ASK>
question
</PT_ASK>

Do not ask for giant compiler dumps; you have local Lean access.

## Git authority
Never commit, push, pull, reset, clean, rebase, merge, switch branches, or edit `PrimeTensor.lean`. The Python supervisor owns synchronization, root-import normalization, validation, commits, and pushes.

You may inspect Git with status/diff/log/show/grep/blame.

## Lean workflow
Rocky Linux repo: `~/Repos/PrimeTensor-NS`.
Lean 4.34.0-rc1 + mathlib4.

Fix the first meaningful compiler error before broad rewrites. Search the repo for exact signatures and compiled idioms.

Recurring fragility:
- Point3 / H3FourierPoint3 typeclass choices;
- local `Fintype (PrimeTensor.Axis d)` and measure instances;
- subtype coercions;
- `(f ∘ m)` vs `fun n => f (m n)`;
- ENNReal / ofReal algebra;
- multiplication order around division;
- `simp`/`dsimp` making no progress;
- missing positivity/nonzero facts.

Prefer explicit `change` and typed intermediate facts when Lean is fragile.

## Checkpoint protocol
When a coherent checkpoint is ready, update `.agent/PROJECT_STATE.md` and end with exactly one:

<PT_CHECKPOINT>
{"file":"PrimeTensor/path/to/Checkpoint.lean","commit_message":"concise commit message"}
</PT_CHECKPOINT>

Do not claim it is green. The supervisor runs:
1. `lake env lean <file>`
2. `lake build <target>`
3. `lake env lean PrimeTensor.lean`
4. `lake build`

On failure, repair from the returned evidence. On green, continue from the new commit unless the user has paused/redirection.

## Scientific precision
Global scalar lower bound != angular concentration.
Nonempty localization != positive atomic mass.
Positive pointwise density != positive singleton mass.
Keep retained hypotheses explicit.
