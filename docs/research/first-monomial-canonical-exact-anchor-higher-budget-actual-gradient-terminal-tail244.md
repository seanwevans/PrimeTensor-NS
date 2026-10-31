# Actual physical velocity-gradient escape on every terminal time tail

Base commit: `6fd6004a`.

The preceding module supplies a conditional eventual statement: for each
`b ∈ (a,T)` and for every `c ≥ 0` satisfying

    4(T-b) · 4422 · c < 16m + 3,

every sufficiently large canonical index `k` has a physical time
`s ∈ (b,τ(v(k)))`, axes `i,j`, and a physical point `x` such that

    |∂ᵢuⱼ(s,x)| > c log(v(k)+1).

For each `b`, take

    A = 4(T-b) · 4422,     c = 1/(1+A) > 0.

Then `A c < 1 ≤ 16m+3`, and strict monotonicity of `v` gives
`log(v(k)+1) → +∞`. Combining the two eventual facts yields

    ∀ b∈(a,T), ∀ M∈ℝ, ∃ s∈(b,T), i,j,x,
      M < |∂ᵢuⱼ(s,x)|.

The first theorem handles the abstract eventual-log-spike to terminal-tail
transfer; the second retains the exact existential canonical selectors and
all original higher-moment, source-ceiling, cutoff, small-tolerance and
noncompressed-clock premises.

This is conditional unbounded pointwise growth on every time tail. It does
**not** imply that the integral in time of an L∞ velocity or vorticity
gradient diverges. Such a temporal-integral result would require an
additional persistence or lower-occupation bound. No unconditional
Navier--Stokes blowup or regularity statement is obtained.

## Verification

1. Register the module, then run `python3 proof/generate_index.py`.
2. Check `python3 proof/generate_index.py --check` and `python3 proof/check_fragment.py --all`.
3. Compile the file and its Lake module target; compile the central theorem audit.
4. Run `lake build` and `bash tools/audit/baseline.sh --reuse-build` before committing.

This patch was structurally inspected but not compiled with Lean/mathlib in
the patch preparation environment. All Lean proof steps require verification
with the repository-pinned toolchain.
