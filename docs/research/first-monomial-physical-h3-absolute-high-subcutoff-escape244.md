# Absolute high-frequency H³ dissipation divergence below arbitrary subcutoffs

**Base commit:** `91cabcd9` (*integrate cubic high radial H3 dissipation on terminal windows*).

## Mathematical increment

For actual physical H³ Fourier dissipation, the exact low/high partition and
monotonicity of the low radial set integral prove, whenever ρ ≤ σ,

    D_high(σ,t) ≤ D_high(ρ,t).

The no-strong-kinetic-L²-terminal-trace branch (with positive terminal
kinetic mass) already gives ONE strict physical terminal sequence τ(n) such
that τ(n) → T and

    (n+1)^3 < D_high(n+1,τ(n)).

Therefore for any radial profile ρ(n) ≤ n+1 eventually, **on the same τ(n)**,

    D_high(ρ(n),τ(n)) → +∞.

This includes every fixed finite radius ρ by choosing the constant profile
ρ(n)=ρ. No time snapshot reselection is required for different profiles.

## Status of time regularity

The repository proves strong positive-time continuity of the actual
H³-weighted spectral state (`h3Audit_initialActualSpectralVelocity_continuousOn`).
But full physical H³ dissipation is an unbounded-frequency multiplier, so its
continuity is NOT a consequence of norm-continuity in the weighted H³ spectral
state alone. Its time modulus, window widths, and unconditional integrated
terminal cost remain open. The explicit corollary proves divergence at every fixed radius, with the same witness. The present theorem is a strict-time pointwise
absolute escape result, not global regularity and not an integrated divergence.

## Verification

Requires `lake env lean` and full `lake build` in the user's Lean 4/mathlib
checkout. No local Lean binary is available in the artifact creation runtime.
Run audit registrar, `proof/generate_index.py`, `--check`, baseline audit and
then push. Axiom audit uses `#print axioms` for all three new theorems.
