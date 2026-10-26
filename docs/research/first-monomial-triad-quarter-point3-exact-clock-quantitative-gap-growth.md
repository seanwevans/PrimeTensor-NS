# Quantitative annular gap and super-sixth PDE concentration

Base commit: `310723a2` (both GitHub Actions runs passing).

## Aim

Restore a stronger fact from the actual high-radial cubic snapshot proof that
was discarded when the earlier exact-width existential interface was built.
The fixed annulus selected at time `t` has height above `3R³/4`. Relative to
the persistent floor `A=R³/2`, this yields an initial annular gap above
`R³/4`. The selected outer cutoff `N` must be the same cutoff used to
construct the exact PDE variation width; applying this estimate afterward
to an arbitrary earlier existential witness would be invalid.

## New mathematics

The local quarter-gap exact-width lemma redoes the cutoff/source-ceiling
selection while retaining both `gap>R³/4` and the literal PDE selector:

`δ = min ((T-t)/4) (min 1 (gap/(2*(Λ+Ξ+1))))`.

The physical no-terminal-L²-trace sequence is rebuilt using this stronger
local choice, without changing existing public theorem signatures. A strict
subsequence with pairwise-separated exact intervals is then extracted.
Full terminal H³ dissipation integrability is an **additional hypothesis**.
It bounds finite disjoint annular costs and hence yields

`δ(v k) * (v k+1)³ → 0`.

For any positive `η`, if eventually

`η ≤ (v k+1)³ * (T-τ(v k))/4`,

then the vanishing-width theorem rules out the geometric minimum and forces

`(v k+1)³ * gap(v k)/(2*(Λ(v k)+Ξ(v k)+1)) → 0`.

Using `gap(v k) > (v k+1)³/4` gives

`(Λ(v k)+Ξ(v k)+1)/(v k+1)^6 → +∞`.

The abstract super-sixth theorem is additionally reusable for any exact
clock sequence with the same quantitative quarter-gap and geometric-floor
hypotheses.

## Proof and scope

Four named theorems are registered; the proofs contain no `sorry`, `admit`,
or new axioms. The new result is an *implication*, not a proof of geometric
noncompression or of globally bounded PDE variation coefficients. It does
not settle the 3D Navier–Stokes regularity problem.

The developer environment used to package the patch does not have the
repository Lean toolchain. Run `lake env lean` and `lake build` locally,
then generate/verify the import index and build the audit as usual.
