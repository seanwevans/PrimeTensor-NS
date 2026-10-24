# Unconditional compact time primitive and one-dimensional distribution kernel

Base: `8f2d5e68` (zero-mean smooth test primitive with explicit interior support bounds).

## Proof strategy

For a compactly supported smooth test `θ` with support `K ⊆ (a,b)`, apply the pinned
`IsCompact.exists_forall_le'` to `id` and `-id` on `K`. This produces `a < m ≤ t`
and `t ≤ M < b` for all `t ∈ K`. Take

`ℓ = min ((a+m)/2) ((2a+b)/3)`,
`r = max ((M+b)/2) ((a+2b)/3)`.

Then `a < ℓ < r < b` and `K ⊆ (ℓ,r)`, including for empty `K`. The previously
proved interior-bounds primitive gives `η∈C_c^∞((a,b))` with `η' = θ` whenever
`∫ θ=0`.

Together with the normalized bump this yields the unconditional decomposition
`θ=η'+(∫θ)ρ`. Hence every zero-derivative scalar distribution is the regular
distribution of a constant on the connected interval.

## Logical boundary

The physical FTC defect is constant as a regular distribution **conditional on
having first established the physical solenoidal distributional momentum
identity**. That identity is not derived from path admissibility in this module.
The next goal is to add distributions, obtain the outer-primitive representation,
and invoke the already-proved outer-primitive weak-FTC theorem. The physically
nontrivial PDE-to-time-distribution interchange remains independent.
