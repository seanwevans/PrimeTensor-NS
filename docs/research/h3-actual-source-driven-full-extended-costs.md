# Source-driven high-H³ windows: extended costs in the full physical H³ dissipation

Base: `bd57ad1c` — extended high-H³ time costs on source-driven disjoint windows.

The existing theorem supplies one projected-source coordinate, independent
moving source/dissipation cutoffs, one common time sequence converging to `T`,
positive widths, and a strictly increasing index subsequence whose intervals
are pairwise separated. On each interval the *actual high-radial* H³
physical dissipation exceeds the prescribed moving threshold.

The exact radial partition of H³ dissipation on each strict physical
energy-class time gives

    D_full(t) = D_≤σ(t) + D_>σ(t),    D_≤σ(t) ≥ 0.

Therefore, for arbitrary σ, `D_>σ(t) ≤ D_full(t)` pointwise. Apply monotonicity
of `ENNReal.ofReal` and the extended nonnegative Lebesgue integral to each
half-open selected window and take finite sums:

    Σ_{k<m} ∫⁻_(t_k,t_k+δ_k] ofReal(M_k)
      ≤ Σ_{k<m} ∫⁻_(t_k,t_k+δ_k] ofReal(D_>σ_k(s))
      ≤ Σ_{k<m} ∫⁻_(t_k,t_k+δ_k] ofReal(D_full(s)).

Here `k` abbreviates the original selected index `v(k)` and every quantity
uses the same physical times and widths as the source-driven theorem.

The new bridge needs **no continuity or measurability of full H³ dissipation**
for the inequality on extended Lebesgue integrals (which are defined for
nonnegative functions without a supplied measurability proof). It does not
infer ordinary Bochner interval integrability or a terminal upper bound.
In particular the no-terminal-trace hypothesis is not proved to occur,
and no divergent cost sum or Navier–Stokes regularity claim follows.

Declarations:

- `h3Critical_actualHighRadialDissipation_le_full`
- `h3Critical_extendedWindowCost_mono`
- `h3Critical_noL2Trace_sourceDriven_disjointExtendedFullDissipationCosts`

Validate with the repository's pinned Lean / Mathlib toolchain before commit.
