# Arbitrary moving-profile highpass source/H³ dissipation windows

Base: `8de8270a` — separate common highpass source and H³ dissipation windows.

The committed `movingDiagonal` theorem has a stronger quantifier order than the
specialized later window theorems. It permits *independent*, predetermined
nonnegative cutoff sequences `ρ(n), σ(n)`, real height sequences `K(n), M(n)`,
and cofinal temporal anchors `c(n)∈(b,T)`. One actual physical projected-source
coordinate is selected once and the same physical witness time meets both
inequalities for every `n`.

This module transfers that exact arbitrary-profile assertion through:

1. The already-proved continuity of the actual source highpass square mass,
   continuity of actual low-radial dissipation, and **explicit** continuity of
   full physical H³ dissipation. At each common selected time, both strict
   inequalities persist on a *single* right-hand interval of positive width.
2. The already-proved terminal-window separation lemma. A strictly increasing
   subsequence of the resulting **same** windows is pairwise separated and
   still converges to `T`.
3. Finite-sum inequalities, with separate lower bounds

   `Σ[k<m] δ(v k) K(v k)` and `Σ[k<m] δ(v k) M(v k)`

   for the respective integrated actual Fourier source mass and high-H³
   dissipation on the very same disjoint intervals.

The theorem supports, for example, growing radii `n+1` and prescribed cubic
heights `(n+1)^3` **without** adding a positive terminal kinetic-mass premise.
As in the committed proof, this remains conditional on failure of strong
terminal physical L² velocity trace and explicit full-H³ dissipation
continuity. No lower bound on `δ(n)`, divergent cost sum, finite terminal
H³ dissipation, noncompression mechanism, or singularity claim is inferred.

Lean declarations:

- `h3Critical_noL2Trace_actualHighpassSourceDissipation_profileWindows`
- `h3Critical_noL2Trace_actualHighpassSourceDissipation_profileDisjointWindows`

Lean elaboration and project baselines require the pinned toolchain.
