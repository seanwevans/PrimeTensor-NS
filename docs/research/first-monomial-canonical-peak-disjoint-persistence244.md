# Canonical source peak-centred H³ persistence and finite dissipation budget

Base: `dcdc7264` (physical mass-to-dissipation costs).

The actual old weighted H³ spectral state is strongly continuous at strictly positive preterminal times (proved in `OneComponentInitialActualPhysicalSourceMeasurability`). At a fixed peak s, choose a positive right-hand radius such that the weighted spectral state changes by less than 1. Then for every r in the resulting closed window,

    max(0, (max(0, ‖U₃(s)‖-1))²-K(ρ) E₀(b)) ≤ HighMass_ρ(U₃(r)),

where b<s is a fixed physical kinetic-energy anchor and `K(ρ)=1+ρ²+ρ⁴+ρ⁶`. This uses the proven kinetic bound on low-radial H³ mass, the actual spectral sup-norm bound by its three-coordinate square energy, and the exact low/high Fourier mass partition.

For any cofinal sequence of actual weighted spectral peaks with divergent spectral norm and lying after b, the explicit floor diverges. Select a positive right-hand persistence interval at each peak, then apply the **existing** strictly increasing pairwise-separated terminal-window subsequence lemma to obtain disjoint intervals. Finite terminal physical H³ dissipation bounds every finite partial height-width cost and implies the selected persistence widths tend to zero.

The theorem concerns newly selected peak-centred intervals. It does **not** identify them with the previously established quadratic-sharp annulus persistence windows. In particular, it gives no universal positive lower bound on width, no divergent cost sum and no contradiction with finite dissipation. To apply directly to the canonical source-maximizer witness sequence, discard an initial finite prefix to place all selected peak times after a fixed kinetic anchor; the existing critical-width regime proves the required spectral norm escape but does not imply a uniform temporal modulus.

Status: static source checks only; Lean compilation must be performed on the target repository.

## End-to-end conditional canonical source-maximizer theorem

`h3Path_noL2Trace_canonicalWidth_sourcePeaks_disjointMassPersistence244` retains the original canonical noncompression, sixth-order linear-rate, and ninth/eighth annulus-width cap. It proves: for every fixed interior kinetic anchor `b` and positive radial cutoff `ρ`, there is a further strictly increasing subsequence of the **original** canonical source-maximizing times. These times have disjoint right-hand persistence windows with nonnegative lower mass floors growing to infinity and finite dissipation height–width costs. Their widths converge to zero. No uniform lower duration or cost contradiction is deduced.

The fixed-anchor time restriction is made only after a finite-prefix discard. The maximizing times themselves are *not* reselected. The originally disjoint quadratic-sharp annulus windows are retained but not identified with the additional peak-centered intervals.
