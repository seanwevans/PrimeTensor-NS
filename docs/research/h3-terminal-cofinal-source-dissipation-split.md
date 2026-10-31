# Physical H³ terminal obstruction: cofinal spikes and source-channel split

Base revision: `0c2ed815`.

## Starting point (already verified)

Under `LoggedPreterminalH3PathAdmissible`, absence of the actual physical
Hilbert `L²` limit at the terminal time forces the projected momentum source
`G = D - N` to fail Bochner `L¹(b,T)` for every `0<b<T`. Under
`PreterminalH3EnergyClass`, the full H³ viscous dissipation is likewise
nonintegrable on every strict terminal subinterval.

The current package derives consequences using only continuity, exact physical
Hilbert FTC, the established pointwise H³ energy estimate, and triangle
inequality. No terminal mass positivity, finite H³ dissipation, frequency cap,
or angular-clock hypothesis is added.

## New results

* `h3Critical_projected_source_integrable_of_terminal_norm_ceiling`: a
  uniform norm bound on the actual source on a terminal interval forces its
  Bochner L¹ integrability, by positive-time source continuity and finite
  interval measure.
* `h3Critical_noL2Trace_projected_source_cofinally_unbounded`: no physical
  terminal L² trace implies every later tail contains source norm spikes
  exceeding every real threshold.
* `h3Critical_noL2Trace_fullEnergy_cofinally_unbounded`: transfer to full
  actual H³ energy via `‖G(t)‖ ≤ (3+C_Leray) E_H3(t)`.
* `h3Critical_noL2Trace_fullDissipation_cofinally_unbounded`: transfer to
  full viscous H³ dissipation using the anchored estimate
  `E_H3(t) ≤ 1 + 6 E0(b) + 3 D_H3(t)`.
* `h3Critical_noL2Trace_laplacian_or_leray_nonintegrable_on_every_tail`:
  either the physical inverse-Fourier Laplacian or the actual reconstructed
  Leray forcing is non-L¹ on each tail (the alternative need not be uniform
  in `b`).
* `h3Critical_noL2Trace_laplacian_or_leray_cofinal_norm_spike`:
  at arbitrarily late times, one of these two source norms exceeds any
  threshold; the identity follows from `G = D - N` and norm triangle inequality.

## Mathematical limitation

All conclusions retain the hypothesis that the strong physical terminal
L² trace fails. The split is necessary, not sufficient, for blowup, and it
does not identify which source dominates uniformly or rule out cancellation.
The cofinal energy result may also be obtainable from older energy/trace
dichotomies; the new direct path avoids a separate positive terminal kinetic
mass premise and exposes the physical source mechanism.

## Verification

The Lean module is a compilation candidate; check with the repository's
pinned Lake toolchain. Do not claim this is a formalized result until the
new module and audit compile. Then execute the full project baseline before
committing.
