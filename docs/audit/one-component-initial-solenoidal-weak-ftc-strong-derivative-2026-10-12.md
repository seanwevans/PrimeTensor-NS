# Initial solenoidal weak FTC to physical Hilbert derivative

Checkpoint prerequisite: `f8437fbe` (`identify actual spectral sources with physical Navier Stokes RHS`).

This module derives a functional-analytic reduction that was not present in the previous initial momentum interface:

1. The corrected **actual** physical projected RHS `h3AuditInitialActualSpectralLaplacianTotal hH3 s - h3AuditInitialActualSpectralLerayTotal hH3 s` is Leray-fixed at every positive time. Outside `(0,T)` it is zero and hence also Leray-fixed.
2. The complete actual old physical zero-jet velocity `h3AuditInitialOldPhysicalHilbertTotal` is Leray-fixed at all strictly positive times, by equality with the canonical old restart zero-jet on a local positive restart window.
3. A new `H3AuditPhysicalSolenoidalWeakFTCOn F G a b` is explicitly a **two-time integral identity** for the velocity increment against every divergence-free compact smooth weak test on `[a,b]`. It is not the instantaneous weak PDE identity.
4. Given the two Leray-fixedness facts and continuity of `G`, solenoidal-test density implies the exact physical Hilbert Bochner evolution `F r = F a + ∫_a^r G` on `[a,b]`.
5. The Banach-valued fundamental theorem of calculus then gives `HasDerivAt F (G r) r` at every strict interior time. Continuous linear real Hilbert pairing yields the scalar `HasDerivAt` against **every** three-component physical Schwartz probe, without requiring that probe to be divergence-free.
6. The last theorem applies this functional-analytic bridge to the actual old velocity and the genuinely reconstructed physical Navier–Stokes projected source. Its sole new temporal-evolution hypothesis is the solenoidal weak FTC on the chosen positive closed interval.

## Main declarations

- `H3AuditPhysicalSolenoidalWeakFTCOn`
- `h3Audit_physicalSolenoidalWeakFTC_implies_HilbertEvolution`
- `h3Audit_physicalSolenoidalWeakFTC_implies_HilbertHasDerivAt`
- `h3Audit_physicalSolenoidalWeakFTC_implies_SchwartzHasDerivAt`
- `h3Audit_initialActualProjectedRHS_lerayFixed_at_positiveTime`
- `h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime`
- `h3Audit_initialActualProjectedRHS_lerayFixed_allTimes`
- `h3Audit_initialActualProjectedRHS_continuousOn_strictInterval`
- `h3Audit_initialActualProjectedRHS_schwartzHasDerivAt_of_solenoidalWeakFTC`

## Open obligations

The *instantaneous* positive-time weak momentum Navier–Stokes PDE has been proved in the previous checkpoint, for solenoidal compact tests. It does **not**, by itself, prove the two-time weak FTC. The solenoidal FTC here is an explicit and visible premise. Future work should connect it to the existing old-branch `H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed` and its precisely documented temporal-product/joint-domination assumptions, transferring the integral identity from elapsed to absolute physical time. This would remove the independent solenoidal FTC premise.

Near initial time zero, `IntervalIntegrable (velocityH3EnergyAt u) volume 0 b` is still an independent hypothesis of the preceding initial trace theorem. The vanishing selected/old relative-energy residual and the unrelated terminal actual-vorticity strong-H³ condition remain independent. No unconditional global Navier–Stokes regularity theorem is asserted.

Lean compilation cannot be run in the artifact-generation environment; the user's Rocky Linux `lake env lean`, `lake build`, proof-index checks, and baseline audit remain authoritative.
