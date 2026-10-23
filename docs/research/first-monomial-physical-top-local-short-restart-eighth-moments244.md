# Sliding local restart windows remove terminal-tail geometry assumptions

Baseline: `0a29d130` (`derive physical eighth moments from projected RHS weak FTC uniqueness`).

## The geometric mismatch

The previous `h3PathVelocityGeometricSlabCoveredAt244` required a fixed
`CanonicalH3TailDataFrom u t₀ T E` extending **all the way to the putative
terminal endpoint** `T`. This is not a consequence of `LoggedPreterminalH3PathAdmissible`
when the H³ energy may grow towards `T`.

The existing theorem
`LoggedPreterminalH3PathAdmissible.exists_localCanonicalRestartWindowAt`
instead gives, for **every** strict time `t∈(0,T)`:

- an earlier positive anchor `t₀`;
- a shorter physical terminal `S<T` with `t<S`;
- a finite energy ceiling `E≥1` only on the local tail `(t₀,S)`;
- `q=t−t₀>0` and `q<R(1,E)`; and
- `t=t₀+q`.

We can choose `Q=q`, so `q` itself is the upper endpoint of the positive
half-slab `[Q/2,Q]`. No geometric covering axiom remains.

## Correct terminal bookkeeping

For the short path `(u,S)`, obtain Navier–Stokes admissibility by restriction
of the original `(u,T)` equation. The selected mild state is formed at the
short anchor `t₀` with energy ceiling `E` and evaluated at elapsed `q`.

If the canonical old projected RHS satisfies scalar weak FTC on `[0,q]`, the
preexisting Grönwall uniqueness theorem proves selected/old physical equality.
The selected/old H³ spectral overlap theorem gives exact spectral agreement.
The old snapshot at absolute time `t₀+q=t` equals the intrinsic
original physical spectral snapshot by the pre-existing theorem
`velocityH3SpectralStateAt_eq_of_time_eq`. This equality explicitly
transports across the time identity, while proof irrelevance handles the
corresponding integrability, measurability, and Fourier-compatibility witnesses.
A direct `rw [hTime]` is invalid here because the spectral state has a
proof-valued argument whose type depends on the time.

The selected mild spectral state has `H3RawFourierMomentIntegrable 8` in each
velocity component. This transfers to the **actual physical** velocity at time
`t`, and hence supplies the moment premise in the existing necessary physical
`D₁`-versus-eighth-moment terminal alternative.

## Analytic assumptions not removed

`h3PathVelocityShortWindowWeakFTCAt244` still assumes the *existence* of one
short local restart window on which the scalar projected-RHS weak FTC holds.
The geometric part is automatic. The stronger repository-wide predicate
`H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier` supplies this
condition for the truncated terminal `S`, not by assuming a global H³ ceiling
on `(t₀,T)`.

No unconditional continuation/regularity theorem is claimed; the remaining
analytic issue is proving the local scalar weak-FTC property from the actual
preterminal PDE and suitable trace/integrability data. The global frontier is
already strong enough to imply separate continuation results elsewhere in the
repository, so the locally conditional formulation is the one to refine.

## Added declarations

- `h3Path_exists_localShortRestartGeometry244`
- `h3PathVelocityShortWindowWeakFTCAt244`
- `h3Path_physicalEighthMoments_of_shortWindowWeakFTC244`
- `h3Path_physicalEighthMoments_of_localShortWeakFTC244`
- `h3Path_localShortWeakFTC_of_globalWeakFTC244`
- `h3Path_physicalEighthMoments_of_globalWeakFTC_noGeometry244`
- `h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_localShortWeakFTC244`
- `h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_globalWeakFTC_noGeometry244`
