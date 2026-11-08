# Actual physical signed sixth-flux replenishment on the original kinetic gaps

**Base:** `1e64f03f698251a24500e2c78968e74330a94408` — recover native signed LowMax flux from actual adverse physical H³ transport.

## Hard mathematical bridge

The previous accepted theorem `thirdFullPhysical_strictGap_adverseThird_tailOrBaselineClockCost244` turned an adverse top-third physical observation into a high-radial H³ tail OR a recovered negative signed LowMax Schwartz flux, but it required an independently provided Fourier-realized reference Schwartz state at the earlier observation. That requirement prevented direct transfer from the physical signed replenishment construction.

`thirdFullPhysical_snapshot_signedLowMax_referenceRecovery244` removes that assumption. At every genuine physical strict time `s∈(a,T)` and for every `sigma>0`, the EXISTING exact real-solenoidal Schwartz recovery gives a complexified Schwartz field `q`, weighted Fourier state `W`, and all the actual conditions:

- `W_j = H3weight * Fourier(q_j)` almost everywhere (no invented pointwise L² representative);
- `Σ_j ∂_j q_j(ξ) = 0` for all frequencies;
- `||U(s)-W|| < sigma`, where `U(s)` is the actual physical weighted-H³ spectral state.

No time-dependent recovery selection or common limiting Schwartz field is asserted. This is a single finite physical-time construction obtained from strong weighted-H³ convergence.

## Signed physical gap outcome

`ThirdFullKineticSignedLowMaxPhysicalGapOutcome244` describes a genuinely *physical* original strict kinetic gap `[x,y]`, a fixed natural LowMax cutoff `R`, and independent positive tolerances `gamma,epsilon,sigma`.

There exists an actual time `t∈[x,y]` with

`eta < -velocityH3TransportDerivative3At(u,t)` and

`eta < ((2*pi)^7/3) * 1944*C1*(E3(t)+1)^3`.

At the actual gap START `x`, there is a solenoidal exact Fourier reference `(q,W)` with `||U(x)-W||<sigma`. At the actual adverse time `t` there is either:

1. the EXACT quadratic physical high-radial-tail charge `(eta/2) < C*1944*C1*(E3(t)+1)*(||P_R U(t)||+gamma)^2`; or
2. an exactly represented solenoidal Schwartz recovery `(p,V)` at `t`, with `||V-U(t)||<epsilon`, and the native LowMax signed-flux baseline / weighted PDE clock / actual in-gap H³ viscous integral trichotomy.

The physical Fourier prefactor `C = ((2*pi)^7/3)` stays in the one-sided LowMax margin `mu=(eta/2)/C`. In the viscous arm, the certified positive persistence width is inside the same kinetic gap, forward if the selected observation is interior and backward if it is the right endpoint. The exact moving radius, cubic spectral amplitudes and width-height product remain visible.

## Triggering without an assumed adverse observation

`thirdFullPhysical_gapSignedSurplus_twoPhysicalSignedRecoveries244` invokes the already accepted *integrated physical surplus* criterion:

`thirdFullKineticGapLowOrderMargin244 u eta x y < thirdFullKineticGapSignedSurplus244 u x y`.

This implies a real adverse third-order time in the SAME original gap by `thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244`. The new proof constructs both physically realized Schwartz profiles automatically; no adverse TWO-time signed flux difference, earlier reference field, or physical source-later approximation is postulated.

`thirdFullPhysical_kineticCumulativeMarginOrTwoPhysicalSignedRecoveries244` then reuses the ORIGINAL cumulative kinetic annular-window theorem `thirdFullPhysical_kineticCumulativeMarginOrGapLowMax244`. For every finite index `m`, it keeps the same three alternatives:

1. one original kinetic window reaches the Riccati-scale branch;
2. the original cumulative dissipation charges are covered by initial H³ energy and integrated lower-order signed transport budget;
3. an original gap `k<m` possesses a common LowMax cutoff `R` (selected before its adverse time), a genuine adverse physical observation and two automatically constructed exact Fourier-solenoidal Schwartz recoveries. The full high-tail/baseline/clock/viscous branch is retained.

No new kinetic gap, time sequence, or radius-selection condition is substituted for the previous construction.

## Remaining obstruction

This is a *finite cumulative trichotomy*, not proof of a positive adverse signed margin on all late gaps. Neither the reference signed-flux baseline nor the weighted source clock is proved uniformly small. The actual seventh-power LowMax coefficient can grow with radius and energy; the certified viscous widths can shrink. Obtaining quantitative baseline control and a noncompressing cofinal width-height charge remains necessary before an H³ continuation conclusion.

## Verification

The source registers one predicate and four theorems with exact `#check` and `#print axioms` audit entries. Run `proof/generate_index.py` before the pinned Lean compilation, then the full Lake and fragment audits. Static validation alone is not kernel verification.
