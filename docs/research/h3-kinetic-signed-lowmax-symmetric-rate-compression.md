# Signed sixth-flux: symmetric kinetic-only annulus rate/clock compression

**Pinned base:** `d478073d733553347c211e277bbb17b085f0f6b9` — physical gamma-free linear-height integrated in-gap dissipation.

## Hard missing implication

The accepted theorem gives a positive-width annular charge inside the original kinetic gap, but the certified width depends on an attained local PDE source coefficient and the gap edge. Its positivity alone does **not** rule out finite dissipation. We instead reuse the previously formalized *kinetic-only* finite-annulus Lipschitz estimate, which controls the SAME annular dissipation at both actual times using only the initial physical kinetic anchor and the natural radii R,N.

Write `L = thirdFullPhysicalKineticLowBandDissipationRate244 N E0 + thirdFullPhysicalKineticLowBandDissipationRate244 R E0 >= 0`, `H = thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244 R eta (velocityH3EnergyAt u t) > 0`. Starting from the gamma-free physical high-tail carrier, the accepted `thirdFullPhysical_signedLowMax_gammaFreeTail_linearHighRadialFloor244` gives `H < D_high,R(t)`, and the actual Fourier annulus theorem finds a finite `N >= R` with true height `Ann_N,R(t)>H/2`.

## Symmetric kinetic persistence

For ANY adverse time `t in [x,y]`, choose the side containing at least half the gap: forward if `t <= (x+y)/2`, backward otherwise. Define a **single exact width**

`w = min((y-x)/4, H/(8*(L+1))) > 0`.

Then `L*w <= H/8`. The preexisting kinetic-only annulus Lipschitz modulus proves `Ann_N,R(r)>H/4` on a subinterval of length `w` wholly inside `[x,y]`, including either endpoint case. Integrating the actual annular dissipation and comparing with full physical H3 dissipation gives

`w*(H/4) <= D_gap := integral_[x,y] velocityH3DissipationAt u r dr`.

No time-uniform H3 trace, full-source supremum, or unproved instantaneous full-dissipation continuity is used. The chosen finite outer cutoff N is retained rather than hidden.

## Quantitative clock-or-rate dichotomy

Resolve the exact min using the two scalar cases:

* Gap-clock compression: `(y-x)*H <= 16*D_gap`.
* Kinetic rate compression: `H^2 <= 32*(L+1)*D_gap`.

This is a stricter physical obstruction than asserting `w>0` with an unspecified shrinking width. The key gain is that L is the **kinetic-only** two-cutoff annular rate already controlled by the original PDE Fourier bounds. For each original separated cofinal kinetic gap, its full actual H3 dissipation tends to zero; therefore for any fixed `epsilon>0`, eventually the same selected physical high-tail carrier forces

`(y_k-x_k)*H_k < 16*epsilon` OR `H_k^2 < 32*(L_k+1)*epsilon`.

The cofinal threshold does not depend on the selected radius R or adverse time t, because the smallness input is the full physical dissipation of the original gap.

## Exact scope

The rightmost theorem is **conditional on the gamma-free physical high-tail branch**. It does not claim every adverse signed-flux sample belongs to that branch: the earlier cubic signed LowMax baseline, the tenth-power radius/physical-energy escape, and the previous quadratic-height integrated branch remain alternatives. Moreover, `N` may grow and with it `L`; the gap may shrink; and H may tend to zero with physical energy. Thus finite dissipation alone does not contradict the quantified fork. This is not an unconditional three-dimensional Navier–Stokes continuation proof.

## Verification

Registrar: `register_h3_full_third_kinetic_signed_lowmax_symmetric_rate_compression.py`, with two definitions and six theorems. Regenerate the proof index and run the pinned Lean compiler, full Lake build, and proof-fragment audit before committing. The archive's structural audit is not Lean kernel verification.
