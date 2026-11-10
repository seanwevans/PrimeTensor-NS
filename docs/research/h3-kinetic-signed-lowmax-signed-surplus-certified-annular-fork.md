# From integrated signed kinetic-gap surplus to a certified annular PDE fork

**Pinned upstream commit:** `2fa89b19dcbc430814dd36fab713252957943f75`

## New mathematical link

The accepted native-adverse theorem starts from a chosen adverse third-order
transport observation. However, the repository already proves a more intrinsic
physical condition: on a strict original kinetic gap `[x,y]`, if the actual
integrated positive signed H3 energy-production surplus exceeds the integrated
lower-order transport margin,

`thirdFullKineticGapLowOrderMargin244 u eta x y <
 thirdFullKineticGapSignedSurplus244 u x y`,

then there is an actual `t in [x,y]` with
`eta < -velocityH3TransportDerivative3At u t`.

The key point is that **this physical time is selected before the Fourier
radius**. Applying the accepted cofinal certified-eleventh theorem uniformly
in all `R` and all such times yields a single adverse `t` for which, at each
inner radius `R <= J`, at least one of these alternatives holds:

1. The original `ThirdFullKineticSignedLowMaxTenthPowerResidual244`, which
   explicitly includes a baseline LowMax flux payment, a radius or physical
   energy cap escape, or an earlier genuine positive-width viscous charge.
2. The physical relative gap cost is large:
   `(y-x)*h <= 16*D`, where `h` is the fixed positive capped linear height.
3. There exists a **physically certified** finite annulus at `Q > B`, with
   an actual positive annular H3 peak at the selected adverse time, its exact
   symmetric kinetic persistence width `w`, an in-gap integrated charge
   `w*(H/4) <= D`, and the quantitative eleven-power rate inequality

   `h^2/(32*K(E0)) <= (Q+1)^11*D`, with
   `K(E0)=1+192*sqrt(E0)*(sqrt(E0)+54*E0)`.

Crucially, option 3 uses the same annulus for the peak and payment. It is not
merely the tautology `exists Q, R <= Q and B < Q`.

The accompanying conditional corollary shows that, if **all** tenth-power
residuals are excluded at adverse samples for all `R <= J`, and relative gap
dissipation is subcritical, the physical integrated surplus forces actual
peak-carrying annuli beyond any prescribed fixed `B` for all `R <= J`, at
that same PDE-selected adverse time.

## Limits of the result

- Signed-gap surplus recurrence is **not** established. A positive surplus on
  any particular gap remains an explicit premise.
- Exclusion of the tenth-power residual is **not** automatic. In particular
  it can hold because of baseline, energy, or an earlier integrated viscous
  payment.
- Finite dissipation alone does not prevent moving high-frequency,
  short-duration annular concentration.
- This is a necessary physical Navier--Stokes PDE obstruction, not a proof of
  global continuation.

## Lean declarations

- `ThirdFullKineticSignedLowMaxSurplusCertifiedAnnulus244`
- `thirdFullPhysical_gapSignedSurplus_producesCommonAdverseTime244`
- `thirdFullPhysical_kineticGaps_signedSurplus_certifiedAnnularFork244`
- `thirdFullPhysical_kineticGaps_signedSurplus_forcesCertifiedOuter244`

The target module imports the accepted native-adverse/eleventh-power chain and
the physical `OffshellGapExcess` PDE integral-to-pointwise theorem. No new
axioms or `sorry` are introduced. Targeted and full Lean verification must be
performed on the user's original Lean/lake toolchain.
