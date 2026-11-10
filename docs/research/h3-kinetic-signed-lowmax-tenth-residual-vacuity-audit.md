# Hard-math audit: unanchored tenth-power residual is automatically true

**Base:** `e827b604e2a6baddb27cc1b1cb17e54f31c40c94`.

## Exact defect

The accepted predicate `ThirdFullKineticSignedLowMaxTenthPowerResidual244`
(from `FullThirdSolenoidalTerminalProfileKineticSignedLowMaxTenthPowerGaugeCoupling.lean`)
contains, as its third disjunct, the existence of a physical time point `z`
and a positive `width` such that:

- `z=t` or `z=x`;
- `0 < width`;
- `z+width<y` or the symmetric backward-time alternative;
- `width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244 R X Y (mu/2) / 4) < epsilon`.

There is **no minimum width** imposed by any actual PDE persistence rate, no
fixed preselected interval and no lower bound on the charged integral.

For every strict gap `x<y`, positive tolerance `epsilon` and real coefficient
`A`, choose `z=x` and

```text
width = min ((y-x)/2) (epsilon / (2*(abs A+1))).
```

Then `width>0`, `x+width<y` and `width*A<epsilon`. In particular the residual
holds even when there is no adverse signed transport, no spectral mass, and
no appreciable dissipation.

## Proven source statements

1. `thirdFullKinetic_signedLowMax_arbitraryWidth_smallCost244`: the scalar
   short-width construction.
2. `thirdFullKinetic_signedLowMax_tenthResidual_automatic244`: the full
   physical tenth-power residual is true on every strict gap for `epsilon>0`.
3. `thirdFullKinetic_signedLowMax_nativeAdverseGap_impossible244`: the native
   adverse-gap predicate is impossible on every strict gap.
4. `thirdFullPhysical_signedLowMax_surplusPackingActive_impossible244`: the
   actual integrated-surplus physical activity predicate is impossible once
   the accepted PDE theorem selects its adverse time. This exposes the empty
   active set in the accepted global inverse-eleventh ledger.

## Consequences for the continuation program

The certificates and global spectral packing theorems derived under
`¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244` are not false, but the
premise is inconsistent with `x<y` and `epsilon>0`. Therefore the preceding
physical occurrence/counting theorems **do not yet provide a nontrivial
obstruction to singularity formation**. This is a logical and mathematical
issue, not a Lean tactic issue.

A real repair must redefine the earlier viscous arm with a time-width tied to
a physical PDE persistence modulus, or instead demand a nonzero positive
physical viscous charge on a preselected interval with the correct direction
of inequality. The accepted `thirdFullKinetic_signedLowMax_lowDensity_forcesRateWidth244`
and `thirdFullKinetic_signedLowMax_certifiedWidth_twoSided244` demonstrate one
usable anchored-width mechanism; their width is derived from an actual
certified annular peak and cannot be set arbitrarily by a disjunction.

This audit does **not** assert unconditional continuation, recurrence of
signed surplus, elimination of energy/viscous residuals, or a new PDE axiom.
All Lean proofs are candidates until compiled by the repository's Lean 4
and mathlib toolchain.
