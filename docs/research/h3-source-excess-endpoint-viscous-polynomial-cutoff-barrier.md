# Explicit eighth-power kinetic barrier for active endpoint cutoffs

**Base:** `b931a5b3` — active finite-band endpoint cutoff escape.

The kinetic-energy ceiling already established in
`h3Path_actualLowRadialDissipation_le_kineticAnchor244` bounds the
H³ low-radial dissipation at cutoff Q by `Q^2 W₃(Q) E₀`, where
`W₃(Q) = 1 + Q^2 + Q^4 + Q^6`. The quartic-clock theorem
`h3Critical_quarticClock_radialWeight_le_fourSixth` states that
`W₃(Q) ≤ 4 Q^6` for Q≥1. Hence at each ACTIVE internal window,

    H(k) := R(k)^2 ε(k)^2 / 8 ≤ 4 E₀ (N(k)+1)^8.

For an arbitrary proposed integer comparison profile L(k), whenever
`4 E₀ (L(k)+1)^8 < H(k)`, the exact synchronized witnesses obey

    η(k) = 0  OR  L(k) < N(k).

This is a pointwise (not merely eventual) lower frequency requirement,
valid without assuming finite full terminal H³ dissipation. It leaves the
four-way physical PDE-clock gate unchanged and does not assert a lower bound
on η(k). The exponent eight reflects frequency-domain H³ dissipation;
it must not be mistaken for the existing quartic temporal PDE clock.

## Declarations

- `h3Critical_scalar_lowRadialKineticCeiling_le_eighthPower`
- `h3Critical_physicalActiveCutoff_eighthPowerCeiling`
- `h3Critical_scalar_eighthPowerBarrier_forcesHigherCutoff`
- `h3Critical_noL2Trace_cofinalFivefold_polynomialCutoffBarrier`

Full audit registration adds the root Lean import and all four pairs of
`#check` and `#print axioms` checks. Run the index generator, Lean
compilation, baseline audit and git push. Nothing is claimed about terminal
continuation from this estimate alone.
