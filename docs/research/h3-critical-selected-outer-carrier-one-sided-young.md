# Selected outer H³ carriers: full signed Young residual and one-sided slope

Expected base: `1ca309cd2` (locally committed anchored-slope module).

## Why the previous disjunction lost information

The earlier anchored-slope theorem used a two-branch `epsilon/2` split:

`epsilon / 2 < A*C` or `epsilon / 2 < M(s)*(Y(s)-Y(x))`.

This was useful for bookkeeping but not sharp. The *exact* physical
annular deficit identity is

`G(x)-G(s) = (M(x)-M(s))*Q(x,s) + M(s)*(Y(s)-Y(x))`

where `Q(x,s)` uses the Young-width cost **at x**. The original physical
momentum FTC bounds `|M(x)-M(s)| <= A`, and the previously proved
finite-radius snapshot estimate bounds `|Q(x,s)| <= C`. As a result:

`G(x)-G(s) > epsilon` implies

`epsilon - A*C < M(s)*(Y(s)-Y(x))`.

If `Y(s) <= Y(x)`, then necessarily `epsilon < A*C`. Conversely,
`A*C <= epsilon` forces `Y(s) > Y(x)`. The sufficient condition for
signed growth is stronger than the earlier `A*C <= epsilon/2`.

## New one-sided polynomial identity

Write `E_x = a*M_x-B` and `E_s = a*M_s-B`, with `a,w,B >= 0`.
For the early-anchored slope `Q = w*a*(E_x+E_s)-(Y_x+wP)`, a direct
polarization yields

`M_x*Q = w*(E_x*E_s + B*(E_x+E_s)) + G_x`.

This equality is exact. If the selected initial kinetic excess is
positive (`E_x>0`), the initial deficit is positive (`G_x>0`), and the
physical sharp highpass mass does not decrease (`M_s >= M_x`), then
`E_s >= E_x > 0` and `Q >= 0`. Consequently
`(M_x-M_s)*Q <= 0`, so a deficit loss greater than `epsilon` forces

`epsilon < M_s*(Y_s-Y_x)`.

This is stronger than the general `epsilon - A*C` residual and uses no
upper envelope for Q. No claim is made about a positive lower bound for
the selected physical time width or total Navier–Stokes continuation.

## Lean results

- `thirdFullKinetic_earlyYoung_fullResidual244`
- `thirdFullKinetic_earlyYoung_noGrowth_fullSourcePayment244`
- `thirdFullKinetic_earlyYoung_fullBudget_forcesIncrease244`
- `thirdFullKinetic_positiveDeficit_earlySlope_nonneg244`
- `thirdFullKinetic_nondecreasingMass_fullYoungCharge244`
- `thirdFullPhysical_outerDeficitDrop_fullYoungResidual244`
- `thirdFullPhysical_outerNoYoungIncrease_fullSourceSlope244`
- `thirdFullPhysical_outerNondecreasingHighpass_fullYoungCharge244`
- `thirdFullPhysical_selectedOuter_lowHalfTail_fullYoungResidual244`
- `thirdFullPhysical_selectedOuter_fullSlopeBudget_forcesYoungGrowth244`
- `thirdFullPhysical_cofinalOuter_fullYoungResidual244`

All file declarations use proof terms without `sorry`, `admit`, or
introduced axioms. Compilation is not verified here; use the pinned
Lean/mathlib toolchain and project audit in the supplied run script.
