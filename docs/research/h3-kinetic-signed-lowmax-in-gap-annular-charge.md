# Signed LowMax sixth flux: physical viscous cost inside original kinetic gaps

**Exact baseline:** `934ee0843282858c209521c2952f937717ef4a08` — certify annular H³ viscous persistence from adverse signed sixth flux.

## The gap endpoint obstruction

The preceding theorem `thirdFullPhysical_strictGap_signedLowMax_clockOrPDEAnnularWindow244` produces an actual PDE-certified forward interval `[z,z+δ]` rooted at an original signed-flux observation time `z = s` or `z = t` inside the **closed** physical gap `[x,y]`. The interval need not lie inside that gap. In particular, if `z = y`, no positive forward interval anchored at `z` can be included in `[x,y]`.

We preserve that genuine endpoint obstruction rather than assuming an interior observation or manufacturing a reverse-in-time viscous PDE rate.

## Exact physical truncation and integrated charge

When `z < y`, set

`ε = min(δ, (y-z)/2) > 0`.

Then `z+ε<y`; the physical annulus with original inner `R`, outer `N`, original state and source ceilings `K,C`, and **exact unmodified** PDE width `δ` retains its lower floor on `[z,z+ε]`. Its integral is proved again on the new interval rather than inferred incorrectly from an integral on the larger window:

`ε × (H/4) ≤ ∫_z^(z+ε) (D_{≤N}(r)-D_{≤R}(r)) dr`.

With the explicit finite full physical H³ dissipation integrability premise, the already verified Fourier physical domination and interval integral monotonicity yield

`ε × (H/4) ≤ ∫_x^y D₃(r) dr`.

The signed adverse height is the previous exact

`H = (R+1)^2 (η/4)^2 / [2(A_R(V,W)^2+1)] > 0`,

where `A_R=243[2(R+1)]⁷ C₀(1+||V||+||W||)^3`. No factor is suppressed.

## Quantifiers and honest alternatives

For **closed-gap** selected signed-flux samples, the theorem proves exactly three branches:

1. weighted Schwartz recovery + actual projected-source L¹ clock exceeds `η/2`;
2. one original selected observation equals the right endpoint `y`, with its certified forward window (which may lie in the next original kinetic window);
3. one original selected observation precedes `y` and generates a strictly positive annular physical cost **inside** the gap.

For original observation samples both **strictly interior**, the endpoint branch disappears. The final theorem then gives the weighted clock-or-physical-integrated-`D₃` alternative on the **same** gap `[x,y]`.

This is a genuine improvement over arbitrary forward persistence windows, but is not yet an unconditional cofinal contradiction: the adverse signed-flux observations need not automatically lie strictly inside the original gaps, the positive widths can collapse, and the radius/amplitude coefficient can grow. Additional signed-flux temporal continuity or an endpoint-overlap allocation argument is required before summing these costs over the original disjoint gaps.

## Verification

Register all six public declarations, run `proof/generate_index.py` and `--check`, targeted Lean elaboration, full Lake build, audit fragment checks and no-placeholder scan. The static archive/registrar tests do not constitute Lean kernel verification.
