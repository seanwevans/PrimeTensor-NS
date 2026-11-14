# One-sided selected outer carrier highpass drain

Base: `93e1847fa` (localized selected outer signed source payment).

## New mathematical reduction

Let `H_x = P_{>=rho} u(x)`, `H_s = P_{>=rho} u(s)` and
`S_rho(x,s) = ||P_{>=rho} int_x^s F(t) dt||`, with `F` the actual
projected physical momentum source. The previously proved physical
Bochner FTC yields `||H_s-H_x||=S_rho`. For **loss**, rather than
absolute mass variation,

    ||H_x||^2 - ||H_s||^2 <= 2||H_x|| S_rho.

The term `S_rho^2` disappears: it came from bounding an *absolute*
square-norm variation, while the signed deficit slope only needs an
upper bound for loss. Both cases in the exact earlier Young polynomial
are handled. The coefficient is bounded by

    K = 2 rho^6 sigma^4 ||H_x||^2.

Therefore every selected deficit drop `epsilon` satisfies

    epsilon - 4 rho^6 sigma^4 ||H_x||^3 S_rho
       < M_s (Y_s-Y_x).

When `Y_s<=Y_x`, the **entire** drop must pay the cubic localized
source term with constant 4, without assuming `S_rho<=||H_x||`.
Moreover this no-growth branch implies a strict highpass mass drain.

The cofinal theorem transports this factor-4 alternative over the
existing physical selected-carrier witnesses; it does not remove the
original global source branch and makes no continuation claim.

## Unresolved mathematical problem

The physical terminal `L1` source yields `S_{rho_k}->0` for arbitrary
moving cutoffs. Finite dissipation does **not** by itself force
`rho_k^6 sigma_k^4 ||H_{x_k}||^3 S_{rho_k}->0`. Closing this
frequency-weighted obstruction requires additional spectral estimates,
possibly triad cancellations and viscous high-frequency coercivity.

## Verification

No new axioms or placeholders. Structural registration and ZIP integrity
are checkable without Lean. Compile with the pinned Lean/mathlib project.
