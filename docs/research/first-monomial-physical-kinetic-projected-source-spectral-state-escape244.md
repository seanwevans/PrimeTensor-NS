# Actual spectral-state escape behind the physical terminal source obstruction

**Base:** `5ea76e7e` — transfer fixed physical PDE source escape to cofinal H3 energy escape.

The *actual* weighted H³ spectral state at positive time `t` is

    S(t) := h3AuditActualSpectralVelocityTotal hH3 t.

The previously identified physical inverse-Fourier sources obey their
primitive linear/quadratic bounds, before collapsing both into `E₃`:

    ‖A(t)‖₂ ≤ 3 ‖S(t)‖,
    ‖B(t)‖₂ ≤ C_L ‖S(t)‖²,
    ‖A(t)-B(t)‖₂ ≤ 3 ‖S(t)‖ + C_L ‖S(t)‖².

The Laplacian estimate uses the Plancherel Fourier multiplier contraction;
the Leray estimate uses the bilinear Fourier convolution source estimate.
The constant `C_L` is exactly `h3AuditInitialLerayEnergyCoefficient`.

## Consequences

If the terminal kinetic mass is positive, and the actual physical Hilbert
velocity has no strong L² trace at T, then the already proven fixed physical
source alternative selects a cofinally unbounded Laplacian or Leray branch.
The respective linear or quadratic majorant proves

    ∀ b ∈ (a,T), ∀ M ∈ ℝ, ∃ t ∈ (b,T), M < ‖S(t)‖.

The direct projected-source bound also gives that implication without selecting
a source component. Conversely, a finite ceiling on `‖S(t)‖` on any one
strict terminal subtail bounds the projected source and yields an exact-mass
strong terminal L² velocity trace.

This is a stricter carrier-level formulation than the prior consequence for
`velocityH3EnergyAt`, because the latter was only a majorant of `‖S‖²`.
The implications are conditional on missing physical L² convergence. No
H³ nonextension-to-L²-nonconvergence inference, no uniform H³ bound, and no
Navier–Stokes regularity closure is claimed.
