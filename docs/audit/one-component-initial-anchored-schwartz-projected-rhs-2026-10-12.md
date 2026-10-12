# Initial anchored Schwartz physical projected-RHS bridge

Base checkpoint `9ffc7039` — "identify quantitative initial physical traces from weak L2 data".

## Content

Added `OneComponentInitialAnchoredSchwartzProjectedRHS.lean` with:

- `H3AuditInitialAnchoredSchwartzPhysicalMomentum`;
- `h3Audit_initialAnchoredSchwartzSource_weakPairing`;
- `h3Audit_initialStrongPhysicalLimit_eq_of_anchoredSchwartzSource`;
- `h3Audit_initialSubcriticalAnchoredSchwartz_physicalMomentumRate`;
- `h3Audit_initialSubcriticalAnchoredSchwartz_kineticRate`.

The previous audited quantitative H³ rate theorem derives both an L¹
physical source `G = Δu − P(u · ∇u)` and a strong right momentum limit `L`.
The new standalone generic lemma shows the following initial-anchored
distributional equation suffices to determine `L`:

    ∀ Schwartz Φ, ∀ 0<t<b,
      ⟪u(t),Φ⟫ − ⟪u(0),Φ⟫ = ∫₀ᵗ ⟪G(s),Φ⟫ ds.

The scalar source pairing is integrable by the already-proved Hilbert
Bochner integrability theorem. The scalar primitive tends to zero from
the right. Dense Schwartz tests then identify `L` with the ACTUAL
time-zero three-component Hilbert L² velocity.

Consequently the momentum and kinetic inequalities from the previous
two checkpoints hold for the physical initial datum, not an unknown
right-limit state:

    ‖u(t)−u(0)‖₂ ≤ K * t^(1−α)/(1−α)

    |E₀(t)−E₀(0)| ≤ δ(t)*(2‖u(0)‖₂+δ(t))

where `K=(3+C_L)*M`, `δ(t)=K*t^(1−α)/(1−α)`.

## Scope / remaining obligations

The old temporal-derivative joint-continuity hypothesis and the
pointwise subcritical H³-energy envelope are both retained. The
initial-anchored Schwartz momentum equation is a new **separate**
input; the positive-time FTC alone only gives time increments strictly
after zero and cannot identify the integration constant.

The vanishing old/selected relative-energy residual and the terminal
actual-vorticity strong-H³ endpoint are not used and remain independent.

The patch is not a proof of unconditional Navier–Stokes global regularity.

## Validation

ZIP/source integrity checked in artifact container. Lean/mathlib
compilation was not available there; local Rocky Linux `lake build`
remains required.
