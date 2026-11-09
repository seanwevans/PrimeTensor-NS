# Signed sixth-flux polynomial Fourier-source index gate

**Base HEAD:** `2a006d3c54ba7d5edce70913b6e7b422d133841e` — bound signed sixth flux kinetic index rates by one physical Fourier source ball.

## Genuine Fourier volume

The physical Fourier carrier is `WithLp 2 Point3`, where `Point3` is the three-axis function space. The `WithLp.ofLp` map is measure-preserving for the canonical product Lebesgue volume used in the accepted kinetic-source theorem. The elementary inequality `‖ξ‖ ≤ 2π‖ξ‖`, followed by the Hilbert-to-sup norm bound, places the gradient-frequency ball `{ξ : 2π‖ξ‖ < ρ}` inside the pullback of the sup-norm ball of radius ρ. The latter is a three-coordinate cube, with volume `(2ρ)^3`. Thus for positive ρ,

`volume({ξ : 2π‖ξ‖ < ρ}) ≤ 8ρ³`.

This bound is deliberately nonsharp and does **not** postulate the sharp Euclidean-ball measure normalization.

## Projected-source ceiling

For `ρ ≥ 1` and physical kinetic anchor `E₀ ≥ 0`, the existing projected-source ceiling is

`S(ρ,E₀) = ρ²√E₀ + √(volume(Bρ) · (18ρE₀)²)`.

Using `8ρ³ ≤ 9ρ⁴` yields

`S(ρ,E₀) ≤ ρ²√E₀ + 54ρ³E₀`.

The accepted one-radius Bernstein multiplier is then bounded by the explicitly polynomial (in cutoff index) coefficient

`P_k(E₀) = 1 + 2(k+1) · 24(k+2)²(k+1)⁶ √E₀ · ((k+1)²√E₀ + 54(k+1)³E₀)`.

The largest frequency power is twelve. The factors depend only on the fixed early kinetic anchor `E₀`, not on moving H³ energies or a source norm at an adverse time.

## Physical signed sixth-flux obstruction

For sufficiently late original separated kinetic gaps, and any physical adverse signed-flux observation whose earlier tenth-power residual is excluded, the established trichotomy is sharpened to

`gap_length · h ≤ 16 D_k` **or** `h² ≤ 32 P_k(E₀) D_k` **or** `∃ Q ≥ R : k < Q`.

Consequently the middle branch charges at least `h² / (32 P_k(E₀))` of actual full-H³ gap dissipation. No limit `P_k(E₀) D_k → 0` or upper bound on the average dissipation has been proved. The polynomial does not by itself imply Navier–Stokes continuation.

## Registration and verification

Module: `PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxPolynomialSourceGate`.

Audit registrar: `tools/audit/register_h3_full_third_kinetic_signed_lowmax_polynomial_source_gate.py` supports `--apply`, `--check`, `#check`, and `#print axioms` for all declarations. Intended verification: targeted `lake env lean`, `lake build`, root `lake build`, `proof/generate_index.py --check`, and `proof/check_fragment.py --all`.

No Lean kernel confirmation was available in the packaging environment; local elaboration is required.
