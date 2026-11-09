# Signed sixth flux: one-radius kinetic Bernstein/source envelope

**Pinned base:** `f62050c326a4681c3da455dfe273e0ab1b60d17a` — exact index-rate Bernstein or annular outer escape.

## The hard mathematical step

The accepted natural-radius index gate retains the physical kinetic variation budget

`C_k(E0) = 1 + 2 * Σ_{j=0}^k L_j(E0)`.

Here the exact physical rate is

`L_j(E0) = 6 (j+2)^2 W_j^2 sqrt(E0) S_{j+1}(E0)`

with `W_j = sqrt(1+(j+1)^2+(j+1)^4+(j+1)^6)`, and

`S_ρ(E0)=ρ^2 sqrt(E0) + sqrt(V_ρ (18 ρ E0)^2)`,

`V_ρ = volume.real { ξ : (2π)‖ξ‖ < ρ }` in the genuine three-axis Fourier product volume.

For natural radii `j <= k` and nonnegative kinetic anchor `E0`, the actual radial balls are nested. The established Fourier-ball finiteness theorem and `measure_mono` imply `V_(j+1) <= V_(k+1)`, and consequently `S_(j+1)(E0) <= S_(k+1)(E0)`. This controls the *source ceiling*, not any unproved monotonicity of the actual nonlinear source state.

Use the accepted cubic natural-radius multiplier ceiling `W_j <= 2(j+1)^3 <= 2(k+1)^3`. Then for all `j <= k`,

`L_j(E0) <= 24 (k+2)^2 (k+1)^6 sqrt(E0) S_(k+1)(E0) = B_k(E0)`.

Therefore the exact physical index-rate coefficient is bounded by one Fourier ball:

`C_k(E0) <= 1 + 2 (k+1) B_k(E0) = Ĉ_k(E0)`.

This proof **does not** need a polynomial formula for the volume of the Fourier-gradient ball. Every cutoff dependence is explicit, with the exact volume retained in the source factor.

## Physical cofinal consequence

The accepted cofinal signed-sixth-flux theorem is transported, without changing its original tenth-power residual or quantifier order, into the three-way alternative

1. Positive average full-H3 dissipation: `(y_k-x_k)*h <= 16 D_k`;
2. One-ball index-rate payment: `h^2 <= 32 Ĉ_k(E0) D_k`, equivalently `D_k >= h^2/(32 Ĉ_k(E0))`, since `Ĉ_k>0`;
3. A certified finite annulus with actual outer radius `Q > k`.

The adverse physical sample remains conditional; the earlier tenth-power residual is excluded explicitly. The adaptive gauge still tends to infinity but is not used to assume uniform rate bounds.

## What is not claimed

The known Fourier-ball volume is finite at each cutoff, but no global *polynomial* volume upper bound is proved in this module. Thus `Ĉ_k D_k -> 0` does not follow from `D_k -> 0` without extra rate information. Positive relative gap dissipation remains a genuine alternative. No claim of unconditional Navier–Stokes continuation is made.

## Verification

Audit registration checks all seven new theorem names, two definitions and the absence of proof placeholders. Run `lake env lean` and `lake build` with the pinned repository toolchain, then the full project build, index check, and fragment audit. Static archive tests are not Lean kernel checking.
