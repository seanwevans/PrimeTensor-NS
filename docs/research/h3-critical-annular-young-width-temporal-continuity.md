# Exact actual annular Young-gap/width continuity

Base: `629130b2922d50931a153210cf4560253350445c`.

## Quantitative multiplier

Let `q(ξ)=((2π)|ξ|)^2`. The genuine cubic Young-gap integral has density
`q(ξ)^3 |N_j(U,U)(ξ)+2q(ξ) z_j(ξ)|²` on the exact sharp annulus
`S_{ρ,σ}=S_σ∩S_ρᶜ`. The fixed-upper-ball multiplier

    m_σ(ξ) = 1_{S_σ}(ξ) sqrt(q(ξ)^3)

satisfies `0≤m_σ(ξ)≤σ³` whenever `σ≥0`. Its action on every Fourier L²
class is realized by a complex continuous linear operator with norm at most
`σ³`. Hence no additional H⁶ velocity moment is required, and the old
weighted Young-gap integrability requirement becomes automatic on a finite
band.

The exact Parseval/Plancherel identity is

    ||m_σ (P_σ−P_ρ) F||₂² = ∫_{S_{ρ,σ}} q³ |F|²,

for `ρ≤σ`, with `F` any unweighted complex Fourier L² state.

## True nonlinear realization

Apply the operator to the already proved genuine antiheat/Leray residual
`G_j(U)=N_j(U,U)−2L_j(U)`, whose raw Fourier representative is
`N_j(U,U)+2qz_j`. This identifies the **actual** Young-gap integral with
`||m_σ(P_σ−P_ρ)G_j(U)||₂²`.

The residual `U↦G_j(U)` is continuous on H³ weighted Fourier states,
while the raw velocity Fourier coordinate map and the sharp annular
projections are continuous. Thus the entire exact Young plus width cost

    2 ∑_j ∫_{S_{ρ,σ}} q³ |G_j(U)|²
    + [2σ⁶((σ²−ρ²)/2)²] ∑_j ∫_{S_{ρ,σ}} |z_j(U)|²

is a continuous function of `U∈H³`, with the same original coefficients.

The actual physical H³ Fourier path is strongly continuous at strictly
positive times. Consequently the original nonlinear cost has automatic
physical-time continuity for every fixed `0≤ρ≤σ`. This removes the
`hYoung` premise from the existing annular-deficit continuity theorem and
its one-snapshot right-window viscous charge.

## Remaining frontier

The proof concerns **fixed finite annuli**. Its multiplier bound grows as
`σ³`. It supplies no cutoff-uniform or cofinal terminal-time modulus, no
uniform lower bound on the selected positive window widths, and no global
Navier–Stokes regularity result. Those remain substantive open goals.

## Verification

The accompanying registrar checks expected declarations and rejects `sorry`,
`admit`, and new axioms; the run script compiles the module with the user's
pinned Lean/mathlib toolchain, checks the audit and proof index, and refuses
to commit or push on compilation failure. No Lean compilation was possible
in the artifact-generation environment.
