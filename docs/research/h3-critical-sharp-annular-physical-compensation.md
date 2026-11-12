# Actual sharp physical kinetic compensation: annular Young-gap / outer-tail closure

Accepted HEAD: `87ee7173719e986ea8d5173f4cb198b11a6f4250` (split actual annular Young gap from outer Fourier tail).

## Hard mathematical step

The previous accepted theorem was an exact Fourier ledger for a **three-coordinate** constant-rate source mismatch, but the physical kinetic rigidity theorem was phrased in terms of the **real physical three-component L²** highpass. This module proves the missing *exact norm identity* using the repository's real Plancherel bridge and real physical sharp cutoff, so the two inequalities can be compared without introducing an abstract Fourier-to-physical surrogate.

For each real scalar physical pair `f,g`, the sharp highpass mismatch

    (f - P_ρ f) - rate · (g - P_ρ g)

has squared physical norm equal to the Fourier integral of `|Ff - rate·Fg|²` over `m(ξ)≥ρ`. The proof is quotient-safe in L² and explicitly handles real scaling under the complex Fourier transform. Summing all three coordinates yields the identity for the **actual strict-time** velocity `U(t)` and projected momentum source `R(t)`.

## Physical annular ledger

Fix a strict physical time `t∈(0,T)`, `0≤ρ≤σ`, and write

    m(ξ) = 2π|ξ|,     q(ξ)=m(ξ)²,
    A = {ρ≤m<σ},     H_ρ = {m≥ρ},     H_σ = {m≥σ},
    rate = (ρ²+σ²)/2,     width = (σ²-ρ²)/2,
    Z_j = raw Fourier velocity,   N_j = genuine Leray forcing,
    F_j = actual projected momentum Fourier source.

The new *physical* estimate, using `P_ρ` for the actual real physical sharp cutoff, reads

    ρ⁶ ||(I-P_ρ)R - rate (I-P_ρ)U||²
       ≤ 2 Σ_j ∫_A q³ |N_j+2qZ_j|²
         + 2 σ⁶ width² Σ_j ∫_A |Z_j|²
         + ρ⁶ Σ_j ∫_{H_σ} |F_j-rate Z_j|².

This equality-to-inequality transfer has no new integrability assumptions: those were discharged at accepted HEAD `3350b1854`. The outer-tail term is NOT suppressed.

## Signed kinetic excess requires paid spectral expenditure

Choose a strict kinetic-energy anchor `b<t<T`, set `E=E₀(b)`, and let

    U_hi = (I-P_ρ)U(t),   R_hi = (I-P_ρ)R(t),
    K(ρ,E) = 3 sqrt(E) * C_kin(ρ,E),
    C_kin(ρ,E) = ρ² sqrt(E) + sqrt( μ({m<ρ}) * (18ρE)² ).

The actual physical kinetic identity, the disjoint sharp Plancherel geometry and the existing low-band source Bernstein ceiling force

    rate ||U_hi||² - K ≤ ||U_hi|| · ||R_hi-rate U_hi||.

On the nonnegative-excess branch `K≤rate ||U_hi||²`, square and combine with the physical annular ledger to obtain

    ρ⁶ (rate ||U_hi||²-K)²
      ≤ ||U_hi||² [ 2 Gap_A + 2σ⁶ width² Mass_A + ρ⁶ Tail_σ ].

The theorem is valid for zero highpass mass; no division by its norm appears. It establishes a *physical necessary spectral payment constraint*, not a sufficient continuation criterion. The moving outer tail and annulus thickness still require a separate estimate. This is particularly important because the finite-annulus multiplier error grows with the moving outer radius.

## Declaration inventory and status

Five new theorems and one explicit cost definition are registered:

- `thirdFullKinetic_sharpFourierRateMismatch_normSquare244`
- `thirdFullKinetic_sharpPhysicalRateMismatch_normSquare244`
- `thirdFullPhysical_sharpActualRateMismatch_normSquare244`
- `thirdFullPhysicalActualAnnularLedgerCost244` (definition)
- `thirdFullPhysical_actualHighpassMismatch_le_annularLedger244`
- `thirdFullPhysical_kineticExcess_forces_annularYoungGapTail244`

The source introduces no `sorry`, `admit`, or new axiom. Full Lean 4/mathlib compilation must be performed in the repository's pinned environment; syntax and registrar checks do not establish kernel acceptance.
