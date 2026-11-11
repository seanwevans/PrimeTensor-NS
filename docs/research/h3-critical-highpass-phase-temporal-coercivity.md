# Critical H³: the signed phase defect is an exact temporal Fourier square

Pinned base HEAD: `c26d3490307c261a4ff0d11832bc7f66def0ca46`.

## The physical identity that was missing

Write `q(ξ)=(2π)²|ξ|²`, `z=û_j(t,ξ)`, and `f=N_j(u,u)(t,ξ)`. The
signed phase density already formalized in the project is

    P(q,z,f) = q⁵|z|² + q³|f|² + 2 q⁴ Re⟨z,f⟩.

Its *exact* square completion is

    P(q,z,f) = q³ |q z + f|².

This is not the loose earlier amplitude-mismatch lower bound. It retains the
complex phase and the precise PDE combination. The project already proved the
actual strict-time PDE for the **fourth-radial time derivative**:

    ∂t V4_j(t,ξ) = -q³ z - q² f = -q²(q z + f).

Consequently, with no interpolation or assumed higher Fourier moment,

    |∂t V4_j(t,ξ)|² = q P(q,z,f).

## Sharp physical Fourier cutoff

For the exact complementary sharp cutoff `sqrt(q)≥ρ`, the multiplier satisfies
`q≥ρ²` whenever `ρ>0`. Applying the canonical a.e. fourth-radial PDE
representative and the genuine L² sharp highpass identity yields:

    ||H_ρ ∂t V4_j(t)||² = ∫_{sqrt(q)≥ρ} q P_j dξ

    ρ² ∫_{sqrt(q)≥ρ} P_j dξ ≤ ||H_ρ ∂t V4_j(t)||².

Integrating in frequency is justified using the already established strict-time
integrability of the physical fifth velocity mass, cubic forcing mass, and
signed nonlinear pairing. No time-uniform moment hypothesis is introduced.

Summing the three real-solenoidal coordinate representatives gives

    ρ² PhaseHigh(ρ,t) ≤ Σ_j ||H_ρ ∂t V4_j(t)||².

## Critical dyadic consequence

The accepted physical dyadic theorem at base HEAD selected one strict time
`r∈(s,t)` **independently of ρ**, where

    [K + Φ5(r) + Φphase(r)] D3(r)
      < 3(2π)⁶ LowBudget(ρ,E0(b)) + 2 FifthHigh(ρ,r) + 2 PhaseHigh(ρ,r).

Combining the exact highpass phase-to-time inequality supplies, for every
`ρ>0`, at the same selected time,

    [K + Φ5(r) + Φphase(r)] D3(r)
      < 3(2π)⁶ LowBudget(ρ,E0(b))
         + 2 FifthHigh(ρ,r)
         + (2/ρ²) Σ_j ||H_ρ ∂t V4_j(r)||².

The high-sixth velocity moment no longer appears in this representation. The
remaining fifth-viscous highband and fourth-temporal highband are actual
physical PDE quantities, but they **are not bounded uniformly** on terminal
tails here. This is a necessary spectral expenditure statement, not a global
regularity or continuation theorem. In particular, it does not identify a
sign-definite dissipative bound sufficient to absorb the entire right side.

## New declarations

1. `thirdFullKinetic_signedPhase_eq_temporalResidualSquare244`
2. `thirdFullKinetic_fourthTemporalSquare_eq_qSignedPhase244`
3. `thirdFullPhysical_highTemporalSquare_eq_qSignedPhaseBand244`
4. `thirdFullPhysical_highSignedPhase_le_highTemporal244`
5. `thirdFullPhysical_highSignedPhaseBand_le_temporalHighMass244`
6. `thirdFullPhysical_nearCriticalAnchor_forces_highFifthTemporalBand244`

No new axioms, sorry/admit, or additional physical regularity premises.
