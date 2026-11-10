# Critical H³ third-Q physical heat: fifth viscous low band versus sixth high band

**Base HEAD:** `e52748c30428a0fb69bf74dada36c6cebe606211`.

## The actual spatial derivative gap

The preceding accepted physical PDE gate resolves the fourth-Q nonlinear Leray
source into the fourth-radial velocity time derivative and the third-Q velocity
heat state. The latter has multiplier `q³` in the Fourier representation,
where `q(ξ) = (2π)²|ξ|²`. Its squared norm is the **sixth** velocity moment
`∫ q⁶ |û|²`; the available genuine fifth viscous expenditure is only
`M5 = Σ_j ∫ q⁵ |û_j|²`.

We do **not** bound `∫q⁶|û|²` by `M5`; such a global inequality would lose
one full derivative and is false without an additional frequency bound.

At any radius `ρ≥0`, on the sharp radial region `sqrt(q)<ρ`, however,

    q⁶ |û_j|² ≤ ρ² q⁵ |û_j|².

The actual cutoff Hilbert state therefore obeys

    Σ_j ||P_ρ Q³ û_j(t)||² ≤ ρ² M5(t).

The Fourier projection is orthogonal, hence with the **exact complementary
sixth-velocity state** `H6_ρ(t) = Σ_j ||(1-P_ρ) Q³ û_j(t)||²`:

    Σ_j ||Q³ û_j(t)||² ≤ ρ² M5(t) + H6_ρ(t).

This uses the existing strict-time physical third-Q Hilbert state, its a.e.
Fourier representation, and the already established `q⁵` integrability; no
raw order-eight velocity moment hypothesis is supplied.

## Critical source clock transfer

The accepted net-growth witness `r∈(s,t)` works for **every** later cutoff
`ρ>0`. In terms of the genuine physical fourth-radial time derivative
`D4_time(r) = Σ_j ||∂_t V4_j(r)||²` and normalized fifth and phase costs,

    (K + Φ5(r) + Φphase(r)) D3(r)
       < 3 (2π)^6 L_ρ(E0(b))
         + 2 ρ⁻² [D4_time(r) + ρ² M5(r) + H6_ρ(r)].

Here `M5(r)=Φ5(r)D3(r)` is exact on strict physical positive-D3 times.
The uncontrolled term is no longer the *whole* third-Q heat norm, but only
its genuine high-sixth Fourier tail, plus the actual fourth-radial temporal
change.

**Not proved:** a bound on this high-sixth remainder by `M5` uniform near
the terminal time, any solenoidal cancellation in the positive norm-square,
or unconditional smooth continuation. The direct PDE obstruction is now a
low-fifth/high-sixth/temporal charge with exact physical Fourier meanings.

## Declarations

- `thirdFullKinetic_fifthSixthLowBand_density_le244`
- `thirdFullPhysical_thirdQHeatLowSquare_le_fifthCoordinate244`
- `thirdFullPhysical_thirdQHeatLowSquare_le_fifthMass244`
- `thirdFullPhysicalCriticalThirdQHeatHighpass244`
- `thirdFullPhysical_thirdQHeatSquare_le_fifthPlusHigh244`
- `thirdFullPhysical_nearCriticalAnchor_forces_fifthTemporalHighSixth244`

This patch has no additional axioms or placeholders. Lean kernel verification
must be performed in the target repository against the pinned base commit.
