# Localized fourth-Q PDE: full fifth dissipation retained at critical H³ peaks

Base HEAD: `35469100b644bc78c09df2fbcbe9a637b534ef0e`.

## Why the previous half-absorption was not sharp

The accepted two-radius estimate first replaced the high-third nonlinear
forcing by the **full** fourth-Q forcing. Using the PDE on the full fourth-Q
norm then paid the entire third-Q heat cost, including its low band. The
additional heat split returned part of the fifth viscosity to the right.

That detour is unnecessary: highpass third-radial forcing depends only on
highpass fourth-Q forcing at the SAME cutoff.

At a strict physical time let

- `F3_j(ξ) = |ξ|³ N_j(u,u)(ξ)` be the true third-radial Leray forcing;
- `G4_j(ξ) = q(ξ)² N_j(u,u)(ξ)` the true fourth-Q forcing;
- `D4_j = ∂t V4_j` the fourth-radial temporal Fourier state;
- `Q3_j(ξ) = q(ξ)³ û_j(ξ)` the third-Q velocity heat state;
- `Hρ = I - Pρ`, the sharp complementary Fourier cutoff at `sqrt(q)=ρ`.

Because `|G4_j|=(2π)³ sqrt(q) |F3_j|` and `sqrt(q)≥ρ` on the complement,

    (2π)^6 ρ² ||Hρ F3_j||² ≤ ||Hρ G4_j||².

The exact physical PDE is `G4_j = -D4_j - Q3_j`. Linearity of the native
complex-L² projection gives, *before any triangle inequality*,

    Hρ G4_j = -Hρ D4_j - Hρ Q3_j,

    ||Hρ G4_j||² ≤ 2(||Hρ D4_j||² + ||Hρ Q3_j||²).

Combining these with the accepted SHARP low-Leray kinetic estimate gives,
for every physical `r>b` with `D3(r)>0` and every `ρ>0`,

    [signedLog(r) + Phi5(r) + PhiPhase(r)] D3(r)
      ≤ 3(2π)^6 Lρ(E0(b))
          + (2/ρ²) [T4_high,ρ(r) + H6_ρ(r)].

The compact critical dyadic log-growth argument then selects a single
actual time `r∈(s,t)` **before** choosing ρ; at that same time,

    [K + Phi5(r) + PhiPhase(r)] D3(r)
      < 3(2π)^6 Lρ(E0(b))
          + (2/ρ²) [T4_high,ρ(r) + H6_ρ(r)]

for every subsequently chosen ρ>0.

## Gains and strict limits

- Full genuine fifth-order viscous expenditure stays on the left, not half.
- Temporal fourth-derivative cost is HIGH-frequency localized; no full temporal
  square norm is charged.
- The sixth-order heat remainder begins at ρ, rather than ρ/2.
- Only existing strict-time physical states and the established kinetic anchor
  are used; no eighth-order raw velocity moment assumption is added.

No terminal-uniform bound of either high temporal or high sixth heat cost is
proved. The argument cannot be converted into a Navier--Stokes continuation
result without an additional solenoidal/parabolic mechanism.

## Declarations

- `thirdFullKinetic_highpass_norm_le_highpass_oneRadialMoment244`
- `thirdFullPhysical_thirdRadialHighpass_le_fourthQHighpass244`
- `thirdFullPhysical_thirdRadialHighpass_fourthQHighpass_square244`
- `thirdFullPhysicalCriticalFourthTemporalHighpass244`
- `thirdFullPhysical_fourthQHighpass_eq_temporalHigh_sub_thirdQHigh244`
- `thirdFullPhysical_fourthQHighpassSquare_le_temporalHighThirdQHigh244`
- `thirdFullPhysical_fourthQHighpassSum_le_temporalHighThirdQHigh244`
- `thirdFullPhysical_signedLogFifthPhase_le_localizedFourthQ244`
- `thirdFullPhysical_nearCriticalAnchor_forces_localizedTemporalSixth244`
