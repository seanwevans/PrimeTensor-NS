# Critical H³ highpass third-radial forcing versus the actual fourth-Q forcing

Base HEAD: `cd57b576471ca341767abab6359c151761aae9cb`.

## Mathematical frontier

The preceding exact Fourier Pythagoras proof has removed the spurious factor of
2 in the physical cubic Leray source. Its remaining nonlinear obstruction is

    H_ρ(t) = Σ_j ||1_{|2πξ|≥ρ} |ξ|³ N_j(u,u)(ξ,t)||²₂.

Here `N_j` is **the actual projected Leray outer-product divergence**, not a
free source or a signed sixth-order energy flux. A high-frequency forcing
*norm* does not automatically enjoy the cancellation of the signed pairing.

The repo already constructs, at every strict physical time, the real
fourth-Q Hilbert forcing state

    G_j(t,ξ) = q(ξ)² N_j(u,u)(ξ,t),
    q(ξ)=(2π)²|ξ|².

Its relation to the third-radial physical forcing is pointwise:

    |G_j(t,ξ)| = (2π)³ |2πξ| · |F³_j(t,ξ)|.

For ρ>0 and |2πξ|≥ρ, the *exact Fourier multiplier inequality* gives

    (2π)^6 ρ² ||1_{|2πξ|≥ρ} F³_j(t)||²₂ ≤ ||G_j(t)||²₂.

No additional eighth raw Fourier moment condition is assumed by the theorem:
`G_j` is the existing canonical strict-time physical fourth-Q forcing state.
No terminal-uniform bound on `G_j` is asserted.

## Dyadic transfer

At the physical net log-growth peak `r` previously selected independently of
ρ, the sharp low/high estimate consequently implies, simultaneously for all
ρ>0,

    [K + Φ₅(r) + Φphase(r)] D₃(r)
        < 3 (2π)^6 L_ρ(E₀(b))
          + ρ⁻² Σ_j ||G_j(r)||²₂.

The low-band kinetic budget is the previously proved explicit
`thirdFullPhysicalCriticalThirdForcingKineticLowBudget244`:

    L_ρ(E) = ρ⁶ volume(|2πξ|<ρ) · (18 ρ E)².

This is a radius-adjustable **true upper bound on the nonlinear highpass**,
not merely a new necessary lower-charge statement. It exhibits an exact
one-derivative tradeoff. The right-hand fourth-Q term is not yet controlled
by fifth-order **velocity** dissipation or a terminal-uniform clock. The
latter step would require an additional physical nonlinear estimate, and is
not silently assumed.

## Proof targets

- `thirdFullKinetic_highpass_norm_le_of_oneRadialMoment244` — exact quotient-safe
  Bernstein estimate under an explicit a.e. frequency-moment premise.
- `thirdFullPhysical_thirdRadial_fourthQ_aeMoment244` — canonical physical
  identity for the *same* Leray source under the two multipliers.
- `thirdFullPhysical_thirdRadialHighpass_le_fourthQ244` — strict-time norm bound.
- `thirdFullPhysical_thirdRadialHighpass_fourthQ_square244` — squared bound
  with all `2π` factors retained.
- `thirdFullPhysical_nearCriticalAnchor_forces_fourthQSourceCharge244` — one
  net-growth witness and all subsequent positive cutoffs.

## Open hard math

Show a coercive solenoidal paraproduct/commutator bound on the fourth-Q forcing
in terms of **available** physical velocity moments and true fifth-order
viscous expenditure, with the frequency-local remainder explicitly tracked.
At a fixed smooth time, a fourth-Q mass is finite; that alone is not enough
for terminal continuation or to contradict the critical cubic profile.

This patch does not solve the Navier–Stokes global regularity problem.
