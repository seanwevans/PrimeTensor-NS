# The physical critical H3 source peak admits a kinetic low / Leray highpass fork

Base commit: `d0f570cedc30cc8efacda9a49a06b9392901c1fd`.

## Mathematical claim

The preceding dyadic convolution gate needed global raw order-eight Fourier
velocity moments to control the nonlinear order-three Leray forcing by
order-four convolutions.  These moments are **not** consequences of H3
admissibility and were never to be silently assumed.

Here we instead apply the genuine sharp radial Fourier projector to the
**already existing** canonical, physical, third-radial forcing L2 state:

- `F_j(t) = h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path ... j t`;
- `P_ρ = h3CriticalFourierSharpLowCutoffCLM ρ` with
  `S_ρ = {ξ : (2π)‖ξ‖ < ρ}`;
- `H_{ρ,j}(t) = F_j(t) - P_ρ(F_j(t))`.

All three are actual Hilbert states of the Navier–Stokes solution; `H` is
an exact high-frequency remainder and **not** an invented spectral carrier.

The accepted kinetic Bernstein estimate bounds the raw nonlinear Leray
forcing on `S_ρ` by `18 ρ E₀(b)` for every strict time after `b`.
The actual third-radial representative is `‖ξ‖³` times that raw forcing.
For `ρ≥0`, on `S_ρ` we have `‖ξ‖≤ρ` (we intentionally discard the positive
`2π` improvement to keep coefficients elementary). Thus, in Fourier L2,

    ||P_ρ(F_j(t))||² ≤ L(ρ,E₀(b)),
    L(ρ,E) = ρ⁶ · measure(S_ρ) · (18 ρ E)².

This is uniform in time after the kinetic anchor `b`; no eighth-order moment,
no H3 ceiling, and no global-in-frequency nonlinear source bound is used.

By the Hilbert triangle inequality,

    Σ_j ||F_j(t)||² ≤ 2 (3 L(ρ,E₀(b)) + Σ_j ||H_{ρ,j}(t)||²).

Hence the genuine physical cubic forcing mass obeys

    (2π)⁶ Σ_j ||F_j(t)||²
      ≤ 2(2π)⁶ [3 L(ρ,E₀(b)) + Σ_j ||H_{ρ,j}(t)||²].

On a physical last-half window `[s,t]`, the accepted critical dyadic
source-peak theorem, together with the strict near-critical anchor
hypothesis at `s`, forces an actual `r∈(s,t)` such that

    K D₃(r) < (2π)⁶ Σ_j ||F_j(r)||².

Combining the last two estimates and splitting a sum produces the **new
no-eighth-moment physical alternative at the same attained time `r`**:

    K D₃(r) < 12(2π)⁶ L(ρ,E₀(b))

or

    K D₃(r) < 4(2π)⁶ Σ_j ||H_{ρ,j}(r)||².

The cutoff `ρ` is arbitrary and fixed before the source-peak witness is
selected; in particular, the output is valid at every prescribed finite
cutoff, not at an adversarially selected one.

## Frontier exposed

For fixed `ρ`, the first branch is controlled by the initial kinetic
anchor and grows only with the explicit cutoff power and ball volume.
The second branch demands **genuine high-frequency nonlinear Leray source
mass**. Excluding this second branch by solenoidal cancellation, a dynamic
radial frequency decomposition, or viscous time-occupation is the next
new-mathematics task. This theorem does **not** establish the required
highpass upper bound or unconditional continuation.

The exact low/high decomposition is preferable to claiming a global
order-four convolution estimate under H3 alone: that would require an
unproved global velocity moment bound.

## Declarations

- `thirdFullPhysicalCriticalThirdForcingKineticLowBudget244`
- `thirdFullPhysicalCriticalThirdForcingHighpass244`
- `thirdFullPhysical_criticalThirdForcingHighpass_norm_sq_eq_integral244`
- `thirdFullPhysical_criticalThirdForcingLowSquare_le_kinetic244`
- `thirdFullKinetic_scalar_threeFourierLowHighSquare244`
- `thirdFullPhysical_criticalThirdForcingMass_kineticLowHigh244`
- `thirdFullPhysical_nearCriticalAnchor_forces_kineticLowOrForcingHigh244`

No axioms, proof placeholders or artificial path assumptions are introduced.
Run `lake env lean` and `lake build` in the user's configured Lean environment;
no Lean kernel is available in this packaging environment.
