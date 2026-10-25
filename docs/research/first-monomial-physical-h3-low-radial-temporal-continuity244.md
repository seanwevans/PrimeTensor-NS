# Bounded-frequency physical H³ dissipation: automatic temporal continuity

**Base:** `d6bb2605` — absolute high-radial dissipation evacuation at all fixed cutoffs.

The previous terminal-window theorems retained two scalar continuity hypotheses:
(1) low-radial physical dissipation, and (2) full physical H³ dissipation.
This increment removes the *first*, but not the second.

## The Fourier multiplier

On the native weighted spectral state `G : H3SpectralVelocityState`, define

    M_ρ(G_j)(ξ) = 1_{|D(ξ)| < ρ} |D(ξ)| G_j(ξ).

Its coefficient is measurable and bounded by `ρ + 1` when `ρ ≥ 0`.
The `Lp` multiplier is complex-linear and bounded; Mathlib's native `Lp` norm
identity then gives the exact **three-coordinate** quadratic formula

    D_low(ρ,G) = sum_{j=0}^2 ‖M_ρ(G_j)‖².

Because each `M_ρ` is continuous linear, `D_low(ρ,·)` is a continuous map
on the native weighted spectral velocity Hilbert state. Existing
`h3Audit_initialActualSpectralVelocity_continuousOn` establishes strong
continuity of the genuine spectral velocity on `(0,T)`. Composition yields

    ContinuousOn (fun t => D_low(ρ,S(t))) (Ioo a T).

No unproven temporal differentiability, no pointwise Fourier evaluation,
and no fourth-order global bound are required.

## Consequence for cubic integrated windows

The already proved cubic snapshot and integrated-window alternative now needs
only continuity of the **full** physical H³ dissipation, since continuity of
the bounded-frequency term is automatic. This is not itself a quantitative
window-width bound: the time-integrated cubic height estimate still carries
an uncontrolled positive width.

Strong `H³`-spectral continuity does **not** automatically imply continuity of
the *unbounded* full H³ dissipation quadratic `∫ |D|² |G|²`. That is the
remaining fourth-order temporal regularity frontier.

## Build gate

Use `lake env lean` on the new module, `lake build` on the module, regenerate
`proof/order.txt` with `python3 proof/generate_index.py`, check the index,
run a full `lake build`, and run the audit baseline. No new axioms or admits
are intended. Local compilation still needs to be performed.
