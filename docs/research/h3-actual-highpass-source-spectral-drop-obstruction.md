# Actual projected source highpass drop: forced spectral displacement and temporal cost

Base: `c00bf9f6`, quantitative highpass Fourier source persistence from H³ spectral motion.

## PDE obstruction from the opposite direction

The completed source estimate bounds the highpass Fourier projected source of the **genuine** Navier--Stokes momentum RHS by a kinetic constant plus high-radial H³ dissipation. For arbitrary independent nonnegative dissipation radius σ and source radius ρ, and physical times t,s in the same strict kinetic tail, set

    U(r) = actual weighted H³ spectral velocity at time r
    H(r) = actual projected highpass Fourier source, coordinate i, cutoff ρ
    B = max(0,(3+C_L)(1+6E₀(b)+3(σ²W₃(σ)E₀(b)+M)))

If D_{>σ}(s) ≤ M, then **‖H(s)‖ ≤ B**. Therefore

    ‖H(t)‖-B ≤ ‖H(t)-H(s)‖
              ≤ (3+C_L(‖U(t)‖+‖U(s)‖)) ‖U(t)-U(s)‖.

This is a direct **necessary condition** for a *drop* of actual physical high-radial H³ dissipation. It requires neither a temporal continuity assumption on full dissipation nor any spectral-time rate. The estimate is independent of the highpass source frequency radius ρ in its Lipschitz constant.

If both endpoint H³ spectral states obey ‖U(t)‖, ‖U(s)‖ ≤ E and a separate spectral-time movement estimate ‖U(t)-U(s)‖ ≤ L(s-t) holds, then

    ‖H(t)‖-B ≤ (3+2C_L E)L(s-t).

For L>0, the first drop cannot occur before

    s-t ≥ (‖H(t)‖-B) / ((3+2C_L E)L).

This supplies the exact *two-time necessary lower-bound* counterpart of the previous sufficient positive persistence window. It quantifies the cost of losing a source peak; it does **not** derive a uniform L from the PDE, a source margin bounded below along the cofinal windows, a divergence of H³ dissipation, or global Navier--Stokes regularity. In particular the no-strong-terminal-trace branch is not asserted to occur.

## New declarations

- `h3Critical_sourceDriven_dissipationDrop_highpassNorm_le_barrier`
- `h3Critical_sourceDriven_dissipationDrop_forces_spectralDisplacement`
- `h3Critical_sourceDriven_dissipationDrop_forces_temporalCost`
- `h3Critical_sourceDriven_dissipationDrop_minimalElapsedTime`

The source should be elaborated under the pinned Lean/Mathlib toolchain. ZIP structure and Python registrar checks are not Lean proof certification.
