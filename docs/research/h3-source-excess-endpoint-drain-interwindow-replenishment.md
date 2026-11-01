# Source-excess H³ endpoint drain and transport replenishment

Base: `fd341b6f`, the accepted signed-energy competition on the cofinal quintic source-excess windows.

## From pointwise signs to whole-window endpoint cost

The actual strict-time physical H³ energy E(s) is differentiable by the already proved `H3OrderEnergyDerivativeIdentities`. On each certified source window `[t_k,t_k+δ_k]`, set

    H_k = M(vk) + q(vk)/κ,   κ = 3(3+C_L)>0.

The prior signed energy and retained-viscosity Riccati estimates give at every time inside the window

    E'(s) ≤ -H_k   OR   H_k < K sqrt(E(s)) E(s).

Here K is the established physical H³ Riccati coefficient. If the second disjunct never holds, the derivative of `F(s)=E(s)+H_k*s` is nonpositive throughout the window. Convex-interval monotonicity yields the **unconditional endpoint alternative**

    (∃ s∈[t_k,t_k+δ_k], H_k < K sqrt(E(s)) E(s))
        OR
    E(t_k+δ_k)+H_k δ_k ≤ E(t_k).

This is a real endpoint drain: the full interval pays `H_k δ_k` in actual energy loss unless the genuine Riccati energy term crosses the high source floor somewhere. No Lebesgue integrability of the full dissipation or of the signed energy derivative is needed for the endpoint argument; it uses differentiability and calculus on a compact strict-time interval.

## Energy compensation between the source windows

If any pair of separated windows has a genuine energy recovery,

    E(t_k+δ_k) < E(t_l)    (k<l),

then the scalar energy cannot be nonincreasing across the gap. Applying the antitone-from-nonpositive-derivative theorem contrapositively yields a real intermediate time

    s ∈ (t_k+δ_k, t_l),   E'(s)>0.

The exact physical identity `E'(s)+2D(s)=-Transport(s)` implies

    2D(s) < -Transport(s).

Thus any net replenishment of drained H³ energy requires signed nonlinear transport to overcome both copies of the physical dissipation at an actual time **between the original selected windows**.

## Scope

The new cofinal theorem preserves the original disjointness, the enhanced source-driven viscous floor, the full extended physical H³ dissipation cost sum, and the three-way quintic local budget gate. It adds the whole-window endpoint drain/large-energy alternative and the inter-window replenishment transport consequence. It asserts no terminal-uniform ceiling, integrable transport, global regularity, or impossibility of either remaining branch.

Lean declarations:

- `h3Critical_actualH3Energy_differentiableAt_onStrict`
- `h3Critical_scalar_uniformDrain_forces_endpointCost`
- `h3Critical_scalar_signedCompetition_forces_endpointOrRiccati`
- `h3Critical_sourceExcessWindow_endpointDrain_or_RiccatiEnergy`
- `h3Critical_scalar_endpointReplenishment_forces_positiveSlope`
- `h3Critical_interWindowH3Replenishment_forces_signedTransportOvershoot`
- `h3Critical_noL2Trace_cofinalQuintic_endpointDrain_or_gapTransport`

The source package receives only static validation here; run Lean and the full pinned repository audit on the user's machine.

## Lean elaboration correction (fix1 at `fd341b6f`)

In the scalar endpoint argument, `HasDerivAt.add` produces the derivative
of the *sum of functions* `E + (fun s => H * s)`. The original `F` was
written as the pointwise lambda `fun s => E s + H * s`, which did not match
under `simpa only [F]`. Define `F` directly as the sum of functions, and
normalize its endpoint evaluations using `Pi.add_apply`. The statement and
the derivative/antitonicity argument are unchanged.
