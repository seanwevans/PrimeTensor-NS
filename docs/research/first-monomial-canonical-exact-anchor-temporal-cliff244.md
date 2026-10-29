# Canonical exact-anchor physical H³ temporal cliffs

Parent: `1bb9a082` — classify canonical H3 physical exposure intermittency and supercubic anchor escape.

## Hard mathematical step

Keep the **same** canonical disjoint witnesses `τ, N, K, C, δ, v`, with
`I_k = [τ(v k), τ(v k)+δ(v k)]`, `D_k = D₃(τ(v k))` and the **actual full**
physical dissipative mass `J_k = ∫_{I_k} D₃(t) dt`. The preceding theorem
establishes `J_k → 0`, `D_k > 3(v k+1)³/4`, and summability of `J_k`.

A direct integral comparison (no mean-value theorem, derivative or continuity
of `D₃`) proves: if `J_k < θ δ(v k) D_k` for `θ>0`, some actual physical
time `s_k ∈ I_k` satisfies

    D₃(s_k) < θ D₃(τ(v k)).

Since `J_k → 0`, for each fixed `η>0, θ>0` eventually

    δ(v k) D_k ≤ η
          OR
    ∃ s_k ∈ I_k, D₃(s_k) < θ D_k.

This is an **unconditional-on-width** temporal concentration alternative.
It holds on the original source-attaining, exact spectral-anchor windows,
without assuming a ninth/eighth annulus-width cap, linear PDE rate ceiling,
or regularity of the unbounded physical dissipation functional.

Under the additional explicit premise that for some `η>0` eventually

    η ≤ δ(v k) D_k,

the first arm is excluded (use `η/2`), so for every fixed `θ>0` the second
arm holds eventually. This is a rigorous relative **downward temporal cliff**.
It exposes the analytically precise obstruction to transporting the cubic
annulus persistence floor into uniform persistence of the FULL dissipation
height. The premise `η ≤ δ D_k` is not derived; neither continuation nor
contradiction is claimed.

## Lean declarations

1. `h3Path_scalar_smallPhysicalMass_peakChargeOrRelativeMean244`
2. `h3Path_physicalIntegral_small_forces_relativeDissipationDip244`
3. `h3Path_physicalVanishingWindowMass_chargeOrTemporalDip244`
4. `h3Path_physicalPersistentAnchorCharge_forces_temporalCliff244`
5. `h3Path_noL2Trace_exactAnchor_physicalTemporalCliffAlternative244`

The final theorem reconstructs its witnesses directly from
`h3Path_noL2Trace_exactAnchor_actualPhysicalExposureCollapse244`; all physical
preterminal hypotheses, absence of the strong terminal L² trace, and
finite full-H³ dissipation remain explicit.

To validate in the pinned repository: run the registrar, regenerate the proof
index, compile the module with `lake build`, then the full build and audit.
The package was statically checked, but no Lean toolchain is present in its
construction environment.
