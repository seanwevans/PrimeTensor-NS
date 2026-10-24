# Physical kinetic terminal-tail dissipation and source action

Baseline: `d87a460b`.

The project already proved kinetic antitonicity and the finite terminal
kinetic left limit `L = h3PathCanonicalTerminalKineticEnergyAt u a T` from
`hH3` and a selected `PreterminalH3EnergyClass u a T`, without additional
`CanonicalH3EnergyDataOnTail` or a prescribed endpoint state.

The new ingredient is the **exact** physical kinetic balance recently
closed through old-pressure Fubini and Hilbert differentiation:

    E0(t) + 2 ∫_s^t D0 = E0(s).

Since `L ≤ E0(t)` for every `t ∈ (a,T)`, the remaining dissipation satisfies

    2 ∫_s^t D0 ≤ E0(s) - L.

The right side tends to zero as `s ↑ T`. Hence for every ε>0, eventually
in the left-terminal filter, *every* `t ∈ [s,T)` obeys

    2 ∫_s^t D0 < ε.

The actual physical Hilbert source satisfies `⟪U,R⟫ = -D0`, so its signed
integral converges to `(L-E0(s))/2`. This is a synchronized signed kinetic
source limit, not a bound on `‖R‖`, the absolute source integral, or any
order-three dissipation `D3`. It does not establish terminal smoothness,
strong endpoint velocity trace, or a positive lower bound for `L`.

The source of the finite limit is the earlier `KineticQuartic...CubicClockWithoutCanonicalData`
module; this package uses, rather than reproves, that endpoint result.
