# Actual physical L² source–viscous dissipation synchronization (2026-10-24)

Parent checkpoint: `9acad351`, global positive-time physical Hilbert FTC and kinetic derivative.

This increment addresses the nontrivial identification between two independent derivatives. The old physical Hilbert norm-square agrees with `velocityH3Energy0At u` for every strict positive time. Since `(0,T)` is open, this gives an equality of germs at each time, not merely a coincidence at one time. Thus its strong physical derivative (`2⟨U,R⟩`) agrees with the scalar PDE order-zero energy derivative. The latter is `velocityH3DiffusionDerivative0At` by the already-proved order-zero transport/pressure cancellations, and is `-2 velocityH3Dissipation0At` by whole-space integration by parts.

Exact result, on `0<t<T`:

    ⟨U(t), R(t)⟩ = -D0(t),
    (d/dt) ‖U(t)‖² = -2 D0(t).

The order-one H³ energy is definitionally `D0` and differentiable through the existing positive-time energy-class cover. Hence `D0` is continuous on the open physical time interval and Bochner/real interval-integrable on every strict compact interval. For `0<s≤t<T`, the true kinetic budget follows without an extra integrability assumption:

    ‖U(t)‖² + 2 ∫_s^t D0(r) dr = ‖U(s)‖².

The last theorem uses the exact physical zero-jet identity to express the same result with the scalar order-zero kinetic energy.

**Scope:** Only a strict preterminal-time identity relative to the existing H³ path admissibility. The formalized old classical NS PDE, curl weak-FTC, physical selected/old agreement, pressure-gradient joint continuity and physical Hilbert derivative are inherited from previous modules. The result does not assert a new terminal H³ bound, integrability at time 0, or regularity across a possible singular time T.
