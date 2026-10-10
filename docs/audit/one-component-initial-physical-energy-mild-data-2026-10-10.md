# Discharge the initial physical Picard ball using actual H³ energy

Parent checkpoint: `9937ef45` — normalize initial physical H3 mild solution for uniqueness.

## Progress

The earlier physical-time initial mild contract required the *abstract* uniform
bound `‖P q‖ ≤ 2*A` on every point of the canonical unit-viscosity restart
interval. This change replaces it by the **actual physical velocity H³ energy
ceiling** `sqrt(velocityH3EnergyAt u t) ≤ 2*A` at all strict positive times
through the restart radius.

The canonical Fourier encoder's existing theorem
`norm_velocityH3SpectralStateAt_le_sqrt_energy` proves that, whenever the old
continuous physical-time path agrees with the actual Fourier velocity state,
its norm is automatically ≤ the physical square-root energy. At the zero-time
endpoint, the separately stated initial-value identity `P 0 = U₀` and
`‖U₀‖ ≤ A` give the required bound. This closes the full Picard-ball bound
without taking it as an explicit assumption.

The resulting `H3AuditInitialOldPhysicalMildDataAt` follows by a theorem.
Previous uniqueness then produces the canonical old/selected overlap,
actual one-sided Fourier H³ trace, and full-time physical homogeneous
H^(3/2) time-L² criterion for either or both transverse components.

## Important remaining hypotheses

`H3AuditInitialPhysicalEnergyMildDataAt` STILL presupposes:

- A bounded continuous physical-time H³ spectral path `P` on the canonical
  restart interval, identified with the **actual** Fourier velocity at every
  positive time.
- The exact signed heat-minus-Duhamel mild identity for that path.
- The initial-state identity `P 0 = U₀`.
- The quantitative old physical-energy ceiling `sqrt(E_H3(t)) ≤ 2*A`.
- A full canonical-radius interval within the old solution's lifespan.

This does not derive local strong solutions from arbitrary initial data or
prove Liu–Zhang continuation or global Navier–Stokes regularity. In particular,
the physical energy ceiling may follow from an initial H³-continuity theorem,
but that theorem is not asserted for the open-time H³ path class.
