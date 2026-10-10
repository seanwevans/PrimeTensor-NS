# Full-time physical homogeneous H³ᐟ² under an initial strong H³ spectral path

Parent checkpoint: `c0c7db2c`, *derive initial H3 spectral bounds from physical energy continuity*.

The earlier full-time criterion assumed scalar `ContinuousAt (velocityH3EnergyAt u) 0`.
The preterminal H³ path interface only guarantees continuity for `0<t<T`.

This patch replaces the initial physical-energy continuity hypothesis with an
explicit **spectral strong-path** condition: there is a Fourier H³ velocity-state
path `U : ℝ → H3SpectralVelocityState` continuous at `t=0`, and for every
strictly preterminal time its components agree with the genuinely encoded,
actual physical velocity states. Continuity bounds `‖U t‖` uniformly for
small positive `t`, which bounds all physical component H³ spectral states.
The already proved early/late gluing then gives full `(0,T)` intrinsic
`L²_t Ḣ^(3/2)_x` for one or both transverse components under the physical
strong-terminal endpoint hypothesis.

The newly defined `H3AuditInitialStrongH3SpectralVelocityPath` is an explicit
hypothesis, not a derivation of strong-path regularity from one H³ initial
snapshot. Its full-line continuous extension around t=0 is a convenient
sufficient interface for the usual one-sided strong solution path; it does
not claim initial continuity for all admissible open-time H³ paths.

Remaining: prove this strong spectral path from the precise initial-data
and local-strong-solution construction; connect the paper's solution class
and its one-component continuation theorem to the repository's real restart.
No new axioms, `sorry`, or unconditional Navier–Stokes conclusions.
