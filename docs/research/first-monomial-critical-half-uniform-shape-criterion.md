# Uniform critical-half coefficient: exact positive-shape threshold

**Baseline:** `cbc2a73a` (`prove actual critical-half Schwartz profile dilation bound`).

This module moves beyond the **fixed-shape dilation-orbit** result. It proves
an exact logical equivalence about the *existing actual* complete physical
first monomial and H³ dissipation, for arbitrary three-component real Schwartz
velocities on PrimeTensor's positive-depth axis carrier.

Let `M(f)` denote `lowNormalRealSchwartzPoint3Monomial f`, let `E(f)` denote
`lowNormalRealSchwartzH3EnergyQuadratic f`, and let `D(f)` denote
`lowNormalRealSchwartzH3TopDissipation f`.

For each fixed `C ≥ 0`, these **two universal statements** are equivalent:

    for every real Schwartz f:   M(f) ≤ C sqrt(1 + E(f)) D(f)

    for every real Schwartz f with M(f)>0: M(f)² ≤ C² D(f)² E(f).

The necessity uses every positive amplitude of f, the previously formalized
amplitude laws (cubic monomial, quadratic energy, quadratic dissipation), and
the existing `criticalHalfEnergyRayBound_iff` theorem. It **does not** drop
the `+1` by an unjustified inequality. Sufficiency uses nonnegativity of
both energy and dissipation and real-square monotonicity.

The *critical-half shape excess* is exactly

    X_C(f) = M(f)² - C² D(f)² E(f).

The module proves `X_C(a·f) = a⁶ X_C(f)` for all real amplitudes, including
negative ones. For M(f)>0 and X_C(f)>0, coefficient C is ruled out for the
universal inequality. The same-C coefficient-existence equivalence is included.

The module also states and proves the SAME equivalence **restricted to the
actual Point3 divergence-free Schwartz class**. Its predicate uses the
project's physical coordinate derivatives; its proof first establishes
that real amplitude scaling preserves Point3 solenoidality. That step is
required because the necessity direction examines arbitrarily large positive
amplitudes of the same admissible profile. Thus the solenoidal version is an
exact characterization of the remaining user-facing mathematical frontier.

**Open:** It is not proved that one universal C exists, that X_C(f)>0 occurs
for arbitrarily large C, or that the Navier--Stokes PDE continues or blows up.
The next mathematical task is a genuine uniform *shape* estimate or a
counterexample across varying Schwartz profiles, not another fixed dilation
identity.

This archive's Python registration and ZIP structure can be verified without
Lean. The actual Lean proof must be checked with `lake env lean`, `lake build`
for the new module, `lake env lean tools/audit/FirstMonomialTriad.lean`, and
`lake build`. No `sorry`, `admit`, or axioms are introduced.
