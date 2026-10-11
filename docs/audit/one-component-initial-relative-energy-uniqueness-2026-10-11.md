# Initial canonical overlap from a scalar relative-energy inequality

Checkpoint `8e3e2a8a` proved that physical compact weak-test equality implies
actual-old/canonical-selected weighted H³ overlap. However the equality of
the two solutions was still an assumption. This patch replaces it with the
ordinary derivative-free scalar relative-energy inequality.

Write `D(t)` for the three-component physical `L²` difference between the
actual old velocity at positive time `t` and the canonical selected mild
velocity restarted at the genuine encoded initial datum. Set `D(0)=0` as a
bookkeeping convention (it does **not** prove initial right continuity).

The PDE-facing data asks for (1) independent strong `L²` continuity of this
anchored difference on `[0,b]`; and (2) a finite nonnegative constant `K`
and an integral energy inequality

    ‖D(t)‖² ≤ K ∫₀ᵗ ‖D(s)‖² ds.

A standalone continuous integral Grönwall argument proves `D(t)=0` throughout
`[0,b]`. At each strict positive physical time, the coordinatewise identity
immediately implies all compact weak-test comparisons. The previously audited
compact-test-density / realizable-real-decoder-injectivity bridge then gives
actual weighted H³ spectral overlap, initial physical `L²` convergence, and
right H³ energy continuity.

The integral relative-energy inequality is not proved from the physical
Navier–Stokes PDE here. Neither is continuity at time zero: continuity of
`D` at the artificially zero-valued endpoint is a genuine initial-value
obligation, and must **not** be supplied from the canonical overlap itself.
The terminal actual-vorticity H³ endpoint remains separate.

Main declarations:
- `h3Audit_initialRelativeEnergy_integralGronwall`
- `h3AuditInitialCanonicalPhysicalDifference`
- `H3AuditInitialCanonicalRelativeEnergyData`
- `h3Audit_initialRelativeEnergy_implies_compactWeakComparisonData`
- `h3Audit_initialRelativeEnergy_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialRelativeEnergy`

No `sorry`, `admit`, or new axioms. The source requires compilation in the
project's Lean/mathlib environment before it can be treated as verified.
