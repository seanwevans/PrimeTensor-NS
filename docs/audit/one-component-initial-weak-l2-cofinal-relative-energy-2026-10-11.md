# Initial weak-L² cofinal trace closes the kinetic escape branch

Parent checkpoint: `2f0e4a66` (`exclude initial kinetic escape under bounded dyadic averages`).

## Mathematical result

A sequence of *actual old physical* real Hilbert `L²` velocities that converges weakly against every Hilbert test has a uniform `L²` norm bound. This is the uniform boundedness principle (`banach_steinhaus`) applied to the real Riesz functionals `innerSL ℝ (U n)`. The proof first derives pointwise boundedness of all test-pairing sequences from ordinary real sequential convergence, including their finitely many early terms.

For positive-time samples `τ n` cofinal at zero, the existing equality

`‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 = velocityH3Energy0At u t`

turns that norm bound into bounded cofinal kinetic anchors. The existing positive-time kinetic antitonicity then bounds the entire old `L²` trajectory on the initial interval, and the already-proved residual-dependent Gronwall argument gives uniqueness.

The weak limit is the physical time-zero vector of *the same old velocity*, assembled from the true time-zero `velocityH3L2JetAt` slots.

## Public declarations

- `h3Audit_initialScalarSequence_normBounded_of_tendsto`
- `h3Audit_initialWeakPairingBoundedSequence_normBounded`
- `h3Audit_initialWeakL2ConvergentSequence_normBounded`
- `h3Audit_initialActualPhysicalHilbertAtZero`
- `h3Audit_initialWeakL2CofinalSequence_kineticAnchors`
- `H3AuditInitialCanonicalWeakL2CofinalRelativeEnergyData`
- `h3Audit_initialWeakL2Cofinal_implies_kineticAnchorData`
- `h3Audit_initialWeakL2Cofinal_implies_compactWeakComparisonData`
- `h3Audit_initialWeakL2Cofinal_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialWeakL2Cofinal`

## Important limitations

The weak tests range over the *complete physical Hilbert space*. Compactly supported smooth test convergence alone cannot control kinetic mass escaping to higher frequencies or spatial infinity. Establishing this genuinely full-Hilbert initial weak trace is still an initial-value PDE obligation, and is **not** derived from open-time `LoggedPreterminalH3PathAdmissible` alone.

The epsilon-vanishing old/selected relative-energy inequality remains a separate PDE input. The terminal actual-vorticity strong-H³ endpoint remains an independent additional hypothesis. No claim of unconditional Navier–Stokes regularity is made.

Source patch was inspected and ZIP integrity-verified, but Lean/lake compilation is not available in the packaging environment.
