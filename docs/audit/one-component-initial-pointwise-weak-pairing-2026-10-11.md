# Initial pointwise weak-pairing boundedness and fixed-test escape obstruction

Parent checkpoint: `a2cb2c82` (`derive initial kinetic control from weak L2 cofinal trace`).

## Substantive reduction

Prior weak-L² criterion `H3AuditInitialCanonicalWeakL2CofinalRelativeEnergyData`
assumed that every real Hilbert pairing of the actual old velocity along a
cofinal positive-time sequence converges to the pairing of the physical
initial-time L² jet. Its kinetic-bound step used convergence only to obtain
one (test-dependent) bound for each scalar pairing.

This module makes that strictly weaker input explicit:

    ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      ∃ C : ℝ, ∀ n : ℕ,
        ‖((innerSL ℝ) (oldPhysicalVelocity (τ n))) ψ‖ ≤ C.

The already-proved `h3Audit_initialWeakPairingBoundedSequence_normBounded`
(Banach–Steinhaus) supplies a uniform Hilbert norm bound on the samples. The
exact physical zeroth-order identity
`h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy` gives bounded
actual kinetic-energy samples. The genuine Navier–Stokes positive-time
antitonicity theorem then propagates the ceiling across the whole initial
interval. No sequential weak limit has to be identified or assumed.

The bridge from the prior sequential weak convergence hypothesis to this
weaker boundedness is proved independently, so old callers remain valid.

## Contrapositive obstruction

If `velocityH3Energy0At u` tends to `atTop` along the right-zero filter, and
`τ` is any cofinal positive-time sample family inside `(0,b)`, then there is
**one fixed full physical L² test** `ψ` such that

    ∀ C : ℝ, ∃ n, C < ‖innerSL ℝ (oldPhysicalVelocity (τ n)) ψ‖.

The result does not say the witness is compactly supported or Schwartz, nor
that the test can be chosen in a predetermined countable compact-test family.
Such stronger conclusions do not follow without additional compactness or
tightness bounds.

## Limitations

1. Pointwise bounded full-Hilbert pairings are themselves an independent
   initial-value requirement. Without a genuine initial condition or kinetic
   budget they do not follow from `LoggedPreterminalH3PathAdmissible`.
2. The vanishing epsilon-dependent old/selected relative-energy residual is
   still required to deduce initial comparison uniqueness.
3. The terminal actual-vorticity strong-H³ endpoint remains independently
   hypothesized for the two transverse whole-time estimates.
4. This ZIP is packaged without running the project's Lean compiler locally;
   the supplied Rocky Linux script compiles and audits before committing.

## New public entry points

- `h3Audit_initialPointwiseWeakPairings_kineticAnchors`
- `h3Audit_initialPointwiseWeakPairings_uniformOldL2`
- `h3Audit_initialKineticEscape_fixedUnboundedWeakProbe`
- `H3AuditInitialCanonicalPointwiseWeakPairingRelativeEnergyData`
- `h3Audit_initialPointwiseWeakPairing_implies_kineticAnchorData`
- `h3Audit_initialWeakL2Cofinal_implies_pointwiseWeakPairingData`
- `h3Audit_initialPointwiseWeakPairing_implies_compactWeakComparisonData`
- `h3Audit_initialPointwiseWeakPairing_implies_physicalZeroJetAndEnergyUpper`
- `h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPointwiseWeakPairing`
