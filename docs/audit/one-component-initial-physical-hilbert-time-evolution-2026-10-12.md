# Strong positive-time physical Hilbert momentum evolution

Base checkpoint: `698ab972` — `transfer canonical weak FTC to absolute physical momentum evolution`.

## This patch

Adds `PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialPhysicalHilbertTimeEvolution.lean`, importing the earlier absolute weak FTC transfer.

Theorems:

1. `h3Audit_initialCanonicalWeakFTC_implies_physicalHilbertEvolution_onElapsed`: upgrades the canonical divergence-free weak FTC to the exact Bochner integral identity for the **actual** physical L² Hilbert velocity on the absolute-time interval, using the previous solenoidal density/uniqueness lemma and the identified physical projected RHS.
2. `h3Audit_initialCanonicalWeakFTC_implies_physicalHilbertHasDerivAt_onElapsed`: gives strong Hilbert `HasDerivAt` with the physical spectral Laplacian-minus-Leray source on strict interior times.
3. `h3Audit_initialOldJoint_implies_physicalHilbertEvolution_onElapsed`: specializes the evolution identity using the existing old-branch weak FTC implication from temporal-derivative joint continuity.
4. `h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_onElapsed`: the corresponding strong derivative on a canonical short interval.
5. `h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime`: uses existing local-window coverage to obtain the strong L² momentum derivative for every positive preterminal time.
6. `h3Audit_initialOldJoint_implies_physicalHilbertContinuousOn_positiveTime`: derives physical L² continuity on `(0,T)`.

## What is *not* closed

- The old temporal-derivative **joint-continuity assumption** is still explicit. Bare `LoggedPreterminalH3PathAdmissible` does not prove it here.
- Local canonical solenoidal weak FTC is an explicit input to the general local results; it is discharged only under the existing additional joint-continuity premise.
- Initial-time H³ energy integrability, initial relative-energy residual vanishing, and the terminal actual-vorticity endpoint are separate.
- No global regularity conclusion or new axiom is asserted.

## Validation

The artifact environment does not contain `lake` or `lean`. Run `lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Audit/OneComponentInitialPhysicalHilbertTimeEvolution.lean` and then `lake build` in the full Rocky Linux repository. The patch is **not claimed to be locally typechecked**.
