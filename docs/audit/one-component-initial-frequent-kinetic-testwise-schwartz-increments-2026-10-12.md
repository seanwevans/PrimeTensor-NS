# Frequent kinetic anchors + testwise Schwartz weak sequences

Parent checkpoint `6373bde8`: initial strong physical L² trace from
ONE joint right-zero sequence and positive-time Schwartz L¹ increments.

This module weakens BOTH sampled initial requirements.

## Kinetic samples: liminf-type, not eventual

For one right-zero kinetic sequence τ, the energy need only be
below E₀(0)+ε at arbitrarily large indices:

    ∀ ε > 0, ∀ N, ∃ n ≥ N, E₀(τ n) ≤ E₀(0)+ε.

This corresponds to an *upper bound on the sampled liminf*, not
the stronger sampled limsup bound from the previous joint contract.
The exact positive-time H³ kinetic antitonicity upgrades those
frequent good samples to the full exact bound E₀(t)≤E₀(0).
It then implies the older eventual energy bound automatically.

## Weak initial tests: independent sequences

Each three-component physical Schwartz test Φ may use its own
right-zero weak matching sequence σΦ. Test-dependent positive-time
scalar L¹ increments yield a unique scalar right limit for Φ.
The matching sequence identifies this constant with the prescribed
initial pairing, so the weak right limit applies on any right-zero
sequence — notably the kinetic witness τ.

This manufactures the existing
`H3AuditInitialJointKineticSchwartzIncrementData`
from weaker, asynchronous initial observations and reuses its
existing strong physical L² / kinetic trace theorem.

## New declarations

1. `h3Audit_initialFrequentScalarSequence_cofinalApproximateAnchors`
2. `h3Audit_initialFrequentKineticSequence_exactPositiveCeiling`
3. `h3Audit_initialFrequentKineticSequence_eventualUpper`
4. `h3Audit_initialSchwartzPositiveIncrements_anchoredFTC_of_testwiseSequences`
5. `h3Audit_initialSchwartzPositiveIncrements_syncTestwiseWeakToSequence`
6. `H3AuditInitialFrequentKineticTestwiseSchwartzIncrementData`
7. `h3Audit_initialFrequentTestwiseData_implies_jointKineticSchwartzData`
8. `h3Audit_initialFrequentKineticTestwiseIncrements_physicalAndKineticRightTrace`

## Unproved PDE-facing obligations

- The frequently good kinetic samples must be supplied.
- Each Schwartz test must have an initial weak matching sequence.
- Its positive-time scalar L¹ increment equation must be supplied.

These do not follow from strictly positive-time H³ admissibility alone.
No unconditional 3D Navier--Stokes regularity, terminal strong-H³
physical vorticity, or continuation beyond T is concluded.

## Required build order

Register the Lean module in `PrimeTensor.lean` and all theorem
checks in `tools/audit/Contracts.lean`, then run the full
source-index regeneration and check BEFORE any Lake compilation:

    python3 proof/generate_index.py
    python3 proof/generate_index.py --check
    python3 proof/check_fragment.py --all

Commit regenerated `proof/order.txt` together with the source.
The ZIP environment cannot compile Lean and makes no build claim.
