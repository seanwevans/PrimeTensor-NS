# Initial energy ceiling + one self pairing: direct strong physical trace

Checkpoint: `e77804b8` — derive exact positive kinetic ceiling from integrable initial budget.

New generic Hilbert results identify the actual prescribed initial datum
without first constructing an unrelated physical strong right limit.

An exact kinetic ceiling plus a scalar correlation inequality gives

    ‖F(t)−U₀‖² ≤ 2 (‖U₀‖² − ⟪F(t),U₀⟫).

In particular a single self-pairing converging to ‖U₀‖² yields
strong right convergence to U₀ (via squeeze on squared norm).
This is a special case of the Hilbert Radon--Riesz principle.

Under the already-proved initial-anchored L¹ kinetic budget,
the exact positive-time kinetic ceiling was established in checkpoint
`e77804b8`. Applying these generic results directly to the old physical
Hilbert velocity gives its strong right initial L² trace and exact
kinetic right-time continuity, with NO subcritical H³ rate and NO
old-branch temporal-derivative joint-continuity hypothesis.

A separate finite-time theorem carries any one-vector correlation
error c(t) into the squared physical initial velocity jump:

    ‖oldPhysical(t)−u₀‖² ≤ 2 c(t),  for t∈(0,T).

Remaining independent hypotheses are the actual initial energy budget
(with L¹ defect) and the full right-filter self-pairing convergence.
They are *not* supplied by the open-time NS PDE alone. Terminal H³
vorticity regularity also remains a distinct issue.

## Public declarations

- `h3Audit_initialEnergySelfPairing_squaredDefect_le`
- `h3Audit_initialHilbert_strong_of_energyCeiling_selfPairing`
- `h3Audit_initialBudget_selfPairing_physicalSquaredDefect`
- `h3Audit_initialBudget_selfPairing_implies_physicalAndKineticRightTrace`

## Required build order

After extraction, register the root import and checks, then ALWAYS run

    python3 proof/generate_index.py
    python3 proof/generate_index.py --check

BEFORE any `lake build` or `tools/audit/baseline.sh` invocation. The
baseline rejects a stale `proof/order.txt`. Include it in the commit.

The ZIP was syntax/integrity checked without a Lean toolchain.
