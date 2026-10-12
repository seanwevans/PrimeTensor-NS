# Initial L¹ budget yields an exact positive-time kinetic ceiling

Base checkpoint: `a40fce7c` — identify initial physical trace from
integrable kinetic budget and self pairing.

## Mathematical advance

The already established H³ kinetic derivative identity proves that
`velocityH3Energy0At u` is antitone on `(0,T)`.

Under the separate initial-value budget

    E₀(s) ≤ E₀(0) + ∫₀ˢ |r(x)| dx,  0<s<b,  |r| ∈ L¹(0,b),

the scalar integral primitive tends to 0 at the initial right filter.
Consequently, for every t>0 and ε>0 there is an earlier s∈(0,min(t,b))
with E₀(s)≤E₀(0)+ε. The existing
`h3Audit_initialKineticEnergy_le_initial_of_cofinalApproximateAnchors`
eliminates ε via positive-time kinetic antitonicity.

Thus the **exact** E₀(t)≤E₀(0) is proved for all t∈(0,T), without
assuming a finite initial kinetic limit, a subcritical H³ energy rate,
or time-zero kinetic-energy continuity.

The actual physical old velocity obeys

    ‖oldPhysical(t)‖ ≤ sqrt(E₀(0))  (0<t<T).

A separate one-vector Hilbert inequality reads

    ⟪L,U₀⟫ + ‖L−U₀‖²/2 ≤ ‖U₀‖²,

whenever ‖L‖²≤‖U₀‖². Under a subcritical H³ envelope, the proven
strong momentum and kinetic right limits plus the initial L¹ budget
yield this inequality for the actual u(0). A nonzero right-limit jump
implies a nonzero deficit in the u(0)-self pairing.

## Public declarations

- `h3Audit_initialIntegrableBudget_cofinalApproximateAnchors`
- `h3Audit_initialIntegrableBudget_exactPositiveKineticCeiling`
- `h3Audit_initialIntegrableBudget_globalPhysicalNormCeiling`
- `h3Audit_initialHilbert_selfPairDeficit_of_kineticCeiling`
- `h3Audit_initialSubcriticalBudget_physicalSelfPairDeficit`

## Remaining obligations

The initial-anchored L¹ kinetic budget is NOT derived from open-time
Navier–Stokes admissibility. The energy/right-limit and self-pairing
arguments keep their previous explicit subcritical H³ growth,
old temporal joint continuity, and/or initial correlation inputs.
No unconditional global regularity is inferred.

## Build and index

Run `tools/audit/register_initial_integrable_budget_exact_ceiling_audit.py`
to register the Lean module and five theorem/axiom checks. Immediately
after source changes, regenerate `proof/order.txt` with
`python3 proof/generate_index.py`, then run `--check` before compiling.
Retain the separate full `tools/audit/Contracts.lean` verification.

Lean toolchain is absent from the artifact environment; Rocky Linux
must typecheck the module.
