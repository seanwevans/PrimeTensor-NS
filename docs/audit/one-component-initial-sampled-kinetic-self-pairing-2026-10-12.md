# Initial physical kinetic/self-pairing trace on a single sequence

Parent checkpoint: `eca5bba8` — identify initial physical trace from kinetic ceiling and self pairing.

## Hypothesis reduction

The prior criterion required `E₀(t) ≤ E₀(0)` eventually in the **whole**
right neighborhood of time zero, together with
`⟪old(t),u(0)⟫ → ‖u(0)‖²` along the whole right filter.

The new criterion requires ONE sequence `τ n → 0+` such that

    ∀ᶠ n, E₀(τ n) ≤ E₀(0)

and

    ⟪old(τ n),u(0)⟫ → ‖u(0)‖².

The known strong physical L² and kinetic right limits already arise from
the subcritical H³ projected-source theorem; composing with the same
sequence gives `‖L‖² ≤ ‖u(0)‖²` and
`⟪L,u(0)⟫ = ‖u(0)‖²`. An already-audited Hilbert polarization lemma
then identifies `L = u(0)`, yielding both quantitative initial
physical momentum and kinetic convergence theorems unchanged.

## New public declarations

- `h3Audit_initialStrongHilbertLimit_eq_of_sampledKineticSelfPairing`
- `H3AuditInitialSampledKineticSelfPairingTrace`
- `h3Audit_initialSubcriticalSampledKineticSelfPairing_identifies_physicalAndKineticRate`

## Boundaries

The sampled kinetic bound and sampled correlation remain separate
initial-data assumptions. The *positive-time* kinetic energy law does
not control `E₀(0)` absent an actual initial energy condition.

The other independent assumptions are the subcritical near-zero H³
envelope and the old temporal-derivative joint continuity. This is a
conditional initial trace result; no claim of unconditional 3D
Navier–Stokes global regularity is made.

## Build/audit integration

`tools/audit/register_initial_sampled_kinetic_self_pairing_audit.py`
adds the import to `PrimeTensor.lean` and checks the three declarations
and axioms of the two theorems in `tools/audit/Contracts.lean`.
The registration is idempotent and retains all earlier audit entries.

Artifact ZIP integrity and Python syntax tested. Lean compilation
requires the user's local Rocky Linux toolchain.
