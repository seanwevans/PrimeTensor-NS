# Initial Schwartz scalar FTC and strong physical L² right trace

Checkpoint: `e8913b3a` (Schwartz weak initial data + initial energy budget
give physical strong L² and kinetic right-time traces).

## New result

The previous proof assumed the *whole right-filter weak trace* for each
physical three-component Schwartz test Φ. This module derives that trace
from a test-dependent scalar initial integral formulation:

    ⟪old(t), Φ⟫ - ⟪u(0), Φ⟫ = ∫₀ᵗ gΦ(s) ds,
    gΦ ∈ L¹(0,b).

Every scalar source may differ; no Hilbert-valued Bochner source or
common dual-norm bound is needed. Each scalar L¹ primitive vanishes
at the initial endpoint, so the prescribed distributional initial
value follows for that test.

The audited dense-Schwartz weak convergence + initial kinetic ceiling
then yields strong physical L² continuity and kinetic right continuity.

A second theorem eliminates *assuming* even these initial-endpoint scalar
integral equations. For each test, it instead takes a real L¹ positive-time
scalar derivative and one right-approaching initial weak sequence. The
earlier scalar weak-FTC theorem identifies the integration constant and
manufactures the initial-anchored scalar equation.

## Public declarations

- `H3AuditInitialSchwartzAnchoredScalarFTCOn`
- `h3Audit_initialSchwartzAnchoredScalarFTC_weakRightTrace`
- `h3Audit_initialSchwartzAnchoredScalarFTC_of_derivativeAndSequence`
- `h3Audit_initialBudget_SchwartzScalarFTC_strongPhysicalAndKineticTrace`
- `h3Audit_initialBudget_SchwartzDerivativeSequence_strongPhysicalAndKineticTrace`

## Remaining obligations

A weak initial-value equation or test-specific derivative plus matching
initial sequence, and the initial-anchored L¹ kinetic energy inequality,
must still be justified from the intended Navier–Stokes solution
formulation. The open-time H³ path alone supplies neither its time-zero
integration constant nor an initial kinetic inequality. No terminal
actual-vorticity strong-H³ assertion is made.

## Build and audit

After unzipping and running the idempotent registration script,
**always run `python3 proof/generate_index.py` and its `--check`
before any `lake build`**, followed by `proof/check_fragment.py --all`.
The generated `proof/order.txt` must be committed with the Lean source.
Run the module, root, contracts, and full default builds before pushing.

Lean compilation must be performed on the user's Rocky Linux machine.
