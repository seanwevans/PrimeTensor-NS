# One approximate kinetic sample sequence + Schwartz weak initial data

Checkpoint: `891abb6c` — quantitative physical L² error from scalar
Schwartz FTC and initial kinetic budget.

The new theorem removes the initial **L¹ kinetic defect budget**
assumption used by the previous physical strong-initial-trace route.
It instead accepts one right-zero sequence τₙ satisfying the precise
uniform-asymptotic initial energy upper statement

    τₙ → 0+,
    ∀ ε>0, E₀(τₙ) ≤ E₀(0)+ε eventually.

The generic scalar sequence lemma extracts an arbitrarily early
energy anchor from every positive interval and every tolerance.
The already proved Navier--Stokes positive-time energy antitonicity
upgrades this to the exact whole-positive-time energy bound

    E₀(t) ≤ E₀(0) for all 0<t<T.

Density of physical three-component Schwartz tests then identifies the
strong physical L² right limit with actual u(0) and gives the kinetic
energy right trace. The proof does not assume subcritical H³ growth,
temporal-derivative joint continuity, or any temporal L¹ kinetic
defect.

Three physical routes are included:

1. Full right weak Schwartz initial trace.
2. Test-dependent initial-anchored scalar L¹ FTC equations.
3. Positive-time scalar derivatives with testwise L¹ sources and
   per-test right-zero initial matching sequences.

These routes require **one shared energy witness sequence** τ, but the
initial matching sequences σ of route 3 may depend independently on
each Schwartz test. No uniform source bound or Hilbert-valued source
is assumed.

## Declarations

- `h3Audit_initialScalarCofinalApproximateAnchors_of_sequence`
- `h3Audit_initialCofinalApproximateKineticSequence_exactCeiling`
- `h3Audit_initialCofinalKinetic_SchwartzWeak_physicalAndKineticTrace`
- `h3Audit_initialCofinalKinetic_SchwartzScalarFTC_physicalAndKineticTrace`
- `h3Audit_initialCofinalKinetic_SchwartzDerivativeSequence_physicalAndKineticTrace`

## Unresolved PDE obligations

The existence of the approximately initial-energy-bounded kinetic
sequence and the weak initial-value matching data are NOT implied by
strictly positive-time H³ path admissibility alone. Nor does the
result prove terminal H³ vorticity regularity or global 3D smoothness.

## Build workflow

After extracting and registering the module in root and Contracts,
run `python3 proof/generate_index.py` then `--check` BEFORE any Lake
build or baseline. Commit updated `proof/order.txt`. The module
has not been compiled in the ZIP preparation environment.
