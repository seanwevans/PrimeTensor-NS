# Actual physical L² tightness closes the critical-eighth kinetic gate

Baseline: `0d4f13dc478a86f3197a493e3e4a5ea3c9273b32`.

## Hard mathematical step

The antecedent of the critical-eighth escape theorem was the vanishing of
raw kinetic Fourier mass `μ_k` inside a moving minimal crossing annulus.
The strong physical L² trace available under **finite full H³ dissipation**
is enough: the *raw* Fourier transform of the physical velocities converges
strongly in L² by Plancherel. Its sharp high-frequency projection is a
contraction and converges strongly to zero at growing radius on every
**fixed** L² state. Therefore the moving-cutoff highpass on the converging
physical sequence tends to zero:

    ‖P_high,n(k) F(u(τ_k))‖_L² → 0,  n(k) → ∞.

This is not true in general for the **weighted H³** tail without an
additional H³ compactness hypothesis, so the proof operates on raw L².

The exact annular mass on

    {n(k)+1 < radial frequency ≤ N_k+1}

is a subintegral of the raw Fourier highpass square mass. Accounting for
three velocity coordinates by a finite-dimensional norm bound gives

    0 ≤ μ_k ≤ 3 ‖P_high,n(k) F(u(τ_k))‖² → 0.

Substituting into the previously proved critical-eighth kinetic cost yields

    (N_{v(k)}+2)/(v(k)+1) → +∞

for the **same minimal first-crossing witnesses**, with the original PDE
source controls and disjoint windows still attached.

## Scope

The conclusion assumes the critical-eighth profile `η(n+1)^8 ≤ M_n`, as
well as the same `hNoTrace` (no *weighted H³* trace), actual admissible
physical path, and finite full-H³-dissipation premise of the prior theorem.
It does not prove that such a profile exists, that an H³ singularity exists,
or that 3D Navier–Stokes regularity follows. There is no new axiom and no
`sorry`/`admit` placeholder.

## Verification

The package is source-only. Run the included registrar `--apply`, then
`proof/generate_index.py`, the registrar `--check` and index `--check`,
compile both modules in dependency order, and perform the project build and
baseline audit **before** staging and pushing. A Lean compiler is not
available in this packaging environment, so local compilation on the user's
Lake toolchain is the definitive verification gate.
