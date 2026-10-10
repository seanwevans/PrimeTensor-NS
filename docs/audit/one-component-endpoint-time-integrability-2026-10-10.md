# One-component endpoint: finite-time domination audit (10 October 2026)

**Verified repository baseline:** `4188200b` (uniform two-component terminal H³ spectral norms).

## What this module proves

Given the existing strong spectral H³ endpoint predicate and an H³ energy-class tail, every globally measurable nonnegative time-density `S` that is bounded pointwise by the **squared weighted H³ spectral norm** of a chosen transverse velocity component is Lebesgue integrable on some terminal interval `(c,T)`. Both transverse components can use a **single later interval**. The proof uses a direct terminal uniform bound and finite measure of the interval; it does not use new nonlinear estimates.

## Why this is not yet the one-component continuation theorem

Liu & Zhang, *On the One Time-Varying Component Regularity Criteria for 3-D Navier-Stokes Equations*, SIAM J. Math. Anal. **56** (2024), pp. 6213–6231, DOI [10.1137/23M1623124](https://doi.org/10.1137/23M1623124), states continuation for a local strong solution whenever the squared homogeneous spatial Sobolev `Ḣ^{3/2}` norm of a velocity projection is time-integrable. The fixed coordinate direction is a special case of the paper's unit-vector hypothesis.

We have **not yet proved** that the particular physical squared `Ḣ^{3/2}`-norm-density is measurable within PrimeTensor's time/space model, nor that it is bounded by the project's exact weighted spectral H³ norm square. We also have **not yet proved** the equivalence between PrimeTensor's PDE path interface and the paper's local strong-solution class, or a project-level formalization of its external continuation theorem.

## Acceptance conditions for closing the literature bridge

1. Define the genuine `Ḣ^{3/2}` homogeneous Fourier quadratic form, with correct `(2π)` convention, and prove `S_j(t) ≤ C ‖G_j(t)‖²` (preferably a numerical constant). The current theorem accepts `S ≤ ‖G‖²`; a uniform factor may be handled by scaling the majorant.
2. Prove temporal measurability of that concrete time-density on the strict preterminal tail. This cannot be inferred just by assigning a name to the density.
3. Establish the published local-strong-solution compatibility and formally state/import the continuation criterion, checking its initial-data, divergence-free, pressure, and time-interval hypotheses.
4. Only then prove `H3AuditOnePhysicalEndpointLiteratureBridge` and simplify the endpoint dichotomy. The global Clay bridge is **separate**.

**Tao averaged-Navier–Stokes check:** These steps establish a known conditional continuation criterion, not a new universal bound. They do not resolve the obstruction of finding a structural estimate specific to the exact nonlinear PDE.
