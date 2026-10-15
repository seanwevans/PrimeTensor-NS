# Actual critical-half inequality along the spatial dilation orbit of one Schwartz profile

**Baseline:** `1bdcf22e` — actual physical 243-slot first-monomial dilation.

The formalization now has the three *actual*, independent scaling identities
on `A3 → SchwartzMap H3FourierPoint3 ℝ`:

- physical 243-slot signed first monomial `M(f_λ) = λ⁴ M(f)`;
- full fourth-derivative square dissipation `D(f_λ) = λ⁸(λ³)⁻¹ D(f)`;
- complete unnormalized H³ square mass `E(f_λ) = (λ³)⁻¹ E₀ + λ²(λ³)⁻¹ E₁ + λ⁴(λ³)⁻¹ E₂ + λ⁶(λ³)⁻¹ E₃`.

The new module first proves nonnegativity of each of the four complete energy
orders and of all 243 fourth-derivative square integrals. It identifies the
previously defined unnormalized `lowNormalRealSchwartzH3EnergyQuadratic`
with the newly scaled four-order energy (without changing definitions).

It then transports the earlier scalar polynomial inequality at a fixed shape
to the genuine real Schwartz functionals:

`M(f_λ)^2 ≤ C^2 D(f_λ)^2 E(f_λ)` for every `λ > 0`, provided the scalar
coefficient hypothesis holds. The exact algebra is obtained by multiplying
the scalar inequality by `λ⁷` and using the positive-scale Jacobian.

The earlier theorem
`criticalHalfDilation_exists_uniform_coefficient` supplies a *single*
profile-dependent `C` valid for all positive `λ`, assuming
`D(f) > 0`, `E₀(f) > 0` and `E₃(f) > 0`. With nonnegativity of the physical
quantities, taking square roots gives the normalized endpoint inequality

`M(f_λ) ≤ C √(1 + E(f_λ)) D(f_λ)`.

**Limitations:** These are conditional **fixed-profile** results. The proof
neither establishes the strictly positive mass hypotheses for every nonzero
Schwartz field nor produces one `C` uniform across all divergence-free
Schwartz profiles. It does not assert PDE path realization, continuation,
regularity or blowup. The uniform-over-shapes estimate is a separate hard
mathematical frontier.

Run `lake env lean` on the module, `lake build` of its module target to create
`.olean`, then the audit and full build. No `sorry`, `admit`, or new axioms
are introduced.
