# H³: nonvacuous cumulative cost alternative for separated active physical annuli

**Base:** `b1c0d55b` — separated the exact-PDE-certified active cubic Fourier annuli.

## Analytic statement

Assume `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`, and
failure of a strong physical terminal L² velocity trace. We do **not** assume
integrability of full H³ dissipation, since the existing theorem
`h3Critical_noL2Trace_incompatible_with_finite_dissipation` already excludes
that conjunction.

The committed disjoint diagonal gives actual physical observation times
`t(v(k)) → T`, strictly separated nonempty intervals
`[t(v(k)), t(v(k)) + δ(v(k))]`, and inner frequency `v(k)+1` with `k ≤ v(k)`.
Each interval has an exact projected-momentum PDE persistence width, selected
physical source maximum, and the local estimate

    f(k) := δ(v(k)) * (v(k)+1)^3 / 2
        ≤ I(k) := ∫_{t(v(k))}^{t(v(k))+δ(v(k))} D_annulus,k(s) ds.

The new theorem gives for every finite prefix `m`:

    Σ_{k<m} f(k) ≤ Σ_{k<m} I(k),

and proves the **genuine alternative**

    (∀ M ∈ ℝ, ∃ m ∈ ℕ, M < Σ_{k<m} f(k))
       OR
    δ(v(k)) * (v(k)+1)^3 → 0.

The second alternative is proved by observing that bounded partial sums of
nonnegative `f(k)` imply summability and hence `f(k)→0`. No integral over the
whole terminal interval is used; this is a local-charge criterion that remains
logically meaningful on the nonintegrable-dissipation branch.

## Scope and missing step

The alternative does **not** establish divergence of the selected local
charges. Strong terminal nonintegrability of total H³ dissipation does not
by itself mean an arbitrarily selected sparse family of finite annuli
captures all divergent dissipation. If the selected charges are bounded,
the exact certified widths must shrink on the inverse-cubic spectral scale.
Closing this branch requires a new quantitative constraint on the exact
physical PDE width selector or a selection construction which captures a
fixed portion of the divergent terminal dissipation. Neither is supplied
here; no unconditional Navier–Stokes regularity follows.

## Lean declarations

- `h3Critical_scalar_disjointCubicCharges_unbounded_or_widthCollapse`
- `h3Critical_scalar_finiteAnnularChargeSum_le_actualIntegralSum`
- `h3Critical_noL2Trace_disjointActiveAnnuli_unboundedCharge_or_cubicClockCollapse`

Run the registrar with `--apply`, then `--check`, generate the proof index,
and verify the full audit. Lean compilation was not available in the patch
construction environment and must be checked with the pinned local toolchain.
