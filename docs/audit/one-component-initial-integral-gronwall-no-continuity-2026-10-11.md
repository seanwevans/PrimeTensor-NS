# Initial comparison: integral Gronwall without positive-time continuity

Base commit: `8a2bf80c` — derive initial uniqueness with continuous integrated coefficients.

## Analytical improvement

If `e ≥ 0` and `e` is interval-integrable on `[0,b]`, the pointwise inequality
`e(t) ≤ K ∫₀ᵗ e(s) ds` forces `e=0` throughout `[0,b]` **without assuming
continuity of `e`**. The cumulative integral `H(t)=∫₀ᵗ e` is continuous;
integrating the bound on `e` gives `H(t) ≤ K∫₀ᵗ H`. The existing scalar
continuous Gronwall lemma, applied to `H`, gives `H=0`, hence `e=0`.
No sign assumption on `K` is required.

The new PDE-facing contract `H3AuditInitialCanonicalTimeIntegratedCoefficientNoContinuityData`
removes positive-time scalar-energy continuity from the time-integrated
coefficient interface. Pointwise vanishing makes the scalar energy continuous
on the closed initial interval as a **conclusion**, so existing compact weak
test agreement and physical initial trace results are reused.

## Still unproved PDE inputs

Actual old/selected integrated relative-energy estimates, interval
integrability of the energy and coefficient product, uniformly bounded
coefficient, and arbitrarily small signed residual total mass remain
explicit premises. The independent strong-H³ terminal endpoint of actual
vorticity also remains a hypothesis. This does not assert Navier--Stokes
global regularity.

An additional PDE-facing contract,
`H3AuditInitialCanonicalContinuousIntegratedCoefficientNoEnergyContinuityData`,
combines this with the preceding theorem that product-integrability
follows from continuous coefficients. This removes **both** the explicit
positive-time energy-continuity premise and the explicit `κ*e`
product-integrability premise while retaining the measurable `L¹`
energy and actual PDE residual obligations.
