# Injective regular physical time distributions and source primitives

Base commit: `abd43c38`.

On any open physical interval `(a,b)` with `0<a<b<T`, the actual physical velocity and projected source pairings are continuous scalar functions, hence locally integrable. The repository’s pinned mathlib distribution constructor is a compact-convergence copy of `TestFunction.integralAgainstBilinCLM`. The first theorem establishes **injectivity on continuous representatives**: if two locally integrable continuous scalar functions induce the same regular distribution, they agree at every point of the open interval.

The proof invokes the pinned mathlib fundamental lemma `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` on the difference, constructs a bundled smooth compact time test, uses the `TestFunction.integrable_bilin` estimate to split the integral, and upgrades the resulting almost-everywhere equality using `eqOn_open_of_ae_eq`. No distributional primitive-uniqueness axiom is added.

A physical specialization identifies any candidate representation of actual compact-test momentum with the true compact-test momentum on `(a,b)` whenever their regular time distributions agree. Another theorem shows the canonical projected scalar-source primitive `t ↦ ∫_a^t ⟨φ,R(s)⟩ ds` is absolutely continuous on the closed strict time window.

**Not yet established:** equality of the distributional derivative of the old physical momentum to the projected source directly from the preterminal PDE; equality of the distribution of its primitive up to a constant; or physical FTC itself. These remain the substantive analytic steps.
