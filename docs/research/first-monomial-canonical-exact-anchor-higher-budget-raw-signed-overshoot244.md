# All-orders canonical higher-budget escape forces unbounded raw signed H³ transport margin

Base: `e6f0482f` — force pointwise signed H3 transport overshoot on every terminal tail.

The committed theorem under explicit conditional higher-moment budget, attained source ceiling, critical outer cap and weighted terminal-clock noncompression forces some time `s` in every terminal subinterval with `-T₃(s) > 2D₃(s)`.

This increment upgrades **strictly positive** to **arbitrarily large raw transport margin**. Cofinal canonical energy escape `E₃(t_k) → +∞`, `t_k → T`, and exact physical time differentiability imply

    ∀ b ∈ (a,T), ∀ M ≥ 0, ∃ s ∈ (b,T),  M < E₃'(s).

The scalar argument applies the existing positive-derivative-every-tail lemma to `F(s) = E(s)-M*s`. This shifted scalar still diverges on the cofinal sequence since `t_k<T` and `M≥0`; and `F'(s)=E'(s)-M`.

The exact PDE identity already proved independently,

    E₃'(s) + 2D₃(s) = -T₃(s),

then gives

    M + 2D₃(s) < -T₃(s),
    M < max(0, -T₃(s) - 2D₃(s)).

The last expression is the repository's genuine `h3PathRawFullDissipationTransportExcessPart`, **not** its normalized cousin `h3PathFullDissipationTransportExcessRate`. The theorem asserts no uniform rate, no lower bound on a set of positive measure, and no new integrability statement: an unbounded pointwise raw derivative may still be integrable. Nor does this prove the conditional budgets from physical H³ dissipation.

The exact same first-crossing canonical `τ,N,K,C,δ,v`, with their existing cofinal/separation and attained-source-envelope statements, are retained. Four new theorem declarations:

- `h3Path_scalar_cofinalEscape_forces_unboundedDerivativeEveryTail244`
- `h3Path_cofinalPhysicalEnergyEscape_forces_arbitrarySignedTransportMargin244`
- `h3Path_arbitrarySignedTransportMargin_forces_rawPositiveExcess244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_unboundedRawSignedTransport244`

**Verification boundary**: structural Python checks and ZIP archive verification are performed offline. Lean 4 with this repository's pinned Mathlib toolchain must compile the new module locally; no full Lean compilation is claimed.

## Lean elaboration correction (fix1)

At both derivative construction sites, simplify `id x` and the real product `M * 1` using `simpa only [id_eq, one_mul]`. Simplify the pointwise subtraction of functions using `simpa [F]`, which unfolds the local shifted-energy definition and the `Pi` subtraction instance. No theorem statements or mathematical assumptions change. The complete Lean build still requires the repository toolchain.

## Local proof correction (fix2)

The scalar theorem now applies `exists_deriv_eq_slope` directly to the original energy function between an interior midpoint and a sufficiently late canonical high-energy point. This removes both uses of `HasDerivAt.const_mul` and both uses of `HasDerivAt.sub`, sidestepping the dependent elaboration mismatches reported with fix1. Statements and PDE consequences are unchanged.
