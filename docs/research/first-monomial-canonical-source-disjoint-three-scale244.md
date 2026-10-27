# Canonical projected source through disjoint quadratic-sharp H³ PDE clocks

**Base:** `993c985f` — constructed the minimal actual first-crossing annulus and exact quadratic-sharp physical PDE clock using the attained maximum of the projected momentum source on the enclosing half-terminal interval.

## The change from the arbitrary-ceiling chain

The older disjoint-window and finite-dissipation barrier selected a possibly inflated upper bound `C(n)` on each strict physical source interval. The canonical constructor instead sets

`C(n) = max_{s in [τ(n), τ(n)+(T-τ(n))/2]} ‖Δu(s) − Leray(u·∇u)(s)‖_{L²}`

and proves existence of a physical time attaining that value. The subsequent persistence width is computed from this exact `C(n)` through the original, unlinearized `Λ δ + Ξ δ²` budget. We **must not substitute** the canonical envelope into previous witnesses after their widths have already been selected.

## New physical theorem

`h3Path_noL2Trace_finiteDissipation_canonicalSourceDisjointThreeScale244` reconstructs the disjoint cofinal extraction using the canonical clock sequence itself. Under logged H³ path admissibility, preterminal energy class, positive terminal kinetic mass, absence of a strong terminal physical L² trace, and **explicit** finite full H³ dissipation integrability, it supplies:

- a strict-increasing subsequence `v`, pairwise separated physical `δ` windows and `τ(v(k)) → T`;
- the actual canonical source envelope at `τ(v(k))`, with a physical maximizer in the enclosing half-terminal interval;
- the minimal three-quarter-cubic first-crossing annulus, the persistent half-cubic floor, and the exact quadratic-sharp width selector;
- `Summable (fun k => δ(v(k)) * (v(k)+1)^3 / 2)` and the existing three-cap alternative: terminal time compression, sixth-power linear-rate growth or ninth-power quadratic-rate growth;
- if the canonical source coefficient square `C(v(k))² → +∞`, then at *actual* times in each corresponding half-terminal interval the projected-source L² norm exceeds every fixed threshold eventually.

The square-growth antecedent is **not** asserted unconditionally. In particular this theorem does not inherit earlier arbitrary-ceiling width-cap/source-escape statements without re-proving those statements for the canonical witnesses. The source maxima are attained somewhere in the half-terminal intervals, not necessarily at `τ(v(k))` or inside the shorter `δ` persistence windows.

## Audit

Registered `#check` and `#print axioms` for the two theorems. No `sorry`, `admit`, or introduced `axiom`. Lean compilation requires local `lake env lean` and full build.
