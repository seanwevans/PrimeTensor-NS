# Exact cofinal cubic PDE-clock concentration alternative

Base commit: `b03e1333` — retain exact cofinal cubic H³ annulus physical PDE persistence clocks.

## New mathematical statement

Assuming no strong terminal physical L² trace, positive terminal kinetic mass, and **additional full H³ dissipation integrability on the terminal interval**, the previously constructed exact PDE cubic windows admit a pairwise-disjoint, cofinal subsequence with the **exact same widths** (no shortening).

Their weighted cubic costs form a summable real series, and along that subsequence `δ(v k) (v k+1)^3 → 0`. More decisively, outside a finite set of indices, one of two alternatives holds:

- **Geometric time compression:** `2M ≥ A(v k) (T − τ(v k))/2`, or
- **Anchored PDE coefficient concentration:** `A(v k) gap(v k) ≤ 2M (Λ(v k)+Ξ(v k)+1)`.

Here `A(n)=(n+1)^3/2`, `gap(n)` is the actual finite-annulus height surplus, `Λ` and `Ξ` are the previously proved **physical projected-PDE** linear and quadratic variation rates, and `M = ∫_a^T velocityH3DissipationAt`.

The fixed-mass branch of the earlier trichotomy eventually disappears because `A(v k)→∞`; no claim is made that the remaining alternatives contradict the PDE. If a selected terminal window is geometrically compressed, no source growth follows merely from its small width.

## Lean scope and audit

* The finite-sum cost control uses the existing nonnegative disjoint-window theorem and the exact Fourier partition inequality, without assuming that finite terminal H³ dissipation follows from H³ path admissibility.
* The exact width equality is propagated through the strict index subsequence.
* The output has three theorems and three explicit supporting definitions. It assumes no `sorry`, `admit`, or extra axioms.
* Lean compilation must be executed in the user repository and the generated proof index refreshed with `proof/generate_index.py`.
