# Source-driven extended H³ costs: explicit height × width and local compression

Base: `02e9489a` (extended high-H³ costs transferred to actual full physical dissipation).

The previous theorem compares **unevaluated** constant-height extended integrals with both moving high-radial and full physical H³ dissipation. This patch evaluates the constant exactly using `setLIntegral_const` and `Real.volume_Ioc`:

```
∫⁻_(t,t+δ] ofReal(M) ds = ofReal(M) * ofReal(δ),   δ ≥ 0.
```

The resulting finite-sum bound on the same strictly separated source-driven windows is:

```
Σ_{k<m} ofReal(M(v k)) * ofReal(δ(v k))
  ≤ Σ_{k<m} ∫⁻_(t(v k),t(v k)+δ(v k)] ofReal(D_full(s)) ds.
```

This holds without a temporal continuity, measurability, ordinary L¹, or terminal-finiteness premise on `D_full`, because the extended Lebesgue integral remains defined.

The second quantitative theorem captures **necessary compression under any finite local budget**: if `M > 0`, the extended physical dissipation integral over one window is at most the finite real number `C ≥ 0`, and the dissipation is at least `M` throughout the window, then `δ ≤ C/M`. The source-driven witness theorem carries this conditional bound for each selected index. It does **not** assert a finite budget exists uniformly near T. Such a global budget cannot be quietly introduced into the no-terminal-L²-trace branch.

**Crucial limitation:** These results impose an upper bound on width when a finite budget is given; they do not supply the missing *lower* bound on persistence width, divergent costs, or global regularity. Comparing finite disjoint window sums to a single full-terminal extended integral is a separate measure-theoretic step, and obtaining a **finite** full-terminal upper bound would contradict the existing no-trace obstruction under suitable measurability.

Declarations:
- `h3Critical_extendedConstantWindow_eq_heightWidth`
- `h3Critical_extendedWindowBudget_width_le`
- `h3Critical_noL2Trace_sourceDriven_explicitFullWidthCosts`

Verify with the project's pinned Lean toolchain; static inspections do not constitute Lean proof elaboration.
