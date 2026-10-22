# Physical order-four velocity convolution: eighth-moment six-factor escape

Base: `cd7cfdc4` — physical order-four velocity convolution escape corridor.

The earlier module derives one fixed third-radial Leray forcing coordinate with cofinally unbounded weighted L² norm when actual physical top dissipation escapes. Under explicit raw eighth-moment integrability on every strict time slice, an ordered velocity pair `(k,j)` then has arbitrarily large order-four convolution norm on every terminal subtail.

The existing raw Fourier Young inequality proves, for this *actual* velocity-pair convolution,

```
‖ |ξ|⁴ (Û_k * Û_j) ‖₂²
 ≤ ‖Û_k‖₂ ‖Û_j‖₂ · C₈ ·
    [M₈(U_k) L₁(U_j) + L₁(U_k) M₈(U_j)]
```

where `C₈ = h3FourierMomentSplitCoefficient 8` is the exact existing Fourier moment-splitting coefficient, `M₈` the eighth-order raw moment mass, and `L₁` the raw Fourier L¹ mass. This is the **actual physical time-slice** velocity state, not a manufactured scalar majorant.

The new module packages this moment expression as an input-pair budget, proves the pointwise norm-square bound, and proves a six-factor elementary lemma: if the two Fourier L² norms, the two Fourier L¹ masses, and the two eighth-order moment masses are all bounded by `H ≥ 0`, their entire Young budget is at most `2 C₈ H⁴`.

Thus physical top-moment escape implies that for every terminal subtail and every `K`, at least one actual velocity input factor exceeds `K`. The factor is one of **six named Fourier quantities**, with the pair and factor index allowed to vary with the tail and threshold. The previously frozen Leray forcing coordinate remains fixed in the upstream result.

## Important limitations

- Eighth-order raw Fourier moment integrability on strict time slices is retained as a hypothesis.
- The conclusion is an input-factor **escape alternative**, not automatic growth of `M₈` alone: Fourier L¹/L² inputs have not yet been uniformly controlled on the terminal tail.
- No upper bound on the input-factor budgets, and no unconditional Navier–Stokes continuation, is proved.

The next analytic step is to use kinetic and Fourier Bessel/Sobolev estimates to constrain the low-order L¹ and L² factors and isolate an eighth-moment obstruction without introducing an unsupported uniform norm bound.
