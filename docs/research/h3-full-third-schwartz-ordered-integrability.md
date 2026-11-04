# Full-third H³: unconditional ordered Schwartz Fourier integrability

**Pinned baseline:** `fc4d630d` — reindex unrestricted complex H³ sixth-power flux through six Schwartz Fourier permutations.

## Precise gap addressed

The existing six-orbit integral was proved under `Integrable (thirdFullSchwartzComplexOrderedKernel244 u) (volume.prod volume)`. This is a genuine technical obligation: finite polynomial formulas do not by themselves justify a noncompact, six-dimensional Fourier integral. For Schwartz inputs the condition is automatic, but the bridge needed to be proved explicitly.

Let `p = z.1`, `q = -(p+r)`, `r = z.2`; let `U,V,W` be the **complex Fourier amplitudes of the same field** at `p,q,r`. Put `a=p·q`, `b=p·r`. The corrected ordered polynomial is

```
 K = (U·W)(r·V) [a³ + 3a²b] + (U·V)(q·W) [3a²b].
```

The products here are **complex bilinear**, with no arbitrary conjugation. Expanding the five physical coordinate sums (`j,m,i,k,l`) gives exactly three kernels:

1. `(U_j W_j)(r_m V_m)(p_i q_i)(p_k q_k)(p_l q_l)` — `3+3+1` Schwartz Fourier kernel.
2. `3(U_j W_j)(r_m V_m)(p_i q_i)(p_k q_k)(p_l r_l)` — `3+2+2` interpolation Fourier kernel.
3. `3(U_j V_j)(q_m W_m)(p_i q_i)(p_k q_k)(p_l r_l)` — a different `3+3+1` gradient Fourier kernel.

Each kernel is absolutely integrable by the already-established `thirdGradientSchwartzKernel_integrable244` and `h3FirstMonomialSchwartzKernel_integrable`. Five finite sums preserve integrability. A separate complex five-sum contraction lemma ensures that the finite expression is the **original corrected ordered symbol**, rather than an ad-hoc surrogate.

It follows that the six-permutation theorem needs **no ordered-kernel integrability hypothesis** for arbitrary complex Schwartz data. Under spectral incompressibility,

```
    ∫ sixthPowerFlux(u) = 6 · ∫ correctedOrderedKernel(u).
```

The final corollary uses `lowNormalRealSchwartz_Point3Solenoidal` to supply spectral solenoidality for a physically divergence-free real Schwartz velocity.

## Mathematical scope

The new result closes the noncompact **integrability and ordered-symbol identification** gap. It does **not** yet prove that the actual five-index physical G₃+3M commutator is the same normalized integral. That remaining equality must retain the physical factor 2, interpolation factor 6, seven-derivative Fourier phase, and six-orbit normalization. The anticipated normalization is `(2π)^7/3` times the imaginary part of the sixth-power flux integral, but it must be proved rather than declared.

The static adverse Schwartz example is consistent with the result: an exact flux decomposition and its absolute integrability do not give uniform dissipative absorption or Navier–Stokes regularity.

## Validation

The five-index algebra was checked independently on 25 generic complex-polarization examples. Python compilation, registrar idempotence and ZIP integrity were checked. Lean is not installed in the authoring environment; the pinned project's `lake env lean` and audit are required to verify elaboration.
