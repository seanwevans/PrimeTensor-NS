# Z³ Galerkin — cross-cutoff convergence of the exact Leray source

Base HEAD: `6a726d4cdffa1a411b3df12b4d9143704693dbec`.

## Question at the infinite-frequency frontier

The constructed Galerkin subsequence converges uniformly in time in the
**infinite** `W_log(3/2)` Fourier norm to a high-analytic-radius limit. But
pointwise convergence of Fourier coefficients is not enough to pass the
quadratic projected source to the limit: its differentiated input index
carries a frequency factor, and different finite Galerkin cutoffs generate
nonlinear output modes outside both original input sets.

## Exact support invariance

For the actual complex transport symbol `-i P_n[(q · u_p)v_q]`, either zero
input makes the ordered interaction vanish. Therefore for `s ⊆ q` and a
field `u` vanishing outside `s`, the **complete collision-sensitive source**
is unchanged by enlarging its input sets: `Q_{q,q}(u,u)_n = Q_{s,s}(u,u)_n`
for **every** output frequency `n ∈ ℤ³`.

This is essential: the source of one finite Galerkin cutoff cannot simply
be compared to another by invoking a same-support theorem until this equality
has been established.

## Cross-cutoff source and full field estimates

Let `U`, `V` be zero-extended states supported on arbitrary `s` and `t`, with
`W_log(9/5)(U), W_log(9/5)(V) ≤ 100`. For every finite output set `A`,

```
Σ_{n∈A} (5/4)^|n|₁ ‖Q_{s,s}(U,U)_n − Q_{t,t}(V,V)_n‖
  ≤ 1000 W_log(3/2)^{s∪t}(U−V).
```

The output set `A` need **not** lie in `s∪t`. The `1000` is exactly the
previously established full-Leray two-radius bound, now applied to the
*common union input support* and transported back to the original sources.

The exact viscosity-plus-Leray fields satisfy the analogous estimate with
factor `1010`, when summed over the union of retained output supports.

## Uniform-time Cauchy consequence

The preceding actual finite Galerkin compactness theorem supplies, along a
single subsequence `φ`, for every `δ>0`, a common `K` such that
`W_log(3/2)^{S_{φ(k)}∪S_{φ(l)}}(U_{φ(k)}(z)−U_{φ(l)}(z))<δ` for every
`k,l≥K` and every `z` in the common closed time interval.

Choosing `δ=ε/1000` yields **one `K` working simultaneously for every time
and every finite set of output frequencies** for the exact nonlinear Leray
source. Choosing `δ=ε/1010` gives the complete field Cauchy estimate.
Finally a theorem constructs strong finite ODE paths from independent
strict-analytic-ball initial states and derives the source Cauchy property.

## What is not yet claimed

This package proves the difficult spatial operator comparison without
assuming any infinite source. It does **not yet construct** the limiting
infinite `W_log(5/4)` source by completeness, assert a time-derivative of
the infinite limit, or justify exchanging the nonlinear infinite sum and
the time integral. Identifying a Navier–Stokes solution requires these steps,
and compatible initial data and exhausting cutoffs for the intended IVP.

Validation: source text and registry checks are static; the user must run
`lake env lean`, full build and repository audit before accepting a commit.
