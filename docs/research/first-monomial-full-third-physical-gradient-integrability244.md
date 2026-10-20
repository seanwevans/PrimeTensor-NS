# Full-third physical gradient L²–L²–L∞ bridge

Parent checkpoint: `e92da383`, identifying the entire original physical signed H³ 243-slot interpolation with its canonical real-Schwartz completion.

## Mathematical result

At a Fourier-compatible, preterminal Navier–Stokes slice, the old physical third derivatives are in `L²(Point3)` and the old physical first derivative is bounded at **every** point by the spectral H³-to-C¹ evaluation coefficient:

`|D_a u_j(x)| ≤ C₁ ‖U_j(t)‖`.

Therefore for arbitrary ordered third-jet slots and one first jet,

`(D³u_j)(D³u_p)(Du_q) ∈ L¹(Point3)`

via Hölder `L²×L²→L¹` and bounded multiplication. In particular, all four 3–3–1 terms in each of the 243 ordered `(j,i,k,l,r)` gradient-axis blocks are integrable. The older `H3RealSchwartzGradientAxesIntegrable244` integrability contract is discharged **without** the old velocity itself being Schwartz.

## Exact reduction

The preceding signed-gap theorem and the existing PDE transport split imply

`physicalFullThird - weightedCanonicalFullThird = physicalGradient - weightedCanonicalGradient`.

Equality of the two full-third transport observables is equivalent to equality of the corresponding gradient observables. The gradient equality remains an unproved identification; the current module instead removes the spatial integrability obstruction to proving it by approximation.

## What is not claimed

No gradient-integral Schwartz-limit equality, favorable nonlinear sign, or continuation of arbitrary Navier–Stokes flows follows from these results. The remaining step is strong `L²` convergence in both third-jet slots together with uniform `L∞` control and convergence of the physical first jets, followed by four-term and 243-slot summation.
