# Freeze an actual cofinal third-radial Leray forcing component

Base: `8001d5c5` — raw physical cubic forcing clock and Fourier source escape.

The raw physical fourth-radial PDE inequality implies that escape of `D3`
requires unbounded full cubic mass `M3`. The original physical Fourier forcing
identity decomposes that mass into exactly three squared Hilbert norms:

```
M3(r) = (2*pi)^6 * sum_{j : Fin 3} ||F^3_j(r)||_2^2.
```

This patch supplies a finite-index unbounded-sum lemma and freezes a **single**
coordinate `j0 : Fin 3` satisfying `forall K, exists r in (s,T)` with
`K < ||F^3_j0(r)||^2`. The quantifiers are important: the same `j0` works
for all thresholds, not a new coordinate chosen at each threshold.

The canonical forcing Hilbert path is continuous on `(a,T)`. Therefore a
fixed coordinate cannot carry its unboundedness entirely on any compact
`[s,sigma]`; this upgrades the statement to each strict subtail `(sigma,T)`.

Finally the existing raw representative theorem identifies the squared norm
with the weighted Fourier integral

```
int_{xi in R^3} |xi|^6 * |P div(U(r) tensor U(r))_j0(xi)|^2 dxi.
```

This is a necessary nonlinear velocity-product obstruction to terminal physical
top-mass escape. It is NOT a new bound on the Fourier convolution, and does
not exclude blowup or imply unconditional Navier-Stokes continuation. It avoids
assuming a Fourier Cauchy endpoint, a vorticity trace, or positive D3.
