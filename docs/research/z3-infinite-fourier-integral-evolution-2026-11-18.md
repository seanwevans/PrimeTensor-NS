# Genuine Z³ Fourier evolution from finite Galerkin ODEs

**Baseline:** `50d98db73fe46479516c8b8f4bbf75c838dc499e`.

## Analytic result

Let `gamma j` be genuine finite-state solutions of the exact Galerkin Navier–Stokes ODE on the common closed horizon, and let `phi` select a subsequence. Suppose every frequency is eventually present in `s (phi k)`; the zero-extended velocities converge uniformly in time at each frequency to `g`; the full (not output-truncated) Leray sources converge uniformly in time at each frequency to `Q`.

Then, for every lattice frequency `n` and every `t` in the horizon,

```text
g(t,n) - g(a,n) =
  integral(a,t) ( -mu * |xi_n|^2 * g(r,n) + Q(r,n) ) dr.
```

When `Q(r,n)` has been identified with the absolutely convergent ordered sum from the previous module, the resulting identity is the physical infinite Navier–Stokes Fourier integral equation.

## Mathematical proof

1. The previous *coordinate projection* theorem converts the actual finite vector-field ODE into a scalar-in-frequency (three-complex-component) ODE at each eventually retained mode. This is why exhaustion is necessary and cannot be hidden.
2. Since the finite vector field is real-C¹ on the finite state and finite paths are Lipschitz, the retained Fourier derivative is continuous on the common interval. Bochner FTC supplies the exact finite increment identity.
3. Constant-coefficient viscosity preserves uniform Fourier coefficient convergence. The exact projected Leray source converges uniformly in time, so the complete derivative fields converge uniformly on every initial subinterval.
4. The uniform convergence theorem for interval integrals passes those actual Bochner integrals to the limit. Simultaneously the Galerkin endpoint values converge. Uniqueness of the Banach-space limit identifies the two.
5. The separately established absolute summability and ordered-series identification replace `Q` by the full Leray convolution inside the integral.

## Scope and next step

The module deliberately exposes the uniform velocity and source coefficient limits as interfaces. The earlier Arzelà–Ascoli, infinite Wiener completion, and infinite source completion theorems establish these for constructed finite trajectories on their common interval. A further **single joint constructor** must connect these interfaces to one common subsequence (including source identity) and to compatible prescribed initial Fourier data. A local periodic Fourier solution is not a Clay three-dimensional global regularity theorem.

No `sorry`, `admit`, `axiom`, or invented PDE evolution hypothesis occurs in the source. Compilation is a required local check.
