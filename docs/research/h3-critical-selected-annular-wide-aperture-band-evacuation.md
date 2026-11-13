# Actual selected-annulus wide-aperture band evacuation

**Base:** `70e6adc59221afa6115b2dbb47dcfab533324ea8` — selected annular aspect escape from the genuine physical L² terminal trace.

## New physical constraint

Let `rho > 0`, `rho <= sigma`, and `sigma² >= 2 rho²`. Put

- `M(t,rho)`: genuine sharp **physical** L² highpass kinetic mass;
- `N(t,rho,sigma)`: sum of squared L² norms of the differences of the true Fourier sharp lowpasses at `sigma` and `rho`; this is the annular *raw* kinetic mass;
- `Y(t,rho,sigma)`: the complete actual q³-weighted Young residual plus the exact finite-annulus width term;
- `D(t,rho,sigma)`: the previously defined physical annular kinetic deficit, including the zero-viscosity outer budget.

The native Hilbert identity for `Y` yields

```
2 * sigma^6 * ((sigma² - rho²)/2)^2 * N <= Y.
```

Suppose the true kinetic excess is **strictly positive**, witnessed by an actual margin `margin>0`, and the true deficit is nonnegative. The squared excess is then at most the square of `((rho²+sigma²)/2)*M`, since the genuine lowpass source `B>=0` and `0<=B<=((rho²+sigma²)/2)*M`. The zero-viscosity outer term is nonnegative, so

```
M * 2*sigma^6*((sigma²-rho²)/2)^2*N
    <= rho^6 * (((rho²+sigma²)/2)*M)^2.
```

The strict positive excess and positive margin make `M>0`, permitting honest cancellation. Since `sigma² >= 2*rho²`, the radial mean is no more than three times the half-aperture. Cancellation of the positive half-aperture square proves the exact spectral evacuation inequality

```
2*sigma^6 * N <= 9*rho^6 * M.
```

This is **a necessary condition** for a nonnegative deficit; it does not show that any such deficit exists. It uses the original sharp Fourier projectors and the original physical zero-viscosity outer budget.

## Terminal consequence

Under finite physical H³ dissipation, the earlier physical L² terminal trace and moving sharp-highpass theorem give *aspect escape* for selected strict-excess natural-radius annuli: for every fixed `K`, eventually `K*(n(k)+1)<sigma(k)`. Adding nonnegative physical deficit at those selected snapshots, this patch obtains, for every `K>=2`, eventually

```
2*K^6 * N(k) <= 9*M(k).
```

The fraction of highpass kinetic mass retained in the interior annulus must therefore be arbitrarily small. In conjunction with the exact sharp Fourier annular/outer partition, this identifies an outer-tail concentration mechanism; the present patch does not assert that extra partition as a new Lean theorem.

## Logical boundary

The selected snapshot strict-excess and nonnegative-deficit hypotheses are *not* derived unconditionally from the 3D Navier–Stokes PDE. Finite terminal H³ dissipation is explicitly assumed in the cofinal statement. No theorem of global H³ continuation or smoothness is claimed.
