# Full actual Young-width cost: a common bounded-annulus modulus

Base: `01b67f59c58c21b227009a1fd4d0be4b8df495fd`.

## New analytic step

The accepted actual physical annular Young-width functional has **two** parts:

1. The squared Fourier norm of the genuine nonlinear Leray residual, weighted by `q(ξ)^3` on the sharp annulus. Its radius-independent difference bound on every finite ball was established in `...AnnularUniformYoungModulus.lean`.
2. The **raw-velocity** sharp-annular Fourier mass, weighted by
   `K(rho,sigma) = 2 (sigma^2)^3 ((sigma^2-rho^2)/2)^2`.

For `0 ≤ rho ≤ sigma ≤ R`, exact Fourier-L² cutoff contractions and H³ deweighting give

```
||B(rho,sigma) U_j||₂ ≤ 2 ||U||ₕ₃,
||B(rho,sigma) U_j - B(rho,sigma) V_j||₂ ≤ 2 ||U-V||ₕ₃,
| ||B U_j||₂² - ||B V_j||₂² | ≤ 4 (||U||ₕ₃+||V||ₕ₃) ||U-V||ₕ₃.
```

The width coefficient satisfies `0 ≤ K(rho,sigma) ≤ 2 R^10`.

Let `G_j(U) = N_j(U,U) - 2 L_j(U)` be the **actual** quadratic Leray forcing minus twice the raw spectral Laplacian. Let

```
C(U,V) = 576 π C₃ (||U|| + ||V||) + 2.
```

The full original Young-width cost `Y_(rho,sigma)(U)` satisfies the cutoff-uniform estimate

```
|Y_(rho,sigma)(U)-Y_(rho,sigma)(V)|
  ≤ M_R(U,V) ||U-V||,

M_R(U,V) = Σ_(j=0,1,2) [
    8 R^6 (||G_j(U)||₂+||G_j(V)||₂) C(U,V)
    + 8 R^10 (||U||+||V||)
  ].
```

`M_R(U,V)` depends on the **states** and their H³ nonlinear Fourier residuals and on the fixed frequency ceiling `R`, but **not** on `rho` or `sigma`. The final theorem transfers this estimate to any pair of actual physical times, without adding a Young-cost continuity premise.

## Scope and remaining barrier

This is an explicit equicontinuity *estimate* for the complete exact Young-width functional on all annuli within a fixed ball; it uses the same finite-band frequency multiplier, true nonlinear forcing, and original radial-width coefficient as the accepted physical PDE budget. It does not prove that the two actual spectral states are uniformly close on a prescribed time interval, and it does not furnish a positive common time-window length when `R → ∞`. The growth `R^6` and `R^10` makes cofinal terminal window collapse a genuine remaining possibility. A next step is to combine this estimate with a locally bounded H³-state/residual envelope and then with the strict excess/deficit margins to derive a common right window for **bounded** annular families; the unbounded-radius case needs additional structure or frequency-tightness.

No `sorry`, `admit`, or new axiom is introduced. Kernel verification must be run in the user's pinned Lean/mathlib environment.
