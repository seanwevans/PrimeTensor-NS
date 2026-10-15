# Unconditional Schwartz cubic interpolation (finite-axis loss)

Base commit: `04dbc2b5`.

The joint physical slotwise Schwarz estimates are now proved unconditionally on the actual real Schwartz velocity, with three spatial axes:

- `E1² ≤ n E0 E2`
- `E2² ≤ n E1 E3`, where `n = card (Axis Depth.three) = 3`.

Algebraic elimination without division (including zero cases) proves:

- `E1³ ≤ n³ E0² E3`
- `E2³ ≤ n³ E0 E3²`.

At any positive balance scale satisfying `λ⁶ E3 = E0 > 0`, the entire unnormalized energy polynomial satisfies

`E0 + λ² E1 + λ⁴ E2 + λ⁶ E3 ≤ (2+2n) E0 = 8 E0`.

These estimates no longer require the conditional Fourier or Schwartz interpolation assumptions from the prior critical-half balanced-shape bridge. They are **nonsharp**: the missing mixed-derivative Hessian/Laplacian contraction is needed for coefficient-one adjacent interpolation. In particular none of these theorems asserts global critical-half coefficient existence or Navier–Stokes regularity.
