# Critical-half coefficient under a single spatial dilation

**Base:** `5d7b5cf2`.

The amplitude-ray theorem proves that `θ = 1/2` is the least exponent not ruled
out by amplitude homogeneity. Uniformity over the full Schwartz class is
not settled by that fact.

For a fixed smooth spatial profile in 3D, consider isotropic dilation
`f_λ(x)=f(λx)` and a seven-derivative trilinear first monomial. Formal
change-of-variable scaling gives

- `M(f_λ) = λ^4 M(f)` (seven spatial derivatives and three-dimensional volume);
- `E_k(f_λ) = λ^(2k-3) E_k(f)` for orders `k=0,1,2,3`;
- `D_4(f_λ) = λ^5 D_4(f)` (four derivative squared).

At the critical exponent, the **squared** uniform estimate reduces, for
`λ>0`, to

    M² λ ≤ C² D² [ E0 + λ² E1 + λ⁴ E2 + λ⁶ E3 ].

For all nonnegative `λ`, one has the key scalar inequality

    λ min(E0,E3) ≤ E0 + λ² E1 + λ⁴ E2 + λ⁶ E3.

For `λ≤1`, the zeroth energy supplies the bound; for `λ≥1`, the third-order
energy and `λ⁶≥λ` do so. Consequently any
`C² D² min(E0,E3) ≥ M²` works for all dilations. If `D,E0,E3` are
positive, there is always such a finite C for **one shape**.

The Lean module proves these **scalar facts**, including the existence of a
single finite coefficient for every nonnegative scalar dilation parameter.
It does **not** prove the spatial-dilation identities for the actual
Schwartz/Point3 operators, which would require a separate rigorous
composition/derivative/measure-change transfer. Even after that transfer,
one fixed shape's dilution family does not settle uniformity across
all divergence-free Schwartz profiles.

Thus a failure of the global endpoint bound, if it exists, must involve
variation of the profile (for example, multiscale concentration), not simply
uniform dilation of one profile.
