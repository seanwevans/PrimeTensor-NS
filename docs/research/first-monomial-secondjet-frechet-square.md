# Second-jet Fréchet/coordinate-square comparison

**Base:** `c3a5a057` — transfer homogeneous Sobolev to all 27 Schwartz second jets.

The physical carrier `Point3` has a supremum norm. Consequently the scalar
Fréchet derivative is controlled pointwise by the sum of the magnitudes of its
three coordinate derivatives. A finite-dimensional Cauchy–Schwarz inequality
gives, for any C¹ physical scalar `g`,

\[
\|Dg(x)\|^2 \le (\#\mathrm{Axis}(\mathrm{Depth.three}))
   \sum_{a} |\partial_a g(x)|^2.
\]

`Axis Depth.three` contains three axes. This is the correct *dimension factor*;
the estimate does not tacitly replace the physical operator norm with the
Euclidean gradient norm.

The second theorem applies the bound to each physical pullback of the genuine
27 ordered second-derivative Schwartz jets and uses the already-proved transport
identity to identify the coordinate derivatives with the corresponding third
Schwartz jets.

**Next:** integrate the pointwise comparison, relate it to the full third-order
Schwartz energy E3, and combine with the previous homogeneous Sobolev bound.
Neither that integral comparison nor the nonlinear quartic GN estimate is
asserted in this patch.
