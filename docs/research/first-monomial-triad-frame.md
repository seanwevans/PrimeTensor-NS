# A common orthogonal frame for a momentum triad

Base checkpoint: `fd8de4cc` (collinear cancellation).

## Construction

Given p,q in real Euclidean three-space, their span K has dimension at most
two. Since dim K + dim K-perp = 3, choose a nonzero w in K-perp and set
n=w/|w|. This produces a common unit normal even if p,q are dependent or zero.

Let e be the third coordinate unit vector. Reflection across the orthogonal
complement of e-n sends e to n, by Mathlib's equal-norm reflection theorem.
Call that real linear isometry O. For either v=p or v=q,

    (O-inverse v)_2 = <e,O-inverse v> = <O e,v> = <n,v> = 0.

Thus there exist x,y,z,w with

    p = O(x,y,0), q = O(z,w,0).

Momentum conservation then gives r=O(-x-z,-y-w,0).
The construction imposes no orientation restriction: reflections are allowed
because the preceding coefficient covariance theorem is orthogonal, not only
rotation invariant.

## Interface with the coefficient

`exists_common_plane_frame` supplies the orthogonal map and the two planar
coordinate pairs for arbitrary momentum-conserving frequencies.
`exists_plane_frame_coefficient` also identifies the actual complete six-order
coefficient with its coordinate-plane expression, with all three complex
amplitudes pulled back by O-inverse.

The construction requires no incompressibility hypothesis. That hypothesis
transfers separately using `mixedDot_inverse_frame`. At nonzero frequencies,
`planePolarization_reconstruct` then supplies the planar/normal amplitudes
needed by the polynomial geometry identity.

## Roadmap

- Completed before this patch: orthogonal covariance, reconstruction in a
  supplied frame, and direct collinear cancellation including zero parameters.
- This patch: pointwise existence of the common frame and coefficient transfer.
- Next: combine reconstruction with the frame to express the surviving
  two-normal-amplitude terms intrinsically; quantify the resulting geometry.
- Then: justify six-order symmetrization at the integral level and compare
  the geometric estimate with the existing third-energy/first-moment bound.

This is pointwise existence. It does not choose a measurable or continuous
frame over frequency space, nor claim a new integral estimate or PDE
continuation theorem. The normalization divides by a chosen nonzero normal,
not by any of the three frequencies. Degenerate triads are included in frame
existence, but the separate polarization reconstruction still requires
nonzero frequencies.

## Validation

The source APIs were checked against the repository's pinned Mathlib commit
`a021f70d9761145082ee6f1b6887faa3e6599afc`, including the reflection theorem and
orthogonal-complement dimension identity. The audit checks the four new
declarations and prints their axioms. Proof-index consistency, prose-fragment
validation, and whitespace checks are run before packaging. Lean compilation
is pending on the user's pinned toolchain; no Lean executable is installed
in the patch-preparation environment.
