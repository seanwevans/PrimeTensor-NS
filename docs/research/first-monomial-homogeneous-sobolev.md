# Quantitative homogeneous Sobolev after the split-cutoff estimate

**Base:** `24160e47` — split quantitative cutoff Sobolev into L2 norms.

This patch implements the previously isolated `R → ∞` analytic step. For a
spatially C1 scalar function `g` on actual physical Point3, assuming `g` and
its Frechet derivative have finite L2 norms, the new theorem asserts:

    ‖g‖_{L6} ≤ S ‖Dg‖_{L2}

`S` is **exactly** Mathlib's original compact-support three-dimensional
Sobolev constant, independent of the field. In particular, there is no
zeroth-order term on the right side.

Proof structure:

1. Instantiate the previously proved uniform split-cutoff bound for radii
   `R_n = n+1`.
2. Use real inverse convergence to prove the ENNReal cutoff factor vanishes.
   Multiplication by the finite `L2` norm of `g` preserves this convergence.
3. The upper bound converges to `S ‖Dg‖_2` by continuity of addition and
   multiplication by the finite Sobolev constant in ENNReal.
4. Existing physical cutoff equality shows that the sequence converges
   pointwise to `g`.
5. Use mathlib's lower semicontinuity of `eLpNorm` and monotonicity of
   liminf to transfer the universal bound to `g`.

This is a classical Sobolev estimate, **not** a Navier--Stokes continuation
theorem. The remaining program still needs to apply it to each physical
second derivative, convert directional and Frechet derivative norms, and
assemble the 243-slot Gagliardo--Nirenberg/Holder estimate.

This ZIP was syntax/structure checked but **not Lean-compiled**, because the
local Lean/mathlib build toolchain is unavailable in the authoring container.
