# Exact 243-slot factor multiplicities in signed 2-4-4 Holder

Base: `2799d7c1` (full 27-slot quartic Gagliardo–Nirenberg).

For the **actual** signed first-monomial slot indexed by `(i,k,l,r,j)`, the
Schwartz factors have derivative patterns `(i,k,l;j)`, `(k,l;r)`, and `(i,r;j)`.

Writing `E3` for all 81 ordered third-derivative squared integrals and `Q4`
for all 27 ordered second-derivative fourth-power integrals, the proofs show:

- `Σ_{i,k,l,r,j} ∫ (D_i D_k D_l f_j)^2 = card(A3) * E3`.
- `Σ_{i,k,l,r,j} ∫ (D_k D_l f_r)^4 = card(A3)^2 * Q4`.
- `Σ_{i,k,l,r,j} ∫ (D_i D_r f_j)^4 = card(A3)^2 * Q4`.

Since `card(A3)=3`, these are respectively `3 E3`, `9 Q4`, and `9 Q4`.
Their exact fourth-power moment product is `card(A3)^6 * E3^2 * Q4^2`,
with the first factor squared (the exponents of discrete 2-4-4 Hölder).
The proof only rotates finite sums. It never commutes differential operators,
identifies Point3 with its Euclidean carrier, drops a slot, or assumes the
incompressible Navier–Stokes equations.

The remaining step is quantitative norm/integral conversion and the discrete
2-4-4 Holder aggregation to `M(f)` itself; these identities alone do not
prove the signed critical-half bound.

Lean compilation of this patch is required locally.
