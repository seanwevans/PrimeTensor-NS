# Orderwise mixed Sobolev-jet graph — checkpoint ae930caf

The signed 243-slot Schwartz first-monomial nonlinear functional is Cauchy under
one scalar late-pair graph discrepancy:

```
G(f,g) = ∑_{j,i,k,l} ‖D_i D_k D_l f_j - D_i D_k D_l g_j‖_{L²}
       + ∑_{j,i,k}   ‖D_i D_k f_j - D_i D_k g_j‖_{L⁴}.
```

The first sum has **81** ordered derivative/component coordinates and the
second has **27**. Every 243-slot third/middle/cross perturbation jet is an
instance of one of these coordinates, so each root is at most `G(f,g)`.
A Cauchy condition on G therefore implies the established uniform-jet-free
243-slot theorem and produces a real signed nonlinear limit.

This is a *mixed derivative graph discrepancy*, not yet a proof that the
standard physical H³ Sobolev norm controls G. The bridge uses the existing
27-slot quartic Gagliardo–Nirenberg theorem to control L⁴ second jets by
H³ energies, and linearity of directional derivatives to relate pairwise jets
to derivatives of a difference. Schwartz density and equality to the
physical H³ transport pairing remain separate obligations.

There are no new axioms, `sorry` or `admit` in the new module. Verify Lean
with the user's project toolchain before committing.
