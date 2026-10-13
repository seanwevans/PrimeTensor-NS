# Schwartz integrability of the first-monomial triad kernel

Base: e5775bd193bc4534c7b4517dbf52a94a8b311a2b.

## Result

`FirstMonomialTriadSchwartz.lean` supplies the integrability hypothesis of
`FirstMonomialTriadIntegral.lean` for a finite family of complex scalar
Schwartz amplitudes `U : ι → 𝓢(ι → ℝ, ℂ)`.

The measure is any SFinite measure with temperate growth on the frequency
space; Lebesgue measure is the intended case. Incompressibility is unnecessary
for integrability. With pointwise incompressibility, the previous integrated
shell identity applies without an additional integrability premise.

## Proof mechanism

Write q = -(p+r). The unsymmetrized kernel is the finite sum over i,k,l,v,j of

    (p_i p_k p_l U_j(p)) (r_i r_v U_j(r)) (q_k q_l U_v(q)).

Coordinate multiplication preserves Schwartz regularity. Each summand is
therefore F(p) G(r) H(-(p+r)) with scalar Schwartz F,G,H. Its absolute value is
bounded by

    |F(p)| |G(r)| sup_x |H(x)|.

The first two factors are separately integrable, so their product is integrable
on the product space. The third is bounded by its zeroth Schwartz seminorm.
Continuity supplies measurability. Finite summation finishes the argument.

This proof applies directly to the existing complex kernel definition: the
coordinate-expansion theorem is an equality, not a replacement kernel or an
extra analytic hypothesis.

## Mathematical boundary

This is an absolute-convergence result. It does not provide a critical H3
estimate: the Schwartz seminorm bound used here can be far too strong for that
purpose. The shell-difference identity remains available without taking its
absolute value in the cancellation theorem.

The remaining bridge is the exact Fourier identity for the physical first
monomial. That bridge must track the derivative multiplier, Fourier
normalization, reality, the pairing factor two, and the interpolation factor
three. A shell interaction estimate still remains after that identification.

## Validation

The source-index and fragment checks are run while preparing the patch.
`tools/audit/FirstMonomialTriad.lean` now includes the new integrability and
integral theorems and their axiom reports. Lean compilation must be performed
with the repository's pinned toolchain; this patch has not been locally
compiled in the preparation environment.
