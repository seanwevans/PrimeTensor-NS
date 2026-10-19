# Actual physical full-third Schwartz commutator: unrestricted Hermitian integral

Base commit: `304da8f9` — *remove full third Schwartz physical spectral mass gate*.

This checkpoint proves the remaining sector-support implication for the real,
windowed physical five-index coefficient. Nonzero physical polynomial implies
nonzero first and last **scalar** Fourier windows. Their existing compact
support puts the physical pair of frequencies inside its correct axis-sup-metric
positive coherent sector whenever `ρ ≤ δ`. We do **not** exchange these
coordinate sectors for Hilbert/L2 balls.

The sector integral is therefore its unrestricted product-volume integral.
Integrability follows by identification with the indicator of the previously
proved absolutely integrable **actual real Schwartz Fourier kernel**, not by
asserting arbitrary bare polynomials are integrable.

The closed previous mass-gate removal, Hermitian reflection and six-sector
identity, along with the previously proved measure-preserving six pair
permutations and true five-index physical/Hermitian orbit identity, now give

    T3(thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C)
      = 2 * (2π)^7 * ∫ W_ρ(p,-p-r,r) * H_projected(A,B,C;p,r) dp dr.

Theorem: `thirdFullAxisRealThirdCommutator_eq_commonWindowHermitian244`.

Hypotheses still include the genuine window width nonresonance bound,
`ρ < δ`, and disjoint physical sector condition `2δ ≤ 1`.

This is an exact global equality, NOT a statement that the integral is
nonzero. The next work is to choose the sharp-center polarizations, a small
window, and prove that the support lies inside the already proven strictly
negative neighborhood and that the common three-window factor is nonnegative
and strictly positive on a set of positive measure. Only after that can we
invoke existing velocity-reversal / kinetic concentration theorems to close
static H3 absorption obstruction. No time-evolution claim is made.
