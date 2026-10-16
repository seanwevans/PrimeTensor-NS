# Exact Schwartz L⁴ interpolation by joint L² Cauchy

Baseline: `86865d2a`, `prove integer-order critical-half Schwartz moment bridge`.

The existing signed Schwartz Cauchy--Schwarz theorem is stronger than the
specific scalar interpolation required here. Let `g` be any real Schwartz map
on the genuine Euclidean physical three-carrier and construct the Schwartz
cube `c := g * (g * g)` through `SchwartzMap.pairing`.

Applying the already proved L² Cauchy theorem to `g` and `c` gives:

    (∫ g⁴)² ≤ (∫ g²) (∫ g⁶).

Apply its joint finite-index version to all 27 ordered second derivative
slots (three velocity components times two derivative directions):

    (Σ_{j,i,k} ∫ (∂_i∂_k f_j)⁴)²
      ≤ E₂(f) × (Σ_{j,i,k} ∫ (∂_i∂_k f_j)⁶).

The constant is exactly one and NO finite-index cardinality loss occurs.
All integrals are genuinely finite because the inputs and their products are
Schwartz maps. There are no new axioms, `sorry`, regularity assumptions,
or imported continuation criteria.

This establishes the L²/L⁶ interpolation substep of the classical
Gagliardo--Nirenberg estimate. It does **not** yet establish the
quantitative homogeneous whole-space Sobolev inequality

    ‖g‖₆ ≤ S ‖∇g‖₂,

for the project's precise physical normalization. The existing cutoff
proof establishes whole-space L⁶ *membership* but must be strengthened to
retain the homogeneous quantitative constant. That is the next analytic
step before aggregating the exact 243-slot physical Hölder bound and
applying the integer-moment closure. None of these classical bounds alone
is a proof of unconditional Navier--Stokes regularity.
