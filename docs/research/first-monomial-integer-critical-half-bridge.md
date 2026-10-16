# Integer-order critical-half route from sharp physical Schwartz energies

Parent commit: `a2abce31`, **prove exact 243-slot physical Schwartz Holder bound**.

## Why change the route?

The prior seventh-power proof isolates a route through homogeneous fractional
Sobolev embedding `Ḣ^(3/4) → L⁴` applied to second derivatives. It is correct,
but establishing fractional Fourier-space equivalence for the project carriers
would create a large bridge solely for this particular estimate.

The *classical three-dimensional Gagliardo–Nirenberg* estimate instead states

    ‖g‖₄ ≤ C ‖g‖₂^(1/4) ‖∇g‖₂^(3/4),

for suitable Schwartz (or H¹) scalar `g`. Setting `g = D²u` and using the
existing, full 243-slot `L²·L⁴·L⁴` Holder inequality, the remaining **quantitative**
analytic task is a profile-independent finite `K` such that

    |M(u)|⁴ ≤ K⁴ E2(u) E3(u)⁵.

This is not established in the new module; it requires actual L²/L⁴/L⁶
norm control and finite-index aggregation. The repository already has a
whole-space `H¹ → L⁶` **membership** theorem and compact-support quantitative
Sobolev machinery, but extracting the homogeneous quantitative constant
requires additional estimates. Membership by itself is not enough.

## New unconditional theorem: coefficient-one six-moment majorization

The existing three Cauchy estimates are

    E2² ≤ E1 E3,    E3² ≤ E2 D,    E2² ≤ E0 D.

They imply, with no division by zero and no external hypothesis,

    E2 E3⁵
      ≤ E2³ E3 D²        (twice E3² ≤ E2 D)
      ≤ E1 E2 E3² D²      (E2² ≤ E1 E3)
      ≤ E1 E2² D³        (E3² ≤ E2 D)
      ≤ E0 E1 D⁴         (E2² ≤ E0 D).

Hence any successfully proved quantitative quartic GN bound immediately yields

    |M|⁴ ≤ K⁴ E0 E1 D⁴.

Since `E0 E1 ≤ (E0 + E1)²`, fourth-power monotonicity gives

    |M| ≤ K sqrt(E0 + E1) D.

The proven coefficient-one moment comparison applies to **all** real Schwartz
velocity fields, whether or not they are divergence-free. It preserves the
true physical fourth-order 243-slot dissipation and exact first-monomial
normalization.

## Formalized statements

- `criticalHalf_integerMoments_E2_mul_E3_pow_five_le`: general nonnegative
  finite-moment lemma, deriving the coefficient-one comparison.
- `lowNormalRealSchwartz_integerMoments_E2_mul_E3_pow_five_le`: exact full
  physical Schwartz specialization, unconditional.
- `criticalHalf_integerMoments_quarticToEnergy`: scalar consequence under an
  **explicit** quantitative nonlinear quartic bound.
- `lowNormalRealSchwartz_criticalHalf_of_integerGNQuartic`: faithful physical
  specialization with the missing analytic hypothesis still visible.

The next proof should establish the genuine scalar Schwartz GN norm bound
from the repo's existing whole-space Sobolev and real `L²×L⁴×L⁴` tools,
then aggregate the 243 slots. This is established classical analysis; it is
not a new 3-D Navier–Stokes regularity mechanism.
