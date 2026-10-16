# Signed first monomial: discrete 2-4-4 fourth-power reduction

**Base:** `2471c228` (the complete 243-slot moment multiplicity identities).

For arbitrary real arrays `a`, `b`, and `c` on one finite index set, two
applications of `Finset.sum_mul_sq_le_sq_mul_sq` show

    (sum a*b*c)^4 <= (sum a^2)^2 * (sum b^4) * (sum c^4).

The coefficient is one, including the zero-mass cases. No Hölder-conjugate
fractional exponents or divisions are necessary.

The physical signed 243-slot first monomial is *exactly twice* the fivefold
sum of its real Schwartz slot integrals. Therefore the generic inequality,
combined with the finite triangle inequality and a **visible** slotwise
real Hölder majorant, gives the fourth-power bound with coefficient 16.

This checkpoint deliberately does not assert the slotwise real Hölder
majorant without proof. The existing analytical theorem produces a bound
in `ENNReal` using `realLpEnorm`; the next step is the explicit finite
Schwartz-norm conversion to real numbers and then application of the
already proved exact 3/9/9 multiplicities and quartic GN bound.

No axioms, `sorry`, or PDE regularity conclusions are added.
