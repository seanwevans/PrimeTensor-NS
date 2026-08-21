# PrimeTensor — first Lean probe

This slice builds the multiplicative object language underneath the proposed
Navier–Stokes experiment.

The core design constraints are structural:

- dimensions and tensor ranks begin at `Depth.one`;
- `Axis.fold` is nonempty, so contraction never needs an empty-product case;
- a `PrimeBag` terminates at the multiplicative pivot `one`;
- `PrimeMultiset` quotients away factor order, making multiplication genuinely commutative;
- finite fractions are oriented pairs of prime bags;
- tensor contraction, divergence, and Laplacian are products;
- ordinary rationals appear only in `Bridge/Rational.lean`.

The first bridge theorem is `Bridge.contract₂_toRat`: interpreting a
multiplicative contraction agrees with multiplying the interpreted diagonal
components.

The derivative is abstract for now.  The next layer is the multiplicative
Cauchy completion of `PrimeRatio`, followed by intrinsic exp/log and a concrete
multiplicative derivative on that completed carrier.
