# Intrinsic normal-shell remainder

Base checkpoint: `68bd0c24` (common plane frames).

## Exact identity

Write S(p,q,r;b) for the existing complexShellCoefficient:

    S(p,q,r;b) = (p·r)(p·b)|q|²(|r|²-|p|²).

For any real three-dimensional momentum triad p+q+r=0 and complex amplitudes
a,b,c satisfying p·a=q·b=r·c=0, the new theorem supplies a real vector n with

    n·n=1, n·p=n·q=n·r=0

and identifies the complete six-order coefficient as

    C6 = S(p,q,r;b) (n·a)(n·c)
       + S(p,r,q;c) (n·a)(n·b)
       + S(q,p,r;a) (n·b)(n·c).

All amplitude contractions are complex bilinear, not Hermitian. The formula
contains the original physical-coordinate frequencies and amplitudes, together
with a common unit normal. It has no inverse-frequency factors and assumes
no frequency is nonzero. Replacing n by -n preserves each paired normal factor.

## Proof structure

1. Re-express the proved coordinate-plane polynomial identity in terms of the
   three existing shell coefficients, retaining just the normal products.
2. For nonzero planar frequencies, reconstruct arbitrary divergence-free
   amplitudes and substitute them into that identity.
3. Handle a zero frequency directly: every ordered coefficient and every
   shell channel vanishes, regardless of amplitude constraints. No division
   is used in these branches.
4. Choose the already constructed common orthogonal frame. Pull back the
   actual amplitudes, use orthogonal covariance of the shell coefficients,
   and identify the third coordinate with contraction against O(0,0,1).

The new `normalShellSum` definition records the three terms, while
`exists_unit_normal_shell_decomposition` is the final intrinsic interface.

## Mathematical significance and remaining work

The earlier shell identity involved full outer-amplitude bilinear pairings.
The new identity removes their purely planar contributions after all six
orderings. Every surviving term contains two normal amplitudes. The established
positive and negative examples are compatible with this remainder, so it does
not assert a universal sign or universal vanishing.

The reconstruction proof uses division internally on its nonzero branches;
the final identity does not. This distinction matters for estimates near zero
frequency. The theorem is still an exact pointwise identity, not an estimate
showing that normal amplitudes are small.

Next mathematical tasks:

- Bound the paired normal contributions while retaining geometric information
  that is lost by replacing each amplitude by its full norm.
- Determine which available PDE or spectral hypotheses can provide a gain;
  incompressibility alone does not force the normal components to be small.
- Justify six-order symmetrization at the field-integral level. Pointwise frame
  existence does not itself provide a measurable frame choice; intrinsic
  estimates may avoid needing such a choice.
- Compare any resulting bound with the established third-energy/first-moment
  estimate before claiming improvement in the comparable-frequency regime.

No new integral estimate, sign theorem, or continuation result is asserted.

## Validation

The audit checks the new covariance and decomposition declarations and prints
their axioms. Generated index consistency, prose-fragment validation, and
whitespace checks are run before packaging. Lean compilation remains pending
on the user's pinned toolchain; this environment has no Lean executable.
