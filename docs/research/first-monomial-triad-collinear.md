# Degenerate triads: direct cancellation

Base checkpoint: `acaeafc0` (polarization reconstruction).

## Result

Let p=s v, q=t v, r=u v for real scalars s,t,u and a common real
frequency vector v in any finite dimension. For a complex polarization b,
assume only q·b=0. Then the ordered coefficient

    (p·r) (p·q)² (r·b)

is zero. Indeed, q·b=t(v·b)=0. If t=0, p·q=0; otherwise v·b=0 and
therefore r·b=0. The Lean proof uses the product-zero alternative directly,
so it never divides by t or by a frequency norm.

If each of a,b,c is perpendicular to its own frequency, all six ordered
coefficients vanish separately. This is stronger than cancellation after
summation. No momentum assumption is needed for the line-parameterized
result; zero line parameters and a zero direction vector are allowed.

A corollary handles (0,q,-q), and another obtains that configuration from
p=0 and p+q+r=0. The amplitude at the zero frequency is unrestricted.
These are exact complex coefficient identities, not merely statements about
their imaginary parts.

## Connection to the previous geometric identity

The planar formula had an area factor, suggesting collinear cancellation,
but extending its parameterization to arbitrary amplitudes required nonzero
frequencies. This direct proof covers the frequency-line case without that
restriction and without choosing an orthogonal frame.

It does not assert that arbitrary noncollinear triads cancel. The existing
mixed-normal sign examples survive and remain relevant to the difficult
comparable-frequency regime.

## Roadmap

- Established: planar/normal polynomial identity, orthogonal covariance,
  reconstruction at nonzero frequencies in a supplied frame.
- This patch: direct collinear cancellation, including zero line parameters,
  and the zero-first-frequency momentum corollary.
- Next: construct an orthogonal frame for a genuinely two-dimensional
  momentum-conserving triad. This construction is not supplied by this patch.
- Then: express and bound the surviving two-normal-amplitude terms intrinsically.
- Integral stage: justify six-order symmetrization and assess whether the
  geometric factor produces an estimate beyond the current energy-moment bound.

No new continuation theorem or uniform control of inverse frequencies is claimed.

## Validation

The audit file checks the new declarations and prints their axioms. Proof-index,
prose-fragment, and whitespace checks are run before packaging. Lean compilation
is pending on the repository's pinned toolchain; this environment has no Lean
executable.
