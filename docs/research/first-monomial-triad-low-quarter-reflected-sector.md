# Reflected sharp Schwartz triad: parity and local integration

Checkpoint: `c56aec16` — prove positive localized integral for sharp Schwartz triad.

## The reflection identity

For a real frequency `p` and a complex polarization `a`, reflection sends
`(p,a)` to `(-p, conj a)`. The scalar contractions satisfy

- `dot(-p,-r) = dot(p,r)`;
- `mixedDot(-r,conj b) = -conj(mixedDot(r,b))`;
- `amplitudeDot(conj a,conj c) = conj(amplitudeDot(a,c))`.

Therefore the complete six-permutation coefficient obeys

`C6(-p,-q,-r; conj a,conj b,conj c) = -conj(C6(p,q,r; a,b,c))`.

The established Schwartz field has `U(-xi) = conj(U(xi))`; hence with
`q=-p-r` and `F(p,r) = Re(i*C6(p,q,r;U(p),U(q),U(r)))`:

`F(-p,-r) = F(p,r)`.

At both resonant orientations the value is exactly `9/64 > 0`. The existing
continuity and compact-ball arguments give a strictly positive localized
signed integral in each orientation.

## Scope and remaining frontier

This is pointwise *global* reflection symmetry of the signed kernel and two
*localized* positive-integral results. It is not a proof that the integral
over all of frequency-pair space is nonzero. The four other permutations
within each orientation and any off-center variations of the kernel still
require control before global noncancellation can be claimed. The physical
seven-derivative Fourier factor is `-(2*pi)^7 i`, so its physical sign is the
negative of the book-keeping `i` phase used to define `F`.
