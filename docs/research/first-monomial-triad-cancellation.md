# First-monomial triad cancellation

Base: `9bae3794`. This is the first mathematical increment following the
Depth-to-continuation roadmap. It investigates the genuine nonlinearity rather
than introducing another conditional terminal alternative.

## Exact calculation

The existing first-monomial aggregate has terms

    (∂i∂k∂l u_j)(∂k∂l u_v)(∂i∂v u_j).

Assign frequencies p, q, r respectively, with p+q+r=0, and polarizations
a, b, c. Summing derivative indices gives, apart from the common Fourier
derivative factor and the velocity contraction a·c,

    C(p,q,r;b) = (p·r)(p·q)^2(r·b).

Incompressibility of the middle factor gives q·b=0. Exchange the two
u_j factors, including both their frequencies and amplitudes. Their common
contraction a·c is unchanged. The exchanged coefficient is

    C(r,q,p;b) = (p·r)(r·q)^2(p·b).

Momentum and incompressibility imply

    r·b = -p·b,
    r·q + p·q = -|q|²,
    r·q - p·q = |p|²-|r|².

Consequently the exact paired coefficient is

    C(p,q,r;b) + C(r,q,p;b)
      = (p·r)(p·b)|q|² (|r|²-|p|²).

The symmetrized coefficient is one half of this expression. Equal-length
outer frequencies cancel exactly. This does not require the outer frequencies
to point in the same direction.

The attached Lean source defines the explicit four-index derivative contraction,
reduces it to C, proves the paired factorization, and derives equal-shell
cancellation and the exact absolute-value formula. It works for any finite
index type over the reals, so positive-dimensional native axes are eligible.
It introduces no PDE or continuation premise. It uses actual momentum and
polarization constraints, beyond the generic four-factor native balance.

## What is suppressed

Two factors remain visible before applying inequalities:

* polarization alignment, p·b, with b perpendicular to q;
* separation of the two outer squared frequency lengths, |r|²-|p|².

For q≠0, the first may be bounded using the component of p perpendicular to q.
For complex Fourier amplitudes, the algebra extends componentwise to real and
imaginary parts, since the identity is linear in b. A complete complex Fourier
bridge is not implemented in this patch.

Momentum also gives

    | |r|²-|p|² | = |(r-p)·(r+p)| ≤ |q| (|r|+|p|).

Thus, writing P=|p|, Q=|q| and R=|r|, elementary Cauchy–Schwarz estimates yield

    |C_sym| ≤ (1/2) P R min(P,R) |b| Q³(P+R).

This bound is a mathematical consequence explained here, not an additional
Lean theorem in this patch. The minimum follows from p·b=-r·b.

When P and R are comparable to N and Q=L≪N, the symmetrized estimate is
O(N⁴L³|b|). Bounding the two unsymmetrized terms separately would give
O(N⁵L²|b|). The exchange therefore gains a factor comparable to L/N in this
specific low-middle-frequency regime. When all three lengths are comparable,
both estimates have degree seven and no such small ratio follows.

This is a concrete reason to retain the signed interaction and organize
frequency regimes before taking absolute values. It is not yet a proof of a
better global Sobolev bound: summation, other regimes, and the actual Fourier
amplitudes still matter.

## Normalization and analytic boundary

With derivative symbol iξ, the seven derivatives contribute i^7=-i; another
Fourier convention introduces its corresponding common powers of 2π. These
constants are not included in C. In addition, the repository defines
`spatialEnergyPairing f g = 2 * ∫ f*g`. Its factor two must be retained when
identifying the repository aggregate A with the symmetrized Fourier integral.
In particular, the factor 1/2 from exchange averaging must not be applied
twice or confused with the factor three in the already-proved I₃=3A identity.

For Schwartz divergence-free fields, the Fourier product formula and a change
of variables exchanging p and r justify averaging the integral. The formal
project still needs that identification, including integrability/Fubini,
complex conjugation or the equivalent three-frequency convention, transform
normalization, and the physical pairing's factor two. General H³ energy-class
fields then require the appropriate approximation and continuity argument.

The new module does NOT claim that the physical aggregate has been replaced
by this Fourier integral in Lean. It proves the algebraic cancellation that
the analytic bridge should preserve.

## The cancellation is not complete

For p=(1,0,0), q=(1,1,0), r=(-2,-1,0), and b=(1,-1,0), the momentum and
polarization constraints hold, but the paired coefficient equals -16.
Changing b to -b reverses it. There is therefore no universal sign or
identical vanishing of this scalar symbol from these constraints alone.
Fourier phases and the remaining a·c contraction also matter for a real
physical integral; this example is only a test of the coefficient identity.

## Next mathematical target

First connect the symmetrized coefficient to the existing first-monomial
aggregate on divergence-free Schwartz fields, with exact normalization.
Then separate low-middle interactions from comparable-frequency interactions
and retain the shell-difference factor in the estimates. The decisive question
is whether the remaining comparable-frequency contribution can be controlled
jointly with the true gradient block and dissipation.

The existing sufficient compensation inequality involving 24 C₁ sqrt(E) E₃
uses a gradient envelope. This patch does not improve that envelope, eliminate
either directed-source branch, or prove temporal integrability. An eventual
useful estimate must control the actual combined signed production, or feed
an already sufficient terminal criterion with an independently derived bound.

## Validation

The sign and normalization-free polynomial identity were checked independently
against the original five-index (243-term) contraction for 300 exact-integer
triads with divergence-free polarizations. No floating-point tolerance was
used. This checks the translation of the physical monomial into the factored
coefficient; it is not a replacement for the proof.

Lean is unavailable in the preparation runtime. The accompanying proof source
has not been compiled here. The run workflow builds the module, prints selected
axiom dependencies, builds the root, and stops before committing if any check
fails. The centralized roadmap remains outside the repository and uncommitted.
