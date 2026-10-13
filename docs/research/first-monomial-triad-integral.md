# Complex amplitudes and integrated triad cancellation

Base: `ef448a53`, the compiled real triad-cancellation checkpoint.

The new module `FirstMonomialTriadIntegral.lean` advances the cancellation
from real scalar coefficients to complex amplitude kernels and their Bochner
integrals. It does not yet identify those integrals with the physical
first-monomial aggregate.

## The correct frequency coordinates

Choose the outer frequencies p and r independently, and define q=-(p+r).
The exchange of the two same-component velocity factors is then simply
(p,r) ↦ (r,p). The middle frequency stays unchanged. This avoids a separate
translation-and-reflection change of variables in a nested integral.

For a complex amplitude vector U, define

    K(p,r) = (p·r)(p·q)^2 (r·U(q)) [U(p)·U(r)].

All contractions here are bilinear. There is no complex conjugation because
the chosen convention writes all three frequencies with p+q+r=0. A subsequent
physical Fourier identification must use this convention consistently, or
explicitly convert a conjugated Plancherel expression into it.

If q·U(q)=0, the real cancellation theorem extends to real and imaginary
parts of U(q). Commutativity of the repeated velocity-component contraction
gives the pointwise complex identity

    K(p,r)+K(r,p) = R(p,r),

    R(p,r) = (p·r)(p·U(q)) |q|² (|r|²-|p|²) [U(p)·U(r)].

The common Fourier derivative constants remain outside these definitions.

## Integral identity and factor two

Assume K is integrable for μ×μ, where μ is any SFinite measure on the
frequency space. The swap preserves μ×μ, so K composed with swap is also
integrable and has the same integral. Therefore R is integrable and

    ∫ R = 2 ∫ K.

The source proves the swap using mathlib's product-measure theorem; equality
of the two integrals is not an extra hypothesis.

For any complex constant c the source also proves

    2 Re(c ∫ K) = Re(c ∫ R).

This keeps the normalization ready for the repository's physical pairing,
which is twice the real spatial integral. The generic c can retain the actual
Fourier derivative and transform-normalization constants. No value for c is
assumed without checking that later Fourier identification.

## Exact hypotheses and what remains

The source requires pointwise Fourier incompressibility at every frequency
and absolute Bochner integrability of K. It proves the complex extension,
exchange identity, integrability of R, and equality of integrals. It does not
derive incompressibility or kernel integrability from a PDE path.

The next analytic obligations are:

1. Instantiate U with the actual Fourier transform of a divergence-free
   Schwartz velocity and prove these two inputs for it.
2. Identify the physical first-monomial aggregate with 2 Re(c ∫K), including
   the exact convention and the existing factor three in I₃=3A.
3. Transfer the identity beyond Schwartz fields with the needed convergence
   and integrability estimates.
4. Use the retained shell/polarization factors in frequency estimates that
   address the surviving signed-production obstruction.

No favorable sign, terminal estimate, or continuation result follows yet.
The pointwise-divergence statement also must not be silently replaced by an
almost-everywhere representative statement without the corresponding measure
argument on the triad frequency plane.

## Validation boundary

The mathlib swap and integrability APIs were inspected at the project's locked
mathlib revision `a021f70d9761145082ee6f1b6887faa3e6599afc`.
Source-index and whitespace checks were run. Lean is unavailable in the
preparation environment; the new Lean source awaits compilation in the normal
local build workflow. The audit file prints the main types and axiom reports.
