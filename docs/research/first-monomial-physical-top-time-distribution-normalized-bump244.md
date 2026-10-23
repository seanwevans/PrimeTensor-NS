# Normalized smooth compact time bump — `8bee3e2c`

This proof step discharges the normalized-bump existence input in the
homogeneous time-distribution kernel program.

For every real interval `a < b`, set `c=(a+b)/2` and `r=(b-a)/4`.
Choose a smooth `ContDiffBump c` with inner radius `r/2` and outer radius `r`.
The normalized bump supplied by pinned mathlib has integral **exactly one**,
compact support `closedBall c r`, and `closedBall c r ⊆ Ioo a b`.
Hence it is a bona fide `TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤`.

The existing conditional span theorem now requires only the following
single scalar analysis obligation:

```
∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
  (∫ t : ℝ, θ t) = 0 →
    ∃ η : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      θ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η
```

A constructive route for this final lemma is to use
`η(t) = ∫ s in a..t, θ s`, then prove global smoothness and support within
an interior compact interval enclosing `tsupport θ`. The zero-integral
hypothesis makes the primitive vanish to the right of `tsupport θ`;
vanishing of `θ` on the left makes it vanish to the left. This is the
actual analytic support lemma, not part of H³ Navier–Stokes assumptions.

Even when the kernel lemma is unconditional, deriving the scalar temporal
distribution identity from the preterminal pointwise PDE remains separate.
