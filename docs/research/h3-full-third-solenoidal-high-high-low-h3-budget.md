# Integrate the middle-frequency cancellation on a high-high-low sector

Base: `fda987b5f` — the exact complex solenoidal sixth-power flux has its
middle frequency `q` present in each channel of the genuine triad `p+q+r=0`.

## The nontrivial derivative allocation

The previous result is algebraic, not yet a Fourier estimate. On the
high-high-low cone

    |q| <= min(|p|, |r|),     p+q+r=0,

momentum implies `|p| <= 2|r|` and `|r| <= 2|p|` (including the zero case).
Thus the maximum squared radius `S=max(|p|²,|q|²,|r|²)` satisfies

    S <= 2 |p||r|,
    (|p|+|r|)|r| <= 3 |p||r|.

For the actual six-power flux, the first complex cubic radius gap is bounded
by `3S²(|p|+|r|)|q|`, and the other two are bounded by `S³`. Incompressibility
transfers the final mixed contraction from `r·A` to `-q·A`. Fourier polarization
Cauchy-Schwarz therefore gives

    |F₆(p,q,r;A,B,C)|
      <= [3S²(|p|+|r|)|r| + 2S³] |q| |A||B||C|
      <= 52 |p|³|r|³|q| |A||B||C|.

No division by frequencies occurs, and Fourier phases remain complex/bilinear.

## Actual six-dimensional integration

Let `f` be a complex solenoidal Schwartz velocity, and let `a_f(ξ)` denote
the Euclidean norm of its three genuine Fourier component amplitudes. For
ANY measurable set `s` of momentum pairs `(p,r)` contained in the high-high-low
cone above, the genuine complex flux obeys

    ‖∫_s F₆(f;p,-p-r,r) dp dr‖
      <= 72 (∫ |ξ|⁶ a_f(ξ)² dξ) (∫ |ξ| a_f(ξ) dξ).

For the proof, apply the *existing* measure-preserving triad estimate
`h3Triad_integral_norm_le_L2_L1` to the indicator of `s` times the flux,
with the frequency functions

    F(ξ) = 6 |ξ|³ a_f(ξ),
    H(ξ) = |ξ| a_f(ξ).

The factor `2 F(p) F(r) H(q)` is `72` times the separated product, so it
absorbs the sharp `52`-coefficient. The old Schwartz-moment integrability
theorems supply `∫F²` and `∫H`; no separate high-frequency cutoff, sector
volume estimate, Fourier L∞ hypothesis, or new analytic axiom is inserted.

## What this closes and what it does not

This proves an actual *integrated* high-high-low channel estimate from a
three-derivative L² moment at EACH outer input and the original first L¹
moment at the middle input. It is stronger than the preceding pointwise
factorization and distinct from the radial common-annulus estimate.

The result does **not** control the complementary comparable-frequency or
high-middle channels. It does not assign a favorable sign to the transport,
nor does it assert uniform H³ bounds as physical time approaches an endpoint.

## Build and audit

The archive includes an idempotent registrar for `PrimeTensor.lean` and
`tools/audit/FirstMonomialTriad.lean`, with `#check` and `#print axioms` for
each new theorem. Run `proof/generate_index.py` before `--check`, followed by
fragment checks, targeted Lean, module build, audit entrypoint, full build,
baseline audit, and only then commit/push. The artifact creation environment
has no Lean or lake, so this module is **not locally build-verified**.

## Lean elaboration correction on base `fda987b5f`

The first local build exposed eight elaboration failures, not a failure of the
high-high-low inequality.  For the three complex product bounds, `mul_le_mul`
requires the real upper bound on the first factor to be nonnegative; each is
now proved explicitly using the Euclidean Fourier-polarization and frequency
norms.  The outer-frequency product comparisons similarly use
`0 <= P`, `0 <= R`, and `0 <= (P+R)*R` rather than asking positivity to unfold
the named norms.  Multiplication of the final coefficient inequality by
`Q*(a*b*c)` is expressed with an explicit ring reassociation.  The sector
indicator outside the set uses `Set.indicator_of_notMem`, the lemma name in
the pinned mathlib.  No mathematical constants or theorem statements change.

The corrected source has not been Lean-compiled in this environment; run the
target build before committing.
