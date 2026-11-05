# The exact middle-frequency gain in the physical H³ solenoidal flux

Baseline: `3ecb05465` (physical off-shell transport persists after bounded thin-shell deletion).

## Why the radial-spread envelope is insufficient

The old bound `|F₆| ≤ 3 S² Δ B`, with `S=max(P,Q,R)` and
`Δ=max(P,Q,R)-min(P,Q,R)`, loses the cancellation as the middle
frequency `q` tends to zero while `p` and `r` are large and opposite.
Then `Δ ≈ S`, so the bound alone has no small-middle-frequency gain.
This does not mean the actual complex flux lacks one: the pointwise symbol
contains a stronger cancellation once momentum and incompressibility are used
*before* taking absolute values.

## New exact factorization

Put `p+q+r=0`, `P=|p|²`, `Q=|q|²`, `R=|r|²`, and use the **bilinear**
complex contraction `X=A·C`, not a Hermitian product. With `p·A=0`,

    R-P = Q + 2 p·q,
    r·A = -q·A,
    R³-P³ = (Q+2 p·q)(R²+RP+P²).

Consequently the actual complex sixth-power transfer is

    F₆ = (A·C)(r·B)(Q+2 p·q)(R²+RP+P²)
       + (A·B)(q·C)(Q³-P³)
       - (B·C)(q·A)(R³-Q³).

Each of the three terms contains the middle frequency **q**: the first
through a squared-radius difference; the second and third through complex
polarization contractions. This holds at zero frequency without a division.
It shows, in particular, that `q=0` forces the full symbol to vanish under
momentum and the `p·A=0` solenoidal condition.

The prior `shell_gap_le_frequencyNorm` lemma supplies

    |R-P| ≤ (|p|+|r|)|q|.

Together with the previously formalized cubic-gap Lipschitz lemma, this gives

    |R³-P³| ≤ 3 S² (|p|+|r|)|q|.

This is a different gain from bounded common-shell width. It is designed for
**high-high-low** triads, where `q` is small while `p` and `r` are comparable.

## Relation to the physical recovery

`thirdFullSchwartzSixthPowerFlux_middleFrequencyFactorization244` uses the
actual Fourier polarization of each solenoidal Schwartz field, with
`q = -(p+r)` on the true six-dimensional integration carrier. Hence the
factorization applies at *every index* of the physical recovery from
`3ecb05465`, without introducing a second approximation family or replacing
complex Fourier vectors with real ones.

## What remains mathematically open

The next step is a localized **integrated** high-high-low estimate, distributing
six derivatives over the two high-frequency H³ factors and the explicit
remaining `|q|` over the low-frequency first-moment L¹ factor. This requires
an exact partition of the high-high-low triads and controlled polynomial
weights; the present module does **not** assert that global estimate, an
off-shell sign bound, endpoint-uniform H³ control, or a continuation theorem.

## Verification status

The archive is constructed without Lean/mathlib installed in this runtime.
Run the target Lean file, target lake build, registrar audit and full build
against the project's existing lockfile. The runner halts on any failure
before committing or pushing. No `sorry`, `admit`, or extra axiom is used.
