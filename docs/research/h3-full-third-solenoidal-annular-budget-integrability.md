# Full H³ solenoidal annular budget: automatic six-dimensional L¹

Baseline: `8c7cf87e12559a78b0335530e92eaf8f0006eaa7`.

## Exact remaining local hypothesis

The committed annular Fourier inequality had a premise
`IntegrableOn (thirdFullSchwartzSixthFluxBudget244 v) s`.
That was left deliberately explicit after proving the sharp pointwise
squared-radius shell gain and the exact solenoidal pure sixth-power flux.

This increment **proves the exact unsigned contraction budget is integrable
on the full R³ × R³ Fourier carrier for every complex Schwartz velocity**.
The three contributions are, at p + q + r = 0:

- `(A(p) · A(r)) (r · A(q))`
- `(A(p) · A(q)) (q · A(r))`
- `(A(q) · A(r)) (r · A(p))`

They are complex-bilinear, not Hermitian contractions. Each finite coordinate
expansion is a true Schwartz Fourier triple; the one linear frequency
coordinate is absorbed by `h3Schwartz_frequencyWeight` on an existing
factor *at exactly that frequency*. `h3Schwartz_triad_integrable` provides
absolute L¹ and `integrable_finsetSum` completes the three contractions.
No `L∞` endpoint assumption, division by radius, or non-Schwartz Fourier
triple is used.

Write `B(v)` for the integral of this exact unsigned budget, finite and
nonnegative for each Schwartz v. The established annular gain now gives

    norm (∫_S F₆(v)) ≤ 3 hi² (hi-lo) B(v)

for every measurable sector S whose three squared radii lie in [lo,hi],
with no separately supplied budget-integrability premise. The precise
complementary excess theorem follows from the existing exact partition:

    3 hi² (hi-lo) B(v) + M < norm (∫ F₆(v))
        => M < norm (∫_(Sᶜ) F₆(v)).

If a *fixed* solenoidal Schwartz field has annuli with uniformly bounded
upper radius and widths tending to zero, their integrated sixth-power flux
tends to zero. This conclusion is for one fixed field and follows from the
finite budget; it is not a new sign result.

## The genuinely open PDE-level issue

When a physical H³ snapshot is realized by a sequence Ψₙ of real solenoidal
Schwartz fields, the individual B(Ψₙ) are each finite. Their **uniform**
boundedness, or a controlled growth rate against the shrinking shell width,
has NOT been deduced from only the old physical E₂, E₃ and viscous energy.
Nor has the off-shell flux been bounded or assigned a favorable sign.
Those are the remaining quantitative questions before any continuation
conclusion can follow.

## Verification

Apply `tools/audit/register_h3_full_third_solenoidal_annular_budget_integrability.py`,
regenerate the proof index, compile the specific Lean module, run fragment
checks, then perform the full Lake build. There are no `sorry`, `admit`,
or new axioms. Static registration is NOT a replacement for Lean checking.
