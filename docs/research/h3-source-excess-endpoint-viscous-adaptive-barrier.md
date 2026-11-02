# Adaptive inverse-height H³ endpoint persistence obstruction

**Base**: `fcf0cb9e` (`bound critical H3 endpoint windows by residual dissipation budget`).

The new scalar lemma uses exactly the finite partial-sum budget inherited
from physical H³ dissipation. Let `H(k) > 0`, let `η(k)` be the length of
the selected internal endpoint window, and define the actual charged floor
`charge(k) = η(k) * H(k)`, where

    H(k) = R(k)^2 * ε(k)^2 / 8.

For a candidate adaptive critical-width scale `γ(k)/H(k)`, suppose the
required costs `γ(k)` have unbounded **finite sums on every tail**:

    ∀ n C, ∃ m, C < Σ_{j<m} γ(n+j).

Then bounded physical endpoint charges force

    ∀ n, ∃ k ≥ n, η(k) < γ(k)/H(k).

Equivalently, it is impossible that all sufficiently late selected endpoint
windows have length at least `γ(k)/H(k)`. Unlike the previous constant-γ
finite-window count, this permits thresholds `γ(k)` tending to zero but
having divergent cumulative cost. The proof preserves the full already
spent prefix, and does not need an extra positivity assumption on `η` or
`γ` beyond the positive physical heights and unbounded-tail hypothesis.

The cofinal theorem invokes the existing residual-budget theorem, preserving
its original witnesses, attained physical source and spectral maxima, and
the four-way physical PDE-clock/endpoint dissipation alternatives.

**Limits**: The unbounded-tail hypothesis is explicit and is not established
for a particular physical lower persistence scale. No claim of a uniform
positive width, exclusion of the alternate branches, or H³ continuation.

## New Lean declarations

- `h3Critical_scalar_boundedCharge_adaptiveShortfallEveryTail`
- `h3Critical_scalar_boundedCharge_noEventualAdaptivePersistence`
- `h3Critical_noL2Trace_cofinalFivefold_adaptiveEndpointPersistenceBarrier`

Run the audit registrar, `proof/generate_index.py` and `--check`, the
selected Lean module, full project build, and baseline audit.
