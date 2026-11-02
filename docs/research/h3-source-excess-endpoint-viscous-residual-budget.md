# Residual physical H³ budget for terminal endpoint persistence

**Base:** `a8943856` — finite number of critical inverse-height windows.

The previous quantitative count was charged against the total physical
terminal H³ dissipation, even for a block far down the selected cofinal
sequence. The new estimate preserves all earlier paid charges:

For `H(k) = R(k)^2 ε(k)^2 / 8 > 0` and `γ > 0`, every `n, m` satisfies

    γ × #{j < m : η(n+j) ≥ γ/H(n+j)}
      + Σ_{k<n} η(k) H(k) ≤ ∫_a^T velocityH3DissipationAt(u,r) dr.

Thus later expensive windows are charged only to the as-yet-unspent
physical real dissipation budget, without double counting earlier endpoint
windows. In particular this refines the global count (take n = 0), and
quantifies the depletion of the finite physical budget along the exact
selected cofinal witnesses.

The theorem retains the four-way alternative of the same synchronized gate:
non-spectral, finite-band physical PDE clock, anchor-point full H³ spike,
or internal finite-band endpoint persistence. It never merges costs from
potentially overlapping source and internal endpoint intervals.

**Important limitation.** No positive lower persistence width, terminal
uniform continuity, or H³ continuation is asserted. The finite terminal
H³ dissipation remains an additional explicit assumption.

## Registered declarations

- `h3Critical_scalar_finiteBudget_depletedTailCount`
- `h3Critical_scalar_finiteBudget_depletedInverseHeightTailCount`
- `h3Critical_noL2Trace_cofinalFivefold_residualCriticalWindowBudget`

The registrar installs one root import and three check/axiom pairs.
Run `proof/generate_index.py` and `--check`, the new module compilation,
full build, and full baseline audit before commit.
