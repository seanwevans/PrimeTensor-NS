# Integrated signed transport replenishment on cofinal source-excess gaps

Base: `4bf1d4b3` (accepted finite cumulative sampled signed-gap budget).

The previous cofinal theorem uses real mean-value samples in gaps
between source-driven physical H³ dissipation windows. The exact signed
Navier–Stokes H³ energy identity gives on every strict physical slice

    E'(s) = -Transport_H3(s) - 2 D_full(s).

Let `a_k=t(v_k)`, `e_k=a_k+δ_k` be its unchanged separated windows and
`H_k=M(v_k)+q(v_k)/[3(3+C_L)]` the previously proved enhanced dissipation
floor. The accepted endpoint theorem gives, for each k,

    (exists s∈[a_k,e_k], H_k < K sqrt(E(s)) E(s))
    OR E(e_k)+H_k δ_k ≤ E(a_k).

## Full integrated positive signed transport budget

For each strict compact gap `[e_k,a_(k+1)]`, assume ONLY the two explicit
local interval-integrability statements

    IntervalIntegrable (deriv E) volume e_k a_(k+1),
    IntervalIntegrable (fun s => max 0(-Transport_H3(s)-2D_full(s)))
      volume e_k a_(k+1).

The scalar fundamental theorem of calculus and integral monotonicity give

    E(a_(k+1))-E(e_k)
      ≤ ∫_(e_k)^(a_(k+1)) max(0,-Transport_H3(s)-2D_full(s)) ds.

This integrates the ACTUAL nonlinear signed transport deficit after retaining
both viscous copies. It is stronger structurally than paying the gap gain
with the single mean-value sample `width_k * max(0,rate(sample_k))` because
it measures the whole positive overshoot of the original PDE rate.

The finite telescoping energy accounting now gives, for all m≥0,

    (exists k≤m, an actual large Riccati H³ energy observation on window k)
    OR
    ∑_(k≤m) H_k δ_k + 1
      ≤ E(a_0) + ∑_(k<m) ∫_(e_k)^(a_(k+1))
          max(0,-Transport_H3(s)-2D_full(s)) ds.

The `+1` is the physical lower energy normalization `E>=1` and the sum is
over the original separated windows; neither branch is discarded.

## Scope and remaining gap

The integrability hypotheses are per compact gap and nested *inside* the
existentially selected cofinal witnesses. Nothing requires integrability
on the terminal half-open interval or a bounded global transport budget.
A subsequent proof must discharge local gap integrability from the path
regularity or bound its positive signed transport integral to obstruct
cumulative replenishment. In particular this theorem does NOT prove
terminal regularity or any unconditional global NS result.

Four Lean theorem candidates:

- `h3Critical_scalar_gapIntegratedMajorant_pays_energyGain`
- `h3Critical_physicalGap_integratedSignedTransport_pays_energyGain`
- `h3Critical_scalar_finiteIntegratedGapDrainOrEnergy`
- `h3Critical_noL2Trace_cofinalQuintic_integratedSignedGapBudget`

Compile with pinned repository Lean/mathlib; static packaging is not
Lean elaboration.

## Lean lexer correction (fix1 on base `4bf1d4b3`)

The module header accidentally ended its doc comment with `-/'` rather than `-/`.
The stray apostrophe was lexed as the start of an unterminated character
literal and reported at the subsequent `namespace` line. Fix1 removes the
extra apostrophe; no mathematical statement or proof body is changed.
