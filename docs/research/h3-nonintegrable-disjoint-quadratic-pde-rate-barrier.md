# Disjoint physical H³ annuli: cumulative charge or exact quadratic PDE clock barriers

Base commit: `91694a7f` (`split disjoint H3 annular charges into divergence or cubic clock collapse`).

## Physical content

Under `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`, and
failure of the actual strong physical L² trace, the previous branch constructs
cofinal, pairwise disjoint, actively dissipative finite Fourier annuli.
The certified height is `A_k = (v(k)+1)^3/2`; their exact persistence widths
are

```
δ_k = min( b_k/2, min(1, min(g_k/[4(Λ_k+1)], sqrt(g_k/[4(Ξ_k+1)]))))
```

where `b_k=(T-t(v(k)))/2`, `g_k` is the actual finite-annular dissipation
above the half-cubic floor at the selected physical snapshot,
`Λ_k` is the actual linear variation coefficient with
`K_k = ‖h3AuditActualSpectralVelocityTotal hH3 (t(v(k)))‖`, and `Ξ_k` is the
actual source-driven quadratic coefficient. The projected source envelope
`C_k` is attained on its original physical half-terminal interval.

Define `q_k = A_k δ_k`. The earlier positive charge alternative, together
with the EXISTING sharp-minimum cap lemma, gives:

- Either `∀M, ∃m, M < ∑_{k<m} q_k`;
- Or for every `ε>0`, eventually at least one of
  `2 A_k * (b_k/2) ≤ ε`,
  `2 A_k * g_k/[4(Λ_k+1)] ≤ ε`, or
  `2 A_k * sqrt(g_k/[4(Ξ_k+1)]) ≤ ε`.

These are statements about genuine PDE-certified disjoint windows, with
no finite full-terminal H³ dissipation hypothesis. The previous comparison
of the cubic charges with the SUM of actual finite-annulus integrals is
preserved exactly. There is no assertion of terminal divergence in either
individual branch; an unbounded positive partial sum is a separate outcome.

## Conditional stronger consequence

If the same chosen windows additionally satisfy `g_k ≥ (v(k)+1)^3/4`
eventually, the sharp-root estimate upgrades the latter two alternatives
to `(v(k)+1)^6 ≤ 16ε(Λ_k+1)` or
`(v(k)+1)^9 ≤ 16ε²(Ξ_k+1)`.

The current disjoint extraction did not explicitly preserve the quarter-gap
certificate from the underlying minimal outer-cutoff constructor. The patch
therefore states this as a separate scalar theorem **with the extra gap
hypothesis**, not as a proven property of the selected physical windows.

## Remaining hard step

Carry the quarter-gap bound from
`h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244` into the
EVERY-TAIL active-window package, then through the diagonal and disjoint
selection. After that, invoke the sixth/ninth barrier with the actual
physical linear and quadratic coefficients. None of the results by themselves
settles global Navier–Stokes continuation.
