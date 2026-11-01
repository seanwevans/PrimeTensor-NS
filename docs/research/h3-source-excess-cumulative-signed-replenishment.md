# Cofinal physical source-excess windows: finite cumulative H³ drain and signed gap replenishment

Base `babf08ae` (`TerminalActualSourceExcessEndpointDrainReplenishment`).

## Exact time-discrete energy bookkeeping

On the actual cofinal, pairwise separated quintic source windows,

    start_k = t(vk),  end_k = t(vk) + delta_k,
    H_k = M(vk) + q(vk)/[3(3+C_L)].

The accepted endpoint theorem supplies a genuine exhaustive alternative for
E=velocityH3EnergyAt: either on that same window there exists r with

    H_k < K sqrt(E(r)) E(r),

or it incurs an actual endpoint drain

    E(end_k) + H_k delta_k <= E(start_k).

This patch sums those endpoint inequalities by an inductive finite accounting
lemma, retaining exactly the signed energy changes between windows.

For each strictly separated gap `(end_k,start_(k+1))`, differentiability of the
physical energy on the strict interval and the *real mean-value theorem* produce
a real physical `gapSample_k` such that

    E(start_(k+1)) - E(end_k)
      = (start_(k+1) - end_k) E'(gapSample_k)
      = (start_(k+1) - end_k)
          * [-Transport(gapSample_k) - 2 D_full(gapSample_k)].

This is an **exact signed secant identity**, not a claim that a transport
integral was evaluated or that its derivative is integrable at the terminal
time. The full physical Navier--Stokes H³ energy identity supplies the second
equality, with both copies of dissipation retained.

## Finite cumulative alternative

For every m>=0, *on the same physical cofinal witness windows*, either some
k<=m has an actual large-Riccati-energy observation, or

    sum_(k<=m) H_k delta_k + 1
      <= E(start_0) + sum_(k<m)
         (start_(k+1)-end_k)
          * max(0,-Transport(gapSample_k)-2D_full(gapSample_k)).

The lower `+1` uses the already proved `E(s)>=1`. Each gap factor is positive
by exact pairwise separation. No separate terminal-uniform transport cost,
H³ energy bound, or integrability premise is inserted.

The scalar `h3Critical_scalar_cumulativeOverdraft_forces_positiveGapRate`
makes the next quantitative inference precise: if the sum of certified
window charges plus one exceeds the initial energy and the Riccati branch
has not occurred, then some gap sample has

    -Transport(gapSample_k) - 2 D_full(gapSample_k) > 0.

This is a necessary strict *transport overshoot* at a genuine time. The
inequality does not yet constrain the magnitude or total integral of positive
transport near T, and therefore does not establish global regularity.

## Lean declarations

- `h3Critical_scalar_finiteDrainOrReplenishmentAccounting`
- `h3Critical_scalar_gapEnergy_exactMeanValueSecant`
- `h3Critical_physicalH3Gap_exactSignedTransportSecant`
- `h3Critical_scalar_cumulativeOverdraft_forces_positiveGapRate`
- `h3Critical_noL2Trace_cofinalQuintic_cumulativeSignedReplenishment`

Static checks are not Lean elaboration. Run the full pinned Lean/mathlib
build and axiom-audit baseline before accepting the checkpoint.

## Lean arithmetic corrections (fix1 on base `babf08ae`)

The scalar finite-sum induction normalizes `Finset.sum_range_succ` both in
the prior-step hypothesis and in the successor goal before `linarith`. The
previous hypothesis retained an unexpanded `sum_range (m+1)`, which `linarith`
regarded as a separate atom. The final energy-floor transfer now uses
`add_le_add_right` to place the same cumulative sum to the left of
`1 ≤ y m`, and composes it with the actual finite accounting inequality.
No theorem signatures or analytical assumptions are altered.
