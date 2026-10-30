# All-orders canonical higher-budget pointwise signed H³ transport overshoot

Base commit: `1fc6dd31` — transfer all-orders critical spectral escape to signed H3 growth obstruction.

The already-committed spectral-energy gate supplies cofinal times `t_k → T` and physical H³ energy `E₃(t_k) → +∞`, conditional on an interval-integrable real envelope for the physical `q^(4+m)` radial top moment, bounded attained physical projected source, critical eighth-power outer cutoff cap, noncompressed terminal lag and a sufficiently small positive tolerance.

The new argument uses no integral of the transport rate. By the closed H³ derivative identities, `E₃` is differentiable at every strict energy-class time. If `E₃' ≤ 0` throughout any terminal subinterval `(b,T)`, the calculus antitone theorem gives `E₃(t_k) ≤ E₃((b+T)/2)` for all sufficiently late `k`, contradicting the actual cofinal energy escape. Thus every `(b,T)` contains a genuine physical time `s` with `E₃'(s)>0`.

The exact Navier–Stokes signed H³ identity `E₃' + 2D₃ = -Transport₃` then yields

    2 D₃(s) < -Transport₃(s).

Since the canonical physical energy is at least one, the *exact* positive full-dissipation normalized transport excess is strictly positive at that `s`:

    max(0, (-Transport₃(s) - 2D₃(s))/E₃(s)) > 0.

The same original first-crossing `τ,N,K,C,δ,v` witnesses are used. The existential `s` is only guaranteed inside **every terminal subinterval** `(b,T)` and is not asserted to be an original canonical anchor or within a particular disjoint annulus window. No theorem infers the upstream higher-moment/source/cutoff/noncompression conditions from finite H³ dissipation. The signed nonintegrability result from the parent is stronger in integrated terms; this theorem supplies a separate, explicit pointwise PDE orientation.

The four new Lean theorems are:

- `h3Path_scalar_cofinalEscape_forces_positiveDerivativeEveryTail244`
- `h3Path_cofinalPhysicalEnergyEscape_forces_pointwiseSignedTransport244`
- `h3Path_signedTransportOvershoot_forces_positiveFullExcess244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_pointwiseSignedTransport244`

Compiled Lean/Mathlib proof verification is not available in this packaging container. Run the exact Lake build and audit commands locally before committing.

## Lean correction (fix1)
The midpoint interval proof avoids `dsimp` after its local definition has been reduced, and the late index is placed in `(b,T)` by transitivity `b < s0 < t(k)`. No theorem or assumptions changed.
