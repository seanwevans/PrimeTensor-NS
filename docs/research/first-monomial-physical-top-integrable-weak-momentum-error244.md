# Integrable-in-time solenoidal weak momentum error

Checkpoint: `66864e94`. Follow-up after quantitative weak residual density.

Let `U(t)` denote the actual physical `L²` velocity and `R(t)` the exact projected source. Their strong continuity on compact strict-time intervals is already established. For compact solenoidal `φ`, suppose

`d/dt <φ,U(t)> = <φ,R(t)> + e_φ(t)` on `(a,b)`

and `|e_φ(t)| ≤ g(t)‖φ‖₂`, with `g` nonnegative continuous on `[a,b]`, and each scalar error continuous there. Scalar FTC yields

`<φ,D(a,r)> = ∫_a^r e_φ(t) dt`.

The interval-integral norm bound yields

`|<φ,D(a,r)>| ≤ (∫_a^r g(t) dt) ‖φ‖₂`.

The already-proved sharp Leray-fixed density theorem upgrades this to

`‖D(a,r)‖₂ ≤ ∫_a^r g(t) dt`.

This is a genuine `L¹_t` error budget; large errors on short sets are admissible. When cumulative error budgets are arbitrarily small, weak FTC follows. The construction of the scalar derivative identities from the old preterminal PDE remains open: separate time/space continuity does not itself justify differentiating the spatially integrated momentum. Pressure is not presumed to have a physical `L²` gradient; solenoidal annihilation should precede any norm estimate.
