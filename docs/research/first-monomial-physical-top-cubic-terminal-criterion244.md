# Actual physical cubic clock: terminal dissipation criterion

Baseline: `f43555c6` — automatic signed-log interval integrability, exact joint fifth/phase action, integrated cubic clock.

## Exact PDE origin

For the physical preterminal H³ state, define

- `D₃(r)` = fourth-radial top dissipation mass of the actual velocity;
- `M₃(r)` = third-radial squared Leray forcing mass;
- `M₅(r)` = fifth-radial squared velocity mass;
- `P(r)` = signed Fourier phase/mismatch defect.

The *actual* Fourier identity is `D₃' + M₅ + P = M₃`, with `M₅,P ≥ 0`.
The predecessor proves automatic compact-time integrability of
`C₃ := M₃/D₃` and of `(log D₃)'` whenever `D₃>0`, yielding

```
log D₃(t) - log D₃(s) ≤ ∫ₛᵗ C₃(r) dr.
```

Exponentiating this bound (using physical positivity of `D₃`) gives

```
D₃(t) ≤ D₃(s) exp(∫ₛᵗ C₃(r) dr).
```

Thus bounded cumulative **genuine physical cubic** action on a strict
terminal subtail gives a uniform fourth-radial dissipation bound. This is a
conditional bound, not a claim of terminal integrability of cubic forcing.

## Sharp necessary escape alternatives

If `D₃` exceeds every finite ceiling on the strict tail `(s,T)`, then:

1. `∫ₛᵗ C₃` exceeds every finite ceiling for suitable `t→T`;
2. for every `K`, an actual later time `r∈(s,T)` has `C₃(r)>K`.

The second conclusion is stronger than simply saying an integrated action
diverges: it identifies arbitrarily high *instantaneous physical normalized
forcing ratios*. Proof uses the one-sided **pointwise** PDE derivative
ceiling and the finite remaining terminal time horizon. If `C₃≤max(K,0)`
throughout the tail, the top mass is bounded by
`D₃(s)*exp(max(K,0)*(T-s))`, contradicting physical mass escape.

## Near-Young bridge

The patch also specializes the existing near-Young necessary fifth-plus-phase
expenditure theorem, discharging its signed-log `IntervalIntegrable`
assumption via the previous automatic compact-time physical PDE result.
The variance, middle-coupling, kinetic and variation integrability premises
are retained as explicit hypotheses rather than silently assumed.

## Open terminal frontier

Nothing here bounds `C₃`, proves finite terminal action, or turns the
conditional dissipation criterion into unconditional Navier–Stokes
regularity. A substantive continuation result still needs a terminal forcing
rate bound from the nonlinear geometry or higher radial/kinetic hierarchy.
