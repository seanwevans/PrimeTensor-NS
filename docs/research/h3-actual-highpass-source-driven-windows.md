# Source-driven actual highpass/H³ windows without full-dissipation continuity

Base: `b0d6f4d4` — extend common source and H³ windows to arbitrary moving profiles.

## New mathematical point

The committed kinetic-anchored estimate holds *pointwise* at every strict physical time, for independent highpass source radius `ρ` and high-H³ dissipation radius `σ`:

```
‖R̂_i,>ρ(t)‖₂ ≤ A (1 + 6 E₀(b) + 3 (σ² W₃(σ) E₀(b) + D_>σ(t)))
A = 3 + C_Leray ≥ 0.
```

Let `B(E,σ,M)` be the nonnegative part of the right-hand side when `D_>σ = M`. Then `‖R̂_i,>ρ(t)‖₂² > B²` forces `D_>σ(t) > M`. This is a genuine PDE-source-to-dissipation implication and requires **no time-continuity of full physical H³ dissipation**.

The previously proved highpass Fourier source-mass escape provides one fixed coordinate `i` and cofinal times with square mass above `max(K(n), B(E₀(b),σ(n),M(n))²)`. Actual projected-source continuity yields a positive right-hand interval where the source mass stays above that *larger* threshold. Consequently, both requested inequalities hold **at every point of the same window** for independently prescribed moving radii `ρ(n),σ(n)` and heights `K(n),M(n)`.

The source-mass integral on the interval exceeds its lower cost `δ(n) K(n)`. For the high-H³ interval-integral cost `δ(n) M(n)`, the theorem supplies an implication whose only premise is interval integrability of that specific high-H³ function on that specific compact interval. No unproved full-dissipation continuity or local time integrability is inserted.

Finally, the previously committed separation lemma yields a strictly increasing cofinal subsequence of **pairwise separated** common source-driven windows. Source costs sum without further hypotheses; high-H³ costs sum if the selected compact-window integrability premises hold.

No lower bound on widths, divergent terminal cost, source derivative estimate, or counterexample to terminal trace existence is proved. In particular, do not confuse a pointwise lower bound with the measurability/integrability required to make its Lebesgue interval integral a genuine quantitative cost.

## Declarations

- `h3CriticalSourceDrivenHighDissipationBarrier`
- `h3Critical_sourceMass_above_barrier_forces_highDissipation`
- `h3Critical_noL2Trace_sourceDriven_profileWindows`
- `h3Critical_noL2Trace_sourceDriven_profileDisjointWindows`

Compile against the pinned Lean/mathlib toolchain. Static package and registrar checks do not replace elaboration or the full project baseline.
