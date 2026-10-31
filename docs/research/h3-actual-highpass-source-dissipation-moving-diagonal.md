# Actual high-pass source and H³ dissipation: a common moving-cutoff diagonal

Base: `4e3aff4e` — synchronize actual highpass source mass and H3 dissipation escape.

## Mathematical result

The previous same-time theorem, with one fixed projected-source component `i`, has the quantifier order `∀ρ≥0 ∀σ≥0 ∀c∈(b,T) ∀K M ∃t∈(c,T)` with **both** spectral source square mass and high-H³ dissipation above the requested thresholds at that same `t`.

Here we select arbitrary sequences `c(n)∈(b,T)` tending to `T`, `ρ(n),σ(n)≥0`, and real threshold sequences `K(n),M(n)`, before choosing any times. Countable choice supplies one `t(n)∈(c(n),T)` meeting both inequalities. The squeeze theorem proves `t(n)→T`.

At the canonical growing radii `ρ(n)=σ(n)=n+1`, both values exceed `n`, and thus both tend to `+∞` along **one** sequence of actual physical times tending to `T`:

```
∫_{(2π|ξ|<n+1)ᶜ} |R̂_i(t_n,ξ)|² dξ → +∞
D_{>(n+1)}(t_n) → +∞
t_n → T.
```

Crucially, this moving-cutoff assertion is stronger in quantifier structure than fixed-cutoff spike statements. It does not assert a terminal singularity. All three theorems retain the explicit `hNoTrace` premise; none supplies temporal noncompression or controls signed H³ transport.

## Lean declarations

- `h3Critical_noL2Trace_actualHighpassSourceDissipation_movingDiagonal`: independent sequences of radii and thresholds, common physical witness times and convergence.
- `h3Critical_noL2Trace_actualHighpassSourceDissipation_natDiagonal`: explicit radii `n+1` and threshold `n` on a cofinal time sequence.
- `h3Critical_noL2Trace_actualHighpassSourceDissipation_commonDivergence`: joint divergence to `Filter.atTop`.

## Verification

ZIP contents/registrar idempotence can be checked offline. Lean elaboration and all project baselines must run in the repository's pinned toolchain before commit.
