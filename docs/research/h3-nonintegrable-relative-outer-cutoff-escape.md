# Disjoint H³ annuli: bounded physical source and relative outer radius force terminal compression

Baseline: `de7bc43e` (`charge disjoint H3 sixth and ninth PDE barriers to physical energy source and outer cutoff`).

## Mathematical statement

On the previously constructed no-terminal-physical-L²-trace sequence of pairwise disjoint exact PDE persistence windows, write

- `R_k = v(k)+1`, `Q_k = N(v(k))+1`, `E_k = velocityH3EnergyAt u (t(v(k)))`,
- `C_k = h3PathActualProjectedSourceWindowEnvelope244 ...`, and
- `δ_k` for the exact quadratic-sharp persistence width.

The existing *nonintegrable-branch* result proves that either the sums of certified cubic annular charges `Σ_{k<m} δ_k R_k³/2` are unbounded, or for every `ε>0` and all sufficiently large `k`, one of the following holds:

```
R_k³ (T - t(v(k)))/4 ≤ ε,
R_k¹² ≤ 512 ε² (2304 E_k C_k² (Q_k+1)¹⁰ + 1),
R_k⁹ ≤ 16 ε² (36 C_k² ((Q_k+1)⁸ + (R_k+1)⁸) + 1).
```

**New conditional theorem.** Suppose that, eventually along the *same* disjoint windows, there are fixed finite real constants `B≥0`, `D≥1` such that

```
E_k C_k² ≤ B,
C_k² ≤ B,
Q_k + 1 ≤ D R_k.
```

Then the linear and quadratic PDE-rate arms cannot persist at arbitrarily large inner frequency, since the coefficient burdens are bounded by

```
E_k C_k² (Q_k+1)¹⁰ ≤ B D¹⁰ R_k¹⁰,
C_k² ((Q_k+1)⁸+(R_k+1)⁸) ≤ B(D⁸+256) R_k⁸.
```

Therefore **either** the cumulative certified charges are unbounded, **or** for every `ε>0` the *geometric* terminal width satisfies

```
R_k³ (T - t(v(k)))/4 ≤ ε
```

for all sufficiently late `k`. The proof is root-free and preserves the exact PDE widths; no finite terminal full-H³ dissipation budget is assumed.

## Explicit scalar frequency thresholds

If the two normalized coefficient burdens are bounded by `B₁ R¹⁰` and `B₂ R⁸`, respectively, then the corresponding PDE-rate arms force

```
R² ≤ 512 ε² (2304 B₁ + 1),
R  ≤ 16 ε² (36 B₂ + 1).
```

Along a strictly increasing inner cutoff, `R_k→∞`, so each bound is eventually false. This identifies *relative* outer-radius escape or physical energy/source amplification as necessary to sustain rate concentration without geometric compression.

## Scope and remaining obstruction

The eventual boundedness of `E_k C_k²`, `C_k²`, and `(Q_k+1)/R_k` is **not** proved by the no-trace premises. This patch provides a genuine necessary condition and separates source amplification, relative outer-frequency escape, geometric terminal compression, and unbounded certified costs. It does not establish Navier–Stokes continuation or select a surviving branch. The prior full physical annular integral-cost comparison remains available via `h3Critical_noL2Trace_disjointQuarterCubicAnnuli_energySourceOuterBarrier`.

## New declarations

- `h3Critical_scalar_relativeOuterCap_bounds_linearAndQuadraticBurdens`
- `h3Critical_scalar_normalizedPhysicalRates_force_boundedInnerRadius`
- `h3Critical_scalar_strictMono_innerRadius_eventually_exceeds`
- `h3Critical_noL2Trace_disjointActiveAnnuli_boundedSourceRelativeOuter_forces_compression`
