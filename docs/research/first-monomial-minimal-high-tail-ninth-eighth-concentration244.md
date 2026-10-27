# Minimal first-crossing ninth/eighth concentration retains the physical high tail

Base commit: `974a8f8e` — retain quarter-cubic high-frequency dissipation below minimal cutoff.

## Mathematical issue

The previous package established two conclusions separately:

1. On finite-dissipation, no-terminal-strong-L²-trace quadratic-sharp cofinal witnesses with *minimal first-crossing cutoffs*, bounded source and sixth-order linear PDE rate plus noncompressed cubic terminal lag force the minimal shifted outer cutoff to satisfy `(Q+1)^8 > M R^9`, at every fixed `M ≥ 0` on late witnesses.
2. A *different existential presentation* of cofinal physical high-radial snapshots retained the original strict high-tail cubic bound `highDiss(R,t) > R³` at the exact first-crossing cutoff. Hence any earlier cutoff `m` has `highDiss(m+1,t) > R³/4`.

It was not permissible to conjoin these existential statements directly: they might select different times and different outer annuli. This module reconstructs one physical cofinal sequence using the **enriched** source selector and performs the separated-window extraction and finite-dissipation cost collapse on that same selection.

## Same physical windows

`h3Path_noL2Trace_finiteDissipation_minimalHighTailThreeScale244` copies the disjoint finite-height cost argument with exact quadratic-sharp clocks and retains simultaneously:

- strict cofinal selected times, pairwise separated persistence intervals, summable cubic-weighted width costs;
- the strictly positive quarter-cubic gap;
- minimality of the first annular three-quarter-cubic crossing;
- the strict high-frequency floor `R_k³/4 < highDiss(m+1, τ_k)` for all integer cutoffs `v(k) ≤ m < N(v(k))`;
- the original three-scale (compression, sixth-rate, ninth-rate) alternative.

No independent choice of the cutoff is made after extracting the cofinal subsequence.

## Ninth/eighth range of retained tail

`h3Path_noL2Trace_finiteDissipation_minimalNinthEighthHighTail244` reuses the earlier abstract three-scale-to-eighth-gain and outer-separation results. For any `η > 0`, `B ≥ 0`, `M ≥ 0` and real `S`, every sufficiently late witness satisfying:

```
η ≤ R_k³ * (T - τ_k)/4,
Λ_k + 1 ≤ B R_k⁶,
C_k² ≤ S²
```

obeys both

```
M R_k⁹ < (N(v(k)) + 2)^8,
```

and, **for all integer m with `v(k) ≤ m` and `(m+2)^8 ≤ M R_k⁹`**,

```
R_k³/4 < highDiss(m+1, τ_k).
```

This is a quantified restriction on the actual physical H³ spectrum below the *minimal* first crossing.

## Divergence on moving subcritical cutoffs

The final theorem allows a selected integer cutoff profile `m(k)` which may grow superlinearly with the inner radius. If the above physical regime holds eventually and `(m(k)+2)^8 ≤ M R_k⁹` and `v(k) ≤ m(k)` eventually, then

```
highDiss(m(k)+1, τ(v(k))) → +∞.
```

Strict monotonicity of `v` makes the quarter-cubic floor diverge; no new energy estimate is assumed. This result is conditional on the original no-strong-terminal-L²-trace branch and additional terminal full-H³ dissipation integrability; noncompression and bounded source/linear rate are **not** proved automatically. High H³ dissipation at sparse terminal snapshots does not contradict its time integrability.

## Validation

The ZIP contains one Lean file, one idempotent registration script, and this research note. It has no `.sh` artifact. Run the Lean file, its module build, audit and index checks, then a full project build before committing. The assistant environment lacks the Lean toolchain; the proof has **not** been Lean-compiled here.
