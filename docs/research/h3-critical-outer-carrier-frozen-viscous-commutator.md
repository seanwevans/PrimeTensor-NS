# Selected outer H3: frozen diffusion and exact temporal commutator

**Base:** `ad9310970` — exact two-step selected outer viscous/Leray transfer.

## New exact decomposition

For `x ≤ s` strictly inside `(0,T)`, let `P_ρ` be the repository's
**actual physical sharp highpass projection**, and set

- `H = P_ρ u(x)`,
- `D = P_ρ Δu(x)` (the actual frozen-time physical Laplacian),
- `A = P_ρ ∫_x^s Δu(t) dt` (time-dependent viscous increment),
- `B = P_ρ ∫_x^s 𝓝(u(t)) dt` (the actual nonlinear Leray increment),
- `C = A - (s-x) D` (the **exact** viscous temporal commutator).

The existing physical Hilbert Bochner FTC proves `P_ρu(s)=H+A-B`.
Two Hilbert polarizations then give

```
||H||² - ||P_ρu(s)||²
= 2(s-x) d(x,ρ) - 2〈H,C〉 - ||A||²
  + 2〈H+A,B〉 - ||B||²,

 d(x,ρ) := -〈P_ρu(x), P_ρΔu(x)〉.
```

Neither `A` nor `H+A` is identified with the heat-semigroup increment.
The actual time-dependent Laplacian remains in `A`; its temporal mismatch
is **retained**, not assumed small.

## Quantitative PDE gate

Suppose `K>0` and `ε<K(M(x)-M(s))`. Then

```
ε - K [2(s-x)d(x,ρ)+2||H||||C||] + K||B||²
  < 2K〈H+A,B〉.
```

Consequently at least one must hold:

1. `ε/2 < 2K(s-x)d(x,ρ)` (frozen diffusion work);
2. `ε/2 < 2K||H||||C||` (temporal Laplacian mismatch);
3. `0 < 〈H+A,B〉` (positively aligned nonlinear Leray transfer).

The quadratic corrections `-||A||²` and `-||B||²` have favorable signs.
These results do **not** assert that `d≥0`, nor do they assume such a sign;
identifying `d` as the sharp highpass Fourier gradient dissipation is a
separate Plancherel/spectral calculation. The source budget needs to be
coupled to the actual annular signed deficit in a subsequent theorem.

## Next hard mathematics

Prove the native spectral identity for frozen highpass Laplacian pairing
and a **uniform-in-cutoff** physical time-oscillation bound on `C`.
The unweighted Bochner source tail tends to zero but gives no automatic
control of its coupling to an escaping outer carrier frequency. That is
still the principal continuation obstruction.

## Lean audit

The module imports the already-established physical two-step momentum FTC,
introduces five explicit physical definitions and proves eleven statements
without `sorry`, `admit`, or new axioms. Compile with the project-pinned
Lean/mathlib toolchain to verify the declarations and the audit registry.
