# Canonical source maxima: a budget-determined amplitude-loss clock

Base: `93865f94` (six cubic-width-collapse theorems; source-maximizer witnesses retained).

## The avoidable-width issue

The prior selected `d_k` is an **arbitrary sufficiently small** persistence duration. It may be shortened without changing the proof, so an upper bound `d_k^3 A_k^8 → 0` by itself cannot constrain a *maximal* physical persistence width. To gain a substantive clock, test a fixed deterministic horizon, not a chosen continuity neighborhood.

## Physical optimized floor at any time above half the original peak

Fix a kinetic anchor `a < b < s < T`, `A = ‖U₃(s)‖`, and `E = E₀(b) ≥ 0`. For `A ≥ 2` and `A² ≥ 32(E+1)`, choose the exact sixth-root Fourier radius `ρ ≥ 1` satisfying `32(E+1)ρ⁶ = A²` and define `H = (ρ²/8)A² > 0`. The previous Fourier mass-dissipation coercivity applies at EVERY later `r ∈ (b,T)` satisfying `A/2 ≤ ‖U₃(r)‖`. Hence:

    A^8 = 16384(E+1)H^3
    A/2 ≤ ‖U₃(r)‖  =>  H ≤ D₃(r).

This implication uses no high-frequency H³ time derivative and no extra time continuity hypothesis. Crucially, it applies to the same fixed chosen `ρ` throughout any interval where the spectral norm has not halved.

## Budget-time dichotomy

Let `B = ∫_a^T D₃(t)dt ≥ 0` (assumed finite and integrable) and set `L=(B+1)/H>0`. Either

    T-s ≤ L,

or there is a real physical time `r ∈ [s,s+L]` such that

    ‖U₃(r)‖ < A/2.

Proof: if `s+L<T` and the norm never halves on `[s,s+L]`, then the physical dissipation integral over this subinterval is at least `L H = B+1`. Nonnegativity of actual physical dissipation implies this subinterval integral is at most `B`, a contradiction. The first branch implies the explicit polynomial clock

    (T-s)^3 A^8 ≤ 16384(E+1)(B+1)^3.

This is a **necessary alternative**, not a lower persistence bound, and no contradiction follows without excluding either terminal compression or rapid high-frequency spectral-norm loss. An improvement to the shorter tail budget `∫_s^T D₃` would strengthen it but requires a separate endpoint-tail integral lemma.

## Canonical witnesses

`h3Path_noL2Trace_canonicalWidth_sourcePeakForcedHalfAmplitude244` retains exactly the disjoint quadratic-sharp original clocks, canonical physical projected-source maximizers `s_k`, and three conditional critical-width constraints. For every fixed kinetic anchor `b∈(a,T)`, it derives the amplitude-loss/terminal-clock alternative for all sufficiently late `s_k`, with no additional subsequence and no arbitrary persistence-width selection.

The theorem uses only prior committed H³ Fourier coercivity, physical kinetic monotonicity, nonnegative interval-integrated dissipation and the existing canonical joint escape witness. It does not assert unconditional 3D Navier–Stokes smoothness.

Status: source and registration checks only in the artifact environment; Lean compilation must be performed in the user's repository.
