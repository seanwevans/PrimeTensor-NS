# Prescribed-gauge frequency escape at the actual physical endpoint

Base commit: `4d7e9f9aa37d536926bc8ac64a33704ae82e79ec`.

## New mathematical consequence

For an **arbitrary prescribed** scalar frequency gauge `H : ℕ → ℝ`
with `H(n) ≥ 1`, consider the positive dissipation height profile

    M_H(n) = H(n)^8.

The existing no-terminal-H³-trace branch selects genuine disjoint
minimal first-crossing annuli at that height, indexed by `v(k)`, with
inner radius `v(k)+1`, outer radius `N(v(k))+2`, and exact positive
physical persistence windows `[τ(v(k)), τ(v(k))+δ(v(k))]`.

The actual physical projected-momentum source `G` is Bochner-L¹ at the
endpoint under finite H³ dissipation. Define its exact terminal physical
state `U = X(b)+∫_b^T G(r)dr`, which satisfies the unconditional physical
Hilbert evolution identity. On every selected persistence window and
for every time `s` inside it, the old pointwise annular H⁴ dissipation
comparison and the terminal Fourier highpass transport imply

    H(v(k))^8 < 48 (N(v(k))+2)^8 [B_H(k)]^2,

where

    B_H(k) = ||P⁺_(v(k)) F(U)|| + ||F|| ∫_(τ(v(k)))^T ||G(r)|| dr,

and `F` is the genuine bounded real-linear physical Fourier map.
Both the fixed-state highpass tail and the source Bochner norm tail vanish,
so `B_H(k) → 0`.

The new scalar comparison shows, for any fixed `D ≥ 0`, that eventually
`D H(v(k)) < N(v(k))+2`. Therefore

    (N(v(k))+2)/H(v(k)) → +∞.

This is a rate-free, quantified necessity. No unproved bound on the
attained source maximum and no substitution of the physical source's peak
for its integrated action is used.

For the illustrative choice `H(n)=(n+1)^p` (`p∈ℕ`), the selected outer
frequency outruns every fixed multiple of that polynomial. **These
sequences depend on p**; there is no single universal cascade that is
proved to outrun all gauges simultaneously.

## What the result does not prove

The result is conditional on the failure of a terminal weighted H³ trace,
and uses the repository's existing arbitrary-height terminal branch. It
proves no uniform upper frequency cutoff, no contradiction, and no Clay
Navier–Stokes regularity theorem. It identifies the precise additional
mechanism to exclude: a terminal source/viscous balance or signed-H³
coercivity estimate that limits the physically accessible outer frequency
for the selected windows.

## Implementation and audit

1. `thirdFull_profile_eighthMoment_transportAmplifier244`: scalar moment bridge.
2. `thirdFull_vanishingTail_eighthMoment_forces_gaugeEscape244`: rate-free scalar gauge-escape lemma.
3. `thirdFullPhysical_profile_window_endpointTailMomentBarrier244`: real-time physical PDE window comparison at arbitrary M.
4. `thirdFullPhysical_noH3Trace_prescribedGauge_endpointTailEscape244`: same-witness arbitrary-gauge carrier escape with disjoint viscous charge.

No new axioms, no placeholders. The source packaging environment has no
Lean/Lake; compilation and global audit must run in the repository toolchain.
