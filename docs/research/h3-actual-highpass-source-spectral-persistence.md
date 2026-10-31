# Actual highpass projected source: spectral-time persistence criterion

Base: `1a23554a` (extended full physical H³ cost and local width compression).

## Hard-math bridge

The already formalized physical projected-source Lipschitz bound on the actual
weighted H³ spectral velocity state is

    ‖R(U)-R(V)‖ ≤ (3+C_L(‖U‖+‖V‖))‖U-V‖.

This module transfers **differences** of the actual highpass Fourier source
through Plancherel and the contractive sharp complementary cutoff. No
frequency-dependent multiplier constant or new Fourier reality assumption is
needed. Consequently the same estimate holds with `R` replaced by its
highpass Fourier coordinate `H_{ρ,i}`.

Assume on an actual physical interval `[t,t+Δ] ⊂ (b,T)` that the H³ spectral
amplitude obeys `‖U(s)‖ ≤ E`, and spectral temporal displacement obeys
`‖U(s)-U(t)‖ ≤ L(s-t)`, for `E,L≥0`. Put

    Q = (3 + 2 C_L E) L,
    B = max(0, (3+C_L)(1+6 E0(b)+3(σ² W₃(σ) E0(b)+M))),
    V = ‖H_{ρ,i}(t)‖.

The exact PDE source-to-dissipation barrier already proved in
`TerminalActualHighpassSourceDrivenWindows` says
`‖H_{ρ,i}(s)‖ > B ⟹ D_{>σ}(s)>M`.
The difference estimate gives `‖H_{ρ,i}(s)‖ ≥ V-Q(s-t)`.
Thus if `V>B`, the **explicit** width

    δ = min(Δ/2, (V-B)/(2(Q+1))) > 0

satisfies `t+δ<T` and `D_{>σ}(s)>M` on *every* point of `[t,t+δ]`.

The critical hypothesis is an actual H³ spectral-time increment bound with
coefficient `L`. Its presence is transparent and **not** deduced from
positive-time continuity alone. In particular, this patch does not infer a
terminal-uniform `E` or `L`, does not derive a lower bound on the widths of
the already selected cofinal source-driven disjoint windows, and does not
establish divergent costs or global Navier–Stokes regularity.

To turn the explicit criterion into an unconditional no-trace obstruction,
quantify `E`, `L`, and the source margin on the **selected moving cutoffs** and
compare their resulting `δ` with the disjoint extended H³ cost budget. The
unresolved estimate is on the *spectral velocity time increment*, not the
already-closed algebra of Fourier cutoff/source differences.

Lean declarations:

- `h3Critical_actualHighpassSource_temporalSub_norm_le_spectral`
- `h3Critical_sourceDriven_spectralClock_persists_highDissipation`
- `h3Critical_positiveHalfMargin_width`
- `h3Critical_sourceDriven_spectralClock_explicitPositiveWindow`

Static package checks are not Lean elaboration. Compile using the pinned
Lean and Mathlib repository toolchain.

## Lean correction after user elaboration (`1a23554a`, fix1)

- In `h3Critical_sourceDriven_spectralClock_explicitPositiveWindow`, the inclusion proof requires `t + δ ≤ t + Δ`. `add_le_add_right hδLe t` has the necessary orientation; `add_le_add_left` instead produced `δ + t ≤ Δ + t`.
- The preliminary `field_simp` already solves the width arithmetic goal, so the unreachable `ring` tactic has been removed.
- This edit follows the supplied Lean diagnostic. It still requires Lean compilation and the full repository baseline on the target environment.
