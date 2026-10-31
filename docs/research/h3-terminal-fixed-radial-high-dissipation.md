# Terminal H³ dissipation above every fixed Fourier radius

Base revision: `31522454`.

## Statement

Let `L_ρ(t)` and `H_ρ(t)` be the **actual** low/high radial H³
viscous spectral dissipation, with the exact partition
`D_H³(t) = L_ρ(t) + H_ρ(t)` at positive preterminal times.
The existing kinetic-anchor estimate proves, for any `a < b < t < T`
and fixed `ρ ≥ 0`,

    0 ≤ L_ρ(t) ≤ ρ² K(ρ) E₀(b).

Existing strong positive-time continuity of the weighted spectral velocity
and continuity of bounded radial multipliers imply `ContinuousOn L_ρ (b,T)`.
The uniform kinetic ceiling then gives `L_ρ ∈ L¹(b,T)` unconditionally
within the preterminal path and H³ energy class.

The previously verified no-strong-L²-trace theorem gives `D_H³ ∉ L¹(b,T)`
on every tail. The exact radial partition therefore yields

    ∀ b∈(a,T), ∀ρ≥0, H_ρ ∉ L¹(b,T).

Cofinal spikes of full H³ dissipation, minus the finite low-frequency ceiling,
further yield

    ∀ b∈(a,T), ∀ρ≥0, ∀M∈ℝ, ∃t∈(b,T), H_ρ(t)>M.

These are two nonvacuous, no-positive-terminal-mass **fixed-frequency**
statements for *H³ dissipation*.

## Explicit frontier

The patch does **not** prove integrability of a Fourier low-pass applied to
the actual projected physical momentum source. In particular, the quadratic
Leray transport requires its own low-frequency convolution estimate.
The present result also does not prove a uniform persistence width for spikes
or unconditional smooth Navier–Stokes continuation.

## Verification

Candidate Lean proofs. ZIP packaging, registrar checks and source checks do not
substitute for a `lake build` on the repository's pinned toolchain.
