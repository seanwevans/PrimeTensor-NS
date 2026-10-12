# Initial physical mismatch and a single defect-direction weak witness

Checkpoint: `b1c0e83a` — restore H3 audit and derive anchored momentum from weak sequences.

## Mathematical advance

The subcritical physical projected-source estimates, together with the
independent old temporal joint-continuity condition, produce a strong right
physical L² limit `L` and a quantitative modulus

    δ(t) = ((3 + C_L) * M) * t^(1-α) / (1-α),  0 ≤ α < 1.

These facts imply, for the *actual* time-zero physical initial state `U₀`:

    |‖F(t)-U₀‖ - ‖L-U₀‖| ≤ δ(t),
    ‖F(t)-U₀‖ ≥ ‖L-U₀‖ - δ(t).

Without a separately proved initial-value compatibility condition, the
quantity `‖L-U₀‖` can be nonzero. The theorem makes this boundary jump
visible instead of silently identifying `L` with the initial datum.

The new uniqueness lemma needs only ONE scalar weak trace along ONE
right-zero sequence, tested in the Hilbert direction `L-U₀`:

    <F(τ_n), L-U₀> → <U₀,L-U₀>.

As `F(τ_n) → L` strongly from the established right-limit theorem, pairing
limits force `<L-U₀,L-U₀> = 0`, hence `L=U₀`. In particular an entire
Schwartz-test family of initial weak sequences is not necessary if this
single adaptive-defect pairing is available. The result supplies the
previous established explicit physical momentum and kinetic rates at the
actual initial datum.

## New declarations

- `h3Audit_initialPhysicalMismatch_normModulus_and_lower`
- `h3Audit_initialSubcriticalEnergyRate_physicalMismatchModulus`
- `h3Audit_initialStrongPhysicalLimit_eq_of_defectDirectionSequence`
- `H3AuditInitialDefectDirectionWeakSequence`
- `h3Audit_initialDefectDirectionWeakSequence_identifies_strongLimit`
- `h3Audit_initialSubcriticalDefectSequence_identifies_physicalAndKineticRate`

## Required inputs / no circularity

The strong limit `L` is derived before the defect-direction pairing is
introduced. The single weak sequence is still a **new independent
initial-data compatibility obligation**, not a theorem of the open-time
Navier–Stokes path. The old temporal-derivative joint-continuity and
subcritical initial H³ energy envelope remain explicit; the terminal
vorticity H³ endpoint and nonlinear relative-energy residual are separate.

## Audit/build integration

The prior commit restored the full Oct 12 source chain into `PrimeTensor.lean`
and theorem checks into `tools/audit/Contracts.lean`. This commit **retains**
that integration. Run `tools/audit/restore_initial_trace_audit.py` first, then
`tools/audit/register_initial_defect_direction_audit.py` (both idempotent)
before `lake build PrimeTensor`, `lake env lean tools/audit/Contracts.lean`,
and `lake build`.

No new axioms, sorry, or admit are used. The artifact environment has no
Lean toolchain: full typechecking must be performed on Rocky Linux.
