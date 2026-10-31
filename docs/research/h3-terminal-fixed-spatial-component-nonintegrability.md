# Fixed spatial component of terminal physical-source nonintegrability

Base commit: `a74ddada88f600b201431f7f14605854ab1d7e00`.

## What is proved

The previous result, `TerminalFixedSpatialComponentSpikes.lean`, produced one
fixed coordinate with arbitrarily large terminal norm spikes. Such spikes
alone do not imply failure of time integrability. The new result closes this
gap using a *finite-component Bochner integral equivalence* from the pinned
mathlib: `MeasureTheory.integrable_piLp_iff` in
`Mathlib.MeasureTheory.SpecificCodomains.WithLp`.

For any ordered terminal interval `b < T` and physical Hilbert path
`F : ℝ → PiLp 2 (fun _ : Fin 3 => H3ScalarL2)`, we prove

    IntervalIntegrable F volume b T
       ↔ ∀ j : Fin 3, IntervalIntegrable (fun t => (F t).ofLp j) volume b T.

This is an exact equivalence, not a pointwise norm estimate.

Suppose failure of strong physical L² velocity trace implies that the actual
projected momentum source `G = Δu - P(u·∇u)` is non-L¹ on **every** positive
terminal interval. If each coordinate of `G` were L¹ on some terminal interval
(with a different left endpoint for each), monotonicity of interval
integrability would make all coordinates L¹ on their common later interval,
contradicting vector nonintegrability. Thus one **single fixed** spatial
coordinate `j : Fin 3` is non-L¹ on every positive terminal interval.

The already-proved positive-time Hilbert source continuity and continuity of
coordinate projection then imply arbitrarily large L² coordinate norms on
every terminal subinterval, *for that same `j`*.

The argument also applies after the previous fixed-source alternative:
there exists one fixed source term (Fourier-reconstructed physical Laplacian
or Leray forcing), and one fixed spatial coordinate, which remain both
non-L¹ and cofinally unbounded on every terminal subinterval.

## Assumptions and limits

- Requires `LoggedPreterminalH3PathAdmissible u T` and **failure** of the
  strong physical L² terminal trace. Does not establish such a failure.
- No `PreterminalH3EnergyClass`, terminal kinetic positivity, finite full H³
  dissipation, terminal clock, or frequency restriction is needed in the
  resulting PDE-facing terminal component theorems.
- The conclusion concerns physical scalar-L² *spatial coordinates*, not a
  fixed Fourier mode, frequency annulus, or spatial point.
- No claim of unconditional Navier–Stokes global regularity or smooth
  terminal extension follows.

## Verification protocol

After the registrar applies its root/audit additions, regenerate the proof
index and compile `TerminalFixedSpatialComponentNonintegrability.lean` first.
Then compile `PrimeTensor.lean`, the FirstMonomialTriad audit module and the
complete project, and run `bash tools/audit/baseline.sh --reuse-build`.

The authoring container does not have the repository's pinned Lean toolchain;
this source is a proof candidate until those checks succeed locally.
