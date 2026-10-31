# Terminal source and full H³ dissipation nonintegrability

Base: `6bc8bb08` (Lean CI passing). Imports the proven finite-dissipation terminal trace module.

## Results

1. On every positive terminal interval `(b,T)`, Bochner `L¹_t L²_x` integrability of the actual projected source, via the exact physical Hilbert FTC, forces a strong physical `L²` terminal trace. Requires only `LoggedPreterminalH3PathAdmissible`.
2. Contraposition: absent an `L²` terminal trace, that actual projected source cannot be Bochner integrable on *any* positive terminal interval.
3. Under `PreterminalH3EnergyClass`, integrability of the **full H³ dissipation** on `(b,T)` implies integrability of that actual projected source on the *same* tail, from the already formalized affine kinetic-anchor/viscous majorant.
4. Therefore absent an `L²` terminal trace, full H³ dissipation cannot be integrable on **any** `(b,T)` with `a<b<T`.

No positive terminal kinetic mass, source ceiling, Fourier cutoff, clock noncompression, or moment majorant is needed. No integrability premise survives in the final obstruction's hypotheses.

This is a necessary conditional singularity obstruction. It does **not** rule out `L²` traces in general, establish unconditional finite dissipation, or imply smooth continuation.

## Verification

Run `lake build PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalDissipationObstruction` and `lake env lean` for the proof file, then run the registrar, source index, full baseline, and commit/push after successful checks. The packaging environment does not contain Lake; proof bodies remain unverified locally until the user's pinned Lean build passes.
