# Initial actual-spectral physical projected-source bounds — 2026-10-12

**Base:** `7adca98a695eeb9a57a24453261316280712f26f`, PrimeTensor-NS `master`.

## Proof increment

The prior `OneComponentInitialH3EnergyMajorizedProjectedRHS` required two pointwise bounds for independently supplied physical diffusion and nonlinear Leray source paths. The new module constructs explicit physical real-L² candidates by taking the real-part physical reconstruction of the canonical raw Fourier Laplacian and the raw Fourier Leray convection force of the **actual positive-time old H³ spectral state**.

Existing Fourier estimates give:

- `‖Δ_spectral(U)‖_{physical L²} ≤ 3 ‖U‖_{H³}`;
- `‖Leray_spectral(U,U)‖_{physical L²} ≤ 3·576·π·C₃ ‖U‖_{H³}²`.

The actual spectral state satisfies `‖U(t)‖² ≤ E₃(t)` and `E₃(t) ≥ 1`. These give the concrete positive-time estimates `‖D(t)‖₂ ≤ 3 E₃(t)` and `‖N(t)‖₂ ≤ (3·576·π·C₃) E₃(t)`; zero totalization makes them valid at the left endpoint. The existing dominated-integrability theorem then yields the stated Bochner source integrability and summed budget, assuming the energy integral and source time-measurability.

## Scope and remaining obligations

These `D` and `N` are explicitly constructed **spectral physical candidates**. This module does not silently assert their a.e. equality with the literal actual PDE Laplacian and Leray nonlinear term, nor that their weak momentum derivative is automatically the old velocity derivative. Those identities, strong time-measurability of the two paths, and initial `L¹_t E₃` remain analytically separate. The old/selected vanishing residual and terminal actual-vorticity strong-H³ endpoint are also unchanged.

No use of `sorry`, `admit`, `axiom`, or `unsafe`. Compile via `lake env lean` and full `lake build`; these are **not available in the assistant environment**.
