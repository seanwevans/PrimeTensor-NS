# Actual initial projected RHS: physical identification on positive restarts

**Parent:** `90e39986` — *correct inverse Fourier sources and derive initial measurability*.

## Claim closed

The corrected actual-time physical `L²` source constructors are **not merely Fourier-norm comparison states**. On every strictly positive canonical restart window on which the old Navier–Stokes solution is represented by its genuine weighted `H³` spectral snapshot, the source constructors agree with the already-proved physical spatial Laplacian and Leray transport.

The Laplacian identity uses the existing scalar Plancherel equality for the genuine old physical second jet, Hermitian reality of the old snapshot's Fourier Laplacian, and injectivity of the scalar Plancherel map. The Leray identity is definitional after replacing the actual spectral state by the canonical old snapshot, since both sides now include the same **inverse Fourier transform** and real projection. Their difference equals the already-identified physical projected old RHS `Δu − P div(u ⊗ u)`.

The old positive-time weak Navier–Stokes temporal identity can therefore be stated with exactly these corrected actual-time source paths for **divergence-free compact tests**, with no new source-identification assumption. Canonical-window coverage transfers the identity to **every** strict positive preterminal time, not just the chosen elapsed snapshot.

## New Lean declarations

- `h3Audit_initialActualSpectralLaplacian_eq_oldPhysicalOnElapsed`
- `h3Audit_initialActualSpectralLeray_eq_oldPhysicalOnElapsed`
- `h3Audit_initialActualSpectralProjectedRHS_eq_oldPhysicalOnElapsed`
- `h3Audit_initialActualSpectralProjectedRHS_weakTemporalPairing_onElapsed`
- `h3Audit_initialActualSpectralProjectedRHS_weakTemporalPairing_at_positiveTime`

## Remaining genuine obligations

The weak temporal PDE is proved here only on positive canonical restart windows and for solenoidal compact tests. It is **not** automatically the scalar `HasDerivAt` identity against every arbitrary three-component Schwartz test required by the previous initial weak-FTC contract. One must still close that test-space/differentiation bridge, and derive initial `∫₀ᵇ E₃(t) dt < ∞` rather than assume it.

The epsilon-vanishing old/selected relative-energy residual and terminal actual-vorticity strong-`H³` endpoint remain independent assumptions. This note asserts no unconditional global Navier–Stokes regularity result.

## Verification

Source contains no `sorry`/`admit`. ZIP integrity is checked by the assistant; Lean compilation and repository audit require the user's Rocky Linux environment. The `lake env lean` step precedes committing/pushing.
