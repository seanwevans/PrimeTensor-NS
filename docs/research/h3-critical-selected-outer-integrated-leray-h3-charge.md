# Selected outer carrier: integrated physical H³² charge for nonlinear Leray transfer

Base: `18b9b277e` (real physical sharp highpass CLM and original-carrier alignment).

## Exact mathematical reduction

Write `U(t)` for the **actual** weighted H³ spectral velocity, `V(t)` for the old real physical L² velocity, and `Q_ρ` for the actual real physical sharp Fourier highpass. On a strict positive-time interval `[x,s]`, define

- `H = Q_ρ V(x)`;
- `A = Q_ρ ∫ₓˢ ΔV(t) dt`;
- `B = Q_ρ ∫ₓˢ N(V(t)) dt`;
- `D = Q_ρ ΔV(x)`;
- `τ = s-x`.

All integrals are Bochner interval integrals in the physical three-coordinate real Hilbert space. The preexisting exact two-stage FTC states `Q_ρ V(s) = H + A - B`.

The already-established sharp highpass CLM is contractive, and the actual inverse-Fourier Leray forcing has the pointwise **quadratic** H³ bound with coefficient

`C_L = h3AuditInitialLerayEnergyCoefficient`:

    ‖N(V(t))‖₂ ≤ C_L ‖U(t)‖².

The strict interior H³ path is continuous; hence `N(V(t))` and `‖U(t)‖²` are integrable on `[x,s]`. The triangle inequality for Bochner integration, monotonicity of the scalar interval integral and highpass contraction give

    ‖B‖₂ ≤ C_L ∫ₓˢ ‖U(t)‖² dt.                             (1)

This is **stronger** than replacing the integral by `(s-x) sup_t ‖U(t)‖²`; it records only the realized source action and has no cutoff factor.

## Signed charge from the forced highpass deficit

The previous `SharpHighpassCLM` result supplies, for each fixed strict initial time `x` and tolerance `η>0`, one `δ(x,η)>0` that works for **all** cutoff radii. For `x≤s<x+δ` and a selected forced highpass kinetic drain `ε<K(M_x-M_s)`, assume frozen viscous work and the temporal commutator budget do not cover this drain:

    K(2τ d_ρ(x) + 2‖H‖ τ η) ≤ ε,

where `d_ρ(x) = -⟨H,D⟩≥0`. The proved full-quadratic ledger forces the **original-carrier** signed alignment

    ‖A-B‖² < 2⟨H,B⟩.

Combined with (1), this gives the new necessary cost

    ‖A-B‖² < 2‖H‖ C_L ∫ₓˢ ‖U(t)‖² dt.                      (2)

This establishes strict positivity of the integrated H³² action on any such transfer window.

If an earlier physical kinetic-energy anchor `b<x` is supplied by `PreterminalH3EnergyClass`, monotonicity of kinetic energy and sharp highpass contractivity yield

    ‖H‖ ≤ √(velocityH3Energy0At u b).

Thus the **fully physical anchored** estimate is

    ‖A-B‖² < 2 C_L √E₀(b) ∫ₓˢ ‖U(t)‖² dt.                 (3)

The prefactor has no frequency cutoff and does not require the current H³ amplitude supremum.

## Formalized declarations

1. `thirdFullPhysical_actualLeray_norm_le_H3Square244`
2. `thirdFullPhysical_actualLeray_and_H3Square_intervalIntegrable244`
3. `thirdFullPhysical_outerIntegratedLeray_norm_le_H3Cost244`
4. `thirdFullKinetic_initialAlignment_forcesLerayActionCost244`
5. `thirdFullKinetic_positiveH3Action_of_alignment244`
6. `thirdFullPhysical_outerForcedLeray_integratedH3Charge244`
7. `thirdFullPhysical_outerForcedLeray_positiveIntegratedH3Charge244`
8. `thirdFullPhysical_outerFrozenHighpass_kineticAnchor_norm_le244`
9. `thirdFullPhysical_outerForcedLeray_kineticAnchoredH3Charge244`

## Boundary / frontier

- This is a **necessary** nonlinear-source cost conditional on the selected annular deficit and the insufficient frozen-diffusion/commutator branch. It does not assert the branch occurs.
- The one-radius-independent `δ(x,η)` is local in the **initial time** and is not uniform as `x↗T`. No terminal-uniform modulus is asserted.
- The coefficient is the existing physical Leray convolution constant. A new geometric estimate exploiting actual signed triad cancellation would be needed to reduce it or trade this H³² action for a stronger dissipation-power barrier.
- Potential next step: synchronize (3) on disjoint cofinal windows and compare their summed H³² charges with the known viscosity ledger. This comparison needs a genuine terminal global budget, not an assumed one.

Compilation requires the repository's Lean toolchain. The ZIP underwent structural checks, not Lean compilation in this environment.
