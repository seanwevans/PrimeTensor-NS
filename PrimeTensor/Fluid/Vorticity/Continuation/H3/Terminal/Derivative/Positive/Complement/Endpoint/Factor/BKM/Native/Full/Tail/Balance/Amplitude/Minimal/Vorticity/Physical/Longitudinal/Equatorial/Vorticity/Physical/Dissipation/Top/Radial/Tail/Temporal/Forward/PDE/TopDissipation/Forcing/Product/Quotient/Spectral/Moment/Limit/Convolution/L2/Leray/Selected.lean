import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product

/-!
# Selected fixed-factor specializations of spectral slope Leray decay

The general finite Leray decay theorem accepts an arbitrary fixed spectral
vector carrying the doubled moment required at radial order `m`.

For the nonlinear product-rule quotient only two fixed vectors are needed:

* the selected mild state `U(x)`;
* the selected projected RHS `R(x)`.

Both already carry every natural moment on the positive compact slab.  This
file specializes the general left/right slope-error Leray limits to those two
canonical choices, eliminating repeated moment bookkeeping from the quotient
algebra.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeLeraySelected
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Fixed selected state -/

/--
The left slope-error Leray channel vanishes against the selected state at the
base slab point.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_selectedState_zero
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    let sx : Set.Icc (Q / 2) Q :=
      ⟨x, hx.1.le, hx.2.le⟩
    let U : H3SpectralFinVectorState :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR sx)
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
          m hNS ht₀ hE hTail hQ hQR i hx
          U
          (h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
            (2 * (m + 1))
            hNS ht₀ hE hTail hQ hQR sx)
          h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  dsimp only

  exact
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_zero
      m hNS ht₀ hE hTail hQ hQR i hx
      (
        h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht₀ hE hTail
          (
            h3SelectedProjectedRHSSlabRadius
              hE hQ hQR
              ⟨x, hx.1.le, hx.2.le⟩
          )
      )
      (
        h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
          (2 * (m + 1))
          hNS ht₀ hE hTail hQ hQR
          ⟨x, hx.1.le, hx.2.le⟩
      )

/--
The right slope-error Leray channel vanishes against the selected state at the
base slab point.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_selectedState_zero
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    let sx : Set.Icc (Q / 2) Q :=
      ⟨x, hx.1.le, hx.2.le⟩
    let U : H3SpectralFinVectorState :=
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hNS ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR sx)
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
          m hNS ht₀ hE hTail hQ hQR i hx
          U
          (h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
            (2 * (m + 1))
            hNS ht₀ hE hTail hQ hQR sx)
          h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  dsimp only

  exact
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_zero
      m hNS ht₀ hE hTail hQ hQR i hx
      (
        h3PreterminalSelectedUnitSpectralStateOnRadius
          hNS ht₀ hE hTail
          (
            h3SelectedProjectedRHSSlabRadius
              hE hQ hQR
              ⟨x, hx.1.le, hx.2.le⟩
          )
      )
      (
        h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
          (2 * (m + 1))
          hNS ht₀ hE hTail hQ hQR
          ⟨x, hx.1.le, hx.2.le⟩
      )

/-! ## Fixed projected RHS -/

/--
The left slope-error Leray channel vanishes against the projected RHS at the
base slab point.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_projectedRHS_zero
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    let sx : Set.Icc (Q / 2) Q :=
      ⟨x, hx.1.le, hx.2.le⟩
    let R : H3SpectralFinVectorState :=
      h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
        hNS ht₀ hE hTail hQ hQR sx
    let hR :
        ∀ r : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (m + 1) : ℕ) : ℝ))
            (R r) :=
      fun r =>
        h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r sx
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
          m hNS ht₀ hE hTail hQ hQR i hx R hR h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  dsimp only

  exact
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_zero
      m hNS ht₀ hE hTail hQ hQR i hx
      (
        h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
          hNS ht₀ hE hTail hQ hQR
          ⟨x, hx.1.le, hx.2.le⟩
      )
      (
        fun r =>
          h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
            (2 * (m + 1)) (by omega)
            hNS ht₀ hE hTail hQ hQR r
            ⟨x, hx.1.le, hx.2.le⟩
      )

/--
The right slope-error Leray channel vanishes against the projected RHS at the
base slab point.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_projectedRHS_zero
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    let sx : Set.Icc (Q / 2) Q :=
      ⟨x, hx.1.le, hx.2.le⟩
    let R : H3SpectralFinVectorState :=
      h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
        hNS ht₀ hE hTail hQ hQR sx
    let hR :
        ∀ r : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (m + 1) : ℕ) : ℝ))
            (R r) :=
      fun r =>
        h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r sx
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
          m hNS ht₀ hE hTail hQ hQR i hx R hR h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  dsimp only

  exact
    tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_zero
      m hNS ht₀ hE hTail hQ hQR i hx
      (
        h3PreterminalSelectedProjectedRHSH3SpectralStateOnSlab
          hNS ht₀ hE hTail hQ hQR
          ⟨x, hx.1.le, hx.2.le⟩
      )
      (
        fun r =>
          h3PreterminalSelectedProjectedRHSH3SpectralScalarOnSlab_natMoment_integrable
            (2 * (m + 1)) (by omega)
            hNS ht₀ hE hTail hQ hQR r
            ⟨x, hx.1.le, hx.2.le⟩
      )

end

end Euclidean
end Bridge
end PrimeTensor
