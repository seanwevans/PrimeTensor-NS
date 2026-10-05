import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Spectral.Moment.Limit.Convolution.L2
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Bound.Forcing

/-!
# Vanishing radial Leray forcing with one selected slope-error input

The preceding checkpoint proves strong radial convolution decay whenever one
scalar factor is a coordinate of the genuine selected spectral slope error.

The quantitative finite Leray estimate is a finite double sum of exactly those
convolution norms one radial order higher.  This file lifts the scalar decay
through the Fourier derivative, the finite divergence, and the Leray matrix.

As before, the local packages are totalized by zero outside the compact slab.
The shifted time lies in that slab eventually at `h → 0`, so the totalization
does not alter the punctured-neighborhood limit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedSpectralSlopeLerayLimit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2400000

/-! ## Totalized finite Leray packages -/

/--
Order-`m` radial finite Leray forcing with the selected spectral slope error
in the left bilinear slot.
-/
noncomputable def h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
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
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (G : H3SpectralFinVectorState)
    (hG :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (G r))
    (h : ℝ) :
    H3FourierComplexL2 :=
  if hxh : x + h ∈ Set.Icc (Q / 2) Q then
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      m
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h
      )
      G
      i
      (fun r =>
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r hx h hxh)
      hG
  else
    0

/--
Order-`m` radial finite Leray forcing with the selected spectral slope error
in the right bilinear slot.
-/
noncomputable def h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
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
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (G : H3SpectralFinVectorState)
    (hG :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (G r))
    (h : ℝ) :
    H3FourierComplexL2 :=
  if hxh : x + h ∈ Set.Icc (Q / 2) Q then
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
      m
      G
      (
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
          hNS ht₀ hE hTail hQ hQR hx h
      )
      i
      hG
      (fun r =>
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r hx h hxh)
  else
    0

/-! ## Left-slot decay -/

/--
The radial finite Leray forcing norm tends to zero with the selected spectral
slope error in the left slot.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left_zero
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
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (G : H3SpectralFinVectorState)
    (hG :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (G r)) :
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
          m hNS ht₀ hE hTail hQ hQR i hx G hG h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let S : ℝ → H3SpectralFinVectorState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h

  let L : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left
        m hNS ht₀ hE hTail hQ hQR i hx G hG h

  let Major : ℝ → ℝ :=
    fun h =>
      ∑ k : Fin 3,
        2 *
          (
            ∑ j : Fin 3,
              (2 * Real.pi) *
                ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left
                    (m + 1) (by omega)
                    hNS ht₀ hE hTail hQ hQR k hx
                    (G j) (hG j) h‖
          )

  have hTerm :
      ∀ k j : Fin 3,
        Tendsto
          (fun h : ℝ =>
            (2 * Real.pi) *
              ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left
                  (m + 1) (by omega)
                  hNS ht₀ hE hTail hQ hQR k hx
                  (G j) (hG j) h‖)
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k j

    have hBase :=
      tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left_zero
        (m + 1) (by omega)
        hNS ht₀ hE hTail hQ hQR k hx
        (G j) (hG j)

    have hConst :
        Tendsto
          (fun _h : ℝ => 2 * Real.pi)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (2 * Real.pi)) :=
      tendsto_const_nhds

    simpa only [mul_zero] using hConst.mul hBase

  have hInner :
      ∀ k : Fin 3,
        Tendsto
          (fun h : ℝ =>
            ∑ j : Fin 3,
              (2 * Real.pi) *
                ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left
                    (m + 1) (by omega)
                    hNS ht₀ hE hTail hQ hQR k hx
                    (G j) (hG j) h‖)
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k

    have hSum :=
      tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun j _hj => hTerm k j)

    simpa only [Finset.sum_const_zero] using hSum

  have hOuterTerm :
      ∀ k : Fin 3,
        Tendsto
          (fun h : ℝ =>
            2 *
              (
                ∑ j : Fin 3,
                  (2 * Real.pi) *
                    ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left
                        (m + 1) (by omega)
                        hNS ht₀ hE hTail hQ hQR k hx
                        (G j) (hG j) h‖
              ))
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k

    have hConst :
        Tendsto
          (fun _h : ℝ => (2 : ℝ))
          (𝓝[≠] (0 : ℝ))
          (𝓝 2) :=
      tendsto_const_nhds

    simpa only [mul_zero] using hConst.mul (hInner k)

  have hMajorTend :
      Tendsto Major
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hSum :=
      tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _hk => hOuterTerm k)

    simpa only [Major, Finset.sum_const_zero] using hSum

  have hhZero :
      Tendsto
        (fun h : ℝ => h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds

  have hArg :
      Tendsto
        (fun h : ℝ => x + h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 x) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add hhZero

  have hInterior :
      Set.Icc (Q / 2) Q ∈ 𝓝 x :=
    Icc_mem_nhds hx.1 hx.2

  have hArgInterior :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        x + h ∈ Set.Icc (Q / 2) Q :=
    hArg.eventually hInterior

  have hNonneg :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        0 ≤ ‖L h‖ :=
    Filter.Eventually.of_forall
      (fun h => norm_nonneg _)

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        ‖L h‖ ≤ Major h := by

    filter_upwards [hArgInterior] with h hxh

    have hS :
        ∀ r : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (m + 1) : ℕ) : ℝ))
            (S h r) := by
      intro r
      dsimp only [S]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r hx h hxh

    have hBound :=
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        m (S h) G i hS hG

    dsimp only [L]

    simp only [
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Left,
      dite_eq_left hxh
    ]

    simpa only [
      Major,
      S,
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Left,
      dite_eq_left hxh
    ] using hBound

  exact
    squeeze_zero'
      hNonneg
      hUpper
      hMajorTend

/-! ## Right-slot decay -/

/--
The radial finite Leray forcing norm tends to zero with the selected spectral
slope error in the right slot.
-/
theorem tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right_zero
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
    (hx : x ∈ Set.Ioo (Q / 2) Q)
    (G : H3SpectralFinVectorState)
    (hG :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (G r)) :
    Tendsto
      (fun h : ℝ =>
        ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
          m hNS ht₀ hE hTail hQ hQR i hx G hG h‖)
      (𝓝[≠] (0 : ℝ))
      (𝓝 0) := by

  let S : ℝ → H3SpectralFinVectorState :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab
        hNS ht₀ hE hTail hQ hQR hx h

  let L : ℝ → H3FourierComplexL2 :=
    fun h =>
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right
        m hNS ht₀ hE hTail hQ hQR i hx G hG h

  let Major : ℝ → ℝ :=
    fun h =>
      ∑ k : Fin 3,
        2 *
          (
            ∑ j : Fin 3,
              (2 * Real.pi) *
                ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right
                    (m + 1) (by omega)
                    hNS ht₀ hE hTail hQ hQR j hx
                    (G k) (hG k) h‖
          )

  have hTerm :
      ∀ k j : Fin 3,
        Tendsto
          (fun h : ℝ =>
            (2 * Real.pi) *
              ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right
                  (m + 1) (by omega)
                  hNS ht₀ hE hTail hQ hQR j hx
                  (G k) (hG k) h‖)
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k j

    have hBase :=
      tendsto_norm_h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right_zero
        (m + 1) (by omega)
        hNS ht₀ hE hTail hQ hQR j hx
        (G k) (hG k)

    have hConst :
        Tendsto
          (fun _h : ℝ => 2 * Real.pi)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (2 * Real.pi)) :=
      tendsto_const_nhds

    simpa only [mul_zero] using hConst.mul hBase

  have hInner :
      ∀ k : Fin 3,
        Tendsto
          (fun h : ℝ =>
            ∑ j : Fin 3,
              (2 * Real.pi) *
                ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right
                    (m + 1) (by omega)
                    hNS ht₀ hE hTail hQ hQR j hx
                    (G k) (hG k) h‖)
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k

    have hSum :=
      tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun j _hj => hTerm k j)

    simpa only [Finset.sum_const_zero] using hSum

  have hOuterTerm :
      ∀ k : Fin 3,
        Tendsto
          (fun h : ℝ =>
            2 *
              (
                ∑ j : Fin 3,
                  (2 * Real.pi) *
                    ‖h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right
                        (m + 1) (by omega)
                        hNS ht₀ hE hTail hQ hQR j hx
                        (G k) (hG k) h‖
              ))
          (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
    intro k

    have hConst :
        Tendsto
          (fun _h : ℝ => (2 : ℝ))
          (𝓝[≠] (0 : ℝ))
          (𝓝 2) :=
      tendsto_const_nhds

    simpa only [mul_zero] using hConst.mul (hInner k)

  have hMajorTend :
      Tendsto Major
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by

    have hSum :=
      tendsto_finsetSum
        (Finset.univ : Finset (Fin 3))
        (fun k _hk => hOuterTerm k)

    simpa only [Major, Finset.sum_const_zero] using hSum

  have hhZero :
      Tendsto
        (fun h : ℝ => h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds

  have hArg :
      Tendsto
        (fun h : ℝ => x + h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 x) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add hhZero

  have hInterior :
      Set.Icc (Q / 2) Q ∈ 𝓝 x :=
    Icc_mem_nhds hx.1 hx.2

  have hArgInterior :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        x + h ∈ Set.Icc (Q / 2) Q :=
    hArg.eventually hInterior

  have hNonneg :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        0 ≤ ‖L h‖ :=
    Filter.Eventually.of_forall
      (fun h => norm_nonneg _)

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[≠] (0 : ℝ)),
        ‖L h‖ ≤ Major h := by

    filter_upwards [hArgInterior] with h hxh

    have hS :
        ∀ r : Fin 3,
          H3RawFourierMomentIntegrable
            (((2 * (m + 1) : ℕ) : ℝ))
            (S h r) := by
      intro r
      dsimp only [S]
      exact
        h3PreterminalSelectedVelocitySpectralSlopeErrorOnSlab_apply_natMoment_integrable
          (2 * (m + 1)) (by omega)
          hNS ht₀ hE hTail hQ hQR r hx h hxh

    have hBound :=
      norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
        m G (S h) i hG hS

    dsimp only [L]

    simp only [
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawFinLerayRadialFourierL2Right,
      dite_eq_left hxh
    ]

    simpa only [
      Major,
      S,
      h3PreterminalSelectedVelocitySpectralSlopeErrorRawProductConvolutionRadialFourierL2Right,
      dite_eq_left hxh
    ] using hBound

  exact
    squeeze_zero'
      hNonneg
      hUpper
      hMajorTend

end

end Euclidean
end Bridge
end PrimeTensor
