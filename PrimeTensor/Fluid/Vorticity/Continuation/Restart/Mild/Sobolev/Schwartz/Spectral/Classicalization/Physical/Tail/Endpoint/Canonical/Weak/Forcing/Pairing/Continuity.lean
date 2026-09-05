import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Diffusion.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C0.Time.Continuity

/-!
# Classicalization: continuity of weak endpoint forcing pairings

The weak diffusion pairing has already been moved onto twice-differentiated
compact tests, so its elapsed-time continuity follows from zeroth-order `L²`
velocity continuity.

This file closes the nonlinear half of the candidate weak time derivative.

For a fixed compactly supported smooth scalar test `φ`, define

    U ↦ ∫ φ(x) Re N(U,U)_i(x) dx.

The existing pointwise forcing difference estimate is uniform in the spatial
point:

    ‖N(U,U)(x) - N(V,V)(x)‖
      ≤ C ‖U-V‖ ‖U‖ + C ‖V‖ ‖U-V‖.

Hence the difference of weak pairings is bounded by the same state expression
times the fixed `L¹` mass of `φ`.  This proves continuity of the weak forcing
pairing as a function of the H³ spectral state.

Composing with the already-continuous endpoint canonical path and summing over
the three velocity coordinates gives continuity of the complete weak forcing
pairing on the closed elapsed interval.

No pointwise Fourier continuity or fixed-frequency evaluation is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakForcingPairingContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakForcingPairingContinuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Fixed `L¹` mass of a compactly supported smooth scalar test function. -/
noncomputable def h3WeakTestFunctionL1Mass
    (φ : H3WeakTestFunction) :
    ℝ :=
  ∫ x : Point3, ‖φ x‖ ∂volume

/-- A compactly supported smooth scalar test function is integrable. -/
theorem h3WeakTestFunction_integrable
    (φ : H3WeakTestFunction) :
    Integrable
      (φ : Point3 → ℝ)
      (volume : Measure Point3) := by
  exact
    φ.continuous.integrable_of_hasCompactSupport
      φ.hasCompactSupport

/-- Pointwise diagonal forcing differences on `Point3` obey the existing
spectral-state difference estimate. -/
theorem norm_h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_diagonal_sub_le_stateDifference
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : Point3) :
    ‖h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U U i x
        -
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          V V i x‖
      ≤
    h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
      h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖ := by
  unfold h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
  exact
    norm_h3RawFinLerayOuterProductDivergenceC0Representative_diagonal_sub_le_stateDifference
      U V i
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

/-- One scalar weak forcing coordinate as a function of the spectral state. -/
noncomputable def h3RawFinLerayOuterProductDivergenceWeakPairing
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (U : H3SpectralFinVectorState) :
    ℝ :=
  ∫ x : Point3,
    (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ x)
      ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U U i x).re)
    ∂volume

/-- Each scalar weak forcing integrand is integrable because the forcing
representative is continuous and the test is compactly supported. -/
theorem h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (U : H3SpectralFinVectorState) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            U U i x).re))
      (volume : Measure Point3) := by
  have hForceContinuous :
      Continuous
        (fun x : Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            U U i x).re) := by
    exact
      Complex.continuous_re.comp
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_continuous
          U U i)

  exact
    φ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hForceContinuous.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- Quantitative continuity estimate for one weak forcing coordinate. -/
theorem abs_h3RawFinLerayOuterProductDivergenceWeakPairing_sub_le
    (φ : H3WeakTestFunction)
    (i : Fin 3)
    (U V : H3SpectralFinVectorState) :
    abs
      (h3RawFinLerayOuterProductDivergenceWeakPairing φ i U -
       h3RawFinLerayOuterProductDivergenceWeakPairing φ i V)
      ≤
    (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
      h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖)
      *
    h3WeakTestFunctionL1Mass φ := by
  let R : ℝ :=
    h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
      h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖

  let FU : Point3 → ℝ :=
    fun x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U U i x).re)

  let FV : Point3 → ℝ :=
    fun x =>
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          V V i x).re)

  have hFU :
      Integrable FU
        (volume : Measure Point3) := by
    dsimp only [FU]
    exact
      h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
        φ i U

  have hFV :
      Integrable FV
        (volume : Measure Point3) := by
    dsimp only [FV]
    exact
      h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
        φ i V

  have hDiff :
      Integrable
        (fun x : Point3 => FU x - FV x)
        (volume : Measure Point3) :=
    hFU.sub hFV

  have hφNorm :
      Integrable
        (fun x : Point3 => ‖φ x‖)
        (volume : Measure Point3) :=
    (h3WeakTestFunction_integrable φ).norm

  have hRNonneg : 0 ≤ R := by
    dsimp only [R]
    have hC : 0 ≤ h3NonlinearForcingL1Coefficient := by
      exact h3NonlinearForcingL1Coefficient_nonneg
    positivity

  have hMajor :
      Integrable
        (fun x : Point3 => R * ‖φ x‖)
        (volume : Measure Point3) :=
    hφNorm.const_mul R

  have hPoint :
      ∀ x : Point3,
        ‖FU x - FV x‖
          ≤
        R * ‖φ x‖ := by
    intro x

    have hForce :=
      norm_h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_diagonal_sub_le_stateDifference
        U V i x

    have hRe :
        abs
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x).re
            -
           (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              V V i x).re)
          ≤
        ‖h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x
            -
          h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              V V i x‖ := by
      have h :=
        Complex.abs_re_le_norm
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x
            -
           h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              V V i x)
      simpa only [Complex.sub_re] using h

    dsimp only [FU, FV, R]
    change
      abs
        ((φ x) *
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            U U i x).re
          -
         (φ x) *
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            V V i x).re)
        ≤
      (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
        h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖)
        *
      abs (φ x)

    rw [← mul_sub, abs_mul]

    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left
        (hRe.trans hForce)
        (abs_nonneg (φ x)))

  unfold h3RawFinLerayOuterProductDivergenceWeakPairing

  rw [← integral_sub hFU hFV]

  calc
    abs (∫ x : Point3, FU x - FV x ∂volume)
        =
      ‖∫ x : Point3, FU x - FV x ∂volume‖ := by
        simp only [Real.norm_eq_abs]
    _ ≤
      ∫ x : Point3, ‖FU x - FV x‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ ≤
      ∫ x : Point3, R * ‖φ x‖ ∂volume := by
        exact
          integral_mono_ae
            hDiff.norm
            hMajor
            (Filter.Eventually.of_forall hPoint)
    _ =
      R * h3WeakTestFunctionL1Mass φ := by
        unfold h3WeakTestFunctionL1Mass
        rw [integral_const_mul]
    _ =
      (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
        h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖)
        *
      h3WeakTestFunctionL1Mass φ := by
        rfl

/-- One weak forcing coordinate is continuous as a function of the H³ spectral
state. -/
theorem continuous_h3RawFinLerayOuterProductDivergenceWeakPairing
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    Continuous
      (h3RawFinLerayOuterProductDivergenceWeakPairing φ i) := by
  rw [continuous_iff_continuousAt]
  intro V

  let B : H3SpectralFinVectorState → ℝ :=
    fun U =>
      (h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
        h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖)
        *
      h3WeakTestFunctionL1Mass φ

  have hBContinuousAt :
      ContinuousAt B V := by
    dsimp only [B]
    fun_prop

  have hBV : B V = 0 := by
    simp [B]

  have hBTend :
      Tendsto B (𝓝 V) (𝓝 0) := by
    change Tendsto B (𝓝 V) (𝓝 (B V)) at hBContinuousAt
    rw [hBV] at hBContinuousAt
    exact hBContinuousAt

  have hBound :
      ∀ U : H3SpectralFinVectorState,
        ‖h3RawFinLerayOuterProductDivergenceWeakPairing φ i U -
          h3RawFinLerayOuterProductDivergenceWeakPairing φ i V‖
          ≤
        B U := by
    intro U
    rw [Real.norm_eq_abs]
    dsimp only [B]
    exact
      abs_h3RawFinLerayOuterProductDivergenceWeakPairing_sub_le
        φ i U V

  have hNormTend :
      Tendsto
        (fun U : H3SpectralFinVectorState =>
          ‖h3RawFinLerayOuterProductDivergenceWeakPairing φ i U -
            h3RawFinLerayOuterProductDivergenceWeakPairing φ i V‖)
        (𝓝 V)
        (𝓝 0) := by
    exact
      squeeze_zero
        (fun U =>
          norm_nonneg
            (h3RawFinLerayOuterProductDivergenceWeakPairing φ i U -
             h3RawFinLerayOuterProductDivergenceWeakPairing φ i V))
        hBound
        hBTend

  exact
    tendsto_iff_norm_sub_tendsto_zero.2 hNormTend

/-- Complete weak nonlinear forcing pairing along the endpoint canonical path
on the closed elapsed interval. -/
noncomputable def h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint
  ∑ i : Fin 3,
    h3RawFinLerayOuterProductDivergenceWeakPairing
      (φ i) i (W (q : ℝ))

/-- The complete endpoint weak nonlinear forcing pairing is continuous on the
closed elapsed interval. -/
theorem continuous_h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector) :
    Continuous
      (h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hW :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint

  unfold h3PreterminalTailCanonicalWeakForcingPairingOnElapsed
  dsimp only [W]

  apply continuous_finsetSum
  intro i hi

  exact
    (continuous_h3RawFinLerayOuterProductDivergenceWeakPairing
      (φ i) i).comp
      (hW.comp continuous_subtype_val)

end

end Euclidean
end Bridge
end PrimeTensor
