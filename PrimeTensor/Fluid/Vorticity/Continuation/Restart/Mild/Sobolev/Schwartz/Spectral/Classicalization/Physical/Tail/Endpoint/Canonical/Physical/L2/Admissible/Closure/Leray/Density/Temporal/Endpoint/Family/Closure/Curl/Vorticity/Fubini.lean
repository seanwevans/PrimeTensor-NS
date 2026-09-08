import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.ProductIntegrable

/-!
# Fubini interchange for the endpoint vorticity temporal derivatives

The complete product-space integrability hypothesis is now available for all
three compactly tested zero-extended vorticity temporal derivatives.

This file spends that hypothesis exactly once: on every shortened elapsed
target `q ≤ tau`, the time integral of the spatial pairing equals the spatial
integral of the time integral.

No fundamental theorem of calculus is used here.  The next increment can work
pointwise in space with the inner one-dimensional temporal integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityFubini :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Generic interval/spatial Fubini interchange for one continuous-map-valued
temporal extension. -/
theorem intervalIntegral_h3WeakTest_continuousMapExtension_swap
    (ψ : H3WeakTestFunction)
    (F : ℝ → C(Point3, ℝ))
    (t q : ℝ)
    (hq : 0 ≤ q)
    (hProd :
      Integrable
        (fun z : ℝ × Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ z.2)
            (F (t + z.1) z.2))
        (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
          (volume : Measure Point3))) :
    (∫ r in (0 : ℝ)..q,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (F (t + r) x)
          ∂volume)
      =
    ∫ x : Point3,
      (∫ r in (0 : ℝ)..q,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (F (t + r) x))
      ∂volume := by
  have hIoc :
      Integrable
        (fun z : ℝ × Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ z.2)
            (F (t + z.1) z.2))
        (((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) q)).prod
          (volume : Measure Point3)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hProd

  have hUIoc :
      Integrable
        (fun z : ℝ × Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ z.2)
            (F (t + z.1) z.2))
        (((volume : Measure ℝ).restrict (Set.uIoc (0 : ℝ) q)).prod
          (volume : Measure Point3)) := by
    simpa only [Set.uIoc_of_le hq] using hIoc

  exact
    MeasureTheory.intervalIntegral_integral_swap
      hUIoc

/-- Product integrability on the full endpoint interval restricts to every
shortened elapsed target. -/
theorem h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ψ : H3WeakTestFunction)
    (hProd :
      H3PreterminalWeakVorticityTemporalProductIntegrableTo
        hNS t tau ψ)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PreterminalWeakVorticityTemporalProductIntegrableTo
      hNS t (q : ℝ) ψ := by
  rcases hProd with ⟨hX, hY, hZ⟩

  have hSubset :
      Set.Ioo (0 : ℝ) (q : ℝ)
        ⊆
      Set.Ioo (0 : ℝ) tau := by
    intro r hr
    exact
      ⟨hr.1, lt_of_lt_of_le hr.2 q.2.2⟩

  have hTimeMeasure :
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (q : ℝ))
        ≤
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) tau) :=
    Measure.restrict_mono
      hSubset
      le_rfl

  have hProdMeasure :
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (q : ℝ))).prod
        (volume : Measure Point3))
        ≤
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) tau)).prod
        (volume : Measure Point3)) :=
    Measure.prod_mono
      hTimeMeasure
      le_rfl

  exact
    ⟨
      hX.mono_measure hProdMeasure,
      hY.mono_measure hProdMeasure,
      hZ.mono_measure hProdMeasure
    ⟩

/-- Fubini interchange for the compactly tested x-vorticity temporal
derivative on every shortened elapsed target. -/
theorem intervalIntegral_h3PreterminalWeakVorticityXTemporalDerivative_swap_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    ∫ x : Point3,
      (∫ r in (0 : ℝ)..(q : ℝ),
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
            hNS (t + r) x))
      ∂volume := by
  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  exact
    intervalIntegral_h3WeakTest_continuousMapExtension_swap
      ψ
      (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
        hNS)
      t
      (q : ℝ)
      q.2.1
      hShort.1

/-- Fubini interchange for the compactly tested y-vorticity temporal
derivative on every shortened elapsed target. -/
theorem intervalIntegral_h3PreterminalWeakVorticityYTemporalDerivative_swap_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    ∫ x : Point3,
      (∫ r in (0 : ℝ)..(q : ℝ),
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
            hNS (t + r) x))
      ∂volume := by
  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  exact
    intervalIntegral_h3WeakTest_continuousMapExtension_swap
      ψ
      (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
        hNS)
      t
      (q : ℝ)
      q.2.1
      hShort.2.1

/-- Fubini interchange for the compactly tested z-vorticity temporal
derivative on every shortened elapsed target. -/
theorem intervalIntegral_h3PreterminalWeakVorticityZTemporalDerivative_swap_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume)
      =
    ∫ x : Point3,
      (∫ r in (0 : ℝ)..(q : ℝ),
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
            hNS (t + r) x))
      ∂volume := by
  have hAll :=
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ

  have hShort :=
    h3PreterminalWeakVorticityTemporalProductIntegrableTo_mono
      hNS ψ hAll q

  exact
    intervalIntegral_h3WeakTest_continuousMapExtension_swap
      ψ
      (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
        hNS)
      t
      (q : ℝ)
      q.2.1
      hShort.2.2

end

end Euclidean
end Bridge
end PrimeTensor
