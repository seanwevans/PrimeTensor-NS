import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingC0Bridge

/-!
# Positive-lag C³ reconstruction of the raw H³ nonlinear forcing

The unheated finite Leray-divergence forcing is already Fourier `L¹ ∩ L²`
coordinatewise.  At any strictly positive heat lag `τ`, multiplying that raw
forcing by the heat symbol gives Fourier moments through order three.  Hence
its ordinary inverse Fourier transform is a genuine spatial `C³` function.

The same heat-multiplied amplitude remains in `L²`, so the generic
`L¹ ∩ L²` Fourier compatibility theorem identifies the classical `C³`
representative almost everywhere with the canonical unitary `L²` inverse
Fourier transform of exactly the same raw amplitude.

This is the fixed-lag spatial kernel needed for the near-endpoint Duhamel
bootstrap.  The remaining issue is now purely the time integration as the lag
`τ = t - s` tends to zero.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingHeatC3Bridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SchwartzSpectralNonlinearForcingHeatC3Bridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Raw positive-lag forcing amplitude -/

/-- Apply a positive heat lag directly to one raw finite nonlinear forcing
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3HeatFourierSymbol ν τ ξ *
    h3RawFinLerayOuterProductDivergence U V i ξ

/-- The heat-multiplied raw forcing is strongly measurable. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative ν τ U V i)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  exact
    (continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
      (h3RawFinLerayOuterProductDivergence_integrable U V i).1

/-- At a positive heat lag, raw nonlinear-forcing Fourier moments through
order three are integrable. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (n : ℕ)
    (hn : n ≤ 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ := (Real.sqrt (ν * (τ / 3)))⁻¹

  have hRawInt :=
    h3RawFinLerayOuterProductDivergence_integrable U V i

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C ^ n * ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawInt.norm.const_mul (C ^ n)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ n *
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow n).aestronglyMeasurable).mul
        (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
          ν τ U V i).norm

  refine hMajorant.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hMoment :=
    h3HeatFourierMomentMultiplier_le_three
      hν hτ n hn ξ

  have hPoint :
      ‖ξ‖ ^ n *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖
        ≤
      C ^ n * ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    rw [norm_mul]
    calc
      ‖ξ‖ ^ n *
          (‖h3HeatFourierSymbol ν τ ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
          =
        (‖ξ‖ ^ n * ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by ring
      _ ≤
        C ^ n * ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
        dsimp [C]
        exact
          mul_le_mul_of_nonneg_right
            hMoment
            (norm_nonneg _)

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ n *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖ :=
    mul_nonneg (pow_nonneg (norm_nonneg _) n) (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  exact hPoint

/-- The heat-multiplied raw forcing remains in Fourier `L²`. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_memLp2
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    MemLp
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative ν τ U V i)
      2
      (volume : Measure H3FourierPoint3) := by
  refine
    (h3RawFinLerayOuterProductDivergence_memLp2 U V i).of_le_mul
      (c := 1) ?_ ?_
  · exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
        ν τ U V i
  · filter_upwards with ξ
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    rw [norm_mul, one_mul]
    exact
      mul_le_of_le_one_left
        (norm_nonneg _)
        (norm_h3HeatFourierSymbol_le_one hν.le hτ.le ξ)

/-! ## Classical fixed-lag reconstruction -/

/-- Ordinary inverse-Fourier reconstruction of the positive-lag raw forcing. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatC3Representative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3RawFinLerayOuterProductDivergenceHeatRepresentative ν τ U V i)

/-- Every strictly positive heat lag gives a spatially `C³` nonlinear-forcing
representative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_contDiff_three
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    ContDiff ℝ 3
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i) := by
  have hFourier :
      ContDiff ℝ 3
        (FourierTransform.fourier
          (h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i)) := by
    apply Real.contDiff_fourier
    intro n hn
    have hn' : n ≤ 3 := by simpa using hn
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ U V i n hn'

  have hEq :
      h3RawFinLerayOuterProductDivergenceHeatC3Representative ν τ U V i
        =
      fun x : H3FourierPoint3 =>
        FourierTransform.fourier
          (h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i) (-x) := by
    funext x
    unfold h3RawFinLerayOuterProductDivergenceHeatC3Representative
    exact
      Real.fourierInv_eq_fourier_neg
        (h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i) x

  rw [hEq]
  exact hFourier.comp (by fun_prop)

/-- Canonical Fourier `L²` package of the positive-lag raw forcing. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFourierL2
    (ν τ : ℝ)
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (h3RawFinLerayOuterProductDivergenceHeatRepresentative_memLp2
      hν hτ U V i).toLp
    (h3RawFinLerayOuterProductDivergenceHeatRepresentative ν τ U V i)

/-- Canonical unitary physical `L²` reconstruction of the same positive-lag
raw forcing amplitude. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatPhysicalL2
    (ν τ : ℝ)
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
    (h3RawFinLerayOuterProductDivergenceHeatFourierL2
      ν τ hν hτ U V i)

/-- The classical positive-lag `C³` representative is the same function a.e.
as the canonical unitary `L²` reconstruction. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_ae_eq_physicalL2
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatC3Representative ν τ U V i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2
        ν τ hν hτ U V i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatC3Representative
  unfold h3RawFinLerayOuterProductDivergenceHeatPhysicalL2
  unfold h3RawFinLerayOuterProductDivergenceHeatFourierL2
  exact
    h3FourierInv_integrable_memLp2_ae_eq_L2
      (by
        rw [← integrable_norm_iff
          (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
            ν τ U V i)]
        simpa using
          (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
            hν hτ U V i 0 (by norm_num)))
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_memLp2
        hν hτ U V i)

/-! ## Transport to `Point3` -/

/-- Positive-lag `C³` nonlinear forcing on the project's spatial carrier. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatC3RepresentativeOnPoint3
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    Point3 → ℂ :=
  fun x =>
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
      ν τ U V i ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

/-- The transported fixed-lag representative is spatially `C³` on `Point3`. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3RepresentativeOnPoint3_contDiff_three
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    ContDiff ℝ 3
      (h3RawFinLerayOuterProductDivergenceHeatC3RepresentativeOnPoint3
        ν τ U V i) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatC3RepresentativeOnPoint3
  exact
    (h3RawFinLerayOuterProductDivergenceHeatC3Representative_contDiff_three
      hν hτ U V i).comp
      (PiLp.contDiff_toLp :
        ContDiff ℝ 3 (WithLp.toLp 2 : Point3 → H3FourierPoint3))

end

end Euclidean
end Bridge
end PrimeTensor
