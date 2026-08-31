import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedRawDivergenceFourierInv
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityThirdJetContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Point3Derivative

/-!
# Physical incompressibility of the selected H³ restart representative

The Fourier-side part of incompressibility is already complete:
`SelectedRawDivergenceFourierInv` proves that the inverse Fourier transform of

    ξ ↦ Σ_j d_j(ξ) û_j(ξ)

vanishes pointwise for every raw-divergence-free H³ spectral state.

`H3.Real.C1.Point3Derivative` now identifies each physical coordinate
derivative of the real inverse-Fourier representative with the real part of
the corresponding inverse-Fourier derivative multiplier.

This file joins those two facts.  The only remaining analytic bookkeeping is
finite-sum linearity of the ordinary inverse Fourier integral; integrability of
each summand follows from the H³ first-moment estimate already proved in
`H3.Real.C1.Derivative`.

The result is a genuine `RealFluid.divergence = 0` theorem for the smooth real
representative of any raw-divergence-free spectral path, followed by the
canonical preterminal selected-restart specialization.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedPhysicalIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Inverse Fourier transform commutes with the three-coordinate raw
divergence sum.  We prove this directly at the integral level because the
ordinary Fourier integral is a total operator, while additivity is only valid
on the integrable summands. -/
theorem h3SpectralFinRawDivergenceFourierInv_eq_sum_coordinateDerivatives
    (G : H3SpectralFinVectorState)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SpectralFinRawDivergenceFourier G)
        x
      =
    ∑ j : Fin 3,
      FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative
          (G j) j)
        x := by
  have hPhaseIntegrable :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            𝐞 (inner ℝ ξ x) •
              h3SpectralScalarRawFourierCoordinateDerivative
                (G j) j ξ)
          (volume : Measure H3FourierPoint3) := by
    intro j

    have h :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            𝐞 (-(inner ℝ ξ (-x))) •
              h3SpectralScalarRawFourierCoordinateDerivative
                (G j) j ξ)
          (volume : Measure H3FourierPoint3) := by
      rw [Real.fourierIntegral_convergent_iff (-x)]
      exact
        h3SpectralScalarRawFourierCoordinateDerivative_integrable
          (G j) j

    simpa only [inner_neg_right, neg_neg] using h

  have hIntegralSum :
      (∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3,
          𝐞 (inner ℝ ξ x) •
            h3SpectralScalarRawFourierCoordinateDerivative
              (G j) j ξ)
        =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3,
          𝐞 (inner ℝ ξ x) •
            h3SpectralScalarRawFourierCoordinateDerivative
              (G j) j ξ := by
    simpa using
      (MeasureTheory.integral_finsetSum
        (μ := (volume : Measure H3FourierPoint3))
        Finset.univ
        (fun j _ => hPhaseIntegrable j))

  simp_rw [Real.fourierInv_eq]

  calc
    (∫ ξ : H3FourierPoint3,
      𝐞 (inner ℝ ξ x) •
        h3SpectralFinRawDivergenceFourier G ξ)
        =
      ∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3,
          𝐞 (inner ℝ ξ x) •
            h3SpectralScalarRawFourierCoordinateDerivative
              (G j) j ξ := by
          apply integral_congr_ae
          filter_upwards with ξ

          unfold h3SpectralFinRawDivergenceFourier
          rw [Finset.smul_sum]

          apply Finset.sum_congr rfl
          intro j hj
          rfl
    _ =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3,
          𝐞 (inner ℝ ξ x) •
            h3SpectralScalarRawFourierCoordinateDerivative
              (G j) j ξ :=
      hIntegralSum

/-- The physical divergence of an arbitrary reconstructed spectral path is the
real part of the inverse Fourier transform of its raw Fourier divergence. -/
theorem h3SpectralRealVelocityOfPath_divergence_eq_rawDivergenceFourierInv_re
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.divergence
        spatial3
        (h3SpectralRealVelocityOfPath W s)
        x
      =
    (FourierTransformInv.fourierInv
      (h3SpectralFinRawDivergenceFourier (W s))
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
  have hComp0 :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component xAxis)
        =
      h3SpectralVelocityRealC1RepresentativeOnPoint3
        (W s) 0 := by
    funext y
    simpa only [h3AxisOfFin3_zero] using
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y (0 : Fin 3)

  have hComp1 :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component yAxis)
        =
      h3SpectralVelocityRealC1RepresentativeOnPoint3
        (W s) 1 := by
    funext y
    simpa only [h3AxisOfFin3_one] using
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y (1 : Fin 3)

  have hComp2 :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath W s y).component zAxis)
        =
      h3SpectralVelocityRealC1RepresentativeOnPoint3
        (W s) 2 := by
    funext y
    simpa only [h3AxisOfFin3_two] using
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3
        W s y (2 : Fin 3)

  have hD0 :
      spatial3.d xAxis
          (h3SpectralVelocityRealC1RepresentativeOnPoint3
            (W s) 0)
          x
        =
      (FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative
          ((W s) 0) 0)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
    change
      spatial3.d xAxis
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            ((W s) 0))
          x
        =
      _
    simpa only [h3AxisOfFin3_zero] using
      h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
        ((W s) 0) (0 : Fin 3) x

  have hD1 :
      spatial3.d yAxis
          (h3SpectralVelocityRealC1RepresentativeOnPoint3
            (W s) 1)
          x
        =
      (FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative
          ((W s) 1) 1)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
    change
      spatial3.d yAxis
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            ((W s) 1))
          x
        =
      _
    simpa only [h3AxisOfFin3_one] using
      h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
        ((W s) 1) (1 : Fin 3) x

  have hD2 :
      spatial3.d zAxis
          (h3SpectralVelocityRealC1RepresentativeOnPoint3
            (W s) 2)
          x
        =
      (FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative
          ((W s) 2) 2)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
    change
      spatial3.d zAxis
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            ((W s) 2))
          x
        =
      _
    simpa only [h3AxisOfFin3_two] using
      h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
        ((W s) 2) (2 : Fin 3) x

  rw [
    h3SpectralFinRawDivergenceFourierInv_eq_sum_coordinateDerivatives
  ]

  unfold PrimeTensor.Bridge.RealFluid.divergence
  rw [axis_fold_three]
  rw [hComp0, hComp1, hComp2]
  rw [hD0, hD1, hD2]

  simp only [
    Fin.sum_univ_three,
    Complex.add_re,
    add_assoc
  ]

/-- Raw Fourier incompressibility therefore implies genuine pointwise physical
incompressibility of the reconstructed real path. -/
theorem h3SpectralRealVelocityOfPath_divergence_eq_zero_of_rawDivergenceFree
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (hDiv : H3SpectralFinRawDivergenceFree (W s))
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.divergence
        spatial3
        (h3SpectralRealVelocityOfPath W s)
        x
      =
    0 := by
  rw [
    h3SpectralRealVelocityOfPath_divergence_eq_rawDivergenceFourierInv_re
  ]
  rw [h3SpectralFinRawDivergenceFourierInv_eq_zero hDiv]
  rfl

/-- The canonical selected restart reconstructed through the generic real path
is pointwise incompressible throughout the full closed restart interval. -/
theorem h3PreterminalTailCanonicalSelectedRestart_realVelocity_divergence_eq_zero
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs0 : 0 ≤ s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν E)
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.divergence
        spatial3
        (h3SpectralRealVelocityOfPath
          (h3PreterminalTailCanonicalSelectedRestart
            hν hNS ht hE hTail)
          s)
        x
      =
    0 := by
  exact
    h3SpectralRealVelocityOfPath_divergence_eq_zero_of_rawDivergenceFree
      (h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail)
      s
      (h3PreterminalTailCanonicalSelectedRestart_rawDivergenceFree
        hν hNS ht hE hTail hs0 hsR)
      x

/-- The named restart-radius selected real velocity launched from the canonical
preterminal anchor is pointwise incompressible on the same interval. -/
theorem h3PreterminalTailCanonicalSelectedRealVelocity_divergence_eq_zero
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs0 : 0 ≤ s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν E)
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.divergence
        spatial3
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν
          (h3PreterminalTailCanonicalAnchorSpectralState
            hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          s)
        x
      =
    0 := by
  simpa only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
    h3PreterminalTailCanonicalSelectedRestart
  ] using
    h3PreterminalTailCanonicalSelectedRestart_realVelocity_divergence_eq_zero
      hν hNS ht hE hTail hs0 hsR x

end
end Euclidean
end Bridge
end PrimeTensor
