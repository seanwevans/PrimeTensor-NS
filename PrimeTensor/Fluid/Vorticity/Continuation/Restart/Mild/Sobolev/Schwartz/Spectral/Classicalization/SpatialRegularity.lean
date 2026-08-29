import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentThirdSeed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Bridge

/-!
# Classicalization: all finite spatial derivatives of the selected mild path

The Fréchet endpoint induction now gives every natural raw Fourier moment of
the selected positive-time mild state.  This file converts that moment
information into classical spatial regularity.

For a fixed positive selected time `s`:

* moments `0` and `1` come directly from the ambient H³ state;
* moment `2` comes from the already-compiled positive-time second-moment
  estimate;
* every moment `n ≥ 3` comes from the generic natural slab theorem.

Therefore every ordinary natural Fourier moment

    ∫ ‖ξ‖^n |Ŵ(s,ξ)| dξ

is finite.  Mathlib's Fourier differentiability theorem then upgrades the
ordinary inverse-Fourier representative to `ContDiff ℝ m` for every finite
natural order `m`.

The representative is deliberately the same inverse-Fourier representative
already used by the H³ real `C¹` bridge.  Consequently all existing almost
everywhere decoder-compatibility theorems remain available without any new
identification argument.

This is the spatial regularity half of the classicalization frontier.  The
remaining work is time/mixed regularity, the pointwise Navier--Stokes/pressure
identity, and gluing to the old preterminal solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSpatialRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SchwartzClassicalizationSpatialRegularity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-!
## Every natural raw Fourier moment at positive selected time
-/

/-- Every natural raw Fourier moment of a selected positive-time mild
coordinate is integrable.

This is the direct bridge from the completed generic moment induction to
classical Fourier reconstruction. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
    {ν A s : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s i) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  by_cases hn3 : 3 ≤ n

  · obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
      h3SelectedMomentSlab_nat_ge_three
        (a := s)
        (t := s)
        n hn3
        hν U₀ hA hU₀
        hs le_rfl hsR

    unfold H3SelectedMomentSlab at hSlab
    rcases hSlab with ⟨_hState0, _hDuhamel0, _hB00, hData⟩

    have hAt :=
      hData s ⟨le_rfl, le_rfl⟩ i

    dsimp only at hAt

    have hGeneric :
        H3RawFourierMomentIntegrable
          (n : ℝ)
          (W s i) :=
      hAt.1

    unfold H3RawFourierMomentIntegrable at hGeneric
    dsimp only [W] at hGeneric ⊢

    simpa only [h3FourierMomentWeight_natCast] using hGeneric

  · have hnlt3 : n < 3 := by
      omega

    by_cases hn1 : n ≤ 1

    · exact
        h3SpectralScalarRawFourier_moment_integrable_one
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s i)
          n hn1

    · have hn2 : n = 2 := by
        omega

      subst n

      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
          hν U₀ hA hU₀ hs hsR i

/-!
## Arbitrary finite spatial differentiability
-/

/-- The canonical inverse-Fourier representative of a selected positive-time
mild coordinate is spatially `C^m` for every natural `m`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
    {ν A s : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ContDiff ℝ m
      (h3SpectralScalarC1Representative
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s i)) := by
  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀ s i

  have hFourier :
      ContDiff ℝ m
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier G)) := by
    apply Real.contDiff_fourier
    intro n _hn
    dsimp only [G]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        n hν U₀ hA hU₀ hs hsR i

  have hEq :
      h3SpectralScalarC1Representative G
        =
      fun x : H3FourierPoint3 =>
        FourierTransform.fourier
          (h3SpectralScalarRawFourier G) (-x) := by
    funext x
    unfold h3SpectralScalarC1Representative
    exact
      Real.fourierInv_eq_fourier_neg
        (h3SpectralScalarRawFourier G) x

  change
    ContDiff ℝ m
      (h3SpectralScalarC1Representative G)

  rw [hEq]
  exact hFourier.comp (by fun_prop)

/-- Taking real parts preserves every finite spatial differentiability order. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1Representative_contDiff_nat
    {ν A s : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ContDiff ℝ m
      (h3SpectralScalarRealC1Representative
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s i)) := by
  unfold h3SpectralScalarRealC1Representative

  simpa [Function.comp_def] using
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
      m hν U₀ hA hU₀ hs hsR i).continuousLinearMap_comp
        Complex.reCLM

/-- Transport to the project's `Point3` carrier preserves every finite
spatial differentiability order. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
    {ν A s : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ContDiff ℝ m
      (h3SpectralScalarRealC1RepresentativeOnPoint3
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s i)) := by
  have hToLp :
      ContDiff ℝ m
        (WithLp.toLp 2 : Point3 → H3FourierPoint3) := by
    exact PiLp.contDiff_toLp

  unfold h3SpectralScalarRealC1RepresentativeOnPoint3

  exact
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1Representative_contDiff_nat
      m hν U₀ hA hU₀ hs hsR i).comp hToLp

/-!
## Velocity-coordinate form and decoder compatibility
-/

/-- Every selected positive-time velocity coordinate has a real `Point3`
representative of arbitrary finite spatial differentiability order. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_contDiff_nat
    {ν A s : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ContDiff ℝ m
      (h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        i) := by
  change
    ContDiff ℝ m
      (h3SpectralScalarRealC1RepresentativeOnPoint3
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s i))

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_contDiff_nat
      m hν U₀ hA hU₀ hs hsR i

/-- In particular, the selected positive-time representative is spatially
`C³`, exactly the regularity level required by the classicalization frontier. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_contDiff_three
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ContDiff ℝ 3
      (h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        i) := by
  simpa using
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_contDiff_nat
      3 hν U₀ hA hU₀ hs hsR i)

/-- The same spatially smooth representative remains exactly the a.e.
representative of the canonical real decoder used by the classicalization
frontier. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        i
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s)
          i) : H3ScalarL2) :
      Point3 → ℝ) := by
  exact
    h3SpectralVelocityRealC1RepresentativeOnPoint3_ae_eq_decodeRealL2
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ s)
      i

end
end Euclidean
end Bridge
end PrimeTensor
