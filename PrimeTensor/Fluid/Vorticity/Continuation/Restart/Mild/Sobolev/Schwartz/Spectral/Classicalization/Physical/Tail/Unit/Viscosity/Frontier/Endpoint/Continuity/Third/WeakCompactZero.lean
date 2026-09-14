import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.WeakCompact
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureOldFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Compact.Deweighting

/-!
# Ordered-third endpoint continuity: close compact weak H³ tests from zeroth L² continuity

The preceding density reductions leave the weak H³ branch at smooth compact
weighted spectral test states.

For a smooth compact frequency test `g`, define the reweighted test

    Ψ(ξ) = W₃(ξ) g(ξ).

Because `g` has compact support and is smooth, `Ψ` is again compactly
supported and smooth, hence Schwartz and in `L²`.

For a genuine encoded old velocity slice,

    U_j(q) = W₃ · û_j(q),

the complex `L²` pairing satisfies exactly

    ⟪U_j(q), g⟫ = ⟪û_j(q), W₃ g⟫.

The weight is real, so moving it from the conjugated first factor to the second
factor introduces no conjugation correction.

Thus strong continuity of the zeroth physical `L²` velocity coordinate,
transported through Plancherel, implies continuity of every smooth-compact
weighted spectral weak pairing.

The current zeroth route already supplies that strong continuity from the
old-pressure frontier.  Consequently, after this file the third-order branch
has only one independent scalar top-order input left:

    continuity of each weighted H³ spectral coordinate norm.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate ContDiff SchwartzMap

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdWeakCompactZero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Reweight a smooth compact spectral test by the exact H³ frequency weight. -/
def h3SmoothCompactReweighted
    (g : H3FourierPoint3 → ℂ) :
    H3FourierPoint3 → ℂ :=
  fun ξ =>
    (h3SobolevFrequencyWeight ξ : ℂ) * g ξ

/-- Reweighting by the H³ weight preserves compact support. -/
theorem h3SmoothCompactReweighted_hasCompactSupport
    {g : H3FourierPoint3 → ℂ}
    (hg : HasCompactSupport g) :
    HasCompactSupport (h3SmoothCompactReweighted g) := by
  apply hg.mono
  simpa [h3SmoothCompactReweighted] using
    (tsupport_mul_subset_right
      (f := fun ξ : H3FourierPoint3 =>
        (h3SobolevFrequencyWeight ξ : ℂ))
      (g := g))

/-- Reweighting by the H³ weight preserves smoothness. -/
theorem h3SmoothCompactReweighted_contDiff
    {g : H3FourierPoint3 → ℂ}
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (h3SmoothCompactReweighted g) := by
  unfold h3SmoothCompactReweighted

  have hW :
      ContDiff ℝ ∞
        (fun ξ : H3FourierPoint3 =>
          (h3SobolevFrequencyWeight ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      contDiff_h3SobolevFrequencyWeight

  exact hW.mul hg

/-- Canonical Schwartz representative of the reweighted compact test. -/
noncomputable def h3SmoothCompactReweightedSchwartz
    (g : H3FourierPoint3 → ℂ)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g) :
    SchwartzMap H3FourierPoint3 ℂ :=
  (h3SmoothCompactReweighted_hasCompactSupport hcompact).toSchwartzMap
    (h3SmoothCompactReweighted_contDiff hsmooth)

@[simp]
theorem h3SmoothCompactReweightedSchwartz_apply
    (g : H3FourierPoint3 → ℂ)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g)
    (ξ : H3FourierPoint3) :
    h3SmoothCompactReweightedSchwartz
        g hcompact hsmooth ξ
      =
    (h3SobolevFrequencyWeight ξ : ℂ) * g ξ :=
  rfl

/-- Exact pairing identity moving the real H³ weight from a genuine encoded
spectral state onto a fixed smooth compact test. -/
theorem inner_velocityH3SpectralScalarAt_smoothCompact_eq_baseFourier_reweighted
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {s : ℝ}
    {hInt : VelocityH3IntegrableAt u s}
    {hMeas : VelocityH3MeasurableAt u s}
    (hFourier :
      VelocityH3FourierCompatibleAt u s hInt hMeas)
    (j : Fin 3)
    (F : H3SpectralScalarState)
    (g : H3FourierPoint3 → ℂ)
    (hF :
      (F : H3FourierPoint3 → ℂ) =ᵐ[volume] g)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g) :
    inner ℂ
        (velocityH3SpectralScalarAt
          u s hInt hMeas hFourier j)
        F
      =
    inner ℂ
        (velocityH3BaseFourierAt
          u s hInt hMeas j)
        ((h3SmoothCompactReweightedSchwartz
          g hcompact hsmooth).toLp
            2 (volume : Measure H3FourierPoint3)) := by
  rw [MeasureTheory.L2.inner_def]
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  filter_upwards [
    velocityH3SpectralScalarAt_ae hFourier j,
    hF,
    SchwartzMap.coeFn_toLp
      (h3SmoothCompactReweightedSchwartz
        g hcompact hsmooth)
      2
      (volume : Measure H3FourierPoint3)
  ] with ξ hEncoded hTest hWeighted

  rw [hEncoded, hTest, hWeighted]

  unfold velocityH3WeightedBaseFourierRaw

  change
    inner ℂ
        ((h3SobolevFrequencyWeight ξ : ℂ) •
          velocityH3BaseFourierAt
            u s hInt hMeas j ξ)
        (g ξ)
      =
    inner ℂ
        (velocityH3BaseFourierAt
          u s hInt hMeas j ξ)
        ((h3SobolevFrequencyWeight ξ : ℂ) • g ξ)

  rw [inner_smul_left, inner_smul_right]
  simp

/-- The same pairing identity for the canonical old-tail elapsed spectral
state and zeroth Fourier jet. -/
theorem inner_h3PreterminalTailCanonicalSpectralStateOnElapsed_smoothCompact_eq_zeroFourier_reweighted
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3)
    (F : H3SpectralScalarState)
    (g : H3FourierPoint3 → ℂ)
    (hF :
      (F : H3FourierPoint3 → ℂ) =ᵐ[volume] g)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g) :
    inner ℂ
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q j)
        F
      =
    inner ℂ
        (h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q)
        ((h3SmoothCompactReweightedSchwartz
          g hcompact hsmooth).toLp
            2 (volume : Measure H3FourierPoint3)) := by
  unfold h3PreterminalTailCanonicalSpectralStateOnElapsed
  unfold h3PreterminalCanonicalFourierJetOnElapsed

  exact
    inner_velocityH3SpectralScalarAt_smoothCompact_eq_baseFourier_reweighted
      (h3PreterminalTailFourierCompatibleOnElapsed
        hNS ht hEnd hTail q)
      j F g hF hcompact hsmooth

/-- Strong zeroth physical `L²` continuity closes every smooth-compact weak
weighted H³ spectral pairing. -/
theorem h3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed_of_zeroContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hZero :
      H3PreterminalCanonicalL2ZeroContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j F hFcompact

  rcases hFcompact with
    ⟨g, hF, hcompact, hsmooth⟩

  let Ψ : H3FourierComplexL2 :=
    (h3SmoothCompactReweightedSchwartz
      g hcompact hsmooth).toLp
        2 (volume : Measure H3FourierPoint3)

  have hFourier :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q) := by
    have hPhysical :
        Continuous
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j)) :=
      hZero j

    exact
      continuous_h3ScalarFourierL2.comp
        hPhysical

  have hPair :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℂ
            (h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q)
            Ψ) := by
    exact
      hFourier.inner continuous_const

  have hRe :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          (inner ℂ
            (h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q)
            Ψ).re) :=
    Complex.continuous_re.comp
      hPair

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        (inner ℂ
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j)
          F).re)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        (inner ℂ
          (h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q)
          Ψ).re) := by
    funext q

    rw [
      inner_h3PreterminalTailCanonicalSpectralStateOnElapsed_smoothCompact_eq_zeroFourier_reweighted
        hNS ht hEnd hTail q j F g hF hcompact hsmooth
    ]

  rw [hEq]

  exact hRe

/-- The local old-pressure frontier supplies zeroth continuity and therefore
closes smooth-compact weak H³ spectral continuity. -/
theorem h3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed_of_oldPressure
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOld :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
      hNS ht hEnd hTail := by
  have hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed_of_oldPressure
      hNS ht hEnd hE hTail hOld

  have hLipschitz :
      H3PreterminalCanonicalL2ZeroLipschitzOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_of_allDivergenceFreePressureDefect
      hNS ht htau hEnd hE hTail hPressure

  have hZero :
      H3PreterminalCanonicalL2ZeroContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalL2ZeroContinuousOnElapsed_of_lipschitz
      hNS ht hEnd hTail hLipschitz

  exact
    h3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed_of_zeroContinuous
      hNS ht hEnd hTail hZero

/-- Radius-wide scalar coordinate-norm continuity frontier.  This is the only
remaining independent third-order topology input after the weak closure above. -/
def H3PreterminalTailUnitViscositySpectralCoordinateNormContinuityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
          hNS ht hEnd hTail

/-- Global scalar spectral-coordinate norm continuity frontier. -/
def H3PreterminalTailUnitViscositySpectralCoordinateNormContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscositySpectralCoordinateNormContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Old-pressure control closes the weak half of the weighted H³ spectral
frontier; scalar coordinate-norm continuity supplies the remaining strong
topology input. -/
theorem h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier_of_oldPressure_of_coordinateNorm
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hNorm :
      H3PreterminalTailUnitViscositySpectralCoordinateNormContinuityFrontier) :
    H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier := by
  intro E hE u T t hNS ht hTail
  intro q hqPos hEnd

  have hOldLocal :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail :=
    hOld E hE u T t hNS ht hTail q hqPos hEnd

  have hCompact :
      H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed_of_oldPressure
      hNS ht hqPos hEnd hE hTail hOldLocal

  have hWeak :
      H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_of_smoothCompact
      hNS ht hEnd hE hTail hCompact

  exact
    ⟨
      hWeak,
      hNorm E hE u T t hNS ht hTail q hqPos hEnd
    ⟩

/-- Current continuation theorem with the third-order topology reduced to
scalar spectral-coordinate norm continuity.  The two remaining independent
analytic fronts are now:

* old preterminal pressure-gradient mass;
* continuity of the weighted H³ spectral coordinate norms.
-/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralCoordinateNormClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hNorm :
      H3PreterminalTailUnitViscositySpectralCoordinateNormContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralWeakNormClosed
      hOld
      (h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier_of_oldPressure_of_coordinateNorm
        hOld hNorm)

end

end Euclidean
end Bridge
end PrimeTensor
