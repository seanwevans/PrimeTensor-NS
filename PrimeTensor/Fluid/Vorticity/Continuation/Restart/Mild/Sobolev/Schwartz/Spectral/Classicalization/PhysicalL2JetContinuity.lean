import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralPathContinuity

/-!
# Classicalization: physical L² jet continuity implies spectral continuity

`SpectralPathContinuity` reduced continuity of the weighted spectral restart
state to strong continuity of every concrete H³ Fourier-jet coordinate.

The Fourier jet is itself only a representation change.  Each slot is obtained
from the corresponding physical `H3ScalarL2` slot by the exact Plancherel map

    h3ScalarFourierL2
      =
    Fourier ∘ complexify ∘ carrierTransport.

All three factors are continuous isometries / continuous linear maps:

* `h3ToFourierRealL2` is composition with the canonical volume-preserving
  `WithLp.ofLp` carrier map;
* `h3ComplexifyFourierL2` is induced by `Complex.ofRealCLM`;
* Mathlib's `Lp.fourierTransformₗᵢ` is a linear isometry.

This file packages that representation bridge and proves:

    physical H³ L²-jet continuity
      → Fourier H³-jet continuity
      → weighted spectral-state continuity.

Thus the remaining time-topology input can be stated directly in the physical
H³ `L²` jet carried by the old strong solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalL2JetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SchwartzClassicalizationPhysicalL2JetContinuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The canonical carrier transport `L²(Point3) → L²(H3FourierPoint3)` is
continuous. -/
theorem continuous_h3ToFourierRealL2 :
    Continuous h3ToFourierRealL2 := by
  unfold h3ToFourierRealL2

  exact
    (MeasureTheory.Lp.isometry_compMeasurePreserving
      (PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three))).continuous

/-- Real-to-complex embedding on Fourier-carrier `L²` is continuous. -/
theorem continuous_h3ComplexifyFourierL2 :
    Continuous h3ComplexifyFourierL2 := by
  let L :
      H3FourierRealL2 →L[ℝ] H3FourierComplexL2 :=
    ContinuousLinearMap.compLpL
      (2 : ENNReal)
      (volume : Measure H3FourierPoint3)
      Complex.ofRealCLM

  have hEq :
      h3ComplexifyFourierL2
        =
      (L : H3FourierRealL2 → H3FourierComplexL2) := by
    funext f

    apply MeasureTheory.Lp.ext

    filter_upwards
      [ContinuousLinearMap.coeFn_compLpL
        Complex.ofRealCLM f,
       Complex.ofRealCLM.coeFn_compLp f]
      with ξ hL hComp

    rw [hL]
    unfold h3ComplexifyFourierL2
    exact hComp

  rw [hEq]

  exact L.continuous

/-- The complete scalar Plancherel bridge used by the H³ spectral encoder is
continuous. -/
theorem continuous_h3ScalarFourierL2 :
    Continuous h3ScalarFourierL2 := by
  unfold h3ScalarFourierL2

  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).continuous.comp
      (continuous_h3ComplexifyFourierL2.comp
        continuous_h3ToFourierRealL2)

/-- One physical ordered H³ `L²` jet coordinate of the old solution as a
function of elapsed time. -/
noncomputable def h3PreterminalCanonicalL2JetOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (a : H3JetIndex)
    (q : Set.Icc (0 : ℝ) τ) :
    H3ScalarL2 :=
  velocityH3L2JetAt
    u
    (t + (q : ℝ))
    (h3PreterminalTailIntegrableOnElapsed
      hEnd hTail q)
    (h3PreterminalTailMeasurableOnElapsed
      hNS ht hEnd hTail q)
    a

/-- Strong continuity of every physical ordered H³ `L²` jet coordinate on the
elapsed overlap interval. -/
def H3PreterminalCanonicalL2JetContinuousOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ a : H3JetIndex,
    Continuous
      (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail a)

/-- The canonical Fourier-jet coordinate is exactly the scalar Plancherel
transform of the corresponding physical `L²` jet coordinate. -/
theorem h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (a : H3JetIndex)
    (q : Set.Icc (0 : ℝ) τ) :
    h3PreterminalCanonicalFourierJetOnElapsed
        hNS ht hEnd hTail a q
      =
    h3ScalarFourierL2
      (h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail a q) := by
  rfl

/-- Physical H³ `L²` jet continuity transports directly through Plancherel to
the concrete Fourier-jet continuity required by `SpectralPathContinuity`. -/
theorem h3PreterminalCanonicalFourierJetContinuousOnElapsed_of_l2Jet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hL2 :
      H3PreterminalCanonicalL2JetContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalFourierJetContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro a

  have hPhysical :
      Continuous
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail a) :=
    hL2 a

  have hFourier :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3ScalarFourierL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail a q)) :=
    continuous_h3ScalarFourierL2.comp
      hPhysical

  have hEq :
      h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail a
        =
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3ScalarFourierL2
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail a q)) := by
    funext q
    exact
      h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
        hNS ht hEnd hTail a q

  rw [hEq]

  exact hFourier

/-- Final physical-to-weighted continuity bridge.

Once the old strong solution's concrete H³ `L²` jet is continuous in elapsed
time, the exact canonical weighted spectral state used by the overlap witness
is continuous. -/
theorem continuous_h3PreterminalCanonicalSpectralStateOnElapsed_of_l2Jet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hL2 :
      H3PreterminalCanonicalL2JetContinuousOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3PreterminalCanonicalSpectralStateOnElapsed
          hNS ht hEnd
          (canonicalH3TailDataFrom_integrableOnElapsed
            hEnd hTail)
          q) := by
  exact
    continuous_h3PreterminalCanonicalSpectralStateOnElapsed_of_fourierJet
      hNS
      ht
      hEnd
      hTail
      (h3PreterminalCanonicalFourierJetContinuousOnElapsed_of_l2Jet
        hNS ht hEnd hTail hL2)

end
end Euclidean
end Bridge
end PrimeTensor
