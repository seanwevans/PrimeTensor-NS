import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Normalized.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.BKM.Frequency.Forcing

/-!
# Relative escape against the canonical BKM endpoint

The H³ path and energy class provide kinetic anchor control on a later
tail. Together with a vorticity envelope they supply the actual-gradient
endpoint estimate with its canonical constant and H³ energy profile.
Consequently either relative-escape orientation forces the canonical
endpoint product to grow superlinearly in the original selected index.
This does not assert that either relative-escape orientation occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem canonicalEndpoint_of_h3Path_on_tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) :
    ActualVelocityGradientLogBoundFrom
      u b T g (velocityH3EnergyAt u)
      (h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b))) := by
  have hbAbs : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  exact
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_kineticEnergyControlledFromAnchor
      hH3.navier_stokes hbAbs hg
      (h3EnergyProfileFrom_h3Path hH3 hbAbs)
      (bkmKineticEnergyControlledFromAnchor_of_h3Path_closed hH3 hClass hb)

/-- On a gradient-dominant relative-escape witness, the canonical BKM
endpoint product divided by the original selected index tends to infinity. -/
theorem positiveGrowth_gradientRatioEscape_canonicalEndpoint_normalized_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))) :
    Tendsto
      (fun n : ℕ =>
        (h3BKMCanonicalSelectedLogGradientConstant
            (Real.sqrt (velocityH3Energy0At u b)) *
          (1 + |g (τ (k n))|) *
          (1 + Real.log (velocityH3EnergyAt u (τ (k n))))) /
            ((k n : ℝ) + 1))
      atTop atTop := by
  exact positiveGrowth_gradientRatioEscape_endpoint_normalized_atTop
    hData hCancellation hkTop hRatio
    (canonicalEndpoint_of_h3Path_on_tail hH3 hClass hb hg)

/-- On a curl-dominant relative-escape witness, the same canonical BKM
endpoint product has divergent original-index normalized rate. -/
theorem positiveGrowth_curlRatioEscape_canonicalEndpoint_normalized_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))) :
    Tendsto
      (fun n : ℕ =>
        (h3BKMCanonicalSelectedLogGradientConstant
            (Real.sqrt (velocityH3Energy0At u b)) *
          (1 + |g (τ (k n))|) *
          (1 + Real.log (velocityH3EnergyAt u (τ (k n))))) /
            ((k n : ℝ) + 1))
      atTop atTop := by
  exact positiveGrowth_curlRatioEscape_endpoint_normalized_atTop
    hData hkTop hRatio
    (canonicalEndpoint_of_h3Path_on_tail hH3 hClass hb hg)

end

end Euclidean
end Bridge
end PrimeTensor
