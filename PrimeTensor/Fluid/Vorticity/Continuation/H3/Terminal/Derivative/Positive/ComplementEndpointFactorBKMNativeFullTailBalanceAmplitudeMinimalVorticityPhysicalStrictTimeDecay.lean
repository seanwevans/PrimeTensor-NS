import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalSpatialGeometry
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialDecayAutomatic

/-!
# Strict-time spatial decay of actual vorticity

The pure physical terminal sequence may escape spatially, so the next analytic
question is what H³ already forces at one fixed strict preterminal time.

The existing spatial-decay theorem shows that the complementary constituent
first derivative of every structural curl pair vanishes along every spatially
escaping sequence.  For a given curl component, the selected constituent of
one pair is exactly the complementary constituent of the swapped pair.  Hence
both first derivatives entering that curl vanish at infinity, and therefore so
does the actual curl component itself.

This file packages that observation first for the six structural curl pairs and
then for the fixed-coordinate actual-vorticity selector
`h3NativeActualVorticityComponentAt`.

No endpoint temporal modulus is assumed here.  This is a fixed-slice H³ fact.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalMinimalVorticityPhysicalStrictTimeDecay
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Swap the two constituent derivatives of one fixed curl component. -/
private def h3TerminalSwapCurlGradientPair :
    H3TerminalCurlGradientPair → H3TerminalCurlGradientPair
  | .x_yz => .x_zy
  | .x_zy => .x_yz
  | .y_zx => .y_xz
  | .y_xz => .y_zx
  | .z_xy => .z_yx
  | .z_yx => .z_xy

/-- The selected constituent derivative of a pair is the complementary
constituent derivative of the swapped pair. -/
@[simp] private theorem h3TerminalGradientFieldForPair_eq_complement_swap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    h3TerminalGradientFieldForPair u p t x =
      h3TerminalComplementGradientFieldForPair
        u (h3TerminalSwapCurlGradientPair p) t x := by
  cases p <;> rfl

/-- At every strict preterminal H³ time, every structural actual-vorticity
component vanishes along each sequence escaping to spatial infinity. -/
theorem h3TerminalCurlFieldForPair_strictTime_tendsto_zero_of_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (p : H3TerminalCurlGradientPair)
    {y : ℕ → Point3}
    (hEscape :
      Tendsto
        (fun n : ℕ => dist (0 : Point3) (y n))
        atTop atTop) :
    Tendsto
      (fun n : ℕ => h3TerminalCurlFieldForPair u p t (y n))
      atTop
      (𝓝 0) := by
  have hComplement :
      Tendsto
        (fun n : ℕ =>
          h3TerminalComplementGradientFieldForPair u p t (y n))
        atTop
        (𝓝 0) :=
    terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
      hH3 ht hEscape

  have hSwapComplement :
      Tendsto
        (fun n : ℕ =>
          h3TerminalComplementGradientFieldForPair
            u (h3TerminalSwapCurlGradientPair p) t (y n))
        atTop
        (𝓝 0) :=
    terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
      hH3 ht hEscape

  have hGradient :
      Tendsto
        (fun n : ℕ => h3TerminalGradientFieldForPair u p t (y n))
        atTop
        (𝓝 0) := by
    simpa only [h3TerminalGradientFieldForPair_eq_complement_swap] using
      hSwapComplement

  cases p with
  | x_yz =>
      simpa [
        h3TerminalCurlFieldForPair,
        h3TerminalGradientFieldForPair,
        h3TerminalGradientDerivativeAxisForPair,
        h3TerminalGradientComponentAxisForPair,
        h3TerminalComplementGradientFieldForPair,
        h3TerminalComplementDerivativeAxisForPair,
        h3TerminalComplementComponentAxisForPair,
        realVorticityX
      ] using hGradient.sub hComplement
  | x_zy =>
      simpa [
        h3TerminalCurlFieldForPair,
        h3TerminalGradientFieldForPair,
        h3TerminalGradientDerivativeAxisForPair,
        h3TerminalGradientComponentAxisForPair,
        h3TerminalComplementGradientFieldForPair,
        h3TerminalComplementDerivativeAxisForPair,
        h3TerminalComplementComponentAxisForPair,
        realVorticityX
      ] using hComplement.sub hGradient
  | y_zx =>
      simpa [
        h3TerminalCurlFieldForPair,
        h3TerminalGradientFieldForPair,
        h3TerminalGradientDerivativeAxisForPair,
        h3TerminalGradientComponentAxisForPair,
        h3TerminalComplementGradientFieldForPair,
        h3TerminalComplementDerivativeAxisForPair,
        h3TerminalComplementComponentAxisForPair,
        realVorticityY
      ] using hGradient.sub hComplement
  | y_xz =>
      simpa [
        h3TerminalCurlFieldForPair,
        h3TerminalGradientFieldForPair,
        h3TerminalGradientDerivativeAxisForPair,
        h3TerminalGradientComponentAxisForPair,
        h3TerminalComplementGradientFieldForPair,
        h3TerminalComplementDerivativeAxisForPair,
        h3TerminalComplementComponentAxisForPair,
        realVorticityY
      ] using hComplement.sub hGradient
  | z_xy =>
      simpa [
        h3TerminalCurlFieldForPair,
        h3TerminalGradientFieldForPair,
        h3TerminalGradientDerivativeAxisForPair,
        h3TerminalGradientComponentAxisForPair,
        h3TerminalComplementGradientFieldForPair,
        h3TerminalComplementDerivativeAxisForPair,
        h3TerminalComplementComponentAxisForPair,
        realVorticityZ
      ] using hGradient.sub hComplement
  | z_yx =>
      simpa [
        h3TerminalCurlFieldForPair,
        h3TerminalGradientFieldForPair,
        h3TerminalGradientDerivativeAxisForPair,
        h3TerminalGradientComponentAxisForPair,
        h3TerminalComplementGradientFieldForPair,
        h3TerminalComplementDerivativeAxisForPair,
        h3TerminalComplementComponentAxisForPair,
        realVorticityZ
      ] using hComplement.sub hGradient

/-- Fixed-coordinate formulation: at every strict preterminal H³ time, any of
the three actual-vorticity components tends to zero along spatial escape. -/
theorem h3NativeActualVorticityComponentAt_strictTime_tendsto_zero_of_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (i : Fin 3)
    {y : ℕ → Point3}
    (hEscape :
      Tendsto
        (fun n : ℕ => dist (0 : Point3) (y n))
        atTop atTop) :
    Tendsto
      (fun n : ℕ => h3NativeActualVorticityComponentAt u i t (y n))
      atTop
      (𝓝 0) := by
  fin_cases i
  · simpa [
      h3NativeActualVorticityComponentAt,
      h3TerminalCurlFieldForPair
    ] using
      (h3TerminalCurlFieldForPair_strictTime_tendsto_zero_of_h3Path
        hH3 ht H3TerminalCurlGradientPair.x_yz hEscape)
  · simpa [
      h3NativeActualVorticityComponentAt,
      h3TerminalCurlFieldForPair
    ] using
      (h3TerminalCurlFieldForPair_strictTime_tendsto_zero_of_h3Path
        hH3 ht H3TerminalCurlGradientPair.y_zx hEscape)
  · simpa [
      h3NativeActualVorticityComponentAt,
      h3TerminalCurlFieldForPair
    ] using
      (h3TerminalCurlFieldForPair_strictTime_tendsto_zero_of_h3Path
        hH3 ht H3TerminalCurlGradientPair.z_xy hEscape)

end

end Euclidean
end Bridge
end PrimeTensor
