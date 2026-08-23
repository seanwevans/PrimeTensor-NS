import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayRetardedIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.PathRealExtension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Continuous-linear packaging of spectral H³ heat evolution

The spectral heat action is already known to be contractive and strongly
continuous in nonnegative time.  This file packages the fixed-time action as a
real continuous linear map.

That is the exact algebraic form needed to commute the heat semigroup through
Bochner interval integrals in the Duhamel restart identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SpectralHeatCLM
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Scalar weighted Fourier heat linearity -/

theorem h3SpectralScalarHeatApplyNN_add
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (F G : H3SpectralScalarState) :
    h3SpectralScalarHeatApplyNN ν hν t (F + G)
      =
    h3SpectralScalarHeatApplyNN ν hν t F +
      h3SpectralScalarHeatApplyNN ν hν t G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3HeatFrequencyApplyNN_coeFn ν hν t (F + G),
    h3HeatFrequencyApplyNN_coeFn ν hν t F,
    h3HeatFrequencyApplyNN_coeFn ν hν t G,
    MeasureTheory.Lp.coeFn_add F G,
    MeasureTheory.Lp.coeFn_add
      (h3SpectralScalarHeatApplyNN ν hν t F)
      (h3SpectralScalarHeatApplyNN ν hν t G)
  ] with ξ hFG hF hG hIn hOut
  simp only [Pi.add_apply] at hIn hOut
  rw [hOut]
  unfold h3SpectralScalarHeatApplyNN
  rw [hFG, hF, hG, hIn]
  ring

theorem h3SpectralScalarHeatApplyNN_smul_real
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (c : ℝ)
    (F : H3SpectralScalarState) :
    h3SpectralScalarHeatApplyNN ν hν t (c • F)
      =
    c • h3SpectralScalarHeatApplyNN ν hν t F := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3HeatFrequencyApplyNN_coeFn ν hν t (c • F),
    h3HeatFrequencyApplyNN_coeFn ν hν t F,
    MeasureTheory.Lp.coeFn_smul c F,
    MeasureTheory.Lp.coeFn_smul c
      (h3SpectralScalarHeatApplyNN ν hν t F)
  ] with ξ hLeft hF hIn hOut
  simp only [Pi.smul_apply] at hIn hOut
  rw [hOut]
  unfold h3SpectralScalarHeatApplyNN
  rw [hLeft, hF, hIn]
  rw [Complex.real_smul, Complex.real_smul]
  ring

/-- Fixed-time scalar spectral heat evolution as a real linear map. -/
noncomputable def h3SpectralScalarHeatLinearMap
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0) :
    H3SpectralScalarState →ₗ[ℝ]
      H3SpectralScalarState where
  toFun := h3SpectralScalarHeatApplyNN ν hν t
  map_add' := h3SpectralScalarHeatApplyNN_add ν hν t
  map_smul' := h3SpectralScalarHeatApplyNN_smul_real ν hν t

/-- Fixed-time scalar heat evolution as a contractive real continuous linear map. -/
noncomputable def h3SpectralScalarHeatCLM
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0) :
    H3SpectralScalarState →L[ℝ]
      H3SpectralScalarState :=
  (h3SpectralScalarHeatLinearMap ν hν t).mkContinuous
    1
    (fun F => by
      change
        ‖h3SpectralScalarHeatApplyNN ν hν t F‖
          ≤
        1 * ‖F‖
      simpa using
        norm_h3SpectralScalarHeatApplyNN_le
          ν hν t F)

@[simp]
theorem h3SpectralScalarHeatCLM_apply
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (F : H3SpectralScalarState) :
    h3SpectralScalarHeatCLM ν hν t F
      =
    h3SpectralScalarHeatApplyNN ν hν t F :=
  rfl

/-! ## Three-component velocity heat CLM -/

theorem h3SpectralVelocityHeatApplyNN_add
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U V : H3SpectralVelocityState) :
    h3SpectralVelocityHeatApplyNN ν hν t (U + V)
      =
    h3SpectralVelocityHeatApplyNN ν hν t U +
      h3SpectralVelocityHeatApplyNN ν hν t V := by
  funext j
  exact
    h3SpectralScalarHeatApplyNN_add
      ν hν t (U j) (V j)

theorem h3SpectralVelocityHeatApplyNN_smul_real
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (c : ℝ)
    (U : H3SpectralVelocityState) :
    h3SpectralVelocityHeatApplyNN ν hν t (c • U)
      =
    c • h3SpectralVelocityHeatApplyNN ν hν t U := by
  funext j
  exact
    h3SpectralScalarHeatApplyNN_smul_real
      ν hν t c (U j)

/-- Fixed-time spectral velocity heat evolution as a real linear map. -/
noncomputable def h3SpectralVelocityHeatLinearMap
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0) :
    H3SpectralVelocityState →ₗ[ℝ]
      H3SpectralVelocityState where
  toFun := h3SpectralVelocityHeatApplyNN ν hν t
  map_add' := h3SpectralVelocityHeatApplyNN_add ν hν t
  map_smul' := h3SpectralVelocityHeatApplyNN_smul_real ν hν t

/-- Fixed-time spectral velocity heat evolution as a contractive real CLM. -/
noncomputable def h3SpectralVelocityHeatCLM
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0) :
    H3SpectralVelocityState →L[ℝ]
      H3SpectralVelocityState :=
  (h3SpectralVelocityHeatLinearMap ν hν t).mkContinuous
    1
    (fun U => by
      change
        ‖h3SpectralVelocityHeatApplyNN ν hν t U‖
          ≤
        1 * ‖U‖
      simpa using
        norm_h3SpectralVelocityHeatApplyNN_le
          ν hν t U)

@[simp]
theorem h3SpectralVelocityHeatCLM_apply
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState) :
    h3SpectralVelocityHeatCLM ν hν t U
      =
    h3SpectralVelocityHeatApplyNN ν hν t U :=
  rfl

theorem norm_h3SpectralVelocityHeatCLM_apply_le
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralVelocityState) :
    ‖h3SpectralVelocityHeatCLM ν hν t U‖
      ≤
    ‖U‖ := by
  exact
    norm_h3SpectralVelocityHeatApplyNN_le
      ν hν t U

end

end Euclidean
end Bridge
end PrimeTensor
