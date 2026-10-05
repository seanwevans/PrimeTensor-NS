import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Raw
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Split
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalLowerWeightedDerivativeClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## The bounded bridge multiplier q / (1 + q²) -/

noncomputable def h3LowerWeightBridgeMultiplier
    (ξ : H3FourierPoint3) : ℂ :=
  ((h3FourierGradientSquare ξ
      /
    (1 + h3FourierGradientSquare ξ ^ 2) : ℝ) : ℂ)

theorem h3LowerWeightBridgeMultiplier_aestronglyMeasurable :
    AEStronglyMeasurable
      h3LowerWeightBridgeMultiplier
      (volume : Measure H3FourierPoint3) := by

  have hQ :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ) := by
    unfold h3FourierGradientSquare
    fun_prop

  have hDen :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          1 + h3FourierGradientSquare ξ ^ 2) :=
    continuous_const.add
      (hQ.pow 2)

  have hReal :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          h3FourierGradientSquare ξ
            /
          (1 + h3FourierGradientSquare ξ ^ 2)) :=
    hQ.div
      hDen
      (fun ξ => by
        have hq :
            0 <= h3FourierGradientSquare ξ :=
          h3FourierGradientSquare_nonneg ξ
        nlinarith [sq_nonneg (h3FourierGradientSquare ξ)])

  unfold h3LowerWeightBridgeMultiplier

  exact
    (Complex.continuous_ofReal.comp hReal).aestronglyMeasurable

theorem norm_h3LowerWeightBridgeMultiplier_le_one
    (ξ : H3FourierPoint3) :
    ‖h3LowerWeightBridgeMultiplier ξ‖ <= 1 := by

  let q : ℝ :=
    h3FourierGradientSquare ξ

  have hq : 0 <= q := by
    dsimp only [q]
    exact h3FourierGradientSquare_nonneg ξ

  have hDen : 0 < 1 + q ^ 2 := by
    nlinarith [sq_nonneg q]

  have hFracNonneg :
      0 <= q / (1 + q ^ 2) :=
    div_nonneg hq hDen.le

  have hFracLe :
      q / (1 + q ^ 2) <= 1 := by
    apply (div_le_iff₀ hDen).2
    nlinarith [sq_nonneg (q - (1 / 2 : ℝ))]

  unfold h3LowerWeightBridgeMultiplier

  change
    ‖((q / (1 + q ^ 2) : ℝ) : ℂ)‖ <= 1

  rw [
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hFracNonneg
  ]

  exact hFracLe

noncomputable def h3LowerWeightBridgeFunction
    (f : H3FourierComplexL2)
    (ξ : H3FourierPoint3) : ℂ :=
  h3LowerWeightBridgeMultiplier ξ * f ξ

theorem h3LowerWeightBridgeFunction_memLp
    (f : H3FourierComplexL2) :
    MemLp
      (h3LowerWeightBridgeFunction f)
      2
      (volume : Measure H3FourierPoint3) := by

  apply
    (MeasureTheory.Lp.memLp f).of_le_mul
      (c := 1)
      (
        h3LowerWeightBridgeMultiplier_aestronglyMeasurable.mul
          (MeasureTheory.Lp.aestronglyMeasurable f)
      )

  filter_upwards with ξ

  change
    ‖h3LowerWeightBridgeMultiplier ξ * f ξ‖ <= 1 * ‖f ξ‖

  rw [norm_mul, one_mul]

  simpa only [one_mul] using
    (
      mul_le_mul_of_nonneg_right
        (norm_h3LowerWeightBridgeMultiplier_le_one ξ)
        (norm_nonneg (f ξ))
    )

noncomputable def h3LowerWeightBridgeL2
    (f : H3FourierComplexL2) :
    H3FourierComplexL2 :=
  (h3LowerWeightBridgeFunction_memLp f).toLp
    (h3LowerWeightBridgeFunction f)

theorem h3LowerWeightBridgeL2_ae
    (f : H3FourierComplexL2) :
    ((h3LowerWeightBridgeL2 f : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3LowerWeightBridgeFunction f := by

  unfold h3LowerWeightBridgeL2
  exact MemLp.coeFn_toLp (h3LowerWeightBridgeFunction_memLp f)

theorem h3LowerWeightBridgeL2_add
    (f g : H3FourierComplexL2) :
    h3LowerWeightBridgeL2 (f + g)
      =
    h3LowerWeightBridgeL2 f + h3LowerWeightBridgeL2 g := by

  rw [Lp.ext_iff]

  filter_upwards [
    h3LowerWeightBridgeL2_ae (f + g),
    h3LowerWeightBridgeL2_ae f,
    h3LowerWeightBridgeL2_ae g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (h3LowerWeightBridgeL2 f) (h3LowerWeightBridgeL2 g)
  ] with ξ hfg hf hg hAdd hOutAdd

  rw [hfg, hOutAdd]
  simp only [Pi.add_apply]
  rw [hf, hg]
  unfold h3LowerWeightBridgeFunction
  rw [hAdd]
  simp only [Pi.add_apply]
  ring

theorem h3LowerWeightBridgeL2_smul_real
    (c : ℝ)
    (f : H3FourierComplexL2) :
    h3LowerWeightBridgeL2 (c • f)
      =
    c • h3LowerWeightBridgeL2 f := by

  rw [Lp.ext_iff]

  filter_upwards [
    h3LowerWeightBridgeL2_ae (c • f),
    h3LowerWeightBridgeL2_ae f,
    Lp.coeFn_smul c f,
    Lp.coeFn_smul c (h3LowerWeightBridgeL2 f)
  ] with ξ hcf hf hInSmul hOutSmul

  rw [hcf, hOutSmul]
  simp only [Pi.smul_apply]
  rw [hf]
  unfold h3LowerWeightBridgeFunction
  rw [hInSmul]
  simp only [Pi.smul_apply, Complex.real_smul]
  ring

@[simp]
theorem h3LowerWeightBridgeL2_zero :
    h3LowerWeightBridgeL2 (0 : H3FourierComplexL2)
      =
    0 := by

  simpa using
    (
      h3LowerWeightBridgeL2_smul_real
        0
        (0 : H3FourierComplexL2)
    )

noncomputable def h3LowerWeightBridgeRealLinearMap :
    H3FourierComplexL2 →ₗ[ℝ] H3FourierComplexL2 where
  toFun := h3LowerWeightBridgeL2
  map_add' := h3LowerWeightBridgeL2_add
  map_smul' := by
    intro c f
    exact h3LowerWeightBridgeL2_smul_real c f

@[simp]
theorem h3LowerWeightBridgeRealLinearMap_apply
    (f : H3FourierComplexL2) :
    h3LowerWeightBridgeRealLinearMap f = h3LowerWeightBridgeL2 f := by
  rfl

theorem norm_h3LowerWeightBridgeL2_le
    (f : H3FourierComplexL2) :
    ‖h3LowerWeightBridgeL2 f‖ <= ‖f‖ := by

  have h : ‖h3LowerWeightBridgeL2 f‖ <= 1 * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [h3LowerWeightBridgeL2_ae f] with ξ hξ
    rw [hξ]
    unfold h3LowerWeightBridgeFunction
    rw [norm_mul]
    exact
      mul_le_mul_of_nonneg_right
        (norm_h3LowerWeightBridgeMultiplier_le_one ξ)
        (norm_nonneg (f ξ))

  simpa only [one_mul] using h

noncomputable def h3LowerWeightBridgeRealCLM :
    H3FourierComplexL2 →L[ℝ] H3FourierComplexL2 :=
  h3LowerWeightBridgeRealLinearMap.mkContinuous
    1
    (fun f => by
      change
        ‖h3LowerWeightBridgeL2 f‖
          ≤
        1 * ‖f‖
      simpa only [one_mul] using
        norm_h3LowerWeightBridgeL2_le f)

@[simp]
theorem h3LowerWeightBridgeRealCLM_apply
    (f : H3FourierComplexL2) :
    h3LowerWeightBridgeRealCLM f = h3LowerWeightBridgeL2 f := by
  rfl

/-! ## Raw and lower RHS representatives -/

theorem h3TerminalPhysicalRawPDERHSFourierL2At_ae_unitPDE
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (((h3TerminalPhysicalRawPDERHSFourierL2At hH3 hClass ht j : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      -(h3FourierGradientSquare ξ : ℂ)
          * h3SpectralScalarRawFourierL2 (U j) ξ
        - h3RawFinLerayOuterProductDivergence U U j ξ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let L : H3FourierComplexL2 :=
    h3SpectralScalarLaplacianRawFourierL2 (U j)
  let F : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceFourierL2 U U j

  have hSub := Lp.coeFn_sub L F

  have hLap :
      ((L : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ)
          * h3SpectralScalarRawFourierL2 (U j) ξ) := by
    dsimp only [L]
    exact h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw (U j)

  have hForcing :
      ((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergence U U j := by
    dsimp only [F]
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact
      MemLp.coeFn_toLp
        (h3RawFinLerayOuterProductDivergence_memLp2 U U j)

  unfold h3TerminalPhysicalRawPDERHSFourierL2At
  change
    (((L - F : H3FourierComplexL2) : H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      -(h3FourierGradientSquare ξ : ℂ)
          * h3SpectralScalarRawFourierL2 (U j) ξ
        - h3RawFinLerayOuterProductDivergence U U j ξ)

  filter_upwards [hSub, hLap, hForcing] with ξ hSubξ hLapξ hFξ
  rw [hSubξ]
  simp only [Pi.sub_apply]
  rw [hLapξ, hFξ]

theorem h3TerminalPhysicalLowerWeightedPDERHSFourierL2At_ae_unitPDE
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (((h3TerminalPhysicalLowerWeightedPDERHSFourierL2At hH3 hClass ht j : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      -((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          * h3SpectralScalarRawFourierL2 (U j) ξ
        - ((h3FourierGradientSquare ξ : ℝ) : ℂ)
          * h3RawFinLerayOuterProductDivergence U U j ξ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let X2 : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At hH3 hClass ht j
  let F1 : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At hH3 hClass ht j

  have hSub := Lp.coeFn_sub (-X2) F1
  have hNeg := Lp.coeFn_neg X2

  have hX2 :
      ((X2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          * h3SpectralScalarRawFourierL2 (U j) ξ) := by
    dsimp only [X2, U]
    exact
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae_gradientSquare
        hH3 hClass ht j

  have hF1 :
      ((F1 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ : ℝ) : ℂ)
          * h3RawFinLerayOuterProductDivergence U U j ξ) := by
    dsimp only [F1, U]
    exact
      h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_ae
        hH3 hClass ht j

  unfold h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
  change
    (((-X2 - F1 : H3FourierComplexL2) : H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      -((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          * h3SpectralScalarRawFourierL2 (U j) ξ
        - ((h3FourierGradientSquare ξ : ℝ) : ℂ)
          * h3RawFinLerayOuterProductDivergence U U j ξ)

  filter_upwards [hSub, hNeg, hX2, hF1] with ξ hSubξ hNegξ hX2ξ hF1ξ
  rw [hSubξ]
  simp only [Pi.sub_apply]
  rw [hNegξ]
  simp only [Pi.neg_apply]
  rw [hX2ξ, hF1ξ]
  ring

/-! ## Exact bounded factorization identities -/

theorem h3LowerWeightBridge_raw_add_fourthRadial_eq_lowerWeightedVelocityAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3LowerWeightBridgeRealCLM
        (h3TerminalPhysicalRawVelocityFourierL2At hH3 hClass ht j
          + h3TerminalPhysicalTopDissipationFourthRadialComponentL2At hH3 hClass ht j)
      =
    h3TerminalPhysicalLowerWeightedVelocityFourierL2At hH3 hClass ht j := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let R0 : H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2 (U j)
  let X2 : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At hH3 hClass ht j

  have hRawAt :
      h3TerminalPhysicalRawVelocityFourierL2At hH3 hClass ht j = R0 := by
    rfl

  rw [hRawAt]
  change h3LowerWeightBridgeL2 (R0 + X2)
      = h3TerminalPhysicalLowerWeightedVelocityFourierL2At hH3 hClass ht j
  rw [Lp.ext_iff]

  have hBridge := h3LowerWeightBridgeL2_ae (R0 + X2)
  have hAdd := Lp.coeFn_add R0 X2

  have hX2 :
      ((X2 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) * R0 ξ) := by
    dsimp only [X2, R0, U]
    exact
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae_gradientSquare
        hH3 hClass ht j

  have hLower :
      (((h3TerminalPhysicalLowerWeightedVelocityFourierL2At hH3 hClass ht j :
          H3FourierComplexL2) : H3FourierPoint3 → ℂ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (h3FourierGradientSquare ξ : ℂ) * R0 ξ) := by
    dsimp only [R0, U]
    exact
      h3TerminalPhysicalLowerWeightedVelocityFourierL2At_ae
        hH3 hClass ht j

  filter_upwards [hBridge, hAdd, hX2, hLower]
    with ξ hBridgeξ hAddξ hX2ξ hLowerξ

  rw [hBridgeξ, hLowerξ]
  unfold h3LowerWeightBridgeFunction h3LowerWeightBridgeMultiplier
  rw [hAddξ]
  simp only [Pi.add_apply]
  rw [hX2ξ]

  let q : ℝ := h3FourierGradientSquare ξ
  let z : ℂ := R0 ξ

  have hDen : 1 + q ^ 2 ≠ 0 := by
    have hq : 0 <= q := by
      dsimp only [q]
      exact h3FourierGradientSquare_nonneg ξ
    nlinarith [sq_nonneg q]

  have hScalar : q / (1 + q ^ 2) * (1 + q ^ 2) = q := by
    field_simp [hDen]

  change
    ((q / (1 + q ^ 2) : ℝ) : ℂ)
        * (z + ((q ^ 2 : ℝ) : ℂ) * z)
      = (q : ℂ) * z

  calc
    ((q / (1 + q ^ 2) : ℝ) : ℂ)
          * (z + ((q ^ 2 : ℝ) : ℂ) * z)
        =
      (((q / (1 + q ^ 2)) * (1 + q ^ 2) : ℝ) : ℂ) * z := by
        push_cast
        ring
    _ = (q : ℂ) * z := by
      rw [hScalar]

theorem h3LowerWeightBridge_rawRHS_add_fourthRadialDerivative_eq_lowerWeightedRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (W : H3FourierComplexL2)
    (hW :
      HasDerivAt
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path hH3 hClass j)
        W t) :
    h3LowerWeightBridgeRealCLM
        (h3TerminalPhysicalRawPDERHSFourierL2At hH3 hClass ht j + W)
      =
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2At hH3 hClass ht j := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let Rraw : H3FourierComplexL2 :=
    h3TerminalPhysicalRawPDERHSFourierL2At hH3 hClass ht j

  change h3LowerWeightBridgeL2 (Rraw + W)
      = h3TerminalPhysicalLowerWeightedPDERHSFourierL2At hH3 hClass ht j
  rw [Lp.ext_iff]

  have hBridge := h3LowerWeightBridgeL2_ae (Rraw + W)
  have hAdd := Lp.coeFn_add Rraw W

  have hRaw :
      ((Rraw : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ)
            * h3SpectralScalarRawFourierL2 (U j) ξ
          - h3RawFinLerayOuterProductDivergence U U j ξ) := by
    dsimp only [Rraw, U]
    exact h3TerminalPhysicalRawPDERHSFourierL2At_ae_unitPDE hH3 hClass ht j

  have hWAE :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            * h3SpectralScalarRawFourierL2 (U j) ξ
          - ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            * h3RawFinLerayOuterProductDivergence U U j ξ) := by
    simpa only [htAbs, U] using
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_derivativeValue_ae_unitPDE
        hH3 hClass ht j W hW)

  have hLower :
      (((h3TerminalPhysicalLowerWeightedPDERHSFourierL2At hH3 hClass ht j :
          H3FourierComplexL2) : H3FourierPoint3 → ℂ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            * h3SpectralScalarRawFourierL2 (U j) ξ
          - ((h3FourierGradientSquare ξ : ℝ) : ℂ)
            * h3RawFinLerayOuterProductDivergence U U j ξ) := by
    simpa only [htAbs, U] using
      (h3TerminalPhysicalLowerWeightedPDERHSFourierL2At_ae_unitPDE
        hH3 hClass ht j)

  filter_upwards [hBridge, hAdd, hRaw, hWAE, hLower]
    with ξ hBridgeξ hAddξ hRawξ hWξ hLowerξ

  rw [hBridgeξ, hLowerξ]
  unfold h3LowerWeightBridgeFunction h3LowerWeightBridgeMultiplier
  rw [hAddξ]
  simp only [Pi.add_apply]
  rw [hRawξ, hWξ]

  let q : ℝ := h3FourierGradientSquare ξ
  let z : ℂ := h3SpectralScalarRawFourierL2 (U j) ξ
  let f : ℂ := h3RawFinLerayOuterProductDivergence U U j ξ

  have hDen : 1 + q ^ 2 ≠ 0 := by
    have hq : 0 <= q := by
      dsimp only [q]
      exact h3FourierGradientSquare_nonneg ξ
    nlinarith [sq_nonneg q]

  have hScalar : q / (1 + q ^ 2) * (1 + q ^ 2) = q := by
    field_simp [hDen]

  change
    ((q / (1 + q ^ 2) : ℝ) : ℂ)
        * ((-(q : ℂ) * z - f)
          + ((-(q ^ 3 : ℝ) : ℂ) * z - ((q ^ 2 : ℝ) : ℂ) * f))
      = -((q ^ 2 : ℝ) : ℂ) * z - (q : ℂ) * f

  calc
    ((q / (1 + q ^ 2) : ℝ) : ℂ)
          * ((-(q : ℂ) * z - f)
            + ((-(q ^ 3 : ℝ) : ℂ) * z - ((q ^ 2 : ℝ) : ℂ) * f))
        =
      -((q / (1 + q ^ 2) : ℝ) : ℂ)
        * (((1 + q ^ 2 : ℝ) : ℂ) * ((q : ℂ) * z + f)) := by
          push_cast
          ring
    _ =
      -(((q / (1 + q ^ 2)) * (1 + q ^ 2) : ℝ) : ℂ)
        * ((q : ℂ) * z + f) := by
          push_cast
          ring
    _ = -(q : ℂ) * ((q : ℂ) * z + f) := by
      rw [hScalar]
    _ = -((q ^ 2 : ℝ) : ℂ) * z - (q : ℂ) * f := by
      push_cast
      ring

/-! ## Global path factorization -/

theorem h3TerminalPhysicalLowerWeightedVelocityFourierL2Path_eq_bridge_raw_add_fourthRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    h3TerminalPhysicalLowerWeightedVelocityFourierL2Path hH3 hClass j
      =
    fun t : ℝ =>
      h3LowerWeightBridgeRealCLM
        (h3TerminalPhysicalRawVelocityFourierL2Path hH3 hClass j t
          + h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path hH3 hClass j t) := by

  funext t
  by_cases ht : t ∈ Set.Ioo a T

  · rw [
      h3TerminalPhysicalLowerWeightedVelocityFourierL2Path_eq hH3 hClass ht j,
      h3TerminalPhysicalRawVelocityFourierL2Path_eq hH3 hClass ht j,
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq hH3 hClass ht j
    ]
    exact
      (h3LowerWeightBridge_raw_add_fourthRadial_eq_lowerWeightedVelocityAt
        hH3 hClass ht j).symm

  · unfold
      h3TerminalPhysicalLowerWeightedVelocityFourierL2Path
      h3TerminalPhysicalRawVelocityFourierL2Path
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
    simp [ht, h3LowerWeightBridgeL2_zero]

/-! ## Close the frontier -/

theorem h3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint hH3 hClass := by

  intro t ht j

  have hRaw :=
    h3TerminalPhysicalRawVelocityFourierL2Path_hasDerivAt_unitPDE
      hH3 hClass ht j

  obtain ⟨W, hWAll⟩ :=
    h3TerminalPhysicalTopDissipationGlobalFourthRadialHilbertDerivativeAtEndpoint_closed
      hH3 hClass t ht

  have hW := hWAll j
  have hSum := hRaw.add hW

  have hMapped :=
    (h3LowerWeightBridgeRealCLM).hasFDerivAt.comp_hasDerivAt t hSum

  have hPath :=
    h3TerminalPhysicalLowerWeightedVelocityFourierL2Path_eq_bridge_raw_add_fourthRadial
      hH3 hClass j

  have hValue :=
    h3LowerWeightBridge_rawRHS_add_fourthRadialDerivative_eq_lowerWeightedRHS
      hH3 hClass ht j (W j) hW

  rw [hPath]
  rw [← hValue]
  simpa only [
    Function.comp_def,
    Pi.add_apply
  ] using hMapped

/-! ## Unconditional temporal/dissipative obstruction -/

theorem exists_fixed_thirdRadialForcing_temporalDissipativePDEChannel_cofinallyUnbounded_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy : H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      ((∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < (‖deriv
              (h3TerminalPhysicalLowerWeightedVelocityFourierL2Path hH3 hClass j₀)
              t‖ : ℝ) ^ 2)
        ∨
        (∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < h3TerminalPhysicalTopDissipation3Path hClass t)
        ∨
        (∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < (‖deriv
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path hH3 hClass j₀)
              t‖ : ℝ) ^ 2)
        ∨
        (∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < (‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
              hH3 hClass j₀ t‖ : ℝ) ^ 2)) := by

  exact
    exists_fixed_thirdRadialForcing_temporalDissipativePDEChannel_cofinallyUnbounded_of_lowerWeightedDerivative_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass
      (h3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint_closed hH3 hClass)
      hPhysical hCauchy hNoExtension

theorem smoothContinuationExtension_or_fixed_thirdRadialForcing_temporalDissipativePDEChannel_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy : H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
      ∨
    (∃ j₀ : Fin 3,
      ((∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < (‖deriv
              (h3TerminalPhysicalLowerWeightedVelocityFourierL2Path hH3 hClass j₀)
              t‖ : ℝ) ^ 2)
        ∨
        (∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < h3TerminalPhysicalTopDissipation3Path hClass t)
        ∨
        (∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < (‖deriv
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path hH3 hClass j₀)
              t‖ : ℝ) ^ 2)
        ∨
        (∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            M < (‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
              hH3 hClass j₀ t‖ : ℝ) ^ 2))) := by

  exact
    smoothContinuationExtension_or_fixed_thirdRadialForcing_temporalDissipativePDEChannel_cofinallyUnbounded_of_lowerWeightedDerivative
      hH3 hClass
      (h3TerminalPhysicalLowerWeightedHilbertDerivativeAtEndpoint_closed hH3 hClass)
      hPhysical hCauchy

end
end Euclidean
end Bridge
end PrimeTensor
