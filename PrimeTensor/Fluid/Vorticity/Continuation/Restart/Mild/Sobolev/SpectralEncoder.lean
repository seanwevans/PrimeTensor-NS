import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FourierCompatibility

/-!
# Physical H³ snapshots as weighted spectral solver states

For velocity component `j`, the spectral solver state stores

    W₃(ξ) * û_j(ξ),

where `W₃² = 1 + q + q² + q³` and `q = (2π)² ‖ξ‖²`.
The weight is unbounded, so its `L²` admissibility is derived from the concrete
first-, second-, and third-order Fourier jet slots rather than from a bounded
multiplier argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SpectralEncoder (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Coordinate-symbol algebra -/

theorem h3FourierPoint3_norm_sq_eq_sum_coordinates
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 2 = ∑ i : PrimeTensor.Axis Depth.three, (ξ i) ^ 2 := by
  calc
    ‖ξ‖ ^ 2 = inner ℝ ξ ξ := by
      symm
      exact real_inner_self_eq_norm_sq ξ
    _ = ∑ i : PrimeTensor.Axis Depth.three, inner ℝ (ξ i) (ξ i) := by
      rw [PiLp.inner_apply]
    _ = ∑ i : PrimeTensor.Axis Depth.three, (ξ i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem norm_h3FourierDerivativeSymbol_sq
    (i : Fin 3) (ξ : H3FourierPoint3) :
    ‖h3FourierDerivativeSymbol i ξ‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (ξ (h3AxisOfFin3 i)) ^ 2 := by
  unfold h3FourierDerivativeSymbol
  simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [mul_pow, sq_abs]

theorem sum_norm_h3FourierDerivativeSymbol_sq
    (ξ : H3FourierPoint3) :
    (∑ i : Fin 3, ‖h3FourierDerivativeSymbol i ξ‖ ^ 2) =
      h3FourierGradientSquare ξ := by
  simp_rw [norm_h3FourierDerivativeSymbol_sq]
  rw [← Finset.mul_sum]
  rw [sum_fin3_comp_h3AxisOfFin3
    (fun i : PrimeTensor.Axis Depth.three => (ξ i) ^ 2)]
  unfold h3FourierGradientSquare
  rw [← h3FourierPoint3_norm_sq_eq_sum_coordinates ξ]

theorem sum_norm_h3FourierDerivativeSymbol2_sq
    (ξ : H3FourierPoint3) :
    (∑ i : Fin 3, ∑ k : Fin 3,
      ‖h3FourierDerivativeSymbol2 i k ξ‖ ^ 2) =
      (h3FourierGradientSquare ξ) ^ 2 := by
  simp_rw [h3FourierDerivativeSymbol2, norm_mul, mul_pow]
  rw [← Finset.sum_mul_sum]
  rw [sum_norm_h3FourierDerivativeSymbol_sq]
  ring

theorem sum_norm_h3FourierDerivativeSymbol3_sq
    (ξ : H3FourierPoint3) :
    (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      ‖h3FourierDerivativeSymbol3 i k l ξ‖ ^ 2) =
      (h3FourierGradientSquare ξ) ^ 3 := by
  simp_rw [h3FourierDerivativeSymbol3, norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.sum_mul_sum]
  rw [sum_norm_h3FourierDerivativeSymbol_sq]
  ring

theorem h3SobolevFrequencyWeight_sq (ξ : H3FourierPoint3) :
    (h3SobolevFrequencyWeight ξ) ^ 2 = h3SobolevFrequencyWeightSq ξ := by
  unfold h3SobolevFrequencyWeight
  rw [Real.sq_sqrt]
  exact le_trans (by norm_num) (one_le_h3SobolevFrequencyWeightSq ξ)

/-! ## Weighted and concrete component densities -/

def velocityH3WeightedBaseFourierRaw
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3SobolevFrequencyWeight ξ : ℂ) *
    velocityH3BaseFourierAt u t hInt hMeas j ξ

def velocityH3FourierComponentSquareDensity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
    + (∑ i : Fin 3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2)
    + (∑ i : Fin 3, ∑ k : Fin 3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2)
    + (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2)

theorem velocityH3WeightedBaseFourierRaw_norm_sq_eq_symbol_density
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖velocityH3WeightedBaseFourierRaw u t hInt hMeas j ξ‖ ^ 2 =
      ‖velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2
        + (∑ i : Fin 3,
            ‖h3FourierDerivativeSymbol i ξ *
                velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2)
        + (∑ i : Fin 3, ∑ k : Fin 3,
            ‖h3FourierDerivativeSymbol2 i k ξ *
                velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2)
        + (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖h3FourierDerivativeSymbol3 i k l ξ *
                velocityH3BaseFourierAt u t hInt hMeas j ξ‖ ^ 2) := by
  unfold velocityH3WeightedBaseFourierRaw
  have hW : 0 ≤ h3SobolevFrequencyWeight ξ :=
    le_of_lt (h3SobolevFrequencyWeight_pos ξ)
  simp_rw [norm_mul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW]
  rw [h3SobolevFrequencyWeight_sq]
  unfold h3SobolevFrequencyWeightSq
  rw [← sum_norm_h3FourierDerivativeSymbol3_sq ξ]
  rw [← sum_norm_h3FourierDerivativeSymbol2_sq ξ]
  rw [← sum_norm_h3FourierDerivativeSymbol_sq ξ]
  simp_rw [← Finset.sum_mul]
  ring

/-! ## Simultaneous finite compatibility -/

theorem velocityH3FourierCompatibleAt_orderOne_all_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ∀ᵐ ξ ∂volume, ∀ i : Fin 3,
      velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ =
        h3FourierDerivativeSymbol i ξ *
          velocityH3BaseFourierAt u t hInt hMeas j ξ := by
  change {ξ : H3FourierPoint3 | ∀ i : Fin 3,
    velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ =
      h3FourierDerivativeSymbol i ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ} ∈ ae volume
  rw [show {ξ : H3FourierPoint3 | ∀ i : Fin 3,
    velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ =
      h3FourierDerivativeSymbol i ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ} =
    ⋂ i : Fin 3, {ξ : H3FourierPoint3 |
      velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ =
        h3FourierDerivativeSymbol i ξ *
          velocityH3BaseFourierAt u t hInt hMeas j ξ} by ext ξ; simp]
  exact Filter.iInter_mem.mpr
    (fun i => velocityH3FourierCompatibleAt_orderOne hFourier j i)

theorem velocityH3FourierCompatibleAt_orderTwo_all_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ∀ᵐ ξ ∂volume, ∀ i k : Fin 3,
      velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ =
        h3FourierDerivativeSymbol2 i k ξ *
          velocityH3BaseFourierAt u t hInt hMeas j ξ := by
  change {ξ : H3FourierPoint3 | ∀ i k : Fin 3,
    velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ =
      h3FourierDerivativeSymbol2 i k ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ} ∈ ae volume
  rw [show {ξ : H3FourierPoint3 | ∀ i k : Fin 3,
    velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ =
      h3FourierDerivativeSymbol2 i k ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ} =
    ⋂ i : Fin 3, ⋂ k : Fin 3, {ξ : H3FourierPoint3 |
      velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ =
        h3FourierDerivativeSymbol2 i k ξ *
          velocityH3BaseFourierAt u t hInt hMeas j ξ} by ext ξ; simp]
  exact Filter.iInter_mem.mpr (fun i =>
    Filter.iInter_mem.mpr (fun k =>
      velocityH3FourierCompatibleAt_orderTwo hFourier j i k))

theorem velocityH3FourierCompatibleAt_orderThree_all_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ∀ᵐ ξ ∂volume, ∀ i k l : Fin 3,
      velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ =
        h3FourierDerivativeSymbol3 i k l ξ *
          velocityH3BaseFourierAt u t hInt hMeas j ξ := by
  change {ξ : H3FourierPoint3 | ∀ i k l : Fin 3,
    velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ =
      h3FourierDerivativeSymbol3 i k l ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ} ∈ ae volume
  rw [show {ξ : H3FourierPoint3 | ∀ i k l : Fin 3,
    velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ =
      h3FourierDerivativeSymbol3 i k l ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ} =
    ⋂ i : Fin 3, ⋂ k : Fin 3, ⋂ l : Fin 3, {ξ : H3FourierPoint3 |
      velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ =
        h3FourierDerivativeSymbol3 i k l ξ *
          velocityH3BaseFourierAt u t hInt hMeas j ξ} by ext ξ; simp]
  exact Filter.iInter_mem.mpr (fun i =>
    Filter.iInter_mem.mpr (fun k =>
      Filter.iInter_mem.mpr (fun l =>
        velocityH3FourierCompatibleAt_orderThree hFourier j i k l)))

theorem velocityH3WeightedBaseFourierRaw_norm_sq_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      ‖velocityH3WeightedBaseFourierRaw u t hInt hMeas j ξ‖ ^ 2) =ᵐ[volume]
      velocityH3FourierComponentSquareDensity u t hInt hMeas j := by
  have h1 := velocityH3FourierCompatibleAt_orderOne_all_ae hFourier j
  have h2 := velocityH3FourierCompatibleAt_orderTwo_all_ae hFourier j
  have h3 := velocityH3FourierCompatibleAt_orderThree_all_ae hFourier j
  filter_upwards [h1, h2, h3] with ξ h1ξ h2ξ h3ξ
  rw [velocityH3WeightedBaseFourierRaw_norm_sq_eq_symbol_density]
  unfold velocityH3FourierComponentSquareDensity
  simp_rw [h1ξ, h2ξ, h3ξ]
  simp only [velocityH3BaseFourierAt]

/-! ## L² admissibility and encoder -/

theorem velocityH3FourierComponentSquareDensity_integrable
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3) :
    Integrable (velocityH3FourierComponentSquareDensity u t hInt hMeas j) volume := by
  have h0 := (MeasureTheory.Lp.memLp
    (velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j))).norm.integrable_sq
  have h1 : Integrable (fun ξ : H3FourierPoint3 => ∑ i : Fin 3,
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2) volume := by
    apply integrable_finsetSum
    intro i hi
    exact (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i))).norm.integrable_sq
  have h2 : Integrable (fun ξ : H3FourierPoint3 => ∑ i : Fin 3, ∑ k : Fin 3,
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2) volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    exact (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k))).norm.integrable_sq
  have h3 : Integrable (fun ξ : H3FourierPoint3 => ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2) volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    exact (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l))).norm.integrable_sq
  unfold velocityH3FourierComponentSquareDensity
  exact ((h0.add h1).add h2).add h3

theorem velocityH3WeightedBaseFourierRaw_aestronglyMeasurable
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3) :
    AEStronglyMeasurable (velocityH3WeightedBaseFourierRaw u t hInt hMeas j) volume := by
  unfold velocityH3WeightedBaseFourierRaw
  have hW :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (h3SobolevFrequencyWeight ξ : ℂ))
        volume :=
    (Complex.continuous_ofReal.comp
      continuous_h3SobolevFrequencyWeight).aestronglyMeasurable
  exact
    hW.mul
      (MeasureTheory.Lp.aestronglyMeasurable
        (velocityH3BaseFourierAt u t hInt hMeas j))

theorem velocityH3WeightedBaseFourierRaw_memLp
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    MemLp (velocityH3WeightedBaseFourierRaw u t hInt hMeas j) 2 volume := by
  have hMeasRaw :=
    velocityH3WeightedBaseFourierRaw_aestronglyMeasurable u t hInt hMeas j
  rw [memLp_two_iff_integrable_sq_norm hMeasRaw]
  exact (velocityH3FourierComponentSquareDensity_integrable u t hInt hMeas j).congr
    (velocityH3WeightedBaseFourierRaw_norm_sq_ae hFourier j).symm

noncomputable def velocityH3SpectralScalarAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) : H3SpectralScalarState :=
  (velocityH3WeightedBaseFourierRaw_memLp hFourier j).toLp
    (velocityH3WeightedBaseFourierRaw u t hInt hMeas j)

noncomputable def velocityH3SpectralStateAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    H3SpectralVelocityState :=
  fun j => velocityH3SpectralScalarAt u t hInt hMeas hFourier j

theorem velocityH3SpectralScalarAt_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    (velocityH3SpectralScalarAt u t hInt hMeas hFourier j : H3FourierPoint3 → ℂ) =ᵐ[volume]
      velocityH3WeightedBaseFourierRaw u t hInt hMeas j := by
  exact MemLp.coeFn_toLp (velocityH3WeightedBaseFourierRaw_memLp hFourier j)

noncomputable def velocityH3SpectralStateAt_of_velocityLogSpatialC3
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hSpatial : VelocityLogSpatialC3 u)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) : H3SpectralVelocityState :=
  velocityH3SpectralStateAt u t hInt hMeas
    (velocityH3FourierCompatibleAt_of_velocityLogSpatialC3 hSpatial hInt hMeas)

/-! ## Exact spectral energy -/

def h3SpectralVelocitySquareEnergy (U : H3SpectralVelocityState) : ℝ :=
  ∑ j : Fin 3, ‖U j‖ ^ 2

theorem integral_velocityH3FourierComponentSquareDensity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3) :
    (∫ ξ : H3FourierPoint3,
      velocityH3FourierComponentSquareDensity u t hInt hMeas j ξ ∂volume) =
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j)‖ ^ 2
        + (∑ i : Fin 3,
            ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i)‖ ^ 2)
        + (∑ i : Fin 3, ∑ k : Fin 3,
            ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k)‖ ^ 2)
        + (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2) := by
  have h0 : Integrable (fun ξ : H3FourierPoint3 =>
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2) volume :=
    (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j))).norm.integrable_sq
  have h1 : ∀ i : Fin 3, Integrable (fun ξ : H3FourierPoint3 =>
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2) volume := by
    intro i
    exact (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i))).norm.integrable_sq
  have h2 : ∀ i k : Fin 3, Integrable (fun ξ : H3FourierPoint3 =>
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2) volume := by
    intro i k
    exact (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k))).norm.integrable_sq
  have h3 : ∀ i k l : Fin 3, Integrable (fun ξ : H3FourierPoint3 =>
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2) volume := by
    intro i k l
    exact (MeasureTheory.Lp.memLp
      (velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l))).norm.integrable_sq
  have h1sum : Integrable (fun ξ : H3FourierPoint3 =>
      ∑ i : Fin 3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2) volume := by
    apply integrable_finsetSum
    intro i hi
    exact h1 i
  have h2sum : Integrable (fun ξ : H3FourierPoint3 =>
      ∑ i : Fin 3, ∑ k : Fin 3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2) volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    exact h2 i k
  have h3sum : Integrable (fun ξ : H3FourierPoint3 =>
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2) volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    exact h3 i k l
  unfold velocityH3FourierComponentSquareDensity

  have h0123 :
      (∫ ξ : H3FourierPoint3,
        ((‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
            + ∑ i : Fin 3,
                ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2)
          + ∑ i : Fin 3, ∑ k : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2)
          + ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume)
        =
      (∫ ξ : H3FourierPoint3,
        (‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
            + ∑ i : Fin 3,
                ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2)
          + ∑ i : Fin 3, ∑ k : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2
        ∂volume)
        +
      ∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume := by
    simpa only [Pi.add_apply] using
      (integral_add ((h0.add h1sum).add h2sum) h3sum)

  have h012 :
      (∫ ξ : H3FourierPoint3,
        (‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
            + ∑ i : Fin 3,
                ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2)
          + ∑ i : Fin 3, ∑ k : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2
        ∂volume)
        =
      (∫ ξ : H3FourierPoint3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
          + ∑ i : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2
        ∂volume)
        +
      ∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2
        ∂volume := by
    simpa only [Pi.add_apply] using
      (integral_add (h0.add h1sum) h2sum)

  have h01 :
      (∫ ξ : H3FourierPoint3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
          + ∑ i : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2
        ∂volume)
        =
      (∫ ξ : H3FourierPoint3,
        ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j) ξ‖ ^ 2
        ∂volume)
        +
      ∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2
        ∂volume := by
    simpa only [Pi.add_apply] using
      (integral_add h0 h1sum)

  have h1int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2
        ∂volume)
        =
      ∑ i : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i) ξ‖ ^ 2
        ∂volume := by
    simpa using
      (integral_finsetSum (μ := volume) Finset.univ
        (fun i _ => h1 i))

  have h2int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2
        ∂volume)
        =
      ∑ i : Fin 3, ∑ k : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2
        ∂volume := by
    calc
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2
        ∂volume)
          =
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ k : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k) ξ‖ ^ 2
            ∂volume := by
              simpa using
                (integral_finsetSum (μ := volume) Finset.univ
                  (fun i _ => by
                    apply integrable_finsetSum
                    intro k hk
                    exact h2 i k))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa using
          (integral_finsetSum (μ := volume) Finset.univ
            (fun k _ => h2 i k))

  have h3int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume)
        =
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume := by
    calc
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume)
          =
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
            ∂volume := by
              simpa using
                (integral_finsetSum (μ := volume) Finset.univ
                  (fun i _ => by
                    apply integrable_finsetSum
                    intro k hk
                    apply integrable_finsetSum
                    intro l hl
                    exact h3 i k l))
      _ =
        ∑ i : Fin 3, ∑ k : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ l : Fin 3,
              ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l) ξ‖ ^ 2
            ∂volume := by
              apply Finset.sum_congr rfl
              intro i hi
              simpa using
                (integral_finsetSum (μ := volume) Finset.univ
                  (fun k _ => by
                    apply integrable_finsetSum
                    intro l hl
                    exact h3 i k l))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        simpa using
          (integral_finsetSum (μ := volume) Finset.univ
            (fun l _ => h3 i k l))

  rw [h0123, h012, h01, h1int, h2int, h3int]
  simp_rw [← h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

theorem norm_velocityH3SpectralScalarAt_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ‖velocityH3SpectralScalarAt u t hInt hMeas hFourier j‖ ^ 2 =
      ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot0 j)‖ ^ 2
        + (∑ i : Fin 3,
            ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot1 j i)‖ ^ 2)
        + (∑ i : Fin 3, ∑ k : Fin 3,
            ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot2 j i k)‖ ^ 2)
        + (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt u t hInt hMeas (h3JetSlot3 j i k l)‖ ^ 2) := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  calc
    (∫ ξ : H3FourierPoint3,
      ‖velocityH3SpectralScalarAt u t hInt hMeas hFourier j ξ‖ ^ 2 ∂volume) =
      ∫ ξ : H3FourierPoint3,
        ‖velocityH3WeightedBaseFourierRaw u t hInt hMeas j ξ‖ ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [velocityH3SpectralScalarAt_ae hFourier j] with ξ hξ
      rw [hξ]
    _ = ∫ ξ : H3FourierPoint3,
        velocityH3FourierComponentSquareDensity u t hInt hMeas j ξ ∂volume := by
      exact integral_congr_ae (velocityH3WeightedBaseFourierRaw_norm_sq_ae hFourier j)
    _ = _ := integral_velocityH3FourierComponentSquareDensity u t hInt hMeas j

theorem h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3SpectralVelocitySquareEnergy
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) =
      h3FourierJetSquareEnergy (velocityH3FourierJetAt u t hInt hMeas) := by
  unfold h3SpectralVelocitySquareEnergy velocityH3SpectralStateAt
  simp_rw [norm_velocityH3SpectralScalarAt_sq hFourier]
  unfold h3FourierJetSquareEnergy
  simp only [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [h3JetSlot0, h3JetSlot1, h3JetSlot2, h3JetSlot3]
  simp only [Finset.sum_add_distrib]
  ring

theorem one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    1 + h3SpectralVelocitySquareEnergy
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) =
      velocityH3EnergyAt u t := by
  rw [h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq hFourier]
  exact one_add_h3FourierJetSquareEnergy_velocityH3FourierJetAt_eq hInt hMeas

theorem one_add_h3SpectralVelocitySquareEnergy_of_velocityLogSpatialC3_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    (hSpatial : VelocityLogSpatialC3 u)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    1 + h3SpectralVelocitySquareEnergy
        (velocityH3SpectralStateAt_of_velocityLogSpatialC3 u t hSpatial hInt hMeas) =
      velocityH3EnergyAt u t := by
  unfold velocityH3SpectralStateAt_of_velocityLogSpatialC3
  exact one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
    (velocityH3FourierCompatibleAt_of_velocityLogSpatialC3 hSpatial hInt hMeas)

end

end Euclidean
end Bridge
end PrimeTensor
