import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Tail.Canonical.Path

/-!
# Classicalization: spectral difference energy

The weighted spectral encoder already has an exact one-state energy identity.
For time continuity we need the corresponding *difference* identity.

For two genuine H³ snapshots of the same velocity component, this file proves

    ‖G₁ - G₂‖²
      =
    ‖F₀¹ - F₀²‖²
      + Σᵢ ‖Fᵢ¹ - Fᵢ²‖²
      + Σᵢₖ ‖Fᵢₖ¹ - Fᵢₖ²‖²
      + Σᵢₖₗ ‖Fᵢₖₗ¹ - Fᵢₖₗ²‖²,

where `G₁,G₂` are the weighted spectral scalar states and the `F` terms are
the concrete Fourier transforms of the ordered H³ jet slots.

The proof is the same exact Fourier-symbol algebra as the existing encoder
energy theorem, now applied to a difference.  Fourier compatibility at both
snapshots converts

    symbol * (F₀¹ - F₀²)

into the corresponding derivative-jet difference.

This is the representation-theoretic input needed for spectral-path
continuity.  No Navier--Stokes evolution theorem is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSpectralDifferenceEnergy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pointwise subtraction of two `L²` representatives has integrable squared
norm.  The `Lp` subtraction itself is only a.e. equal to pointwise subtraction,
so this helper performs that coercion transfer once. -/
theorem h3FourierComplexL2_pointwise_sub_norm_sq_integrable
    (F G : H3FourierComplexL2) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖F ξ - G ξ‖ ^ 2)
      volume := by
  have hRaw :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((F - G : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖ ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp (F - G)).norm.integrable_sq

  refine hRaw.congr ?_

  filter_upwards
    [MeasureTheory.Lp.coeFn_sub F G]
    with ξ hSub

  simpa only [Pi.sub_apply] using
    congrArg
      (fun z : ℂ => ‖z‖ ^ 2)
      hSub

/-- Exact `L²` norm-square identity with subtraction written pointwise on the
chosen representatives. -/
theorem h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
    (F G : H3FourierComplexL2) :
    ‖F - G‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖F ξ - G ξ‖ ^ 2
      ∂volume := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  apply integral_congr_ae

  filter_upwards
    [MeasureTheory.Lp.coeFn_sub F G]
    with ξ hSub

  simpa only [Pi.sub_apply] using
    congrArg
      (fun z : ℂ => ‖z‖ ^ 2)
      hSub

/-- Difference square-density of one velocity component's complete ordered H³
Fourier jet. -/
def velocityH3FourierComponentDifferenceSquareDensity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t s : ℝ)
    (hIntT : VelocityH3IntegrableAt u t)
    (hMeasT : VelocityH3MeasurableAt u t)
    (hIntS : VelocityH3IntegrableAt u s)
    (hMeasS : VelocityH3MeasurableAt u s)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℝ :=
  ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j) ξ
      -
    velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
    +
  (∑ i : Fin 3,
    ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
        -
      velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2)
    +
  (∑ i : Fin 3, ∑ k : Fin 3,
    ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
        -
      velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2)
    +
  (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
        -
      velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2)

/-- Pure frequency algebra: the H³ weight applied to a scalar difference has
exactly the ordered derivative-symbol square energy. -/
theorem h3SobolevFrequencyWeight_mul_sub_norm_sq
    (ξ : H3FourierPoint3)
    (F G : ℂ) :
    ‖(h3SobolevFrequencyWeight ξ : ℂ) * F
        -
      (h3SobolevFrequencyWeight ξ : ℂ) * G‖ ^ 2
      =
    ‖F - G‖ ^ 2
      +
    (∑ i : Fin 3,
      ‖h3FourierDerivativeSymbol i ξ * (F - G)‖ ^ 2)
      +
    (∑ i : Fin 3, ∑ k : Fin 3,
      ‖h3FourierDerivativeSymbol2 i k ξ * (F - G)‖ ^ 2)
      +
    (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      ‖h3FourierDerivativeSymbol3 i k l ξ * (F - G)‖ ^ 2) := by
  rw [← mul_sub]

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

/-- Pointwise a.e. difference identity for the two weighted raw Fourier
representatives. -/
theorem velocityH3WeightedBaseFourierRaw_sub_norm_sq_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t s : ℝ}
    {hIntT : VelocityH3IntegrableAt u t}
    {hMeasT : VelocityH3MeasurableAt u t}
    {hIntS : VelocityH3IntegrableAt u s}
    {hMeasS : VelocityH3MeasurableAt u s}
    (hFourierT :
      VelocityH3FourierCompatibleAt u t hIntT hMeasT)
    (hFourierS :
      VelocityH3FourierCompatibleAt u s hIntS hMeasS)
    (j : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      ‖velocityH3WeightedBaseFourierRaw
          u t hIntT hMeasT j ξ
          -
        velocityH3WeightedBaseFourierRaw
          u s hIntS hMeasS j ξ‖ ^ 2)
      =ᵐ[volume]
    velocityH3FourierComponentDifferenceSquareDensity
      u t s hIntT hMeasT hIntS hMeasS j := by
  have h1T :=
    velocityH3FourierCompatibleAt_orderOne_all_ae
      hFourierT j
  have h2T :=
    velocityH3FourierCompatibleAt_orderTwo_all_ae
      hFourierT j
  have h3T :=
    velocityH3FourierCompatibleAt_orderThree_all_ae
      hFourierT j

  have h1S :=
    velocityH3FourierCompatibleAt_orderOne_all_ae
      hFourierS j
  have h2S :=
    velocityH3FourierCompatibleAt_orderTwo_all_ae
      hFourierS j
  have h3S :=
    velocityH3FourierCompatibleAt_orderThree_all_ae
      hFourierS j

  filter_upwards
    [h1T, h2T, h3T, h1S, h2S, h3S]
    with ξ h1Tξ h2Tξ h3Tξ h1Sξ h2Sξ h3Sξ

  unfold velocityH3WeightedBaseFourierRaw

  rw [h3SobolevFrequencyWeight_mul_sub_norm_sq]

  unfold velocityH3FourierComponentDifferenceSquareDensity

  simp_rw [h1Tξ, h2Tξ, h3Tξ, h1Sξ, h2Sξ, h3Sξ]
  simp only [velocityH3BaseFourierAt]
  ring_nf

/-- The difference square-density is integrable and its integral is the finite
sum of squared `L²` distances of all ordered H³ Fourier jet slots. -/
theorem integral_velocityH3FourierComponentDifferenceSquareDensity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t s : ℝ)
    (hIntT : VelocityH3IntegrableAt u t)
    (hMeasT : VelocityH3MeasurableAt u t)
    (hIntS : VelocityH3IntegrableAt u s)
    (hMeasS : VelocityH3MeasurableAt u s)
    (j : Fin 3) :
    (∫ ξ : H3FourierPoint3,
      velocityH3FourierComponentDifferenceSquareDensity
        u t s hIntT hMeasT hIntS hMeasS j ξ
      ∂volume)
      =
    ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j)
        -
      velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j)‖ ^ 2
      +
    (∑ i : Fin 3,
      ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i)
          -
        velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i)‖ ^ 2)
      +
    (∑ i : Fin 3, ∑ k : Fin 3,
      ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k)
          -
        velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k)‖ ^ 2)
      +
    (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l)
          -
        velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l)‖ ^ 2) := by
  let F0T :=
    velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j)
  let F0S :=
    velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j)

  have h0 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖F0T ξ - F0S ξ‖ ^ 2)
        volume := by
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        F0T F0S

  have h1 :
      ∀ i : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot1 j i) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2)
          volume := by
    intro i
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (velocityH3FourierJetAt
          u t hIntT hMeasT (h3JetSlot1 j i))
        (velocityH3FourierJetAt
          u s hIntS hMeasS (h3JetSlot1 j i))

  have h2 :
      ∀ i k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot2 j i k) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2)
          volume := by
    intro i k
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (velocityH3FourierJetAt
          u t hIntT hMeasT (h3JetSlot2 j i k))
        (velocityH3FourierJetAt
          u s hIntS hMeasS (h3JetSlot2 j i k))

  have h3 :
      ∀ i k l : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2)
          volume := by
    intro i k l
    exact
      h3FourierComplexL2_pointwise_sub_norm_sq_integrable
        (velocityH3FourierJetAt
          u t hIntT hMeasT (h3JetSlot3 j i k l))
        (velocityH3FourierJetAt
          u s hIntS hMeasS (h3JetSlot3 j i k l))

  have h1sum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3,
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot1 j i) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2)
        volume := by
    apply integrable_finsetSum
    intro i hi
    exact h1 i

  have h2sum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3, ∑ k : Fin 3,
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot2 j i k) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2)
        volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    exact h2 i k

  have h3sum :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                -
              velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2)
        volume := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    exact h3 i k l

  unfold velocityH3FourierComponentDifferenceSquareDensity

  have h0123 :
      (∫ ξ : H3FourierPoint3,
        ((‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
            +
          ∑ i : Fin 3,
            ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
                -
              velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2)
          +
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2)
        +
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
            -
          velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
      ∂volume)
        =
      (∫ ξ : H3FourierPoint3,
        (‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
            +
          ∑ i : Fin 3,
            ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
                -
              velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2)
          +
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2
      ∂volume)
        +
      ∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
      ∂volume := by
    simpa only [Pi.add_apply] using
      (integral_add ((h0.add h1sum).add h2sum) h3sum)

  have h012 :
      (∫ ξ : H3FourierPoint3,
        (‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
            +
          ∑ i : Fin 3,
            ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
                -
              velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2)
          +
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2
      ∂volume)
        =
      (∫ ξ : H3FourierPoint3,
        ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
          +
        ∑ i : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2
      ∂volume)
        +
      ∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2
      ∂volume := by
    simpa only [Pi.add_apply] using
      (integral_add (h0.add h1sum) h2sum)

  have h01 :
      (∫ ξ : H3FourierPoint3,
        ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
          +
        ∑ i : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2
      ∂volume)
        =
      (∫ ξ : H3FourierPoint3,
        ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
      ∂volume)
        +
      ∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2
      ∂volume := by
    simpa only [Pi.add_apply] using
      (integral_add h0 h1sum)

  have h1int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2
      ∂volume)
        =
      ∑ i : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i) ξ‖ ^ 2
        ∂volume := by
    simpa using
      (integral_finsetSum (μ := volume) Finset.univ
        (fun i _ => h1 i))

  have h2int :
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2
      ∂volume)
        =
      ∑ i : Fin 3, ∑ k : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2
        ∂volume := by
    calc
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2
        ∂volume)
          =
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ k : Fin 3,
              ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k) ξ
                  -
                velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k) ξ‖ ^ 2
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
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
      ∂volume)
        =
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ∫ ξ : H3FourierPoint3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume := by
    calc
      (∫ ξ : H3FourierPoint3,
        ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
              -
            velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
        ∂volume)
          =
        ∑ i : Fin 3,
          ∫ ξ : H3FourierPoint3,
            ∑ k : Fin 3, ∑ l : Fin 3,
              ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                  -
                velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
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
              ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                  -
                velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2
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

  simp_rw [
    ← h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
  ]

/-- Exact squared spectral distance for one genuine encoded velocity component. -/
theorem norm_velocityH3SpectralScalarAt_sub_sq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t s : ℝ}
    {hIntT : VelocityH3IntegrableAt u t}
    {hMeasT : VelocityH3MeasurableAt u t}
    {hIntS : VelocityH3IntegrableAt u s}
    {hMeasS : VelocityH3MeasurableAt u s}
    (hFourierT :
      VelocityH3FourierCompatibleAt u t hIntT hMeasT)
    (hFourierS :
      VelocityH3FourierCompatibleAt u s hIntS hMeasS)
    (j : Fin 3) :
    ‖velocityH3SpectralScalarAt
        u t hIntT hMeasT hFourierT j
        -
      velocityH3SpectralScalarAt
        u s hIntS hMeasS hFourierS j‖ ^ 2
      =
    ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot0 j)
        -
      velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot0 j)‖ ^ 2
      +
    (∑ i : Fin 3,
      ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot1 j i)
          -
        velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot1 j i)‖ ^ 2)
      +
    (∑ i : Fin 3, ∑ k : Fin 3,
      ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot2 j i k)
          -
        velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot2 j i k)‖ ^ 2)
      +
    (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      ‖velocityH3FourierJetAt u t hIntT hMeasT (h3JetSlot3 j i k l)
          -
        velocityH3FourierJetAt u s hIntS hMeasS (h3JetSlot3 j i k l)‖ ^ 2) := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  calc
    (∫ ξ : H3FourierPoint3,
      ‖(velocityH3SpectralScalarAt
          u t hIntT hMeasT hFourierT j
          -
        velocityH3SpectralScalarAt
          u s hIntS hMeasS hFourierS j) ξ‖ ^ 2
      ∂volume)
        =
      ∫ ξ : H3FourierPoint3,
        ‖velocityH3WeightedBaseFourierRaw
            u t hIntT hMeasT j ξ
            -
          velocityH3WeightedBaseFourierRaw
            u s hIntS hMeasS j ξ‖ ^ 2
        ∂volume := by
      apply integral_congr_ae

      let GT : H3SpectralScalarState :=
        velocityH3SpectralScalarAt
          u t hIntT hMeasT hFourierT j

      let GS : H3SpectralScalarState :=
        velocityH3SpectralScalarAt
          u s hIntS hMeasS hFourierS j

      filter_upwards
        [MeasureTheory.Lp.coeFn_sub GT GS,
         velocityH3SpectralScalarAt_ae hFourierT j,
         velocityH3SpectralScalarAt_ae hFourierS j]
        with ξ hSub hT hS

      calc
        ‖((GT - GS : H3SpectralScalarState) :
            H3FourierPoint3 → ℂ) ξ‖ ^ 2
            =
          ‖(GT : H3FourierPoint3 → ℂ) ξ
              -
            (GS : H3FourierPoint3 → ℂ) ξ‖ ^ 2 := by
              simpa only [Pi.sub_apply] using
                congrArg
                  (fun z : ℂ => ‖z‖ ^ 2)
                  hSub
        _ =
          ‖velocityH3WeightedBaseFourierRaw
              u t hIntT hMeasT j ξ
              -
            velocityH3WeightedBaseFourierRaw
              u s hIntS hMeasS j ξ‖ ^ 2 := by
              rw [hT, hS]

    _ =
      ∫ ξ : H3FourierPoint3,
        velocityH3FourierComponentDifferenceSquareDensity
          u t s hIntT hMeasT hIntS hMeasS j ξ
        ∂volume := by
      exact
        integral_congr_ae
          (velocityH3WeightedBaseFourierRaw_sub_norm_sq_ae
            hFourierT hFourierS j)

    _ = _ :=
      integral_velocityH3FourierComponentDifferenceSquareDensity
        u t s hIntT hMeasT hIntS hMeasS j

end
end Euclidean
end Bridge
end PrimeTensor
