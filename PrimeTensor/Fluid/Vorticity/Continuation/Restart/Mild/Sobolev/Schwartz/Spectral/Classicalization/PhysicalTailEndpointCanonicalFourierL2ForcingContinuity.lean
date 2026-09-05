import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalFourierL2DiffusionContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.Difference
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.C0.Bridge

/-!
# Classicalization: strong Fourier `L²` continuity of endpoint forcing

The nonlinear endpoint forcing is already known to belong to Fourier `L²`,
but membership alone does not give strong time continuity of the packaged
quotient class.

This file proves the missing topology without evaluating `L²` representatives
at a fixed frequency.

The construction has three bounded layers.

1. For one weighted H³ scalar state `P`, spend one derivative after
   deweighting:

       P ↦ (∂̂ⱼ W₃⁻¹) P.

   The multiplier norm is bounded by `2π`.

2. Build the finite divergence by applying this bounded derivative map to the
   weighted H³ product states

       B(Uᵢ,Vⱼ).

   The existing two-input difference estimate proves joint continuity of `B`.

3. Apply the already-constructed bounded finite Leray multiplier.

The resulting `L²` state is identified almost everywhere with the repository's
existing raw Leray-divergence forcing package.  Therefore

    (U,V) ↦ P div(U ⊗ V)

is strongly continuous as a map into Fourier `L²`, coordinatewise.

Composing with the continuous endpoint weighted H³ path gives strong Fourier
`L²` continuity of the endpoint nonlinear forcing on the whole closed elapsed
interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalFourierL2ForcingContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## One bounded deweighted derivative -/

/-- One raw Fourier derivative of a weighted H³ scalar state, packaged in
Fourier `L²`. -/
theorem h3SpectralScalarRawDerivative_memLp2
    (j : Fin 3)
    (P : H3SpectralScalarState) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol j ξ *
          h3SpectralScalarRawFourier P ξ)
      2
      (volume : Measure H3FourierPoint3) := by
  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol j ξ *
            h3SpectralScalarRawFourier P ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.mul
        (h3SpectralScalarRawFourier_memLp2 P).1

  have hMajorant :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          (((2 * Real.pi : ℝ) : ℂ) * P ξ))
        2
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp P).const_mul
      (((2 * Real.pi : ℝ) : ℂ))

  refine hMajorant.of_le hTargetMeas ?_

  filter_upwards with ξ

  have hTwoPi : 0 ≤ 2 * Real.pi := by
    positivity

  have hInvNonneg :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  have hDerivWeight :
      ‖h3FourierDerivativeSymbol j ξ‖ *
          h3SobolevFrequencyWeightInv ξ
        ≤
      2 * Real.pi := by
    calc
      ‖h3FourierDerivativeSymbol j ξ‖ *
          h3SobolevFrequencyWeightInv ξ
          ≤
        h3FourierGradientMagnitude ξ *
          h3SobolevFrequencyWeightInv ξ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ)
          hInvNonneg
      _ =
        (2 * Real.pi) *
          h3SobolevFrequencyFirstMomentInv ξ := by
        unfold
          h3FourierGradientMagnitude
          h3SobolevFrequencyFirstMomentInv
        ring
      _ ≤ (2 * Real.pi) * 1 :=
        mul_le_mul_of_nonneg_left
          (h3SobolevFrequencyFirstMomentInv_le_one ξ)
          hTwoPi
      _ = 2 * Real.pi := by ring

  unfold
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex

  rw [
    norm_mul,
    norm_mul,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hInvNonneg,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hTwoPi
  ]

  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right
      hDerivWeight
      (norm_nonneg (P ξ))

/-- Packaged bounded raw derivative map. -/
noncomputable def h3SpectralScalarRawDerivativeFourierL2
    (j : Fin 3)
    (P : H3SpectralScalarState) :
    H3FourierComplexL2 :=
  (h3SpectralScalarRawDerivative_memLp2 j P).toLp
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol j ξ *
        h3SpectralScalarRawFourier P ξ)

/-- Representative of the packaged raw derivative map. -/
theorem h3SpectralScalarRawDerivativeFourierL2_ae
    (j : Fin 3)
    (P : H3SpectralScalarState) :
    ((h3SpectralScalarRawDerivativeFourierL2 j P :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol j ξ *
        h3SpectralScalarRawFourier P ξ) := by
  exact
    MemLp.coeFn_toLp
      (h3SpectralScalarRawDerivative_memLp2 j P)

/-- Spending one derivative costs at most `2π` in Fourier `L²`. -/
theorem norm_h3SpectralScalarRawDerivativeFourierL2_le
    (j : Fin 3)
    (P : H3SpectralScalarState) :
    ‖h3SpectralScalarRawDerivativeFourierL2 j P‖
      ≤
    (2 * Real.pi) * ‖P‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    h3SpectralScalarRawDerivativeFourierL2_ae j P
  ] with ξ hξ

  rw [hξ]

  have hTwoPi : 0 ≤ 2 * Real.pi := by
    positivity

  have hInvNonneg :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  have hDerivWeight :
      ‖h3FourierDerivativeSymbol j ξ‖ *
          h3SobolevFrequencyWeightInv ξ
        ≤
      2 * Real.pi := by
    calc
      ‖h3FourierDerivativeSymbol j ξ‖ *
          h3SobolevFrequencyWeightInv ξ
          ≤
        h3FourierGradientMagnitude ξ *
          h3SobolevFrequencyWeightInv ξ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ)
          hInvNonneg
      _ =
        (2 * Real.pi) *
          h3SobolevFrequencyFirstMomentInv ξ := by
        unfold
          h3FourierGradientMagnitude
          h3SobolevFrequencyFirstMomentInv
        ring
      _ ≤ (2 * Real.pi) * 1 :=
        mul_le_mul_of_nonneg_left
          (h3SobolevFrequencyFirstMomentInv_le_one ξ)
          hTwoPi
      _ = 2 * Real.pi := by ring

  unfold
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex

  rw [
    norm_mul,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hInvNonneg
  ]

  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right
      hDerivWeight
      (norm_nonneg (P ξ))

/-- The bounded raw derivative map respects subtraction. -/
theorem h3SpectralScalarRawDerivativeFourierL2_sub
    (j : Fin 3)
    (P Q : H3SpectralScalarState) :
    h3SpectralScalarRawDerivativeFourierL2 j (P - Q)
      =
    h3SpectralScalarRawDerivativeFourierL2 j P
      -
    h3SpectralScalarRawDerivativeFourierL2 j Q := by
  apply MeasureTheory.Lp.ext

  have hPQ :=
    h3SpectralScalarRawDerivativeFourierL2_ae j (P - Q)
  have hP :=
    h3SpectralScalarRawDerivativeFourierL2_ae j P
  have hQ :=
    h3SpectralScalarRawDerivativeFourierL2_ae j Q
  have hIn :=
    MeasureTheory.Lp.coeFn_sub P Q
  have hOut :=
    MeasureTheory.Lp.coeFn_sub
      (h3SpectralScalarRawDerivativeFourierL2 j P)
      (h3SpectralScalarRawDerivativeFourierL2 j Q)

  filter_upwards [hPQ, hP, hQ, hIn, hOut] with
      ξ hPQξ hPξ hQξ hInξ hOutξ

  rw [hPQξ, hOutξ]
  simp only [Pi.sub_apply]
  rw [hPξ, hQξ]

  unfold
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex

  rw [hInξ]
  simp only [Pi.sub_apply]
  ring

/-- One bounded raw derivative is Lipschitz in the weighted H³ state. -/
theorem norm_h3SpectralScalarRawDerivativeFourierL2_sub_le
    (j : Fin 3)
    (P Q : H3SpectralScalarState) :
    ‖h3SpectralScalarRawDerivativeFourierL2 j P
        -
      h3SpectralScalarRawDerivativeFourierL2 j Q‖
      ≤
    (2 * Real.pi) * ‖P - Q‖ := by
  rw [
    ← h3SpectralScalarRawDerivativeFourierL2_sub
  ]
  exact
    norm_h3SpectralScalarRawDerivativeFourierL2_le
      j (P - Q)

/-- Strong continuity of the bounded raw derivative map. -/
theorem continuous_h3SpectralScalarRawDerivativeFourierL2
    (j : Fin 3) :
    Continuous
      (h3SpectralScalarRawDerivativeFourierL2 j) := by
  rw [continuous_iff_continuousAt]
  intro P

  unfold ContinuousAt
  rw [tendsto_iff_norm_sub_tendsto_zero]

  apply squeeze_zero

  · intro Q
    exact norm_nonneg _

  · intro Q
    exact
      norm_h3SpectralScalarRawDerivativeFourierL2_sub_le
        j Q P

  · have hBound :
        ContinuousAt
          (fun Q : H3SpectralScalarState =>
            (2 * Real.pi) * ‖Q - P‖)
          P := by
      fun_prop

    simpa using hBound.tendsto

/-! ## Joint continuity of the weighted product state -/

/-- The existing quantitative product-convolution difference estimate implies
joint strong continuity of the weighted H³ product state. -/
theorem continuous_h3WeightedRawProductConvolutionL2_pair :
    Continuous
      (fun p : H3SpectralScalarState × H3SpectralScalarState =>
        h3WeightedRawProductConvolutionL2 p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨F, G⟩

  unfold ContinuousAt
  rw [tendsto_iff_norm_sub_tendsto_zero]

  let C : ℝ :=
    16 * h3SobolevDeweightingConstant

  let B :
      H3SpectralScalarState × H3SpectralScalarState → ℝ :=
    fun p =>
      C * ‖p.1 - F‖ * ‖p.2‖
        +
      C * ‖F‖ * ‖p.2 - G‖

  apply squeeze_zero

  · intro p
    exact norm_nonneg _

  · intro p
    dsimp only [B, C]
    exact
      norm_h3WeightedRawProductConvolutionL2_sub_le
        p.1 F p.2 G

  · have hB :
        ContinuousAt B (F, G) := by
      dsimp only [B, C]
      fun_prop

    simpa only [
      B,
      C,
      sub_self,
      norm_zero,
      mul_zero,
      zero_mul,
      add_zero
    ] using hB.tendsto

/-! ## Finite unheated divergence as an `L²` state -/

/-- Pre-Leray finite divergence assembled from bounded raw derivative maps of
the exact weighted H³ product states. -/
noncomputable def h3SpectralFinUnheatedDivergenceApply
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  fun i =>
    ∑ j : Fin 3,
      h3SpectralScalarRawDerivativeFourierL2
        j
        (h3WeightedRawProductConvolutionL2
          (U i) (V j))

/-- The packaged pre-Leray divergence has exactly the existing raw divergence
representative almost everywhere. -/
theorem h3SpectralFinUnheatedDivergenceApply_ae
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    ((h3SpectralFinUnheatedDivergenceApply U V i :
        H3SpectralScalarState) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3RawFinOuterProductDivergence U V i := by
  unfold h3SpectralFinUnheatedDivergenceApply

  have hSum :=
    MeasureTheory.Lp.coeFn_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun j : Fin 3 =>
        h3SpectralScalarRawDerivativeFourierL2
          j
          (h3WeightedRawProductConvolutionL2
            (U i) (V j)))

  have hTerms :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ j : Fin 3,
          ((h3SpectralScalarRawDerivativeFourierL2
              j
              (h3WeightedRawProductConvolutionL2
                (U i) (V j)) :
              H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ
            =
          h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution (U i) (V j) ξ := by
    exact ae_all_iff.2 (fun j => by
      have hDer :=
        h3SpectralScalarRawDerivativeFourierL2_ae
          j
          (h3WeightedRawProductConvolutionL2
            (U i) (V j))

      have hRaw :=
        h3SpectralScalarRawFourier_weightedRawProductConvolutionL2_ae
          (U i) (V j)

      filter_upwards [hDer, hRaw] with ξ hDerξ hRawξ

      rw [hDerξ, hRawξ])

  filter_upwards [hSum, hTerms] with ξ hSumξ hTermsξ

  rw [hSumξ]
  simp only [Finset.sum_apply]

  unfold h3RawFinOuterProductDivergence

  apply Finset.sum_congr rfl
  intro j hj
  exact hTermsξ j

/-- One Leray matrix entry is `2`-Lipschitz on scalar Fourier `L²`. -/
theorem lipschitzWith_h3SpectralScalarLerayCoefficientApply_forcing
    (i k : Fin 3) :
    LipschitzWith 2
      (h3SpectralScalarLerayCoefficientApply i k :
        H3SpectralScalarState → H3SpectralScalarState) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  rw [dist_eq_norm, dist_eq_norm]
  rw [← h3SpectralScalarLerayCoefficientApply_sub]
  exact
    norm_h3SpectralScalarLerayCoefficientApply_le
      i k (F - G)

/-- One Leray matrix entry is strongly continuous on scalar Fourier `L²`. -/
theorem continuous_h3SpectralScalarLerayCoefficientApply_forcing
    (i k : Fin 3) :
    Continuous
      (h3SpectralScalarLerayCoefficientApply i k :
        H3SpectralScalarState → H3SpectralScalarState) :=
  (lipschitzWith_h3SpectralScalarLerayCoefficientApply_forcing
    i k).continuous

/-- Joint strong continuity of one output coordinate of the finite pre-Leray
divergence.  The intermediate maps are named explicitly so elaboration never
has to normalize the whole dependent product expression at once. -/
theorem continuous_h3SpectralFinUnheatedDivergenceApply_coordinate_pair
    (i : Fin 3) :
    Continuous
      (fun p :
          H3SpectralFinVectorState × H3SpectralFinVectorState =>
        h3SpectralFinUnheatedDivergenceApply p.1 p.2 i) := by
  let S :
      H3SpectralFinVectorState × H3SpectralFinVectorState →
        H3SpectralScalarState :=
    fun p =>
      ∑ j : Fin 3,
        h3SpectralScalarRawDerivativeFourierL2
          j
          (h3WeightedRawProductConvolutionL2
            (p.1 i) (p.2 j))

  have hTarget :
      (fun p :
          H3SpectralFinVectorState × H3SpectralFinVectorState =>
        h3SpectralFinUnheatedDivergenceApply p.1 p.2 i)
        =
      S := by
    funext p
    rfl

  rw [hTarget]

  dsimp only [S]

  apply continuous_finsetSum
  intro j hj

  let E :
      H3SpectralFinVectorState × H3SpectralFinVectorState →
        H3SpectralScalarState × H3SpectralScalarState :=
    fun p => (p.1 i, p.2 j)

  let B :
      H3SpectralScalarState × H3SpectralScalarState →
        H3SpectralScalarState :=
    fun q =>
      h3WeightedRawProductConvolutionL2 q.1 q.2

  let R :
      H3SpectralScalarState →
        H3FourierComplexL2 :=
    h3SpectralScalarRawDerivativeFourierL2 j

  have hE : Continuous E := by
    dsimp only [E]
    exact
      Continuous.prodMk
        ((continuous_apply i).comp continuous_fst)
        ((continuous_apply j).comp continuous_snd)

  have hB : Continuous B := by
    dsimp only [B]
    exact continuous_h3WeightedRawProductConvolutionL2_pair

  have hR : Continuous R := by
    dsimp only [R]
    exact continuous_h3SpectralScalarRawDerivativeFourierL2 j

  have hComp :
      Continuous (R ∘ B ∘ E) :=
    hR.comp (hB.comp hE)

  have hFun :
      (R ∘ B ∘ E)
        =
      (fun p :
          H3SpectralFinVectorState × H3SpectralFinVectorState =>
        h3SpectralScalarRawDerivativeFourierL2
          j
          (h3WeightedRawProductConvolutionL2
            (p.1 i) (p.2 j))) := by
    rfl

  rw [hFun] at hComp
  exact hComp

/-! ## Full unheated Leray forcing -/

/-- Full finite unheated Leray forcing assembled in Fourier `L²`. -/
noncomputable def h3SpectralFinUnheatedLerayForcingApply
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  h3SpectralFinLerayApply
    (h3SpectralFinUnheatedDivergenceApply U V)

/-- The assembled forcing has the repository's raw Leray-divergence amplitude
as its representative almost everywhere. -/
theorem h3SpectralFinUnheatedLerayForcingApply_ae
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    ((h3SpectralFinUnheatedLerayForcingApply U V i :
        H3SpectralScalarState) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3RawFinLerayOuterProductDivergence U V i := by
  unfold
    h3SpectralFinUnheatedLerayForcingApply
    h3SpectralFinLerayApply

  have hSum :=
    MeasureTheory.Lp.coeFn_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun k : Fin 3 =>
        h3SpectralScalarLerayCoefficientApply
          i k
          (h3SpectralFinUnheatedDivergenceApply U V k))

  have hTerms :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ k : Fin 3,
          ((h3SpectralScalarLerayCoefficientApply
              i k
              (h3SpectralFinUnheatedDivergenceApply U V k) :
              H3SpectralScalarState) :
            H3FourierPoint3 → ℂ) ξ
            =
          h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ := by
    exact ae_all_iff.2 (fun k => by
      have hL :=
        h3SpectralScalarLerayCoefficientApply_ae
          i k
          (h3SpectralFinUnheatedDivergenceApply U V k)

      have hD :=
        h3SpectralFinUnheatedDivergenceApply_ae U V k

      filter_upwards [hL, hD] with ξ hLξ hDξ

      rw [hLξ, hDξ])

  filter_upwards [hSum, hTerms] with ξ hSumξ hTermsξ

  rw [hSumξ]
  simp only [Finset.sum_apply]

  unfold h3RawFinLerayOuterProductDivergence

  apply Finset.sum_congr rfl
  intro k hk
  exact hTermsξ k

/-- The assembled strongly continuous forcing is exactly the already-packaged
raw forcing `L²` class. -/
theorem h3SpectralFinUnheatedLerayForcingApply_eq_rawFourierL2
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3SpectralFinUnheatedLerayForcingApply U V i
      =
    h3RawFinLerayOuterProductDivergenceFourierL2
      U V i := by
  apply MeasureTheory.Lp.ext

  have hNew :=
    h3SpectralFinUnheatedLerayForcingApply_ae U V i

  have hOld :
      ((h3RawFinLerayOuterProductDivergenceFourierL2
          U V i :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawFinLerayOuterProductDivergence U V i := by
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact
      MemLp.coeFn_toLp
        (h3RawFinLerayOuterProductDivergence_memLp2
          U V i)

  filter_upwards [hNew, hOld] with ξ hNewξ hOldξ

  rw [hNewξ, hOldξ]

/-- Joint strong continuity of one output coordinate of the assembled unheated
Leray forcing. -/
theorem continuous_h3SpectralFinUnheatedLerayForcingApply_coordinate_pair
    (i : Fin 3) :
    Continuous
      (fun p :
          H3SpectralFinVectorState × H3SpectralFinVectorState =>
        h3SpectralFinUnheatedLerayForcingApply p.1 p.2 i) := by
  unfold
    h3SpectralFinUnheatedLerayForcingApply
    h3SpectralFinLerayApply

  apply continuous_finsetSum
  intro k hk

  exact
    (continuous_h3SpectralScalarLerayCoefficientApply_forcing i k).comp
      (continuous_h3SpectralFinUnheatedDivergenceApply_coordinate_pair k)

/-- Therefore the repository's existing raw forcing Fourier `L²` package is
jointly strongly continuous, coordinatewise. -/
theorem continuous_h3RawFinLerayOuterProductDivergenceFourierL2
    (i : Fin 3) :
    Continuous
      (fun p :
          H3SpectralFinVectorState × H3SpectralFinVectorState =>
        h3RawFinLerayOuterProductDivergenceFourierL2
          p.1 p.2 i) := by
  have hNew :
      Continuous
        (fun p :
            H3SpectralFinVectorState × H3SpectralFinVectorState =>
          h3SpectralFinUnheatedLerayForcingApply
            p.1 p.2 i) :=
    continuous_h3SpectralFinUnheatedLerayForcingApply_coordinate_pair i

  have hEq :
      (fun p :
          H3SpectralFinVectorState × H3SpectralFinVectorState =>
        h3RawFinLerayOuterProductDivergenceFourierL2
          p.1 p.2 i)
        =
      (fun p :
          H3SpectralFinVectorState × H3SpectralFinVectorState =>
        h3SpectralFinUnheatedLerayForcingApply
          p.1 p.2 i) := by
    funext p
    exact
      (h3SpectralFinUnheatedLerayForcingApply_eq_rawFourierL2
        p.1 p.2 i).symm

  rw [hEq]
  exact hNew

/-! ## Endpoint forcing continuity -/

/-- Strong Fourier `L²` continuity of the normalized-real endpoint forcing on
the complete closed elapsed interval. -/
theorem continuous_h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (i : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
          hNS ht htau.le hEnd hE hTail hEndpoint
          (q : ℝ) i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hW :
      Continuous W :=
    continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let D :
      Set.Icc (0 : ℝ) tau →
        H3SpectralFinVectorState × H3SpectralFinVectorState :=
    fun q => (W (q : ℝ), W (q : ℝ))

  let F :
      H3SpectralFinVectorState × H3SpectralFinVectorState →
        H3FourierComplexL2 :=
    fun p =>
      h3RawFinLerayOuterProductDivergenceFourierL2
        p.1 p.2 i

  have hD : Continuous D := by
    dsimp only [D]
    exact
      Continuous.prodMk
        (hW.comp continuous_subtype_val)
        (hW.comp continuous_subtype_val)

  have hF : Continuous F := by
    dsimp only [F]
    exact
      continuous_h3RawFinLerayOuterProductDivergenceFourierL2 i

  have hComp :
      Continuous (F ∘ D) :=
    hF.comp hD

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
          hNS ht htau.le hEnd hE hTail hEndpoint
          (q : ℝ) i)
        =
      F ∘ D := by
    funext q
    rfl

  rw [hEq]
  exact hComp

/-- Strong Fourier `L²` continuity of the bounded physical endpoint forcing
package itself. -/
theorem continuous_h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (i : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
          hNS ht hEnd hE hTail hEndpoint q i) := by
  have hNorm :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
            hNS ht htau.le hEnd hE hTail hEndpoint
            (q : ℝ) i) :=
    continuous_h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint i

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
          hNS ht hEnd hE hTail hEndpoint q i)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
          hNS ht htau.le hEnd hE hTail hEndpoint
          (q : ℝ) i) := by
    funext q
    exact
      (h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2_eq_on_physical
        hNS ht htau hEnd hE hTail hEndpoint
        (q : ℝ) q.property i).symm

  rw [hEq]
  exact hNorm

end

end Euclidean
end Bridge
end PrimeTensor
