import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralRealizability

/-!
# Algebraic closure of realizable spectral H³ states

Before proving that the concrete heat--Leray Picard map preserves the physical
(real) spectral subspace, we isolate the purely linear bookkeeping.

The exact spectral decoder is linear because deweighting is pointwise
multiplication by a fixed real weight and inverse Fourier transform is linear.
Consequently the realizable states are closed under zero, addition, negation,
and subtraction.  The same statements are then lifted coordinatewise to
velocity states and pointwise to normalized velocity paths.

No heat or nonlinear estimate appears here.  This file is only the algebraic
closure layer needed by the subsequent operator-invariance proof.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SpectralRealizabilityClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Deweighting is additive -/

@[simp]
theorem h3SpectralScalarRawFourierL2_zero :
    h3SpectralScalarRawFourierL2 (0 : H3SpectralScalarState) = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae (0 : H3SpectralScalarState)
  ] with ξ hξ
  rw [hξ]
  simp [h3SpectralScalarRawFourier]

@[simp]
theorem h3SpectralScalarRawFourierL2_add
    (G H : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2 (G + H)
      =
    h3SpectralScalarRawFourierL2 G +
      h3SpectralScalarRawFourierL2 H := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae (G + H),
    h3SpectralScalarRawFourierL2_ae G,
    h3SpectralScalarRawFourierL2_ae H,
    MeasureTheory.Lp.coeFn_add G H,
    MeasureTheory.Lp.coeFn_add
      (h3SpectralScalarRawFourierL2 G)
      (h3SpectralScalarRawFourierL2 H)
  ] with ξ hGH hG hH hIn hOut
  rw [hGH, hOut]
  change
    h3SpectralScalarRawFourier (G + H) ξ
      =
    (h3SpectralScalarRawFourierL2 G : H3FourierPoint3 → ℂ) ξ +
      (h3SpectralScalarRawFourierL2 H : H3FourierPoint3 → ℂ) ξ
  rw [hG, hH]
  unfold h3SpectralScalarRawFourier
  rw [hIn]
  simpa only [Pi.add_apply] using
    (mul_add
      (h3SobolevFrequencyWeightInvComplex ξ)
      ((G : H3FourierPoint3 → ℂ) ξ)
      ((H : H3FourierPoint3 → ℂ) ξ))

@[simp]
theorem h3SpectralScalarRawFourierL2_neg
    (G : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2 (-G)
      =
    -h3SpectralScalarRawFourierL2 G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae (-G),
    h3SpectralScalarRawFourierL2_ae G,
    MeasureTheory.Lp.coeFn_neg G,
    MeasureTheory.Lp.coeFn_neg
      (h3SpectralScalarRawFourierL2 G)
  ] with ξ hNeg hG hIn hOut
  rw [hNeg, hOut]
  change
    h3SpectralScalarRawFourier (-G) ξ
      =
    -(h3SpectralScalarRawFourierL2 G : H3FourierPoint3 → ℂ) ξ
  rw [hG]
  unfold h3SpectralScalarRawFourier
  rw [hIn]
  simpa only [Pi.neg_apply] using
    (mul_neg
      (h3SobolevFrequencyWeightInvComplex ξ)
      ((G : H3FourierPoint3 → ℂ) ξ))

@[simp]
theorem h3SpectralScalarRawFourierL2_sub
    (G H : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2 (G - H)
      =
    h3SpectralScalarRawFourierL2 G -
      h3SpectralScalarRawFourierL2 H := by
  simpa only [
    sub_eq_add_neg,
    h3SpectralScalarRawFourierL2_add,
    h3SpectralScalarRawFourierL2_neg
  ]

/-! ## Exact decoder linearity -/

@[simp]
theorem h3SpectralScalarDecodeComplexL2_zero :
    h3SpectralScalarDecodeComplexL2 (0 : H3SpectralScalarState) = 0 := by
  simp [h3SpectralScalarDecodeComplexL2]

@[simp]
theorem h3SpectralScalarDecodeComplexL2_add
    (G H : H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2 (G + H)
      =
    h3SpectralScalarDecodeComplexL2 G +
      h3SpectralScalarDecodeComplexL2 H := by
  simp [h3SpectralScalarDecodeComplexL2]

@[simp]
theorem h3SpectralScalarDecodeComplexL2_neg
    (G : H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2 (-G)
      =
    -h3SpectralScalarDecodeComplexL2 G := by
  simp [h3SpectralScalarDecodeComplexL2]

@[simp]
theorem h3SpectralScalarDecodeComplexL2_sub
    (G H : H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2 (G - H)
      =
    h3SpectralScalarDecodeComplexL2 G -
      h3SpectralScalarDecodeComplexL2 H := by
  simpa only [
    sub_eq_add_neg,
    h3SpectralScalarDecodeComplexL2_add,
    h3SpectralScalarDecodeComplexL2_neg
  ]

/-! ## Real decoder linearity -/

@[simp]
theorem h3RealPartFourierL2_zero :
    h3RealPartFourierL2 (0 : H3FourierComplexL2) = 0 := by
  unfold h3RealPartFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.reCLM.coeFn_compLp (0 : H3FourierComplexL2)
  ] with ξ hZero
  rw [hZero]
  simp

@[simp]
theorem h3RealPartFourierL2_add
    (f g : H3FourierComplexL2) :
    h3RealPartFourierL2 (f + g)
      =
    h3RealPartFourierL2 f + h3RealPartFourierL2 g := by
  unfold h3RealPartFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.reCLM.coeFn_compLp (f + g),
    Complex.reCLM.coeFn_compLp f,
    Complex.reCLM.coeFn_compLp g,
    MeasureTheory.Lp.coeFn_add f g,
    MeasureTheory.Lp.coeFn_add
      (Complex.reCLM.compLp f)
      (Complex.reCLM.compLp g)
  ] with ξ hfg hf hg hIn hOut
  rw [hfg, hOut]
  change
    Complex.reCLM ((f + g : H3FourierComplexL2) ξ)
      =
    (Complex.reCLM.compLp f : H3FourierPoint3 → ℝ) ξ +
      (Complex.reCLM.compLp g : H3FourierPoint3 → ℝ) ξ
  rw [hf, hg, hIn]
  simp

@[simp]
theorem h3RealPartFourierL2_neg
    (f : H3FourierComplexL2) :
    h3RealPartFourierL2 (-f)
      =
    -h3RealPartFourierL2 f := by
  unfold h3RealPartFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.reCLM.coeFn_compLp (-f),
    Complex.reCLM.coeFn_compLp f,
    MeasureTheory.Lp.coeFn_neg f,
    MeasureTheory.Lp.coeFn_neg (Complex.reCLM.compLp f)
  ] with ξ hNeg hf hIn hOut
  rw [hNeg, hOut]
  change
    Complex.reCLM ((-f : H3FourierComplexL2) ξ)
      =
    -(Complex.reCLM.compLp f : H3FourierPoint3 → ℝ) ξ
  rw [hf, hIn]
  simp

@[simp]
theorem h3SpectralScalarDecodeRealL2_zero :
    h3SpectralScalarDecodeRealL2 (0 : H3SpectralScalarState) = 0 := by
  simp [h3SpectralScalarDecodeRealL2]

@[simp]
theorem h3SpectralScalarDecodeRealL2_add
    (G H : H3SpectralScalarState) :
    h3SpectralScalarDecodeRealL2 (G + H)
      =
    h3SpectralScalarDecodeRealL2 G +
      h3SpectralScalarDecodeRealL2 H := by
  simp [h3SpectralScalarDecodeRealL2]

@[simp]
theorem h3SpectralScalarDecodeRealL2_neg
    (G : H3SpectralScalarState) :
    h3SpectralScalarDecodeRealL2 (-G)
      =
    -h3SpectralScalarDecodeRealL2 G := by
  simp [h3SpectralScalarDecodeRealL2]

@[simp]
theorem h3SpectralScalarDecodeRealL2_sub
    (G H : H3SpectralScalarState) :
    h3SpectralScalarDecodeRealL2 (G - H)
      =
    h3SpectralScalarDecodeRealL2 G -
      h3SpectralScalarDecodeRealL2 H := by
  simpa only [
    sub_eq_add_neg,
    h3SpectralScalarDecodeRealL2_add,
    h3SpectralScalarDecodeRealL2_neg
  ]

/-! ## Complexification is additive -/

@[simp]
theorem h3ComplexifyFourierL2_zero :
    h3ComplexifyFourierL2 (0 : H3FourierRealL2) = 0 := by
  unfold h3ComplexifyFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.ofRealCLM.coeFn_compLp (0 : H3FourierRealL2)
  ] with ξ hZero
  rw [hZero]
  simp

@[simp]
theorem h3ComplexifyFourierL2_add
    (f g : H3FourierRealL2) :
    h3ComplexifyFourierL2 (f + g)
      =
    h3ComplexifyFourierL2 f + h3ComplexifyFourierL2 g := by
  unfold h3ComplexifyFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.ofRealCLM.coeFn_compLp (f + g),
    Complex.ofRealCLM.coeFn_compLp f,
    Complex.ofRealCLM.coeFn_compLp g,
    MeasureTheory.Lp.coeFn_add f g,
    MeasureTheory.Lp.coeFn_add
      (Complex.ofRealCLM.compLp f)
      (Complex.ofRealCLM.compLp g)
  ] with ξ hfg hf hg hIn hOut
  rw [hfg, hOut]
  change
    Complex.ofRealCLM ((f + g : H3FourierRealL2) ξ)
      =
    (Complex.ofRealCLM.compLp f : H3FourierPoint3 → ℂ) ξ +
      (Complex.ofRealCLM.compLp g : H3FourierPoint3 → ℂ) ξ
  rw [hf, hg, hIn]
  simp

@[simp]
theorem h3ComplexifyFourierL2_neg
    (f : H3FourierRealL2) :
    h3ComplexifyFourierL2 (-f)
      =
    -h3ComplexifyFourierL2 f := by
  unfold h3ComplexifyFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.ofRealCLM.coeFn_compLp (-f),
    Complex.ofRealCLM.coeFn_compLp f,
    MeasureTheory.Lp.coeFn_neg f,
    MeasureTheory.Lp.coeFn_neg (Complex.ofRealCLM.compLp f)
  ] with ξ hNeg hf hIn hOut
  rw [hNeg, hOut]
  change
    Complex.ofRealCLM ((-f : H3FourierRealL2) ξ)
      =
    -(Complex.ofRealCLM.compLp f : H3FourierPoint3 → ℂ) ξ
  rw [hf, hIn]
  simp

@[simp]
theorem h3ComplexifyFourierL2_sub
    (f g : H3FourierRealL2) :
    h3ComplexifyFourierL2 (f - g)
      =
    h3ComplexifyFourierL2 f - h3ComplexifyFourierL2 g := by
  simpa only [
    sub_eq_add_neg,
    h3ComplexifyFourierL2_add,
    h3ComplexifyFourierL2_neg
  ]

/-! ## Scalar realizability is an additive subgroup property -/

@[simp]
theorem h3SpectralScalarRealizable_zero :
    H3SpectralScalarRealizable (0 : H3SpectralScalarState) := by
  unfold H3SpectralScalarRealizable
  simp

theorem H3SpectralScalarRealizable.add
    {G H : H3SpectralScalarState}
    (hG : H3SpectralScalarRealizable G)
    (hH : H3SpectralScalarRealizable H) :
    H3SpectralScalarRealizable (G + H) := by
  unfold H3SpectralScalarRealizable at hG hH ⊢
  rw [
    h3SpectralScalarDecodeComplexL2_add,
    h3SpectralScalarDecodeRealL2_add,
    h3ComplexifyFourierL2_add,
    hG,
    hH
  ]

theorem H3SpectralScalarRealizable.neg
    {G : H3SpectralScalarState}
    (hG : H3SpectralScalarRealizable G) :
    H3SpectralScalarRealizable (-G) := by
  unfold H3SpectralScalarRealizable at hG ⊢
  rw [
    h3SpectralScalarDecodeComplexL2_neg,
    h3SpectralScalarDecodeRealL2_neg,
    h3ComplexifyFourierL2_neg,
    hG
  ]

theorem H3SpectralScalarRealizable.sub
    {G H : H3SpectralScalarState}
    (hG : H3SpectralScalarRealizable G)
    (hH : H3SpectralScalarRealizable H) :
    H3SpectralScalarRealizable (G - H) := by
  rw [sub_eq_add_neg]
  exact hG.add hH.neg

/-! ## Velocity-state realizability closure -/

@[simp]
theorem h3SpectralVelocityRealizable_zero :
    H3SpectralVelocityRealizable (0 : H3SpectralVelocityState) := by
  intro j
  exact h3SpectralScalarRealizable_zero

theorem H3SpectralVelocityRealizable.add
    {U V : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRealizable U)
    (hV : H3SpectralVelocityRealizable V) :
    H3SpectralVelocityRealizable (U + V) := by
  intro j
  exact (hU j).add (hV j)

theorem H3SpectralVelocityRealizable.neg
    {U : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRealizable U) :
    H3SpectralVelocityRealizable (-U) := by
  intro j
  exact (hU j).neg

theorem H3SpectralVelocityRealizable.sub
    {U V : H3SpectralVelocityState}
    (hU : H3SpectralVelocityRealizable U)
    (hV : H3SpectralVelocityRealizable V) :
    H3SpectralVelocityRealizable (U - V) := by
  intro j
  exact (hU j).sub (hV j)

/-! ## Pointwise realizability of normalized paths -/

/-- A normalized spectral velocity path is physically realizable at every
normalized time. -/
def H3SpectralVelocityPathRealizable
    (U : H3SpectralVelocityPath) : Prop :=
  ∀ s : H3UnitTime, H3SpectralVelocityRealizable (U s)

@[simp]
theorem h3SpectralVelocityPathRealizable_zero :
    H3SpectralVelocityPathRealizable (0 : H3SpectralVelocityPath) := by
  intro s
  exact h3SpectralVelocityRealizable_zero

theorem H3SpectralVelocityPathRealizable.add
    {U V : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRealizable U)
    (hV : H3SpectralVelocityPathRealizable V) :
    H3SpectralVelocityPathRealizable (U + V) := by
  intro s
  exact (hU s).add (hV s)

theorem H3SpectralVelocityPathRealizable.neg
    {U : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRealizable U) :
    H3SpectralVelocityPathRealizable (-U) := by
  intro s
  exact (hU s).neg

theorem H3SpectralVelocityPathRealizable.sub
    {U V : H3SpectralVelocityPath}
    (hU : H3SpectralVelocityPathRealizable U)
    (hV : H3SpectralVelocityPathRealizable V) :
    H3SpectralVelocityPathRealizable (U - V) := by
  intro s
  exact (hU s).sub (hV s)

end

end Euclidean
end Bridge
end PrimeTensor
