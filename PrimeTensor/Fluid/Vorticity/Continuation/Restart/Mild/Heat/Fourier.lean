import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge.Energy
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fourier heat evolution on the concrete H³ L² jet state

This file begins the genuinely PDE-specific mild layer.  The concrete H³ state
uses `L²(Point3)` where `Point3 = Axis.three → ℝ` carries the ordinary finite
product sup norm.  Mathlib's `L²` Fourier transform, however, is formulated on
a finite-dimensional real inner-product space.  We therefore transport each
scalar `L²(Point3)` class through the canonical volume-preserving equivalence

    Axis.three → ℝ  ↔  EuclideanSpace ℝ Axis.three,

apply the Fourier multiplier

    exp (-4 π² ν t |ξ|²),

and transport back.  This avoids installing a mathematically false inner-product
structure on the sup-norm `Point3` carrier.

The multiplier has modulus at most one for nonnegative viscosity and time, so
the scalar heat evolution is an `L²` contraction.  We then lift it coordinatewise
to the concrete 120-slot H³ jet and obtain both sup-norm contraction and
sum-of-squares energy dissipation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3HeatFourier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3HeatFourier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Euclidean copy of the three-dimensional spatial frequency carrier. -/
abbrev H3FourierPoint3 : Type :=
  EuclideanSpace ℝ (PrimeTensor.Axis Depth.three)

/-- Real scalar `L²` on the Euclidean Fourier carrier. -/
abbrev H3FourierRealL2 : Type :=
  MeasureTheory.Lp ℝ 2 (volume : Measure H3FourierPoint3)

/-- Complex scalar `L²` on the Euclidean Fourier carrier. -/
abbrev H3FourierComplexL2 : Type :=
  MeasureTheory.Lp ℂ 2 (volume : Measure H3FourierPoint3)

/-! ## Volume-preserving transport between the project carrier and Fourier carrier -/

/-- Transport a project scalar `L²(Point3)` class to the Euclidean Fourier carrier. -/
def h3ToFourierRealL2
    (f : H3ScalarL2) : H3FourierRealL2 :=
  MeasureTheory.Lp.compMeasurePreserving
    (WithLp.ofLp : H3FourierPoint3 → Point3)
    (PiLp.volume_preserving_ofLp (PrimeTensor.Axis Depth.three))
    f

/-- Transport a Euclidean Fourier real `L²` class back to `L²(Point3)`. -/
def h3FromFourierRealL2
    (f : H3FourierRealL2) : H3ScalarL2 :=
  MeasureTheory.Lp.compMeasurePreserving
    (WithLp.toLp 2 : Point3 → H3FourierPoint3)
    (PiLp.volume_preserving_toLp (PrimeTensor.Axis Depth.three))
    f

/-- Transport to the Fourier carrier preserves the scalar `L²` norm. -/
theorem norm_h3ToFourierRealL2
    (f : H3ScalarL2) :
    ‖h3ToFourierRealL2 f‖ = ‖f‖ := by
  unfold h3ToFourierRealL2
  exact
    MeasureTheory.Lp.norm_compMeasurePreserving
      f
      (PiLp.volume_preserving_ofLp (PrimeTensor.Axis Depth.three))

/-- Transport back from the Fourier carrier preserves the scalar `L²` norm. -/
theorem norm_h3FromFourierRealL2
    (f : H3FourierRealL2) :
    ‖h3FromFourierRealL2 f‖ = ‖f‖ := by
  unfold h3FromFourierRealL2
  exact
    MeasureTheory.Lp.norm_compMeasurePreserving
      f
      (PiLp.volume_preserving_toLp (PrimeTensor.Axis Depth.three))

/-! ## Heat multiplier -/

/--
The Fourier multiplier of `exp (ν t Δ)` for Mathlib's Fourier convention
`exp (-2π i x·ξ)`.
-/
def h3HeatFourierSymbol
    (ν t : ℝ)
    (ξ : H3FourierPoint3) : ℂ :=
  Complex.ofReal
    (Real.exp (-((2 * Real.pi) ^ 2 * ν * t * ‖ξ‖ ^ 2)))

/-- The heat Fourier symbol depends continuously on frequency. -/
theorem continuous_h3HeatFourierSymbol
    (ν t : ℝ) :
    Continuous (h3HeatFourierSymbol ν t) := by
  unfold h3HeatFourierSymbol
  fun_prop

/-- For nonnegative viscosity and time, the heat symbol has modulus at most one. -/
theorem norm_h3HeatFourierSymbol_le_one
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (ξ : H3FourierPoint3) :
    ‖h3HeatFourierSymbol ν t ξ‖ ≤ 1 := by
  have hprod :
      0 ≤ (2 * Real.pi) ^ 2 * ν * t * ‖ξ‖ ^ 2 := by
    positivity
  have hexp :
      Real.exp (-((2 * Real.pi) ^ 2 * ν * t * ‖ξ‖ ^ 2)) ≤ 1 := by
    calc
      Real.exp (-((2 * Real.pi) ^ 2 * ν * t * ‖ξ‖ ^ 2))
          ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr hprod)
      _ = 1 := Real.exp_zero
  unfold h3HeatFourierSymbol
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hexp

/-! ## Complexification and real projection on the Fourier carrier -/

/-- Embed a real Fourier-carrier `L²` class into complex `L²` pointwise. -/
def h3ComplexifyFourierL2
    (f : H3FourierRealL2) : H3FourierComplexL2 :=
  Complex.ofRealCLM.compLp f

/-- Take the real part of a complex Fourier-carrier `L²` class pointwise. -/
def h3RealPartFourierL2
    (f : H3FourierComplexL2) : H3FourierRealL2 :=
  Complex.reCLM.compLp f

/-- Complexification does not increase the Fourier-carrier `L²` norm. -/
theorem norm_h3ComplexifyFourierL2_le
    (f : H3FourierRealL2) :
    ‖h3ComplexifyFourierL2 f‖ ≤ ‖f‖ := by
  unfold h3ComplexifyFourierL2
  apply MeasureTheory.Lp.norm_le_norm_of_ae_le
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
  rw [hx]
  simp [Real.norm_eq_abs]

/-- Taking real part does not increase the Fourier-carrier `L²` norm. -/
theorem norm_h3RealPartFourierL2_le
    (f : H3FourierComplexL2) :
    ‖h3RealPartFourierL2 f‖ ≤ ‖f‖ := by
  unfold h3RealPartFourierL2
  apply MeasureTheory.Lp.norm_le_norm_of_ae_le
  filter_upwards [Complex.reCLM.coeFn_compLp f] with x hx
  rw [hx]
  simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (f x)

/-! ## Multiplication by the heat symbol in frequency space -/

/-- Multiplication by the bounded heat symbol preserves complex `L²`. -/
theorem h3HeatFrequency_memLp
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (f : H3FourierComplexL2) :
    MemLp
      (fun ξ : H3FourierPoint3 => h3HeatFourierSymbol ν t ξ * f ξ)
      2 volume := by
  refine (MeasureTheory.Lp.memLp f).of_le_mul (c := 1) ?_ ?_
  · exact
      (continuous_h3HeatFourierSymbol ν t).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable f)
  · filter_upwards with ξ
    calc
      ‖h3HeatFourierSymbol ν t ξ * f ξ‖
          = ‖h3HeatFourierSymbol ν t ξ‖ * ‖f ξ‖ := norm_mul _ _
      _ ≤ 1 * ‖f ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3HeatFourierSymbol_le_one hν ht ξ)
          (norm_nonneg _)

/-- Apply the heat multiplier to one complex `L²` function in frequency space. -/
def h3HeatFrequencyApply
    (ν t : ℝ)
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (f : H3FourierComplexL2) : H3FourierComplexL2 :=
  (h3HeatFrequency_memLp hν ht f).toLp
    (fun ξ : H3FourierPoint3 => h3HeatFourierSymbol ν t ξ * f ξ)

/-- The frequency-space heat multiplier is an `L²` contraction. -/
theorem norm_h3HeatFrequencyApply_le
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (f : H3FourierComplexL2) :
    ‖h3HeatFrequencyApply ν t hν ht f‖ ≤ ‖f‖ := by
  unfold h3HeatFrequencyApply
  apply MeasureTheory.Lp.norm_le_norm_of_ae_le
  filter_upwards [
    MeasureTheory.MemLp.coeFn_toLp
      (h3HeatFrequency_memLp hν ht f)
  ] with ξ hx
  rw [hx]
  calc
    ‖h3HeatFourierSymbol ν t ξ * f ξ‖
        = ‖h3HeatFourierSymbol ν t ξ‖ * ‖f ξ‖ := norm_mul _ _
    _ ≤ 1 * ‖f ξ‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h3HeatFourierSymbol_le_one hν ht ξ)
        (norm_nonneg _)
    _ = ‖f ξ‖ := one_mul _

/-! ## Scalar heat evolution -/

/-- Inverse Fourier transform is an isometry on complex Fourier-carrier `L²`. -/
theorem norm_fourierInv_h3FourierComplexL2
    (f : H3FourierComplexL2) :
    ‖(MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm f‖ = ‖f‖ := by
  exact (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm.norm_map f

/-- Complex `L²` heat evolution via Fourier multiplier. -/
def h3ComplexHeatApply
    (ν t : ℝ)
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (f : H3FourierComplexL2) : H3FourierComplexL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
    (h3HeatFrequencyApply ν t hν ht
      ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) f))

/-- The complex Fourier heat evolution is an `L²` contraction. -/
theorem norm_h3ComplexHeatApply_le
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (f : H3FourierComplexL2) :
    ‖h3ComplexHeatApply ν t hν ht f‖ ≤ ‖f‖ := by
  unfold h3ComplexHeatApply
  rw [norm_fourierInv_h3FourierComplexL2]
  calc
    ‖h3HeatFrequencyApply ν t hν ht
        ((MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) f)‖
        ≤ ‖(MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) f‖ :=
      norm_h3HeatFrequencyApply_le hν ht _
    _ = ‖f‖ :=
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).norm_map f

/--
Real scalar heat evolution on the project's `L²(Point3)` state.  It is defined
by volume-preserving transport to Euclidean space, complexification, the exact
Fourier heat multiplier, inverse transform, real projection, and transport back.
-/
def h3ScalarHeatApply
    (ν t : ℝ)
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (f : H3ScalarL2) : H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      (h3ComplexHeatApply ν t hν ht
        (h3ComplexifyFourierL2 (h3ToFourierRealL2 f))))

/-- The real scalar heat evolution is an `L²` contraction. -/
theorem norm_h3ScalarHeatApply_le
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (f : H3ScalarL2) :
    ‖h3ScalarHeatApply ν t hν ht f‖ ≤ ‖f‖ := by
  unfold h3ScalarHeatApply
  rw [norm_h3FromFourierRealL2]
  calc
    ‖h3RealPartFourierL2
        (h3ComplexHeatApply ν t hν ht
          (h3ComplexifyFourierL2 (h3ToFourierRealL2 f)))‖
        ≤ ‖h3ComplexHeatApply ν t hν ht
          (h3ComplexifyFourierL2 (h3ToFourierRealL2 f))‖ :=
      norm_h3RealPartFourierL2_le _
    _ ≤ ‖h3ComplexifyFourierL2 (h3ToFourierRealL2 f)‖ :=
      norm_h3ComplexHeatApply_le hν ht _
    _ ≤ ‖h3ToFourierRealL2 f‖ :=
      norm_h3ComplexifyFourierL2_le _
    _ = ‖f‖ := norm_h3ToFourierRealL2 f

/-! ## Coordinatewise heat evolution on the concrete H³ jet -/

/-- Apply the scalar heat evolution to every derivative slot. -/
def h3L2JetHeatApply
    (ν t : ℝ)
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (J : H3L2JetState) : H3L2JetState :=
  fun a => h3ScalarHeatApply ν t hν ht (J a)

@[simp]
theorem h3L2JetHeatApply_apply
    (ν t : ℝ)
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (J : H3L2JetState)
    (a : H3JetIndex) :
    h3L2JetHeatApply ν t hν ht J a =
      h3ScalarHeatApply ν t hν ht (J a) :=
  rfl

/-- Coordinatewise heat evolution contracts the finite-product jet norm. -/
theorem norm_h3L2JetHeatApply_le
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (J : H3L2JetState) :
    ‖h3L2JetHeatApply ν t hν ht J‖ ≤ ‖J‖ := by
  apply
    (pi_norm_le_iff_of_nonneg (norm_nonneg J)).2
  intro a
  calc
    ‖h3L2JetHeatApply ν t hν ht J a‖
        ≤ ‖J a‖ := norm_h3ScalarHeatApply_le hν ht (J a)
    _ ≤ ‖J‖ := h3L2Jet_coordinate_norm_le J a

/-- The sum-of-squares jet energy is dissipated by the heat evolution. -/
theorem h3L2JetSquareEnergy_heat_le
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t)
    (J : H3L2JetState) :
    h3L2JetSquareEnergy (h3L2JetHeatApply ν t hν ht J)
      ≤ h3L2JetSquareEnergy J := by
  unfold h3L2JetSquareEnergy
  apply Finset.sum_le_sum
  intro a ha
  have hnorm := norm_h3ScalarHeatApply_le hν ht (J a)
  have hleft : 0 ≤ ‖h3ScalarHeatApply ν t hν ht (J a)‖ := norm_nonneg _
  have hright : 0 ≤ ‖J a‖ := norm_nonneg _
  change
    ‖h3ScalarHeatApply ν t hν ht (J a)‖ ^ 2 ≤ ‖J a‖ ^ 2
  nlinarith

/--
For a genuine logged H³ snapshot, heat evolution is controlled by the square
root of the existing canonical H³ energy.
-/
theorem norm_h3L2JetHeatApply_velocityH3L2JetAt_le_sqrt_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t₀ ν t : ℝ}
    (hInt : VelocityH3IntegrableAt u t₀)
    (hMeas : VelocityH3MeasurableAt u t₀)
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t) :
    ‖h3L2JetHeatApply ν t hν ht
        (velocityH3L2JetAt u t₀ hInt hMeas)‖
      ≤ Real.sqrt (velocityH3EnergyAt u t₀) := by
  calc
    ‖h3L2JetHeatApply ν t hν ht
        (velocityH3L2JetAt u t₀ hInt hMeas)‖
        ≤ ‖velocityH3L2JetAt u t₀ hInt hMeas‖ :=
      norm_h3L2JetHeatApply_le hν ht _
    _ ≤ Real.sqrt (velocityH3EnergyAt u t₀) :=
      velocityH3L2JetAt_norm_le_sqrt_energy hInt hMeas

end

end Euclidean
end Bridge
end PrimeTensor
