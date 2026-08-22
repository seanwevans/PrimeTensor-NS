import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral

/-!
# Plancherel bridge for the concrete H³ jet

The spectral H³ solver state introduced in `Sobolev.Spectral` is deliberately
a one-field-per-velocity-component representation.  Before collapsing the
existing 120 derivative slots into that weighted representation, we first
perform a completely assumption-free Plancherel step.

Every concrete real `L²(Point3)` slot is

1. transported isometrically to the Euclidean Fourier carrier,
2. complexified isometrically,
3. transformed by Mathlib's `L²` Fourier isometry.

Thus the complete 120-slot derivative jet has exactly the same sum-of-squares
energy before and after Fourier transform.  Combining this with
`Bridge.Energy` gives

    1 + FourierJetEnergy = velocityH3EnergyAt.

This part requires no Fourier/derivative theorem at all: each derivative slot
is transformed independently.

The second half of the file records the exact remaining analytic boundary.
`VelocityH3FourierCompatibleAt` says that the Fourier transforms of the
pointwise Euclidean derivative slots are the expected products by

    2 π i ξ_k.

Proving this predicate from the existing `VelocityH3IntegrableAt` hypotheses
requires identifying the project's pointwise `deriv` derivatives with weak /
distributional derivatives.  We expose that obligation explicitly instead of
silently strengthening the hypotheses to Schwartz or `L¹`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3Plancherel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3Plancherel :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Complexification is an exact L² isometry -/

/--
Real projection after complexification is exactly the original real `L²`
class.
-/
theorem h3RealPartFourierL2_complexify_eq
    (f : H3FourierRealL2) :
    h3RealPartFourierL2 (h3ComplexifyFourierL2 f) = f := by
  unfold h3RealPartFourierL2 h3ComplexifyFourierL2
  apply MeasureTheory.Lp.ext
  filter_upwards [
    Complex.reCLM.coeFn_compLp (Complex.ofRealCLM.compLp f),
    Complex.ofRealCLM.coeFn_compLp f
  ] with ξ hre hof
  rw [hre, hof]
  simp

/-- Complexification preserves the `L²` norm exactly. -/
theorem norm_h3ComplexifyFourierL2_eq
    (f : H3FourierRealL2) :
    ‖h3ComplexifyFourierL2 f‖ = ‖f‖ := by
  apply le_antisymm
  · exact norm_h3ComplexifyFourierL2_le f
  · calc
      ‖f‖
          = ‖h3RealPartFourierL2
              (h3ComplexifyFourierL2 f)‖ := by
              rw [h3RealPartFourierL2_complexify_eq]
      _ ≤ ‖h3ComplexifyFourierL2 f‖ :=
        norm_h3RealPartFourierL2_le _

/-! ## Scalar and jet Fourier transforms -/

/--
The canonical complex `L²` Fourier transform of a project scalar `L²` class.
-/
def h3ScalarFourierL2
    (f : H3ScalarL2) :
    H3FourierComplexL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
    (h3ComplexifyFourierL2 (h3ToFourierRealL2 f))

/-- The scalar Fourier bridge is an exact `L²` isometry. -/
theorem norm_h3ScalarFourierL2
    (f : H3ScalarL2) :
    ‖h3ScalarFourierL2 f‖ = ‖f‖ := by
  unfold h3ScalarFourierL2
  calc
    ‖(MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3ComplexifyFourierL2 (h3ToFourierRealL2 f))‖
        =
      ‖h3ComplexifyFourierL2 (h3ToFourierRealL2 f)‖ :=
      MeasureTheory.Lp.norm_fourier_eq _
    _ = ‖h3ToFourierRealL2 f‖ :=
      norm_h3ComplexifyFourierL2_eq _
    _ = ‖f‖ :=
      norm_h3ToFourierRealL2 f

/-- Fourier-side copy of all 120 concrete H³ derivative slots. -/
abbrev H3FourierJetState : Type :=
  H3JetIndex → H3FourierComplexL2

/-- Apply the scalar Plancherel transform independently to every jet slot. -/
def h3L2JetFourierApply
    (J : H3L2JetState) :
    H3FourierJetState :=
  fun a => h3ScalarFourierL2 (J a)

@[simp]
theorem h3L2JetFourierApply_apply
    (J : H3L2JetState)
    (a : H3JetIndex) :
    h3L2JetFourierApply J a =
      h3ScalarFourierL2 (J a) :=
  rfl

/-- Fourier transform preserves every individual jet coordinate norm. -/
theorem norm_h3L2JetFourierApply_coordinate
    (J : H3L2JetState)
    (a : H3JetIndex) :
    ‖h3L2JetFourierApply J a‖ = ‖J a‖ := by
  exact norm_h3ScalarFourierL2 (J a)

/-- Sum-of-squares energy of a 120-slot Fourier jet. -/
def h3FourierJetSquareEnergy
    (F : H3FourierJetState) : ℝ :=
  ∑ a : H3JetIndex, ‖F a‖ ^ 2

/-- Plancherel preserves the full 120-coordinate jet energy exactly. -/
theorem h3FourierJetSquareEnergy_h3L2JetFourierApply
    (J : H3L2JetState) :
    h3FourierJetSquareEnergy (h3L2JetFourierApply J)
      = h3L2JetSquareEnergy J := by
  unfold h3FourierJetSquareEnergy h3L2JetSquareEnergy
  apply Finset.sum_congr rfl
  intro a ha
  rw [norm_h3L2JetFourierApply_coordinate]

/-- Fourier jet of an actual logged H³ velocity snapshot. -/
def velocityH3FourierJetAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    H3FourierJetState :=
  h3L2JetFourierApply
    (velocityH3L2JetAt u t hInt hMeas)

@[simp]
theorem velocityH3FourierJetAt_apply
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (a : H3JetIndex) :
    velocityH3FourierJetAt u t hInt hMeas a =
      h3ScalarFourierL2
        (velocityH3L2JetAt u t hInt hMeas a) :=
  rfl

/--
Exact normalized Plancherel identity for the full H³ velocity snapshot.
-/
theorem one_add_h3FourierJetSquareEnergy_velocityH3FourierJetAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    1 +
      h3FourierJetSquareEnergy
        (velocityH3FourierJetAt u t hInt hMeas)
      =
      velocityH3EnergyAt u t := by
  calc
    1 +
        h3FourierJetSquareEnergy
          (velocityH3FourierJetAt u t hInt hMeas)
        =
      1 +
        h3L2JetSquareEnergy
          (velocityH3L2JetAt u t hInt hMeas) := by
          rw [velocityH3FourierJetAt]
          rw [h3FourierJetSquareEnergy_h3L2JetFourierApply]
    _ = velocityH3EnergyAt u t :=
      one_add_h3L2JetSquareEnergy_velocityH3L2JetAt_eq
        hInt hMeas

/-! ## Semantic jet-slot constructors -/

/-- Zeroth-order slot for velocity component `j`. -/
def h3JetSlot0
    (j : Fin 3) :
    H3JetIndex :=
  Sum.inl j

/-- First-order slot `∂ᵢ uⱼ`. -/
def h3JetSlot1
    (j i : Fin 3) :
    H3JetIndex :=
  Sum.inr (Sum.inl (j, i))

/-- Second-order slot `∂ᵢ ∂ₖ uⱼ`. -/
def h3JetSlot2
    (j i k : Fin 3) :
    H3JetIndex :=
  Sum.inr (Sum.inr (Sum.inl (j, (i, k))))

/-- Third-order slot `∂ᵢ ∂ₖ ∂ₗ uⱼ`. -/
def h3JetSlot3
    (j i k l : Fin 3) :
    H3JetIndex :=
  Sum.inr (Sum.inr (Sum.inr (j, (i, (k, l)))))

/-! ## Fourier derivative symbol -/

/--
Fourier multiplier for one Euclidean coordinate derivative under Mathlib's
`exp (-2π i x·ξ)` convention.
-/
def h3FourierDerivativeSymbol
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  (2 * Real.pi * Complex.I) *
    (ξ (h3AxisOfFin3 i) : ℂ)

/-- Product of two coordinate-derivative symbols. -/
def h3FourierDerivativeSymbol2
    (i k : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol i ξ *
    h3FourierDerivativeSymbol k ξ

/-- Product of three coordinate-derivative symbols. -/
def h3FourierDerivativeSymbol3
    (i k l : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol i ξ *
    h3FourierDerivativeSymbol k ξ *
    h3FourierDerivativeSymbol l ξ

/-! ## Explicit derivative/Fourier compatibility boundary -/

/--
The exact analytic compatibility still required to collapse the Fourier jet to
one weighted Fourier field per velocity component.

It asserts, almost everywhere in frequency, that each already-constructed
Fourier transform of a concrete pointwise derivative slot equals the expected
coordinate multiplier times the Fourier transform of the underlying component.

This predicate is intentionally *not* derived merely from
`VelocityH3IntegrableAt`: doing so requires a separate theorem identifying
`spatial3.d` (defined using Mathlib's total pointwise `deriv`) with the
corresponding weak/distributional derivative under the H³ regularity
hypotheses.
-/
def VelocityH3FourierCompatibleAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) : Prop :=
  ∀ j : Fin 3,
    (∀ i : Fin 3,
      (velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot1 j i) : H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      fun ξ =>
        h3FourierDerivativeSymbol i ξ *
          velocityH3FourierJetAt u t hInt hMeas
            (h3JetSlot0 j) ξ)
    ∧
    (∀ i k : Fin 3,
      (velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot2 j i k) : H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      fun ξ =>
        h3FourierDerivativeSymbol2 i k ξ *
          velocityH3FourierJetAt u t hInt hMeas
            (h3JetSlot0 j) ξ)
    ∧
    (∀ i k l : Fin 3,
      (velocityH3FourierJetAt u t hInt hMeas
          (h3JetSlot3 j i k l) : H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      fun ξ =>
        h3FourierDerivativeSymbol3 i k l ξ *
          velocityH3FourierJetAt u t hInt hMeas
            (h3JetSlot0 j) ξ)

/--
The zeroth-order Fourier field for one velocity component.
-/
def velocityH3BaseFourierAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  velocityH3FourierJetAt u t hInt hMeas
    (h3JetSlot0 j)

/--
Under Fourier compatibility, every first derivative multiplier of the base
field agrees a.e. with the corresponding concrete derivative slot.
-/
theorem velocityH3FourierCompatibleAt_orderOne
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i : Fin 3) :
    (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot1 j i) : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    fun ξ =>
      h3FourierDerivativeSymbol i ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ := by
  exact (hFourier j).1 i

/--
Under Fourier compatibility, every second derivative multiplier of the base
field agrees a.e. with the corresponding concrete derivative slot.
-/
theorem velocityH3FourierCompatibleAt_orderTwo
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i k : Fin 3) :
    (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot2 j i k) : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    fun ξ =>
      h3FourierDerivativeSymbol2 i k ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ := by
  exact (hFourier j).2.1 i k

/--
Under Fourier compatibility, every third derivative multiplier of the base
field agrees a.e. with the corresponding concrete derivative slot.
-/
theorem velocityH3FourierCompatibleAt_orderThree
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i k l : Fin 3) :
    (velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot3 j i k l) : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    fun ξ =>
      h3FourierDerivativeSymbol3 i k l ξ *
        velocityH3BaseFourierAt u t hInt hMeas j ξ := by
  exact (hFourier j).2.2 i k l

end

end Euclidean
end Bridge
end PrimeTensor
