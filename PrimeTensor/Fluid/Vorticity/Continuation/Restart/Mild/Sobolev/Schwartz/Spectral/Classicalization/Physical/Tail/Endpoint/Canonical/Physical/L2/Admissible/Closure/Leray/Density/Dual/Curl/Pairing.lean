import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Test

/-!
# Classicalization: extract weak curl identities from solenoidal annihilation

`Dual.Curl.Test` constructed the three compact smooth divergence-free tests

    curl01(ψ) = ( ∂₁ψ, -∂₀ψ,      0 ),
    curl02(ψ) = ( ∂₂ψ,      0, -∂₀ψ ),
    curl12(ψ) = (     0,  ∂₂ψ, -∂₁ψ ).

This file feeds those tests into the annihilator hypothesis from
`Dual.Reduction`.

For a physical `L²` vector `V`, annihilation of all compact smooth
divergence-free tests therefore implies, for every scalar weak test `ψ`,

    ⟪V₀, ∂₁ψ⟫ - ⟪V₁, ∂₀ψ⟫ = 0,
    ⟪V₀, ∂₂ψ⟫ - ⟪V₂, ∂₀ψ⟫ = 0,
    ⟪V₁, ∂₂ψ⟫ - ⟪V₂, ∂₁ψ⟫ = 0.

These are exactly the three distributional curl-zero identities, written
entirely inside the physical `L²` Hilbert pairing API.

The only bookkeeping added here is that the canonical `L²` package of weak
test functions respects zero and negation.  Both facts are proved by `Lp.ext`
from the existing almost-everywhere representative theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlPairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Linearity bookkeeping for scalar weak-test `L²` packaging -/

@[simp]
theorem h3WeakTestFunctionPhysicalL2_zero :
    h3WeakTestFunctionPhysicalL2
        (0 : H3WeakTestFunction)
      =
    (0 : H3ScalarL2) := by
  apply MeasureTheory.Lp.ext

  have hTest :=
    h3WeakTestFunctionPhysicalL2_ae
      (0 : H3WeakTestFunction)

  have hLpZero :=
    MeasureTheory.Lp.coeFn_zero
      ℝ
      (2 : ℝ≥0∞)
      (volume : Measure Point3)

  filter_upwards [hTest, hLpZero] with x hTestx hLpZerox

  rw [hTestx, hLpZerox]
  rfl

@[simp]
theorem h3WeakTestFunctionPhysicalL2_neg
    (ψ : H3WeakTestFunction) :
    h3WeakTestFunctionPhysicalL2 (-ψ)
      =
    - h3WeakTestFunctionPhysicalL2 ψ := by
  apply MeasureTheory.Lp.ext

  have hNeg :=
    h3WeakTestFunctionPhysicalL2_ae (-ψ)

  have hPos :=
    h3WeakTestFunctionPhysicalL2_ae ψ

  have hLpNeg :=
    MeasureTheory.Lp.coeFn_neg
      (h3WeakTestFunctionPhysicalL2 ψ)

  filter_upwards [hNeg, hPos, hLpNeg] with x hNegx hPosx hLpNegx

  rw [hNegx, hLpNegx]

  change
    - ψ x
      =
    - (h3WeakTestFunctionPhysicalL2 ψ : Point3 → ℝ) x

  exact
    congrArg Neg.neg hPosx.symm

/-! ## Coordinate expansion of the finite physical Hilbert pairing -/

/-- Pairing an arbitrary physical `L²` vector with an embedded weak-test vector
is the finite sum of coordinatewise scalar `L²` pairings. -/
theorem inner_h3PhysicalRealFinVectorL2Hilbert_weakTestVector
    (V : H3PhysicalRealFinVectorL2Hilbert)
    (φ : H3WeakTestVector) :
    inner ℝ
        V
        (h3WeakTestVectorPhysicalL2Hilbert φ)
      =
    ∑ i : Fin 3,
      inner ℝ
        (V i)
        (h3WeakTestFunctionPhysicalL2 (φ i)) := by
  unfold h3WeakTestVectorPhysicalL2Hilbert
  rw [PiLp.inner_apply]

/-! ## Weak curl-free predicate -/

/-- The three scalar distributional curl-zero identities for a physical
three-component `L²` vector.

The derivatives remain on the compact smooth scalar test `ψ`; this is the
correct weak formulation for an arbitrary `L²` vector. -/
def H3PhysicalRealFinVectorL2HilbertWeakCurlFree
    (V : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  ∀ ψ : H3WeakTestFunction,
    inner ℝ
        (V 0)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 1)
            ψ))
      -
      inner ℝ
        (V 1)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 0)
            ψ))
      =
    0
    ∧
    inner ℝ
        (V 0)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 2)
            ψ))
      -
      inner ℝ
        (V 2)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 0)
            ψ))
      =
    0
    ∧
    inner ℝ
        (V 1)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 2)
            ψ))
      -
      inner ℝ
        (V 2)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 1)
            ψ))
      =
    0

/-! ## Each curl identity follows from the corresponding curl test -/

theorem h3WeakCurl01_pairing_eq_zero_of_annihilates_divergenceFreeWeakTests
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hAnnihilates :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            V
            (h3WeakTestVectorPhysicalL2Hilbert φ)
          =
        0)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        (V 0)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 1)
            ψ))
      -
      inner ℝ
        (V 1)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 0)
            ψ))
      =
    0 := by
  have hPair :=
    hAnnihilates
      (h3WeakTestCurl01 ψ)
      (h3WeakTestCurl01_divergenceFree ψ)

  rw [
    inner_h3PhysicalRealFinVectorL2Hilbert_weakTestVector,
    Fin.sum_univ_three
  ] at hPair

  simpa only [
    h3WeakTestCurl01_apply_zero,
    h3WeakTestCurl01_apply_one,
    h3WeakTestCurl01_apply_two,
    h3WeakTestFunctionPhysicalL2_neg,
    h3WeakTestFunctionPhysicalL2_zero,
    inner_neg_right,
    inner_zero_right,
    add_zero,
    sub_eq_add_neg
  ] using hPair

theorem h3WeakCurl02_pairing_eq_zero_of_annihilates_divergenceFreeWeakTests
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hAnnihilates :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            V
            (h3WeakTestVectorPhysicalL2Hilbert φ)
          =
        0)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        (V 0)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 2)
            ψ))
      -
      inner ℝ
        (V 2)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 0)
            ψ))
      =
    0 := by
  have hPair :=
    hAnnihilates
      (h3WeakTestCurl02 ψ)
      (h3WeakTestCurl02_divergenceFree ψ)

  rw [
    inner_h3PhysicalRealFinVectorL2Hilbert_weakTestVector,
    Fin.sum_univ_three
  ] at hPair

  simpa only [
    h3WeakTestCurl02_apply_zero,
    h3WeakTestCurl02_apply_one,
    h3WeakTestCurl02_apply_two,
    h3WeakTestFunctionPhysicalL2_neg,
    h3WeakTestFunctionPhysicalL2_zero,
    inner_neg_right,
    inner_zero_right,
    zero_add,
    add_zero,
    sub_eq_add_neg
  ] using hPair

theorem h3WeakCurl12_pairing_eq_zero_of_annihilates_divergenceFreeWeakTests
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hAnnihilates :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            V
            (h3WeakTestVectorPhysicalL2Hilbert φ)
          =
        0)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        (V 1)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 2)
            ψ))
      -
      inner ℝ
        (V 2)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 1)
            ψ))
      =
    0 := by
  have hPair :=
    hAnnihilates
      (h3WeakTestCurl12 ψ)
      (h3WeakTestCurl12_divergenceFree ψ)

  rw [
    inner_h3PhysicalRealFinVectorL2Hilbert_weakTestVector,
    Fin.sum_univ_three
  ] at hPair

  simpa only [
    h3WeakTestCurl12_apply_zero,
    h3WeakTestCurl12_apply_one,
    h3WeakTestCurl12_apply_two,
    h3WeakTestFunctionPhysicalL2_neg,
    h3WeakTestFunctionPhysicalL2_zero,
    inner_neg_right,
    inner_zero_right,
    zero_add,
    sub_eq_add_neg
  ] using hPair

/-! ## All three identities at once -/

/-- Annihilation of every compact smooth divergence-free weak test forces the
physical `L²` vector to be weakly curl-free. -/
theorem h3PhysicalRealFinVectorL2Hilbert_weakCurlFree_of_annihilates_divergenceFreeWeakTests
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hAnnihilates :
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ
            V
            (h3WeakTestVectorPhysicalL2Hilbert φ)
          =
        0) :
    H3PhysicalRealFinVectorL2HilbertWeakCurlFree V := by
  intro ψ

  exact
    ⟨
      h3WeakCurl01_pairing_eq_zero_of_annihilates_divergenceFreeWeakTests
        hAnnihilates ψ,
      h3WeakCurl02_pairing_eq_zero_of_annihilates_divergenceFreeWeakTests
        hAnnihilates ψ,
      h3WeakCurl12_pairing_eq_zero_of_annihilates_divergenceFreeWeakTests
        hAnnihilates ψ
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
