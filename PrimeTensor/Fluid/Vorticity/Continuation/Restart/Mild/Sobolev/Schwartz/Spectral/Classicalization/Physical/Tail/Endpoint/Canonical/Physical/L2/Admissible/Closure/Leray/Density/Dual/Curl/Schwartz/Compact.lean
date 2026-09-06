import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Fourier.Tempered

/-!
# Classicalization: compact Schwartz tests are already weak curl tests

The Fourier/tempered reduction has isolated one remaining analytic statement:

    compact weak-test curl-free  ==>  tempered-distribution curl-free.

Before doing the genuinely analytic density step, this file removes a purely
representational ambiguity.

A real Schwartz function on the physical carrier `Point3` which has compact
support is automatically one of the project's scalar weak test functions:

* it is `C^∞` because it is Schwartz;
* it has compact support by hypothesis;
* its support is automatically contained in the full open set.

Thus the weak-curl identities already proved for `H3WeakTestFunction` apply
verbatim to every compactly supported physical Schwartz scalar.

We package this as an explicit compact-Schwartz curl predicate.  The next
checkpoint can therefore focus only on extending these identities from compact
Schwartz tests to arbitrary Schwartz tests.  No Leray or Fourier algebra is
left in that step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCompact
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCompact :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Compact physical Schwartz scalars as weak tests -/

/-- Real Schwartz scalar functions on the physical carrier. -/
abbrev H3PhysicalScalarSchwartz : Type :=
  𝓢(Point3, ℝ)

/-- A compactly supported physical Schwartz scalar, bundled as the project's
ordinary scalar weak test function. -/
noncomputable def h3CompactPhysicalSchwartzToWeakTest
    (ψ : H3PhysicalScalarSchwartz)
    (hψ : HasCompactSupport (ψ : Point3 → ℝ)) :
    H3WeakTestFunction :=
  ⟨
    (ψ : Point3 → ℝ),
    ψ.smooth _,
    hψ,
    Set.subset_univ _
  ⟩

@[simp]
theorem h3CompactPhysicalSchwartzToWeakTest_apply
    (ψ : H3PhysicalScalarSchwartz)
    (hψ : HasCompactSupport (ψ : Point3 → ℝ))
    (x : Point3) :
    h3CompactPhysicalSchwartzToWeakTest ψ hψ x = ψ x := by
  rfl

/-- The bundled weak-test coordinate derivative has exactly the project's
ordinary spatial derivative of the original compact Schwartz scalar as its
underlying function. -/
theorem h3CompactPhysicalSchwartzToWeakTest_spatialDerivative_eq
    (ψ : H3PhysicalScalarSchwartz)
    (hψ : HasCompactSupport (ψ : Point3 → ℝ))
    (i : Fin 3) :
    (h3WeakTestFunctionSpatialDerivative
        (h3AxisOfFin3 i)
        (h3CompactPhysicalSchwartzToWeakTest ψ hψ) :
      Point3 → ℝ)
      =
    spatial3.d
      (h3AxisOfFin3 i)
      (ψ : Point3 → ℝ) := by
  exact
    h3WeakTestFunctionSpatialDerivative_eq_spatial3_d
      (h3CompactPhysicalSchwartzToWeakTest ψ hψ)
      i

/-! ## Compact-Schwartz weak curl predicate -/

/-- The same three weak curl identities as
`H3PhysicalRealFinVectorL2HilbertWeakCurlFree`, restricted to compactly
supported physical Schwartz scalar tests.

The derivative is intentionally kept in the already-green weak-test `L²`
package.  This makes the implication from the existing weak predicate exact,
without introducing a second derivative realization before it is needed. -/
def H3PhysicalRealFinVectorL2HilbertCompactSchwartzCurlFree
    (V : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  ∀ (ψ : H3PhysicalScalarSchwartz)
      (hψ : HasCompactSupport (ψ : Point3 → ℝ)),
    inner ℝ
        (V 0)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 1)
            (h3CompactPhysicalSchwartzToWeakTest ψ hψ)))
      -
      inner ℝ
        (V 1)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 0)
            (h3CompactPhysicalSchwartzToWeakTest ψ hψ)))
      =
    0
    ∧
    inner ℝ
        (V 0)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 2)
            (h3CompactPhysicalSchwartzToWeakTest ψ hψ)))
      -
      inner ℝ
        (V 2)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 0)
            (h3CompactPhysicalSchwartzToWeakTest ψ hψ)))
      =
    0
    ∧
    inner ℝ
        (V 1)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 2)
            (h3CompactPhysicalSchwartzToWeakTest ψ hψ)))
      -
      inner ℝ
        (V 2)
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 1)
            (h3CompactPhysicalSchwartzToWeakTest ψ hψ)))
      =
    0

/-! ## Existing weak curl-freeness already gives compact-Schwartz curl-freeness -/

/-- No new analysis is needed for compact Schwartz tests: they are literally
members of the weak-test space, so the previously proved weak-curl identities
specialize immediately. -/
theorem h3PhysicalRealFinVectorL2Hilbert_compactSchwartzCurlFree_of_weakCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak :
      H3PhysicalRealFinVectorL2HilbertWeakCurlFree V) :
    H3PhysicalRealFinVectorL2HilbertCompactSchwartzCurlFree V := by
  intro ψ hψ

  exact
    hWeak
      (h3CompactPhysicalSchwartzToWeakTest ψ hψ)

/-! ## Exact remaining extension frontier -/

/-- The remaining analytic extension theorem, isolated from all weak-test
bundling: compactly supported physical Schwartz curl identities suffice to
produce the tempered-distribution curl identities.

The next checkpoint will prove this by continuity/density. -/
def H3PhysicalL2CompactSchwartzCurlFreeImpliesTemperedCurlFree : Prop :=
  ∀ V : H3PhysicalRealFinVectorL2Hilbert,
    H3PhysicalRealFinVectorL2HilbertCompactSchwartzCurlFree V →
    H3PhysicalRealFinVectorL2HilbertTemperedCurlFree V

/-- Once the compact-Schwartz extension theorem is available, the weak-to-
tempered bridge isolated in `Fourier.Tempered` follows immediately. -/
theorem H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree_of_compactSchwartzExtension
    (hExtension :
      H3PhysicalL2CompactSchwartzCurlFreeImpliesTemperedCurlFree) :
    H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree := by
  intro V hWeak

  exact
    hExtension
      V
      (h3PhysicalRealFinVectorL2Hilbert_compactSchwartzCurlFree_of_weakCurlFree
        hWeak)

/-- Hence the same compact-Schwartz extension theorem is sufficient for the
full parameter-free physical Leray-density result. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_compactSchwartzExtension
    (hExtension :
      H3PhysicalL2CompactSchwartzCurlFreeImpliesTemperedCurlFree) :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan := by
  exact
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_temperedBridge
      (H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree_of_compactSchwartzExtension
        hExtension)

end

end Euclidean
end Bridge
end PrimeTensor
