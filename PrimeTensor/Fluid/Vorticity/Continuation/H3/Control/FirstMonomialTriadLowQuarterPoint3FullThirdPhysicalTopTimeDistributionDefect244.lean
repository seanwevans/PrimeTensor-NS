import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionPrimitive244
import Mathlib.Tactic

/-!
# Physical momentum time distribution: exact homogeneous defect reduction

The previous module proves that the canonical time primitive of the projected
physical source has distributional derivative equal to that source.

Consequently the *still-to-be-established* projected momentum distributional
PDE on a strict interval is equivalent to a homogeneous distributional
equation for the difference between actual momentum and source primitive.
This module makes the reduction exact and exposes the precise remaining
uniqueness problem. It does NOT silently infer the PDE from its pointwise
spatially tested version, nor infer constancy from a zero distributional
derivative without proving the associated connected-interval lemma.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- The regular time distribution of actual scalar momentum minus the
regular time distribution of the actual projected source's canonical
primitive. This is not a pointwise derivative or a zero-discrepancy axiom. -/
noncomputable def h3PathPhysicalTestFTCDefectDistribution244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) (φ : H3WeakTestVector) :
    Distribution (h3PathStrictTimeOpen244 a b) ℝ ⊤ :=
  h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b)
      (h3PathPhysicalTestMomentumTime244 hH3 φ) -
    h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b)
      (fun t : ℝ => ∫ s in a..t,
        h3PathPhysicalTestProjectedSourceTime244 hH3 φ s)

/-- **Exact analytic reduction:** the physical time-distribution momentum
identity holds if and only if the distributional derivative of the physical
momentum-minus-primitive defect vanishes. The forward source-primitive
identity is unconditional; the physical momentum PDE is not assumed here. -/
theorem h3Path_distributionalMomentum_iff_defectDerivativeZero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b ↔
      ∀ φ : H3WeakTestVector, H3WeakTestVectorDivergenceFree φ →
        Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
          (h3PathPhysicalTestFTCDefectDistribution244 hH3 a b φ) =
            (0 : Distribution (h3PathStrictTimeOpen244 a b) ℝ ⊤) := by
  let Ω : Opens ℝ := h3PathStrictTimeOpen244 a b
  let D : Distribution Ω ℝ ⊤ →L[ℝ] Distribution Ω ℝ ⊤ :=
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ)
  constructor
  · intro hMomentum φ hφ
    let M : Distribution Ω ℝ ⊤ :=
      h3PathRegularTimeDistribution244 Ω
        (h3PathPhysicalTestMomentumTime244 hH3 φ)
    let J : Distribution Ω ℝ ⊤ :=
      h3PathRegularTimeDistribution244 Ω
        (fun t : ℝ => ∫ s in a..t,
          h3PathPhysicalTestProjectedSourceTime244 hH3 φ s)
    let R : Distribution Ω ℝ ⊤ :=
      h3PathRegularTimeDistribution244 Ω
        (h3PathPhysicalTestProjectedSourceTime244 hH3 φ)
    have hM : D M = R := hMomentum φ hφ
    have hJ : D J = R :=
      h3Path_physicalProjectedSourcePrimitive_distributionalDerivative244
        hH3 ha hab hb φ
    change D (M - J) = 0
    rw [D.map_sub, hM, hJ, sub_self]
  · intro hDefect φ hφ
    let M : Distribution Ω ℝ ⊤ :=
      h3PathRegularTimeDistribution244 Ω
        (h3PathPhysicalTestMomentumTime244 hH3 φ)
    let J : Distribution Ω ℝ ⊤ :=
      h3PathRegularTimeDistribution244 Ω
        (fun t : ℝ => ∫ s in a..t,
          h3PathPhysicalTestProjectedSourceTime244 hH3 φ s)
    let R : Distribution Ω ℝ ⊤ :=
      h3PathRegularTimeDistribution244 Ω
        (h3PathPhysicalTestProjectedSourceTime244 hH3 φ)
    have hZero : D (M - J) = 0 := hDefect φ hφ
    have hJ : D J = R :=
      h3Path_physicalProjectedSourcePrimitive_distributionalDerivative244
        hH3 ha hab hb φ
    change D M = R
    rw [D.map_sub, hJ] at hZero
    exact sub_eq_zero.mp hZero

end
end PrimeTensor.FirstMonomialTriad
