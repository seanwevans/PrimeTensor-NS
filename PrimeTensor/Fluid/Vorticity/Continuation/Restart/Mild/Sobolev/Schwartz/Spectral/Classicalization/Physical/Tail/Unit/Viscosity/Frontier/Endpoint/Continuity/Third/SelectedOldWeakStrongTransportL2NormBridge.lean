import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongTransportIntegralBound

/-!
# Selected--old weak--strong transport: physical L² norm bridge

The weak--strong transport estimate has reached the whole-space square-density
integral.  This file identifies that density with the native norm on the
three-component physical `L²` Hilbert product.

For one real scalar `L²` state,

    ‖f‖² = ∫ f(x)² dx.

For the finite `PiLp 2` product this gives

    ‖V‖² = Σ_j ∫ V_j(x)² dx
          = ∫ (V_0(x)² + V_1(x)² + V_2(x)²) dx.

This is entirely quotient-native: no selected/old classical representatives
are used yet.  The next layer only has to identify those classical
representatives almost everywhere with the coordinates of the concrete
selected-minus-old `L²` difference.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportL2NormBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongTransportL2NormBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3SelectedOldWeakStrongTransportL2NormBridge Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Real scalar `L²` norm squared is the integral of the pointwise square. -/
theorem h3ScalarL2_norm_sq_eq_integral_sq
    (f : H3ScalarL2) :
    ‖f‖ ^ 2
      =
    ∫ x : Point3, (f x) ^ 2 := by
  calc
    ‖f‖ ^ 2
        =
      inner ℝ f f := by
        symm
        exact real_inner_self_eq_norm_sq f
    _ =
      ∫ x : Point3, inner ℝ (f x) (f x) := by
        rw [MeasureTheory.L2.inner_def]
    _ =
      ∫ x : Point3, (f x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [
          real_inner_self_eq_norm_sq,
          Real.norm_eq_abs,
          sq_abs
        ]

/-- The squared norm of the physical three-component Hilbert product is the
sum of the three scalar square integrals. -/
theorem h3PhysicalRealFinVectorL2_norm_sq_eq_sum_integral_sq
    (V : H3PhysicalRealFinVectorL2Hilbert) :
    ‖V‖ ^ 2
      =
    ∑ j : Fin 3,
      ∫ x : Point3, (V j x) ^ 2 := by
  calc
    ‖V‖ ^ 2
        =
      inner ℝ V V := by
        symm
        exact real_inner_self_eq_norm_sq V
    _ =
      ∑ j : Fin 3,
        inner ℝ (V j) (V j) := by
          rw [PiLp.inner_apply]
    _ =
      ∑ j : Fin 3,
        ‖V j‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact real_inner_self_eq_norm_sq (V j)
    _ =
      ∑ j : Fin 3,
        ∫ x : Point3, (V j x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact h3ScalarL2_norm_sq_eq_integral_sq (V j)

/-- Native pointwise square density of a physical three-component `L²`
Hilbert state. -/
noncomputable def h3PhysicalRealFinVectorL2SquareDensity
    (V : H3PhysicalRealFinVectorL2Hilbert)
    (x : Point3) : ℝ :=
  (V (0 : Fin 3) x) ^ 2
    +
  (
    (V (1 : Fin 3) x) ^ 2
      +
    (V (2 : Fin 3) x) ^ 2
  )

/-- The native three-component square density is integrable. -/
theorem h3PhysicalRealFinVectorL2SquareDensity_integrable
    (V : H3PhysicalRealFinVectorL2Hilbert) :
    MeasureTheory.Integrable
      (h3PhysicalRealFinVectorL2SquareDensity V)
      (volume : Measure Point3) := by
  have h0norm :
      MeasureTheory.Integrable
        (fun x : Point3 => ‖V (0 : Fin 3) x‖ ^ 2)
        (volume : Measure Point3) :=
    (MeasureTheory.Lp.memLp (V (0 : Fin 3))).integrable_norm_pow
      (by norm_num)

  have h1norm :
      MeasureTheory.Integrable
        (fun x : Point3 => ‖V (1 : Fin 3) x‖ ^ 2)
        (volume : Measure Point3) :=
    (MeasureTheory.Lp.memLp (V (1 : Fin 3))).integrable_norm_pow
      (by norm_num)

  have h2norm :
      MeasureTheory.Integrable
        (fun x : Point3 => ‖V (2 : Fin 3) x‖ ^ 2)
        (volume : Measure Point3) :=
    (MeasureTheory.Lp.memLp (V (2 : Fin 3))).integrable_norm_pow
      (by norm_num)

  have h0 :
      MeasureTheory.Integrable
        (fun x : Point3 => (V (0 : Fin 3) x) ^ 2)
        (volume : Measure Point3) := by
    simpa only [Real.norm_eq_abs, sq_abs] using h0norm

  have h1 :
      MeasureTheory.Integrable
        (fun x : Point3 => (V (1 : Fin 3) x) ^ 2)
        (volume : Measure Point3) := by
    simpa only [Real.norm_eq_abs, sq_abs] using h1norm

  have h2 :
      MeasureTheory.Integrable
        (fun x : Point3 => (V (2 : Fin 3) x) ^ 2)
        (volume : Measure Point3) := by
    simpa only [Real.norm_eq_abs, sq_abs] using h2norm

  unfold h3PhysicalRealFinVectorL2SquareDensity
  exact h0.add (h1.add h2)

/-- Exact quotient-level bridge:

    ∫ |V(x)|² dx = ‖V‖²

for the native three-component physical `L²` Hilbert product. -/
theorem integral_h3PhysicalRealFinVectorL2SquareDensity_eq_norm_sq
    (V : H3PhysicalRealFinVectorL2Hilbert) :
    (∫ x : Point3,
      h3PhysicalRealFinVectorL2SquareDensity V x)
      =
    ‖V‖ ^ 2 := by
  have h0norm :
      MeasureTheory.Integrable
        (fun x : Point3 => ‖V (0 : Fin 3) x‖ ^ 2)
        (volume : Measure Point3) :=
    (MeasureTheory.Lp.memLp (V (0 : Fin 3))).integrable_norm_pow
      (by norm_num)

  have h1norm :
      MeasureTheory.Integrable
        (fun x : Point3 => ‖V (1 : Fin 3) x‖ ^ 2)
        (volume : Measure Point3) :=
    (MeasureTheory.Lp.memLp (V (1 : Fin 3))).integrable_norm_pow
      (by norm_num)

  have h2norm :
      MeasureTheory.Integrable
        (fun x : Point3 => ‖V (2 : Fin 3) x‖ ^ 2)
        (volume : Measure Point3) :=
    (MeasureTheory.Lp.memLp (V (2 : Fin 3))).integrable_norm_pow
      (by norm_num)

  have h0 :
      MeasureTheory.Integrable
        (fun x : Point3 => (V (0 : Fin 3) x) ^ 2)
        (volume : Measure Point3) := by
    simpa only [Real.norm_eq_abs, sq_abs] using h0norm

  have h1 :
      MeasureTheory.Integrable
        (fun x : Point3 => (V (1 : Fin 3) x) ^ 2)
        (volume : Measure Point3) := by
    simpa only [Real.norm_eq_abs, sq_abs] using h1norm

  have h2 :
      MeasureTheory.Integrable
        (fun x : Point3 => (V (2 : Fin 3) x) ^ 2)
        (volume : Measure Point3) := by
    simpa only [Real.norm_eq_abs, sq_abs] using h2norm

  have h12 :
      (∫ x : Point3,
        (V (1 : Fin 3) x) ^ 2
          +
        (V (2 : Fin 3) x) ^ 2)
        =
      (∫ x : Point3, (V (1 : Fin 3) x) ^ 2)
        +
      (∫ x : Point3, (V (2 : Fin 3) x) ^ 2) := by
    exact MeasureTheory.integral_add h1 h2

  have h012 :
      (∫ x : Point3,
        (V (0 : Fin 3) x) ^ 2
          +
        (
          (V (1 : Fin 3) x) ^ 2
            +
          (V (2 : Fin 3) x) ^ 2
        ))
        =
      (∫ x : Point3, (V (0 : Fin 3) x) ^ 2)
        +
      (∫ x : Point3,
        (V (1 : Fin 3) x) ^ 2
          +
        (V (2 : Fin 3) x) ^ 2) := by
    exact MeasureTheory.integral_add h0 (h1.add h2)

  calc
    (∫ x : Point3,
      h3PhysicalRealFinVectorL2SquareDensity V x)
        =
      (∫ x : Point3, (V (0 : Fin 3) x) ^ 2)
        +
      (
        (∫ x : Point3, (V (1 : Fin 3) x) ^ 2)
          +
        (∫ x : Point3, (V (2 : Fin 3) x) ^ 2)
      ) := by
        unfold h3PhysicalRealFinVectorL2SquareDensity
        rw [h012, h12]
    _ =
      ∑ j : Fin 3,
        ∫ x : Point3, (V j x) ^ 2 := by
        rw [Fin.sum_univ_three]
        ring
    _ =
      ‖V‖ ^ 2 := by
        symm
        exact
          h3PhysicalRealFinVectorL2_norm_sq_eq_sum_integral_sq V

end

end Euclidean
end Bridge
end PrimeTensor
