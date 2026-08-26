import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Derivative.Continuity

/-!
# Positive-time continuity of the Fin-indexed heat--Leray kernel

`HeatDerivativeContinuity` proves positive-time strong continuity of one scalar
heat-derivative multiplier.  This file lifts that result through:

* the finite three-coordinate divergence sum,
* the velocity outer-product input for fixed states,
* and the bounded Fourier Leray multiplier.

The resulting zero-extended heat--Leray kernel is continuous on `(0, ∞)` for
each fixed pair of H³ spectral velocity states.

This is deliberately the fixed-input continuity checkpoint.  The next file
will combine it with bilinearity and continuity of `U(s), V(s)` to obtain
continuity of the full retarded path integrand on `0 < s < t`, then use the
already-proved reciprocal-square-root majorant to conclude genuine Bochner
interval integrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-! ## The Leray multiplier is a Lipschitz map -/

/--
The lifted Leray multiplier is `6`-Lipschitz in the finite-product sup norm.

This is exactly the coarse operator constant already proved in
`FinLerayMultiplier`.
-/
theorem lipschitzWith_h3SpectralFinLerayApply :
    LipschitzWith 6
      (h3SpectralFinLerayApply :
        H3SpectralFinVectorState →
          H3SpectralFinVectorState) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  rw [dist_eq_norm]
  rw [dist_eq_norm]
  rw [← h3SpectralFinLerayApply_sub]
  norm_num
  exact
    norm_h3SpectralFinLerayApply_le (F - G)

/-- The lifted Leray multiplier is continuous. -/
theorem continuous_h3SpectralFinLerayApply :
    Continuous
      (h3SpectralFinLerayApply :
        H3SpectralFinVectorState →
          H3SpectralFinVectorState) :=
  lipschitzWith_h3SpectralFinLerayApply.continuous

/-! ## Zero-extended finite heat divergence -/

/--
Zero-extended finite tensor heat-divergence operator.

It is written coordinatewise using the scalar zero extension from
`HeatDerivativeContinuity`, so positive-time continuity is inherited by a
finite sum.
-/
noncomputable def h3SpectralFinTensorHeatDivergenceApplyZero
    (ν t : ℝ)
    (hν : 0 < ν)
    (T : H3SpectralFinTensorState) :
    H3SpectralFinVectorState :=
  fun i =>
    ∑ j : Fin 3,
      h3SpectralScalarHeatDerivativeApplyZero
        ν t hν j (T i j)

/-- At positive time, the zero extension is the genuine heat-divergence operator. -/
theorem h3SpectralFinTensorHeatDivergenceApplyZero_of_pos
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (T : H3SpectralFinTensorState) :
    h3SpectralFinTensorHeatDivergenceApplyZero
        ν t hν T
      =
    h3SpectralFinTensorHeatDivergenceApply
        ν t hν ht T := by
  funext i
  unfold h3SpectralFinTensorHeatDivergenceApplyZero
  unfold h3SpectralFinTensorHeatDivergenceApply
  apply Finset.sum_congr rfl
  intro j _hj
  exact
    h3SpectralScalarHeatDerivativeApplyZero_of_pos
      hν ht j (T i j)

/-- For a fixed tensor, finite heat divergence is strongly continuous for positive time. -/
theorem continuousOn_h3SpectralFinTensorHeatDivergenceApplyZero
    {ν : ℝ}
    (hν : 0 < ν)
    (T : H3SpectralFinTensorState) :
    ContinuousOn
      (fun t : ℝ =>
        h3SpectralFinTensorHeatDivergenceApplyZero
          ν t hν T)
      (Set.Ioi (0 : ℝ)) := by
  rw [continuousOn_pi]
  intro i
  unfold h3SpectralFinTensorHeatDivergenceApplyZero
  apply continuousOn_finsetSum
  intro j _hj
  exact
    continuousOn_h3SpectralScalarHeatDerivativeApplyZero
      hν j (T i j)

/-! ## Fixed-input velocity heat divergence -/

/-- Zero-extended pre-Leray velocity kernel for fixed spatial inputs. -/
noncomputable def h3SpectralFinVelocityHeatDivergenceApplyZero
    (ν t : ℝ)
    (hν : 0 < ν)
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  h3SpectralFinTensorHeatDivergenceApplyZero
    ν t hν (h3SpectralFinOuterProduct U V)

/-- At positive time this is the genuine pre-Leray velocity kernel. -/
theorem h3SpectralFinVelocityHeatDivergenceApplyZero_of_pos
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    h3SpectralFinVelocityHeatDivergenceApplyZero
        ν t hν U V
      =
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U V := by
  unfold h3SpectralFinVelocityHeatDivergenceApplyZero
  unfold h3SpectralFinVelocityHeatDivergenceApply
  exact
    h3SpectralFinTensorHeatDivergenceApplyZero_of_pos
      hν ht (h3SpectralFinOuterProduct U V)

/-- The fixed-input pre-Leray velocity kernel is continuous on positive time. -/
theorem continuousOn_h3SpectralFinVelocityHeatDivergenceApplyZero
    {ν : ℝ}
    (hν : 0 < ν)
    (U V : H3SpectralFinVectorState) :
    ContinuousOn
      (fun t : ℝ =>
        h3SpectralFinVelocityHeatDivergenceApplyZero
          ν t hν U V)
      (Set.Ioi (0 : ℝ)) := by
  unfold h3SpectralFinVelocityHeatDivergenceApplyZero
  exact
    continuousOn_h3SpectralFinTensorHeatDivergenceApplyZero
      hν (h3SpectralFinOuterProduct U V)

/-! ## Fixed-input full heat--Leray kernel -/

/-- Zero-extended genuine heat--Leray velocity kernel. -/
noncomputable def h3SpectralFinHeatLerayVelocityApplyZero
    (ν t : ℝ)
    (hν : 0 < ν)
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  h3SpectralFinLerayApply
    (h3SpectralFinVelocityHeatDivergenceApplyZero
      ν t hν U V)

/-- At positive time, the zero extension is the genuine heat--Leray kernel. -/
theorem h3SpectralFinHeatLerayVelocityApplyZero_of_pos
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayVelocityApplyZero
        ν t hν U V
      =
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U V := by
  unfold h3SpectralFinHeatLerayVelocityApplyZero
  unfold h3SpectralFinHeatLerayVelocityApply
  rw [
    h3SpectralFinVelocityHeatDivergenceApplyZero_of_pos
      hν ht U V
  ]

/--
For fixed H³ spectral velocity states, the genuine heat--Leray kernel is
strongly continuous on positive elapsed time.
-/
theorem continuousOn_h3SpectralFinHeatLerayVelocityApplyZero
    {ν : ℝ}
    (hν : 0 < ν)
    (U V : H3SpectralFinVectorState) :
    ContinuousOn
      (fun t : ℝ =>
        h3SpectralFinHeatLerayVelocityApplyZero
          ν t hν U V)
      (Set.Ioi (0 : ℝ)) := by
  unfold h3SpectralFinHeatLerayVelocityApplyZero
  exact
    continuous_h3SpectralFinLerayApply.comp_continuousOn
      (continuousOn_h3SpectralFinVelocityHeatDivergenceApplyZero
        hν U V)

end

end Euclidean
end Bridge
end PrimeTensor
