import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralHeatDivergencePhysicalClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralLerayReality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayBilinear

/-!
# Physical closure under the finite Leray projector

The previous checkpoint realizes the decoded positive-time heat divergence as
an `L²` limit of finite sums of genuine Schwartz-product heat-derivative
anchors.  The remaining instantaneous operation in the nonlinear mild kernel
is the finite Leray projector.

On physical `L²` we realize Leray by Fourier transform, application of the
existing finite spectral Leray multiplier, and inverse Fourier transform.  The
Fourier maps are isometries and the finite Leray multiplier already has the
coarse operator bound `6`, so this physical operator is `6`-Lipschitz.

Exact deweighting commutes with each Leray matrix entry.  Hence decoding the
weighted spectral Leray output agrees exactly with applying this physical
Leray operator to the decoded input.  The heat-divergence physical closure can
therefore be transported through Leray without any additional regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Set
open scoped ENNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatLerayPhysicalClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Finite Leray projection acting directly on complex physical `L²` vectors:
Fourier transform coordinatewise, apply the existing finite spectral Leray
matrix, then inverse Fourier transform coordinatewise. -/
noncomputable def h3PhysicalFinLerayApply
    (u : H3ComplexPhysicalFinVectorL2) :
    H3ComplexPhysicalFinVectorL2 :=
  fun i =>
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
      (h3SpectralFinLerayApply
        (fun j =>
          (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) (u j)) i)

@[simp]
theorem h3PhysicalFinLerayApply_apply
    (u : H3ComplexPhysicalFinVectorL2)
    (i : Fin 3) :
    h3PhysicalFinLerayApply u i
      =
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm
      (h3SpectralFinLerayApply
        (fun j =>
          (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) (u j)) i) :=
  rfl

/-- Fourier transform applied coordinatewise does not increase the finite
product sup norm.  In fact it is an isometry; the one-sided form is all that
is needed below. -/
theorem norm_h3PhysicalFinVector_fourier_le
    (u : H3ComplexPhysicalFinVectorL2) :
    ‖(fun j : Fin 3 =>
        (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) (u j))‖
      ≤ ‖u‖ := by
  have hnonneg : 0 ≤ ‖u‖ := norm_nonneg _
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro j
  rw [(MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).norm_map]
  exact h3SpectralFinVector_coordinate_norm_le u j

/-- The physical finite Leray projector inherits the existing coarse operator
bound `6`. -/
theorem norm_h3PhysicalFinLerayApply_le
    (u : H3ComplexPhysicalFinVectorL2) :
    ‖h3PhysicalFinLerayApply u‖ ≤ 6 * ‖u‖ := by
  have hRhs : 0 ≤ 6 * ‖u‖ := by positivity
  apply (pi_norm_le_iff_of_nonneg hRhs).2
  intro i
  rw [h3PhysicalFinLerayApply_apply]
  rw [(MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm.norm_map]
  calc
    ‖h3SpectralFinLerayApply
        (fun j : Fin 3 =>
          (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) (u j)) i‖
        ≤
      ‖h3SpectralFinLerayApply
        (fun j : Fin 3 =>
          (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) (u j))‖ :=
      h3SpectralFinVector_coordinate_norm_le _ i
    _ ≤
      6 * ‖(fun j : Fin 3 =>
        (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) (u j))‖ :=
      norm_h3SpectralFinLerayApply_le _
    _ ≤ 6 * ‖u‖ :=
      mul_le_mul_of_nonneg_left
        (norm_h3PhysicalFinVector_fourier_le u)
        (by norm_num)

/-- Physical Leray is linear with respect to subtraction. -/
theorem h3PhysicalFinLerayApply_sub
    (u v : H3ComplexPhysicalFinVectorL2) :
    h3PhysicalFinLerayApply (u - v)
      = h3PhysicalFinLerayApply u - h3PhysicalFinLerayApply v := by
  funext i
  unfold h3PhysicalFinLerayApply
  have hFourierSub :
      (fun j : Fin 3 =>
        (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) ((u - v) j))
        =
      (fun j : Fin 3 =>
        (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) (u j))
        -
      (fun j : Fin 3 =>
        (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ) (v j)) := by
    funext j
    simp only [Pi.sub_apply, map_sub]
  rw [hFourierSub]
  rw [h3SpectralFinLerayApply_sub]
  simp only [Pi.sub_apply, map_sub]

/-- The physical finite Leray projector is `6`-Lipschitz in the finite-product
physical `L²` norm. -/
theorem dist_h3PhysicalFinLerayApply_le
    (u v : H3ComplexPhysicalFinVectorL2) :
    dist (h3PhysicalFinLerayApply u) (h3PhysicalFinLerayApply v)
      ≤ 6 * dist u v := by
  simp only [dist_eq_norm]
  rw [← h3PhysicalFinLerayApply_sub]
  exact norm_h3PhysicalFinLerayApply_le (u - v)

/-- Exact deweighting commutes with arbitrary finite sums. -/
theorem h3SpectralScalarRawFourierL2_sum
    {ι : Type}
    (s : Finset ι)
    (F : ι → H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2 (s.sum F)
      =
    s.sum (fun j => h3SpectralScalarRawFourierL2 (F j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih]

/-- Exact deweighting commutes with the full finite Leray matrix. -/
theorem h3SpectralFinLerayApply_rawFourierL2_apply
    (G : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3SpectralScalarRawFourierL2 (h3SpectralFinLerayApply G i)
      =
    h3SpectralFinLerayApply
      (fun j => h3SpectralScalarRawFourierL2 (G j)) i := by
  unfold h3SpectralFinLerayApply
  rw [h3SpectralScalarRawFourierL2_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact h3SpectralScalarRawFourierL2_lerayCoefficientApply i j (G j)

/-- Decoding the weighted spectral Leray projection agrees exactly with
applying the physical Leray operator to the decoded vector. -/
theorem h3SpectralFinVectorDecodeComplexL2_lerayApply
    (G : H3SpectralFinVectorState) :
    h3SpectralFinVectorDecodeComplexL2 (h3SpectralFinLerayApply G)
      =
    h3PhysicalFinLerayApply (h3SpectralFinVectorDecodeComplexL2 G) := by
  funext i
  rw [h3SpectralFinVectorDecodeComplexL2_apply]
  rw [h3PhysicalFinLerayApply_apply]
  unfold h3SpectralScalarDecodeComplexL2
  rw [h3SpectralFinLerayApply_rawFourierL2_apply]
  simp only [h3SpectralFinVectorDecodeComplexL2_apply]
  rw [show
    (fun j : Fin 3 =>
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3SpectralScalarDecodeComplexL2 (G j)))
      =
    (fun j : Fin 3 => h3SpectralScalarRawFourierL2 (G j)) by
      funext j
      exact h3Fourier_h3SpectralScalarDecodeComplexL2 (G j)]

/-- A physical finite vector is a heat--Leray Schwartz anchor when it is the
physical Leray image of one of the genuine heat-divergence Schwartz anchors
from the previous checkpoint. -/
def H3SchwartzHeatLerayPhysicalFinVectorL2Anchor
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (u : H3ComplexPhysicalFinVectorL2) : Prop :=
  ∃ v : H3ComplexPhysicalFinVectorL2,
    H3SchwartzHeatDivergencePhysicalFinVectorL2Anchor ν t hν ht v ∧
    u = h3PhysicalFinLerayApply v

/-- Epsilon realization of the complete decoded positive-time heat--Leray
nonlinearity by physical Leray images of genuine Schwartz-product
heat-divergence anchors. -/
theorem exists_h3SchwartzHeatLerayPhysicalFinVectorL2Anchor_dist_lt
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ u : H3ComplexPhysicalFinVectorL2,
      H3SchwartzHeatLerayPhysicalFinVectorL2Anchor ν t hν ht u ∧
      dist
        (h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayVelocityApply ν t hν ht U V))
        u < ε := by
  have hδ : 0 < ε / 12 := by linarith

  obtain ⟨v, hAnchor, hDist⟩ :=
    exists_h3SchwartzHeatDivergencePhysicalFinVectorL2Anchor_dist_lt
      hν ht U V hδ

  let u : H3ComplexPhysicalFinVectorL2 :=
    h3PhysicalFinLerayApply v

  refine ⟨u, ?_, ?_⟩
  · exact ⟨v, hAnchor, rfl⟩
  · have hLip :=
      dist_h3PhysicalFinLerayApply_le
        (h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V))
        v

    calc
      dist
          (h3SpectralFinVectorDecodeComplexL2
            (h3SpectralFinHeatLerayVelocityApply ν t hν ht U V))
          u
          =
        dist
          (h3PhysicalFinLerayApply
            (h3SpectralFinVectorDecodeComplexL2
              (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V)))
          (h3PhysicalFinLerayApply v) := by
            dsimp [u]
            unfold h3SpectralFinHeatLerayVelocityApply
            rw [h3SpectralFinVectorDecodeComplexL2_lerayApply]
      _ ≤
        6 * dist
          (h3SpectralFinVectorDecodeComplexL2
            (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V))
          v := hLip
      _ < 6 * (ε / 12) :=
        mul_lt_mul_of_pos_left hDist (by norm_num)
      _ = ε / 2 := by ring
      _ < ε := by linarith

/-- Closure form for the complete decoded positive-time heat--Leray nonlinear
kernel. -/
theorem h3SpectralFinHeatLerayVelocity_decodeComplexL2_mem_closure
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayVelocityApply ν t hν ht U V)
      ∈ closure
        {u : H3ComplexPhysicalFinVectorL2 |
          H3SchwartzHeatLerayPhysicalFinVectorL2Anchor ν t hν ht u} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨u, hAnchor, hDist⟩ :=
    exists_h3SchwartzHeatLerayPhysicalFinVectorL2Anchor_dist_lt
      hν ht U V hε
  exact ⟨u, hAnchor, hDist⟩

end

end Euclidean
end Bridge
end PrimeTensor
