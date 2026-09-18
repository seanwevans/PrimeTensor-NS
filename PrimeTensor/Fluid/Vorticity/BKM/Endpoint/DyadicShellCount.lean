import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicShellSum

/-!
# BKM endpoint: exact middle dyadic shell count

The middle-frequency contribution is now reduced to the cardinality of the
natural-number interval indexing the occupied dyadic shells.

For `lo, hi : ℕ`,

    #(Finset.Icc lo hi) = hi + 1 - lo.

Substituting this exact count into the finite shell-sum estimate removes the
remaining abstract `Finset.card` term.  The next checkpoint can compare this
integer dyadic width with the logarithm of the corresponding frequency ratio.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicShellCount
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicShellCount :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact cardinality of the closed natural dyadic-index interval. -/
theorem h3BKMMiddleDyadicShellCount
    (lo hi : ℕ) :
    (Finset.Icc lo hi).card
      =
    hi + 1 - lo := by

  exact
    Nat.card_Icc lo hi

/--
The generic middle dyadic shell sum with the interval cardinality written
explicitly.
-/
theorem norm_h3BKMMiddleDyadicShellSum_le_shellCount_mul
    (lo hi : ℕ)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ z : Point3, ‖f z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum lo hi i k f x‖
      ≤
    ((hi + 1 - lo : ℕ) : ℝ)
      * (M * h3BKMDyadicKernelUnitMassConstant) := by

  have h :=
    norm_h3BKMMiddleDyadicShellSum_le_card_mul
      lo hi i k f M hM hf x

  rw [h3BKMMiddleDyadicShellCount lo hi] at h

  exact h

/-- X-vorticity middle-frequency estimate with the exact shell count. -/
theorem norm_h3BKMMiddleDyadicShellSum_vorticityX_le_shellCount_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (lo hi : ℕ)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum
        lo hi i k (h3BKMPhysicalVorticityX u t) x‖
      ≤
    ((hi + 1 - lo : ℕ) : ℝ)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicShellSum_le_shellCount_mul
      lo
      hi
      i
      k
      (h3BKMPhysicalVorticityX u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityX_le hEnvelope)
      x

/-- Y-vorticity middle-frequency estimate with the exact shell count. -/
theorem norm_h3BKMMiddleDyadicShellSum_vorticityY_le_shellCount_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (lo hi : ℕ)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum
        lo hi i k (h3BKMPhysicalVorticityY u t) x‖
      ≤
    ((hi + 1 - lo : ℕ) : ℝ)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicShellSum_le_shellCount_mul
      lo
      hi
      i
      k
      (h3BKMPhysicalVorticityY u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityY_le hEnvelope)
      x

/-- Z-vorticity middle-frequency estimate with the exact shell count. -/
theorem norm_h3BKMMiddleDyadicShellSum_vorticityZ_le_shellCount_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (lo hi : ℕ)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum
        lo hi i k (h3BKMPhysicalVorticityZ u t) x‖
      ≤
    ((hi + 1 - lo : ℕ) : ℝ)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMMiddleDyadicShellSum_le_shellCount_mul
      lo
      hi
      i
      k
      (h3BKMPhysicalVorticityZ u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityZ_le hEnvelope)
      x

end

end Euclidean
end Bridge
end PrimeTensor
