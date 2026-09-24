import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Kernel.Constant

/-!
# BKM endpoint: finite dyadic shell sums

The coordinate-kernel bookkeeping is now uniform in both radius and coordinate
pair.  This checkpoint performs the next finite-dimensional step: summing a
bounded dyadic convolution over a finite collection of shells.

For the standard dyadic radius

    Rₙ = 2ⁿ,

every shell contribution is bounded by the same BKM kernel constant.  Hence a
finite shell sum is bounded by its cardinality times that constant.  The final
theorems specialize the index set to a natural interval `Finset.Icc lo hi`;
the next checkpoint can identify that cardinality explicitly and convert the
number of occupied shells into a logarithmic frequency factor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicShellSum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicShellSum :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Standard positive dyadic frequency radius `2ⁿ`. -/
def h3BKMDyadicRadius
    (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n

/-- Every standard dyadic radius is strictly positive. -/
theorem h3BKMDyadicRadius_pos
    (n : ℕ) :
    0 < h3BKMDyadicRadius n := by

  unfold h3BKMDyadicRadius
  positivity

/--
Finite sum of one coordinate dyadic BKM convolution over a collection of shell
indices.
-/
noncomputable def h3BKMPhysicalDyadicShellSum
    (J : Finset ℕ)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (x : Point3) : ℂ :=
  ∑ n ∈ J,
    h3BKMPhysicalConvolution
      (h3BKMDyadicPhysicalKernel
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        i
        k)
      f
      x

/--
A finite collection of dyadic shells costs at most its cardinality times the
single scale-independent BKM kernel constant.
-/
theorem norm_h3BKMPhysicalDyadicShellSum_le_card_mul
    (J : Finset ℕ)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ z : Point3, ‖f z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMPhysicalDyadicShellSum J i k f x‖
      ≤
    (J.card : ℝ)
      * (M * h3BKMDyadicKernelUnitMassConstant) := by

  unfold h3BKMPhysicalDyadicShellSum

  calc
    ‖∑ n ∈ J,
        h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i
            k)
          f
          x‖
        ≤
      ∑ n ∈ J,
        ‖h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            i
            k)
          f
          x‖ := by
      exact
        norm_sum_le
          J
          (fun n =>
            h3BKMPhysicalConvolution
              (h3BKMDyadicPhysicalKernel
                (h3BKMDyadicRadius n)
                (h3BKMDyadicRadius_pos n)
                i
                k)
              f
              x)

    _ ≤
      ∑ _n ∈ J,
        M * h3BKMDyadicKernelUnitMassConstant := by
      exact
        Finset.sum_le_sum
          (fun n _hn =>
            norm_h3BKMPhysicalConvolution_dyadic_le_constant
              (h3BKMDyadicRadius_pos n)
              i
              k
              f
              M
              hM
              hf
              x)

    _ =
      (J.card : ℝ)
        * (M * h3BKMDyadicKernelUnitMassConstant) := by
      simp

/-- X-vorticity specialization of the finite shell-count estimate. -/
theorem norm_h3BKMPhysicalDyadicShellSum_vorticityX_le_card_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (J : Finset ℕ)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalDyadicShellSum
        J i k (h3BKMPhysicalVorticityX u t) x‖
      ≤
    (J.card : ℝ)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMPhysicalDyadicShellSum_le_card_mul
      J
      i
      k
      (h3BKMPhysicalVorticityX u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityX_le hEnvelope)
      x

/-- Y-vorticity specialization of the finite shell-count estimate. -/
theorem norm_h3BKMPhysicalDyadicShellSum_vorticityY_le_card_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (J : Finset ℕ)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalDyadicShellSum
        J i k (h3BKMPhysicalVorticityY u t) x‖
      ≤
    (J.card : ℝ)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMPhysicalDyadicShellSum_le_card_mul
      J
      i
      k
      (h3BKMPhysicalVorticityY u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityY_le hEnvelope)
      x

/-- Z-vorticity specialization of the finite shell-count estimate. -/
theorem norm_h3BKMPhysicalDyadicShellSum_vorticityZ_le_card_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (J : Finset ℕ)
    (i k : Fin 3)
    (x : Point3) :
    ‖h3BKMPhysicalDyadicShellSum
        J i k (h3BKMPhysicalVorticityZ u t) x‖
      ≤
    (J.card : ℝ)
      * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  exact
    norm_h3BKMPhysicalDyadicShellSum_le_card_mul
      J
      i
      k
      (h3BKMPhysicalVorticityZ u t)
      (g t)
      (h3BKM_vorticityEnvelope_nonneg hEnvelope)
      (norm_h3BKMPhysicalVorticityZ_le hEnvelope)
      x

/--
Middle-frequency shell sum over the consecutive dyadic indices from `lo`
through `hi`.
-/
noncomputable def h3BKMMiddleDyadicShellSum
    (lo hi : ℕ)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (x : Point3) : ℂ :=
  h3BKMPhysicalDyadicShellSum
    (Finset.Icc lo hi)
    i
    k
    f
    x

/--
The middle-frequency interval is controlled by the cardinality of its dyadic
index window.
-/
theorem norm_h3BKMMiddleDyadicShellSum_le_card_mul
    (lo hi : ℕ)
    (i k : Fin 3)
    (f : Point3 → ℂ)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ z : Point3, ‖f z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMMiddleDyadicShellSum lo hi i k f x‖
      ≤
    ((Finset.Icc lo hi).card : ℝ)
      * (M * h3BKMDyadicKernelUnitMassConstant) := by

  unfold h3BKMMiddleDyadicShellSum

  exact
    norm_h3BKMPhysicalDyadicShellSum_le_card_mul
      (Finset.Icc lo hi)
      i
      k
      f
      M
      hM
      hf
      x

end

end Euclidean
end Bridge
end PrimeTensor
