import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Lipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Forcing.Continuity

/-!
# Zeroth-order endpoint continuity: uniform Fourier L² RHS bound

`Zero.Lipschitz` reduced the zeroth-order continuity problem to a quantitative
physical `L²` Lipschitz estimate.  The PDE mechanism behind that estimate is

    u(q₂) - u(q₁) = ∫_{q₁}^{q₂} (Δu - P div (u ⊗ u)) ds.

Before proving this increment identity without assuming endpoint continuity, we
isolate the needed uniform `L²` bound for its right-hand side.

This file is deliberately endpoint-continuity free.  At each old-tail elapsed
time it uses the canonical weighted H³ spectral state directly.  The retained
tail energy ceiling gives a coarse `‖U(q)‖ ≤ 2E` bound.  The already-proved
bounded Fourier operators then give:

* the deweighted Laplacian is contractive;
* one deweighted derivative costs at most `2π`;
* the weighted H³ product costs
  `16 * h3SobolevDeweightingConstant`;
* the finite three-coordinate divergence costs the corresponding finite sum;
* the finite Leray multiplier costs at most `6`.

Consequently each coordinate of the exact spectral projected RHS has a uniform
Fourier `L²` bound depending only on `E`.

No time-continuity or mild-equation hypothesis is used in this estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroRHSBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The retained old-tail energy ceiling gives a coarse uniform bound on the
canonical weighted spectral state at every elapsed time. -/
theorem norm_h3PreterminalTailCanonicalSpectralStateOnElapsed_le_twoE
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q‖
      ≤
    2 * E := by
  unfold h3PreterminalTailCanonicalSpectralStateOnElapsed

  exact
    norm_velocityH3SpectralStateAt_le_energyCeiling
      (h3PreterminalTailFourierCompatibleOnElapsed
        hNS ht hEnd hTail q)
      (by linarith)
      (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
        hE hEnd hTail q)

/-- Quantitative finite-vector bound for the endpoint-independent unheated
spectral divergence package. -/
theorem norm_h3SpectralFinUnheatedDivergenceApply_le
    (U V : H3SpectralFinVectorState) :
    ‖h3SpectralFinUnheatedDivergenceApply U V‖
      ≤
    96 * Real.pi * h3SobolevDeweightingConstant *
      ‖U‖ * ‖V‖ := by
  have hRhs :
      0 ≤
        96 * Real.pi * h3SobolevDeweightingConstant *
          ‖U‖ * ‖V‖ := by
    positivity [h3SobolevDeweightingConstant_nonneg]

  apply (pi_norm_le_iff_of_nonneg hRhs).2
  intro i

  calc
    ‖h3SpectralFinUnheatedDivergenceApply U V i‖
        ≤
      ∑ j : Fin 3,
        ‖h3SpectralScalarRawDerivativeFourierL2
          j
          (h3WeightedRawProductConvolutionL2
            (U i) (V j))‖ := by
      unfold h3SpectralFinUnheatedDivergenceApply
      exact
        norm_sum_le
          Finset.univ
          (fun j : Fin 3 =>
            h3SpectralScalarRawDerivativeFourierL2
              j
              (h3WeightedRawProductConvolutionL2
                (U i) (V j)))
    _ ≤
      ∑ j : Fin 3,
        (2 * Real.pi) *
          ‖h3WeightedRawProductConvolutionL2
            (U i) (V j)‖ := by
      exact
        Finset.sum_le_sum
          (fun j _ =>
            norm_h3SpectralScalarRawDerivativeFourierL2_le
              j
              (h3WeightedRawProductConvolutionL2
                (U i) (V j)))
    _ ≤
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (16 * h3SobolevDeweightingConstant *
            ‖U‖ * ‖V‖) := by
      apply Finset.sum_le_sum
      intro j hj

      have hProduct :
          ‖h3WeightedRawProductConvolutionL2
              (U i) (V j)‖
            ≤
          16 * h3SobolevDeweightingConstant *
            ‖U‖ * ‖V‖ := by
        calc
          ‖h3WeightedRawProductConvolutionL2
              (U i) (V j)‖
              ≤
            16 * h3SobolevDeweightingConstant *
              ‖U i‖ * ‖V j‖ :=
            norm_h3WeightedRawProductConvolutionL2_le
              (U i) (V j)
          _ =
            (16 * h3SobolevDeweightingConstant) *
              (‖U i‖ * ‖V j‖) := by
            ring
          _ ≤
            (16 * h3SobolevDeweightingConstant) *
              (‖U‖ * ‖V‖) := by
            apply mul_le_mul_of_nonneg_left
            · exact
                mul_le_mul
                  (h3SpectralFinVector_coordinate_norm_le U i)
                  (h3SpectralFinVector_coordinate_norm_le V j)
                  (norm_nonneg _)
                  (norm_nonneg _)
            · exact
                mul_nonneg
                  (by norm_num)
                  h3SobolevDeweightingConstant_nonneg
          _ =
            16 * h3SobolevDeweightingConstant *
              ‖U‖ * ‖V‖ := by
            ring

      exact
        mul_le_mul_of_nonneg_left
          hProduct
          (by positivity)
    _ =
      96 * Real.pi * h3SobolevDeweightingConstant *
        ‖U‖ * ‖V‖ := by
      simp
      ring

/-- The repository's raw unheated Leray forcing therefore has a uniform
quadratic H³-to-Fourier-`L²` bound, coordinatewise. -/
theorem norm_h3RawFinLerayOuterProductDivergenceFourierL2_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    ‖h3RawFinLerayOuterProductDivergenceFourierL2 U V i‖
      ≤
    576 * Real.pi * h3SobolevDeweightingConstant *
      ‖U‖ * ‖V‖ := by
  rw [
    ← h3SpectralFinUnheatedLerayForcingApply_eq_rawFourierL2
      U V i
  ]

  unfold h3SpectralFinUnheatedLerayForcingApply

  calc
    ‖h3SpectralFinLerayApply
        (h3SpectralFinUnheatedDivergenceApply U V) i‖
        ≤
      6 * ‖h3SpectralFinUnheatedDivergenceApply U V‖ :=
      norm_h3SpectralFinLerayApply_coordinate_le
        (h3SpectralFinUnheatedDivergenceApply U V) i
    _ ≤
      6 *
        (96 * Real.pi * h3SobolevDeweightingConstant *
          ‖U‖ * ‖V‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (norm_h3SpectralFinUnheatedDivergenceApply_le U V)
          (by norm_num)
    _ =
      576 * Real.pi * h3SobolevDeweightingConstant *
        ‖U‖ * ‖V‖ := by
      ring

/-- Endpoint-independent spectral projected RHS of the old preterminal branch.

This is the exact unit-viscosity Leray form `Δu - P div (u ⊗ u)`, expressed
directly from the canonical old-tail weighted spectral state. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  let U :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q
  h3SpectralScalarLaplacianRawFourierL2 (U i)
    -
  h3RawFinLerayOuterProductDivergenceFourierL2
    U U i

/-- Uniform old-tail Fourier `L²` bound for the exact unit-viscosity projected
RHS coordinate. -/
theorem norm_h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    ‖h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
        hNS ht hEnd hTail q i‖
      ≤
    2 * E
      +
    2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2 := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  have hU :
      ‖U‖ ≤ 2 * E := by
    dsimp only [U]
    exact
      norm_h3PreterminalTailCanonicalSpectralStateOnElapsed_le_twoE
        hNS ht hEnd hE hTail q

  have hTwoE : 0 ≤ 2 * E := by
    linarith

  have hLap :
      ‖h3SpectralScalarLaplacianRawFourierL2 (U i)‖
        ≤
      2 * E := by
    exact
      (norm_h3SpectralScalarLaplacianRawFourierL2_le
        (U i)).trans
        ((h3SpectralFinVector_coordinate_norm_le U i).trans hU)

  have hForce0 :=
    norm_h3RawFinLerayOuterProductDivergenceFourierL2_le
      U U i

  have hUU :
      ‖U‖ * ‖U‖ ≤ (2 * E) * (2 * E) := by
    exact
      mul_le_mul
        hU hU
        (norm_nonneg U)
        hTwoE

  have hCoeff :
      0 ≤
        576 * Real.pi * h3SobolevDeweightingConstant := by
    positivity [h3SobolevDeweightingConstant_nonneg]

  have hForce :
      ‖h3RawFinLerayOuterProductDivergenceFourierL2
          U U i‖
        ≤
      2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2 := by
    calc
      ‖h3RawFinLerayOuterProductDivergenceFourierL2
          U U i‖
          ≤
        576 * Real.pi * h3SobolevDeweightingConstant *
          ‖U‖ * ‖U‖ :=
        hForce0
      _ =
        (576 * Real.pi * h3SobolevDeweightingConstant) *
          (‖U‖ * ‖U‖) := by
        ring
      _ ≤
        (576 * Real.pi * h3SobolevDeweightingConstant) *
          ((2 * E) * (2 * E)) := by
        exact
          mul_le_mul_of_nonneg_left
            hUU hCoeff
      _ =
        2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2 := by
        ring

  unfold h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
  dsimp only

  exact
    (norm_sub_le
      (h3SpectralScalarLaplacianRawFourierL2 (U i))
      (h3RawFinLerayOuterProductDivergenceFourierL2
        U U i)).trans
      (add_le_add hLap hForce)

end

end Euclidean
end Bridge
end PrimeTensor
