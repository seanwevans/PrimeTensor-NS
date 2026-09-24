import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Increment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Selected.RHS.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHSPhysicalWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Restart.Bound

/-!
# Uniform physical Hilbert bound for the selected--old RHS difference

The weak energy closure now has the exact two-time scalar evolution identity and
density of compact smooth divergence-free tests in the Leray-fixed physical
Hilbert subspace.

To pass a weak-test approximation to the actual state `D(a)` under the time
integral, we also need a test-independent integrable majorant for the RHS
pairing.  This file packages that majorant.

The old endpoint-independent branch already proves the coordinatewise physical
`L²` estimate

    ‖R_old,i(r)‖₂ ≤ C(E),

where `C(E) = h3UnitViscosityZeroRHSBound E`.

The selected restart obeys the same estimate: its weighted spectral state stays
in the `2E` ball, and the same Laplacian and Leray-forcing estimates therefore
give

    ‖R_sel,i(r)‖₂ ≤ C(E).

A small finite-`PiLp 2` lemma turns three coordinate bounds into the coarse but
convenient Hilbert estimate

    ‖R_branch(r)‖ ≤ 3 C(E).

Hence on the physical elapsed interval

    ‖RDelta(r)‖ ≤ 6 C(E),

and Cauchy--Schwarz gives the corresponding uniform pairing bound.

No temporal derivative or endpoint continuity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyRHSBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A coarse finite-dimensional estimate: if every one of three `PiLp 2`
coordinates has norm at most `C`, then the full Hilbert norm is at most
`3 * C`. -/
theorem norm_h3PhysicalRealFinVectorL2Hilbert_le_three_mul_of_coordinate_norm_le
    (V : H3PhysicalRealFinVectorL2Hilbert)
    {C : ℝ}
    (hC : 0 ≤ C)
    (hCoord : ∀ i : Fin 3, ‖V i‖ ≤ C) :
    ‖V‖ ≤ 3 * C := by
  have hSq :
      ‖V‖ ^ 2
        =
      ∑ i : Fin 3, ‖V i‖ ^ 2 := by
    exact
      PiLp.norm_sq_eq_of_L2
        (fun _ : Fin 3 => H3ScalarL2)
        V

  have hCoordSq :
      ∀ i : Fin 3, ‖V i‖ ^ 2 ≤ C ^ 2 := by
    intro i
    have hNorm0 : 0 ≤ ‖V i‖ := norm_nonneg _
    nlinarith [hCoord i]

  have hSum :
      (∑ i : Fin 3, ‖V i‖ ^ 2)
        ≤
      ∑ _i : Fin 3, C ^ 2 := by
    exact
      Finset.sum_le_sum
        (fun i hi => hCoordSq i)

  have hNormSq :
      ‖V‖ ^ 2 ≤ (3 * C) ^ 2 := by
    calc
      ‖V‖ ^ 2
          =
        ∑ i : Fin 3, ‖V i‖ ^ 2 := hSq
      _ ≤
        ∑ _i : Fin 3, C ^ 2 := hSum
      _ = 3 * C ^ 2 := by
        simp
      _ ≤ (3 * C) ^ 2 := by
        nlinarith [sq_nonneg C]

  have hNorm0 : 0 ≤ ‖V‖ := norm_nonneg _
  have hThreeC0 : 0 ≤ 3 * C := by positivity

  nlinarith

/-- The selected unit-viscosity projected RHS has the same coordinatewise
physical `L²` ceiling as the endpoint-independent old projected RHS. -/
theorem norm_h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : Fin 3) :
    ‖h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius
        hNS ht hE hTail q i‖
      ≤
    h3UnitViscosityZeroRHSBound E := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht hE hTail q

  have hU :
      ‖U‖ ≤ 2 * E := by
    dsimp only [U, h3PreterminalSelectedUnitSpectralStateOnRadius]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht hE hTail)
        (q : ℝ)

  have hTwoE : 0 ≤ 2 * E := by
    linarith

  have hLapFourier :
      ‖h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
          hNS ht hE hTail q i‖
        ≤
      2 * E := by
    change
      ‖h3SpectralScalarLaplacianRawFourierL2 (U i)‖
        ≤
      2 * E

    exact
      (norm_h3SpectralScalarLaplacianRawFourierL2_le
        (U i)).trans
        ((h3SpectralFinVector_coordinate_norm_le U i).trans hU)

  have hLap :
      ‖h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
          hNS ht hE hTail q i‖
        ≤
      2 * E := by
    calc
      ‖h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
          hNS ht hE hTail q i‖
          =
        ‖h3ScalarFourierL2
          (h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
            hNS ht hE hTail q i)‖ := by
              symm
              exact
                norm_h3ScalarFourierL2
                  (h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
                    hNS ht hE hTail q i)
      _ =
        ‖h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
          hNS ht hE hTail q i‖ := by
              rw [
                h3ScalarFourierL2_h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
              ]
      _ ≤ 2 * E := hLapFourier

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

  have hForceFourier :
      ‖h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
          hNS ht hE hTail q i‖
        ≤
      2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2 := by
    change
      ‖h3RawFinLerayOuterProductDivergenceFourierL2
          U U i‖
        ≤
      2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2

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

  have hForce :
      ‖h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
          hNS ht hE hTail q i‖
        ≤
      2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2 := by
    calc
      ‖h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
          hNS ht hE hTail q i‖
          =
        ‖h3ScalarFourierL2
          (h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
            hNS ht hE hTail q i)‖ := by
              symm
              exact
                norm_h3ScalarFourierL2
                  (h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
                    hNS ht hE hTail q i)
      _ =
        ‖h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
          hNS ht hE hTail q i‖ := by
              rw [
                h3ScalarFourierL2_h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
              ]
      _ ≤
        2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2 :=
        hForceFourier

  unfold h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius
  unfold h3UnitViscosityZeroRHSBound

  exact
    (norm_sub_le
      (h3PreterminalSelectedUnitLaplacianPhysicalL2OnRadius
        hNS ht hE hTail q i)
      (h3PreterminalSelectedUnitLerayForcingPhysicalL2OnRadius
        hNS ht hE hTail q i)).trans
      (add_le_add hLap hForce)

/-- Coarse native-Hilbert bound for the selected projected RHS. -/
theorem norm_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_le_three_mul
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    ‖h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail q‖
      ≤
    3 * h3UnitViscosityZeroRHSBound E := by
  apply
    norm_h3PhysicalRealFinVectorL2Hilbert_le_three_mul_of_coordinate_norm_le
      (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
        hNS ht hE hTail q)
      (h3UnitViscosityZeroRHSBound_nonneg hE)

  intro i

  change
    ‖h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius
        hNS ht hE hTail q i‖
      ≤
    h3UnitViscosityZeroRHSBound E

  exact
    norm_h3PreterminalSelectedUnitProjectedRHSPhysicalL2OnRadius_le
      hNS ht hE hTail q i

/-- Coarse native-Hilbert bound for the old endpoint-independent projected
RHS. -/
theorem norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_le_three_mul
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q‖
      ≤
    3 * h3UnitViscosityZeroRHSBound E := by
  apply
    norm_h3PhysicalRealFinVectorL2Hilbert_le_three_mul_of_coordinate_norm_le
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      (h3UnitViscosityZeroRHSBound_nonneg hE)

  intro i

  rw [
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_apply
  ]

  exact
    norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_le
      hNS ht hEnd hE hTail q i

/-- Uniform Hilbert bound for the selected-minus-old projected RHS on the
physical elapsed interval. -/
theorem norm_h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_le_six_mul
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed
        hNS ht hEnd hE hTail htauR q‖
      ≤
    6 * h3UnitViscosityZeroRHSBound E := by
  unfold h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed

  have hSelected :=
    norm_h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius_le_three_mul
      hNS ht hE hTail
      (h3PreterminalElapsedToSelectedUnitRadius htauR q)

  have hOld :=
    norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_le_three_mul
      hNS ht hEnd hE hTail q

  calc
    ‖h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)
        -
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q‖
        ≤
      ‖h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertOnRadius
          hNS ht hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius htauR q)‖
        +
      ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q‖ :=
      norm_sub_le _ _
    _ ≤
      (3 * h3UnitViscosityZeroRHSBound E)
        +
      (3 * h3UnitViscosityZeroRHSBound E) :=
      add_le_add hSelected hOld
    _ =
      6 * h3UnitViscosityZeroRHSBound E := by
      ring

/-- Ambient-real form of the uniform RHS-difference bound at physical elapsed
times. -/
theorem norm_h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed_le_six_mul_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
        hNS ht hEnd hE hTail htauR r‖
      ≤
    6 * h3UnitViscosityZeroRHSBound E := by
  rw [
    h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed_apply_of_mem
      hNS ht hEnd hE hTail htauR hr
  ]

  exact
    norm_h3PreterminalSelectedOldUnitProjectedRHSDifferenceOnElapsed_le_six_mul
      hNS ht hEnd hE hTail htauR ⟨r, hr⟩

/-- Uniform Cauchy--Schwarz majorant for pairing any physical Hilbert vector
with the selected-minus-old projected RHS at a physical elapsed time. -/
theorem abs_inner_selectedOldProjectedRHSDifferenceRealOnElapsed_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hr : r ∈ Set.Icc (0 : ℝ) tau)
    (V : H3PhysicalRealFinVectorL2Hilbert) :
    |inner ℝ
        V
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r)|
      ≤
    ‖V‖ * (6 * h3UnitViscosityZeroRHSBound E) := by
  calc
    |inner ℝ
        V
        (h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r)|
        ≤
      ‖V‖ *
        ‖h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed
          hNS ht hEnd hE hTail htauR r‖ :=
      abs_real_inner_le_norm _ _
    _ ≤
      ‖V‖ * (6 * h3UnitViscosityZeroRHSBound E) := by
      exact
        mul_le_mul_of_nonneg_left
          (norm_h3PreterminalSelectedOldUnitProjectedRHSDifferenceRealOnElapsed_le_six_mul_of_mem
            hNS ht hEnd hE hTail htauR hr)
          (norm_nonneg V)

end

end Euclidean
end Bridge
end PrimeTensor
