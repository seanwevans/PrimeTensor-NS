import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Uniform.Radial.L2.Generic
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Forcing.Continuity

/-!
# Quotient-safe radial Fourier L² states for selected forcing

The previous checkpoint proves uniform weighted `L²` estimates for the selected
unheated nonlinear forcing at every finite radial order.  This file turns
those estimates into an actual `H3FourierComplexL2`-valued path on the positive
terminal slab `[q/2,q]`.

For every natural `m ≥ 1` and coordinate `i` we package

    ξ ↦ |ξ|^m N_i(W(s),W(s))(ξ)

with `MemLp.toLp`.

The package comes with:

* an exact a.e. representative theorem;
* the exact `L²` norm-square integral identity;
* one source-time-uniform norm-square bound on the whole terminal slab.

This is the quotient-safe interface needed for the next interpolation
continuity step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingRadialL2State
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Order-`m` radially weighted selected nonlinear forcing, packaged as a genuine
Fourier `L²` state at one source time in the positive terminal slab.
-/
noncomputable def h3SelectedRestartForcingRadialFourierL2OnSlab
    {ν A q : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    H3FourierComplexL2 := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hsPos : 0 < (s : ℝ) := by
    have hHalf : 0 < q / 2 := by
      positivity
    exact lt_of_lt_of_le hHalf s.property.1

  have hsR :
      (s : ℝ) ≤ h3FinHeatLerayRestartRadius ν A :=
    s.property.2.trans hqR

  exact
    (h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
      m hν U₀ hA hU₀ hsPos hsR i).toLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            (W (s : ℝ)) (W (s : ℝ)) i ξ)

/--
The packaged weighted forcing state has exactly the expected raw Fourier
representative almost everywhere.
-/
theorem h3SelectedRestartForcingRadialFourierL2OnSlab_ae
    {ν A q : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    ((h3SelectedRestartForcingRadialFourierL2OnSlab
        m hν U₀ hA hU₀ hq hqR i s :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          i ξ) := by

  unfold h3SelectedRestartForcingRadialFourierL2OnSlab

  exact
    MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
        m hν U₀ hA hU₀
        (by
          have hHalf : 0 < q / 2 := by
            positivity
          exact lt_of_lt_of_le hHalf s.property.1)
        (s.property.2.trans hqR)
        i)

/--
Exact norm-square formula for the quotient-safe weighted forcing state.
-/
theorem norm_sq_h3SelectedRestartForcingRadialFourierL2OnSlab
    {ν A q : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    ‖h3SelectedRestartForcingRadialFourierL2OnSlab
        m hν U₀ hA hU₀ hq hqR i s‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (s : ℝ))
          i ξ‖ ^ 2 := by

  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  apply integral_congr_ae

  filter_upwards [
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      m hν U₀ hA hU₀ hq hqR i s
  ] with ξ hξ

  rw [hξ]

/--
The order-`m` weighted forcing path has one finite norm-square ceiling on the
entire terminal slab.
-/
theorem exists_norm_sq_bound_h3SelectedRestartForcingRadialFourierL2OnSlab
    {ν A q : ℝ}
    (m : ℕ)
    (hm : 1 ≤ m)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ Bm : ℝ,
      0 ≤ Bm ∧
      ∀ i : Fin 3,
        ∀ s : Set.Icc (q / 2) q,
          ‖h3SelectedRestartForcingRadialFourierL2OnSlab
              m hν U₀ hA hU₀ hq hqR i s‖ ^ 2
            ≤
          Bm := by

  obtain ⟨Bm, hBm0, hBm⟩ :=
    exists_selectedRestart_forcing_radialL2_uniform_nat
      m hm hν U₀ hA hU₀ hq hqR

  refine ⟨Bm, hBm0, ?_⟩

  intro i s

  have hRaw :=
    hBm (s : ℝ) s.property i

  dsimp only at hRaw
  rcases hRaw with ⟨_hMem, hIntegral⟩

  rw [
    norm_sq_h3SelectedRestartForcingRadialFourierL2OnSlab
      m hν U₀ hA hU₀ hq hqR i s
  ]

  exact hIntegral

/-- Fourth-order specialization. -/
theorem exists_norm_sq_bound_h3SelectedRestartForcingFourthRadialFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ B4 : ℝ,
      0 ≤ B4 ∧
      ∀ i : Fin 3,
        ∀ s : Set.Icc (q / 2) q,
          ‖h3SelectedRestartForcingRadialFourierL2OnSlab
              4 hν U₀ hA hU₀ hq hqR i s‖ ^ 2
            ≤
          B4 :=
  exists_norm_sq_bound_h3SelectedRestartForcingRadialFourierL2OnSlab
    4 (by norm_num) hν U₀ hA hU₀ hq hqR

/-- Fifth-order specialization. -/
theorem exists_norm_sq_bound_h3SelectedRestartForcingFifthRadialFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ B5 : ℝ,
      0 ≤ B5 ∧
      ∀ i : Fin 3,
        ∀ s : Set.Icc (q / 2) q,
          ‖h3SelectedRestartForcingRadialFourierL2OnSlab
              5 hν U₀ hA hU₀ hq hqR i s‖ ^ 2
            ≤
          B5 :=
  exists_norm_sq_bound_h3SelectedRestartForcingRadialFourierL2OnSlab
    5 (by norm_num) hν U₀ hA hU₀ hq hqR

/-- Sixth-order specialization, reserved as the high-frequency envelope for
fifth-order continuity. -/
theorem exists_norm_sq_bound_h3SelectedRestartForcingSixthRadialFourierL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ B6 : ℝ,
      0 ≤ B6 ∧
      ∀ i : Fin 3,
        ∀ s : Set.Icc (q / 2) q,
          ‖h3SelectedRestartForcingRadialFourierL2OnSlab
              6 hν U₀ hA hU₀ hq hqR i s‖ ^ 2
            ≤
          B6 :=
  exists_norm_sq_bound_h3SelectedRestartForcingRadialFourierL2OnSlab
    6 (by norm_num) hν U₀ hA hU₀ hq hqR

end

end Euclidean
end Bridge
end PrimeTensor
