import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2.Continuity

/-!
# Selected forcing radial Fourier L² continuity on the open restart interval

The generic selected forcing radial state is already strongly continuous on
every positive terminal slab `[Q/2,Q]` at every finite radial order.  This file
removes the auxiliary slab parameter.

For `q ∈ (0,R)` we package directly

    ξ ↦ |ξ|^m N_i(W(q),W(q))(ξ)

as a quotient-safe Fourier `L²` state.  Around an arbitrary interior time
`q₀`, choose a terminal slab `[Q/2,Q]` with

    Q / 2 < q₀ < Q < R.

The direct open state agrees exactly with the existing slab package wherever
the two domains overlap.  Extending the continuous slab path by `Set.IccExtend`
therefore supplies a continuous local model around `q₀`.

This closes open-restart continuity simultaneously for every natural radial
order, in particular orders five and six needed by the remaining order-two
velocity argument and the later order-three closure.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingRadialOpenL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Order-`m` radially weighted selected nonlinear forcing, packaged directly
on the whole strict restart interval. -/
noncomputable def h3SelectedRestartForcingRadialFourierL2OnRestartRadius
    {ν A : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (i : Fin 3) :
    H3FourierComplexL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
      m hν U₀ hA hU₀ q.property.1 q.property.2.le i).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          (W (q : ℝ)) (W (q : ℝ)) i ξ)

/-- The direct open package has the expected weighted forcing representative
almost everywhere. -/
theorem h3SelectedRestartForcingRadialFourierL2OnRestartRadius_ae
    {ν A : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (i : Fin 3) :
    ((h3SelectedRestartForcingRadialFourierL2OnRestartRadius
        m hν U₀ hA hU₀ q i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (q : ℝ))
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ (q : ℝ))
          i ξ) := by
  unfold h3SelectedRestartForcingRadialFourierL2OnRestartRadius
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
        m hν U₀ hA hU₀ q.property.1 q.property.2.le i)

/-- Whenever an open restart time lies in a positive terminal slab, the direct
open package equals the existing slab package. -/
theorem h3SelectedRestartForcingRadialFourierL2OnRestartRadius_eq_onSlab
    {ν A Q : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hQ : 0 < Q)
    (hQR : Q ≤ h3FinHeatLerayRestartRadius ν A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (hqQ : (q : ℝ) ∈ Set.Icc (Q / 2) Q)
    (i : Fin 3) :
    h3SelectedRestartForcingRadialFourierL2OnRestartRadius
        m hν U₀ hA hU₀ q i
      =
    h3SelectedRestartForcingRadialFourierL2OnSlab
      m hν U₀ hA hU₀ hQ hQR i
      ⟨(q : ℝ), hqQ⟩ := by
  apply MeasureTheory.Lp.ext

  have hOpen :=
    h3SelectedRestartForcingRadialFourierL2OnRestartRadius_ae
      m hν U₀ hA hU₀ q i

  have hSlab :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      m hν U₀ hA hU₀ hQ hQR i
      ⟨(q : ℝ), hqQ⟩

  filter_upwards [hOpen, hSlab] with ξ hxOpen hxSlab
  exact hxOpen.trans hxSlab.symm

/-- Elementary local-slab geometry for an arbitrary interior restart time. -/
private theorem exists_h3SelectedRestartForcingRadialLocalSlab
    {R q : ℝ}
    (hq0 : 0 < q)
    (hqR : q < R) :
    ∃ Q : ℝ,
      0 < Q ∧
      Q < R ∧
      Q / 2 < q ∧
      q < Q := by
  let Q : ℝ :=
    min
      (3 * q / 2)
      ((q + R) / 2)

  have hqQ : q < Q := by
    dsimp only [Q]
    apply lt_min
    · linarith
    · linarith

  have hQR : Q < R := by
    dsimp only [Q]
    exact
      lt_of_le_of_lt
        (min_le_right
          (3 * q / 2)
          ((q + R) / 2))
        (by linarith)

  have hQ0 : 0 < Q :=
    lt_trans hq0 hqQ

  have hQltTwoQ : Q < 2 * q := by
    calc
      Q ≤ 3 * q / 2 := by
        dsimp only [Q]
        exact min_le_left _ _
      _ < 2 * q := by
        linarith

  have hHalfQq : Q / 2 < q := by
    linarith

  exact ⟨Q, hQ0, hQR, hHalfQq, hqQ⟩

set_option maxHeartbeats 2000000

/-- Local open-interval continuity of the generic selected radial forcing
package. -/
private theorem continuousAt_h3SelectedRestartForcingRadialFourierL2OnRestartRadius
    {ν A : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (q₀ : Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius ν A)) :
    ContinuousAt
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartForcingRadialFourierL2OnRestartRadius
          m hν U₀ hA hU₀ q i)
      q₀ := by
  obtain ⟨Q, hQ0, hQR, hHalfQq₀, hq₀Q⟩ :=
    exists_h3SelectedRestartForcingRadialLocalSlab
      q₀.property.1 q₀.property.2

  have hHalfLe : Q / 2 ≤ Q := by
    linarith

  let Fslab : Set.Icc (Q / 2) Q → H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      m hν U₀ hA hU₀ hQ0 hQR.le i

  have hFslab : Continuous Fslab := by
    dsimp only [Fslab]
    exact
      continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
        m hν U₀ hA hU₀ hQ0 hQR.le i

  let Y : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Fslab

  have hY : Continuous Y := by
    dsimp only [Y]
    exact hFslab.Icc_extend'

  let G :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν A) →
        H3FourierComplexL2 :=
    fun q => Y (q : ℝ)

  have hG : Continuous G := by
    dsimp only [G]
    exact hY.comp continuous_subtype_val

  have hNearReal :
      Set.Ioo (Q / 2) Q ∈ 𝓝 (q₀ : ℝ) :=
    Ioo_mem_nhds hHalfQq₀ hq₀Q

  have hNear :
      ∀ᶠ q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) in 𝓝 q₀,
        (q : ℝ) ∈ Set.Ioo (Q / 2) Q :=
    continuous_subtype_val.continuousAt hNearReal

  have hEq :
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartForcingRadialFourierL2OnRestartRadius
          m hν U₀ hA hU₀ q i)
        =ᶠ[𝓝 q₀]
      G := by
    filter_upwards [hNear] with q hq

    have hqClosed :
        (q : ℝ) ∈ Set.Icc (Q / 2) Q :=
      ⟨hq.1.le, hq.2.le⟩

    have hDirect :=
      h3SelectedRestartForcingRadialFourierL2OnRestartRadius_eq_onSlab
        m hν U₀ hA hU₀ hQ0 hQR.le q hqClosed i

    dsimp only [G, Y]
    rw [Set.IccExtend_of_mem hHalfLe Fslab hqClosed]
    simpa only [Fslab] using hDirect

  exact
    hG.continuousAt.congr_of_eventuallyEq hEq

/-- At every finite radial order, the selected forcing is strongly continuous
in Fourier `L²` on the whole strict restart interval. -/
theorem continuous_h3SelectedRestartForcingRadialFourierL2OnRestartRadius
    {ν A : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    Continuous
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartForcingRadialFourierL2OnRestartRadius
          m hν U₀ hA hU₀ q i) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  exact
    continuousAt_h3SelectedRestartForcingRadialFourierL2OnRestartRadius
      m hν U₀ hA hU₀ i q₀

/-- Fifth-order specialization used by the remaining order-two velocity
argument. -/
theorem continuous_h3SelectedRestartForcingFifthRadialFourierL2OnRestartRadius
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    Continuous
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartForcingRadialFourierL2OnRestartRadius
          5 hν U₀ hA hU₀ q i) :=
  continuous_h3SelectedRestartForcingRadialFourierL2OnRestartRadius
    5 hν U₀ hA hU₀ i

/-- Sixth-order specialization reserved for the order-three continuation of
the same argument. -/
theorem continuous_h3SelectedRestartForcingSixthRadialFourierL2OnRestartRadius
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    Continuous
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartForcingRadialFourierL2OnRestartRadius
          6 hν U₀ hA hU₀ q i) :=
  continuous_h3SelectedRestartForcingRadialFourierL2OnRestartRadius
    6 hν U₀ hA hU₀ i

end

end Euclidean
end Bridge
end PrimeTensor
