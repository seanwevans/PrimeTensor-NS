import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Duhamel.Tail.Weighted.Kernel.L2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.CLM

/-!
# Closure of the selected fourth/fifth weighted terminal-tail kernel frontier

The remaining terminal-tail obstruction is temporal, not spatial.

The selected nonlinear forcing is now strongly continuous on the terminal half
in every finite radial Fourier `L²` weight.  Acting on a moving `L²` state with
a moving nonnegative heat time preserves strong continuity by the usual
contraction-plus-fixed-state argument.

For each radial order `n`, define the natural closed-slab source path

    s ↦ exp (ν (q-s) Δ) (|ξ|^n N_s)

on `[q/2,q]`.  This path is continuous all the way through `s=q`.

The repository's endpoint-safe Duhamel source convention instead sets the
source state to zero exactly at `s=q`.  That single endpoint has zero measure.
We therefore:

* prove the natural closed-slab source path continuous;
* zero-extend it to ambient real time and obtain `ContinuousOn`;
* obtain Bochner interval integrability;
* identify it with the endpoint-safe weighted Duhamel source on
  `Ioo (q/2,q)`;
* transfer integrability across that a.e. equality.

Orders four and five follow immediately, closing
`H3CanonicalSelectedDuhamelTailFourthFifthWeightedKernelIntervalIntegrableOnRestartRadius`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedDuhamelTailWeightedKernelL2Closure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/-! ## Moving scalar heat time and moving Fourier L² state -/

/-- Joint strong continuity of scalar Fourier heat evolution in both
nonnegative heat time and the moving `L²` state. -/
theorem tendsto_h3SpectralScalarHeatApplyNN_moving
    {ι : Type*}
    {l : Filter ι}
    (ν : ℝ)
    (hν : 0 ≤ ν)
    {τ : ι → ℝ≥0}
    {τ₀ : ℝ≥0}
    {V : ι → H3SpectralScalarState}
    {V₀ : H3SpectralScalarState}
    (hτ :
      Tendsto
        τ
        l
        (𝓝 τ₀))
    (hV :
      Tendsto
        V
        l
        (𝓝 V₀)) :
    Tendsto
      (fun n : ι =>
        h3SpectralScalarHeatApplyNN
          ν hν (τ n) (V n))
      l
      (𝓝
        (h3SpectralScalarHeatApplyNN
          ν hν τ₀ V₀)) := by

  let E : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN
      ν hν τ₀ V₀

  let g : ι → ℝ :=
    fun n =>
      ‖V n - V₀‖ +
        ‖h3SpectralScalarHeatApplyNN
              ν hν (τ n) V₀
            - E‖

  have hVConst :
      Tendsto
        (fun _n : ι => V₀)
        l
        (𝓝 V₀) :=
    tendsto_const_nhds

  have hEConst :
      Tendsto
        (fun _n : ι => E)
        l
        (𝓝 E) :=
    tendsto_const_nhds

  have hVdiff :
      Tendsto
        (fun n : ι => ‖V n - V₀‖)
        l
        (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hV.sub hVConst).norm

  have hHeatAt :
      Tendsto
        (fun r : ℝ≥0 =>
          h3SpectralScalarHeatApplyNN
            ν hν r V₀)
        (𝓝 τ₀)
        (𝓝 E) := by
    dsimp only [E]
    exact
      (continuous_h3SpectralScalarHeatApplyNN
        ν hν V₀).continuousAt

  have hHeatFixed :
      Tendsto
        (fun n : ι =>
          h3SpectralScalarHeatApplyNN
            ν hν (τ n) V₀)
        l
        (𝓝 E) :=
    hHeatAt.comp hτ

  have hHeatDiff :
      Tendsto
        (fun n : ι =>
          ‖h3SpectralScalarHeatApplyNN
                ν hν (τ n) V₀
              - E‖)
        l
        (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hHeatFixed.sub hEConst).norm

  have hgZero :
      Tendsto
        g
        l
        (𝓝 0) := by
    dsimp only [g]
    simpa using
      hVdiff.add hHeatDiff

  have hUpper :
      ∀ᶠ n : ι in l,
        ‖h3SpectralScalarHeatApplyNN
              ν hν (τ n) (V n)
            - E‖
          ≤
        g n := by
    refine Eventually.of_forall ?_
    intro n

    have hDiff :
        h3SpectralScalarHeatApplyNN
              ν hν (τ n) (V n)
            - E
          =
        h3SpectralScalarHeatApplyNN
              ν hν (τ n) (V n - V₀)
          +
        (h3SpectralScalarHeatApplyNN
              ν hν (τ n) V₀
            - E) := by
      change
        h3SpectralScalarHeatCLM
              ν hν (τ n) (V n)
            - E
          =
        h3SpectralScalarHeatCLM
              ν hν (τ n) (V n - V₀)
          +
        (h3SpectralScalarHeatCLM
              ν hν (τ n) V₀
            - E)
      rw [map_sub]
      abel

    rw [hDiff]

    calc
      ‖h3SpectralScalarHeatApplyNN
              ν hν (τ n) (V n - V₀)
          +
        (h3SpectralScalarHeatApplyNN
              ν hν (τ n) V₀
            - E)‖
          ≤
        ‖h3SpectralScalarHeatApplyNN
            ν hν (τ n) (V n - V₀)‖
          +
        ‖h3SpectralScalarHeatApplyNN
              ν hν (τ n) V₀
            - E‖ :=
        norm_add_le _ _
      _ ≤
        ‖V n - V₀‖
          +
        ‖h3SpectralScalarHeatApplyNN
              ν hν (τ n) V₀
            - E‖ := by
        exact
          add_le_add
            (norm_h3SpectralScalarHeatApplyNN_le
              ν hν (τ n) (V n - V₀))
            (le_refl _)
      _ = g n := by
        rfl

  have hNonneg :
      ∀ᶠ n : ι in l,
        0 ≤
          ‖h3SpectralScalarHeatApplyNN
                ν hν (τ n) (V n)
              - E‖ :=
    Eventually.of_forall fun n =>
      norm_nonneg _

  have hResult :
      Tendsto
        (fun n : ι =>
          h3SpectralScalarHeatApplyNN
            ν hν (τ n) (V n))
        l
        (𝓝 E) := by
    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (squeeze_zero'
          hNonneg
          hUpper
          hgZero)

  simpa only [E] using hResult

/-! ## Natural continuous closed-slab weighted tail source -/

/-- Natural order-`n` weighted terminal-tail source state on the closed source
slab.  Unlike the endpoint-safe Duhamel convention, this keeps its genuine
zero-lag value at `s=q`. -/
noncomputable def h3SelectedDuhamelTailRadialClosedFourierL2IntegrandOnSlab
    {ν A q : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (s : Set.Icc (q / 2) q) :
    H3FourierComplexL2 :=
  h3SpectralScalarHeatApplyNN
    ν hν.le
    (Real.toNNReal (q - (s : ℝ)))
    (h3SelectedRestartForcingRadialFourierL2OnSlab
      n hν U₀ hA hU₀ hq hqR i s)

/-- The natural weighted terminal-tail source state is strongly continuous on
the complete closed terminal half, including zero heat lag at the right
endpoint. -/
theorem continuous_h3SelectedDuhamelTailRadialClosedFourierL2IntegrandOnSlab
    {ν A q : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Continuous
      (h3SelectedDuhamelTailRadialClosedFourierL2IntegrandOnSlab
        n hν U₀ hA hU₀ hq hqR i) := by

  let Tm : Set.Icc (q / 2) q → ℝ≥0 :=
    fun s => Real.toNNReal (q - (s : ℝ))

  let F : Set.Icc (q / 2) q → H3SpectralScalarState :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      n hν U₀ hA hU₀ hq hqR i

  have hSub :
      Continuous
        (fun s : Set.Icc (q / 2) q =>
          q - (s : ℝ)) :=
    continuous_const.sub continuous_subtype_val

  have hTm :
      Continuous Tm := by
    dsimp only [Tm]
    exact continuous_real_toNNReal.comp hSub

  have hF :
      Continuous F := by
    dsimp only [F]
    exact
      continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
        n hν U₀ hA hU₀ hq hqR i

  rw [continuous_iff_continuousAt]
  intro s

  change
    Tendsto
      (fun y : Set.Icc (q / 2) q =>
        h3SpectralScalarHeatApplyNN
          ν hν.le
          (Tm y) (F y))
      (𝓝 s)
      (𝓝
        (h3SpectralScalarHeatApplyNN
          ν hν.le
          (Tm s) (F s)))

  exact
    tendsto_h3SpectralScalarHeatApplyNN_moving
      ν hν.le
      hTm.continuousAt
      hF.continuousAt

/-! ## Ambient real-time zero extension -/

/-- Zero extension of the natural closed-slab weighted source state to ambient
real source time.  Only its restriction to `[q/2,q]` is used. -/
noncomputable def h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
    {ν A q : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (s : ℝ) :
    H3FourierComplexL2 :=
  if hs : s ∈ Set.Icc (q / 2) q then
    h3SelectedDuhamelTailRadialClosedFourierL2IntegrandOnSlab
      n hν U₀ hA hU₀ hq hqR i ⟨s, hs⟩
  else
    0

/-- On the terminal half, the ambient extension is exactly the natural
closed-slab source state. -/
theorem h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal_apply_of_mem
    {ν A q s : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (hs : s ∈ Set.Icc (q / 2) q) :
    h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
        n hν U₀ hA hU₀ hq hqR i s
      =
    h3SelectedDuhamelTailRadialClosedFourierL2IntegrandOnSlab
      n hν U₀ hA hU₀ hq hqR i ⟨s, hs⟩ := by
  simp only [
    h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal,
    dif_pos hs
  ]

/-- The ambient zero extension is continuous on the only interval relevant to
the terminal-tail Bochner integral. -/
theorem continuousOn_h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
    {ν A q : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ContinuousOn
      (h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
        n hν U₀ hA hU₀ hq hqR i)
      (Set.Icc (q / 2) q) := by

  rw [continuousOn_iff_continuous_domRestrict]

  have hClosed :=
    continuous_h3SelectedDuhamelTailRadialClosedFourierL2IntegrandOnSlab
      n hν U₀ hA hU₀ hq hqR i

  have hEq :
      (Set.Icc (q / 2) q).domRestrict
        (h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
          n hν U₀ hA hU₀ hq hqR i)
        =
      h3SelectedDuhamelTailRadialClosedFourierL2IntegrandOnSlab
        n hν U₀ hA hU₀ hq hqR i := by
    funext s
    exact
      h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal_apply_of_mem
        n hν U₀ hA hU₀ hq hqR i s.property

  rw [hEq]
  exact hClosed

/-- The natural closed-slab weighted source state is genuinely Bochner
interval-integrable. -/
theorem h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal_intervalIntegrable
    {ν A q : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    IntervalIntegrable
      (h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
        n hν U₀ hA hU₀ hq hqR i)
      volume
      (q / 2)
      q := by
  have hhalf : q / 2 ≤ q := by
    linarith
  exact
    (continuousOn_h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
      n hν U₀ hA hU₀ hq hqR i).intervalIntegrable_of_Icc
      hhalf

/-! ## Identification with the endpoint-safe weighted Duhamel source -/

/-- On the strict terminal half, the endpoint-safe weighted Duhamel source
state is exactly the natural closed-slab heat evolution of the weighted
unheated forcing state. -/
theorem h3SelectedDuhamelTailRadialRawFourierL2Integrand_eq_closedReal_of_mem_Ioo
    {ν A q s : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (q / 2) q) :
    h3SelectedDuhamelTailRadialRawFourierL2Integrand
        n ν A q hν U₀ hA hU₀ i s
      =
    h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
      n hν U₀ hA hU₀ hq hqR i s := by

  have hsIcc : s ∈ Set.Icc (q / 2) q :=
    ⟨hs.1.le, hs.2.le⟩

  rw [
    h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal_apply_of_mem
      n hν U₀ hA hU₀ hq hqR i hsIcc
  ]

  unfold h3SelectedDuhamelTailRadialClosedFourierL2IntegrandOnSlab
  unfold h3SpectralScalarHeatApplyNN

  apply MeasureTheory.Lp.ext

  have hTarget :=
    h3SelectedDuhamelTailRadialRawFourierL2Integrand_ae_of_mem_Ioo
      n hν U₀ hA hU₀ i hs

  have hForce :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      n hν U₀ hA hU₀ hq hqR i
      ⟨s, hsIcc⟩

  have hHeat :=
    h3HeatFrequencyApplyNN_coeFn
      ν hν.le
      (Real.toNNReal (q - s))
      (h3SelectedRestartForcingRadialFourierL2OnSlab
        n hν U₀ hA hU₀ hq hqR i ⟨s, hsIcc⟩)

  have hlag0 : 0 ≤ q - s :=
    sub_nonneg.mpr hs.2.le

  have hTime :
      (((Real.toNNReal (q - s) : ℝ≥0) : ℝ))
        =
      q - s :=
    Real.coe_toNNReal (q - s) hlag0

  filter_upwards [hTarget, hForce, hHeat] with ξ hTargetξ hForceξ hHeatξ

  rw [
    hTargetξ,
    hHeatξ,
    hForceξ,
    hTime
  ]

  unfold h3SelectedDuhamelTailComplexKernel
  dsimp only
  ring

/-- Every finite radial order of the endpoint-safe selected terminal-tail
source state is Bochner interval-integrable on the terminal half. -/
theorem h3SelectedDuhamelTailRadialRawFourierL2Integrand_intervalIntegrable
    {ν A q : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    IntervalIntegrable
      (h3SelectedDuhamelTailRadialRawFourierL2Integrand
        n ν A q hν U₀ hA hU₀ i)
      volume
      (q / 2)
      q := by

  have hhalf : q / 2 ≤ q := by
    linarith

  have hClosed :=
    h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal_intervalIntegrable
      n hν U₀ hA hU₀ hq hqR i

  rw [
    intervalIntegrable_iff_integrableOn_Ioo_of_le hhalf
  ] at hClosed ⊢

  have hEqAE :
      h3SelectedDuhamelTailRadialClosedFourierL2IntegrandReal
          n hν U₀ hA hU₀ hq hqR i
        =ᵐ[
          (volume : Measure ℝ).restrict
            (Set.Ioo (q / 2) q)
        ]
      h3SelectedDuhamelTailRadialRawFourierL2Integrand
        n ν A q hν U₀ hA hU₀ i := by
    filter_upwards [
      ae_restrict_mem measurableSet_Ioo
    ] with s hs
    exact
      (h3SelectedDuhamelTailRadialRawFourierL2Integrand_eq_closedReal_of_mem_Ioo
        n hν U₀ hA hU₀ hq hqR i hs).symm

  exact hClosed.congr_fun_ae hEqAE

/-! ## Closure of the named fourth/fifth frontier -/

/-- The fourth/fifth weighted terminal-tail source-kernel temporal frontier is
automatic from the selected forcing radial `L²` continuity proved above. -/
theorem h3CanonicalSelectedDuhamelTailFourthFifthWeightedKernelIntervalIntegrableOnRestartRadius :
    H3CanonicalSelectedDuhamelTailFourthFifthWeightedKernelIntervalIntegrableOnRestartRadius := by

  unfold
    H3CanonicalSelectedDuhamelTailFourthFifthWeightedKernelIntervalIntegrableOnRestartRadius

  intro E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only

  have hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ :
      ‖h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail‖
        ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  have hqR :
      q ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    hq.2.le

  constructor

  · intro j
    exact
      h3SelectedDuhamelTailRadialRawFourierL2Integrand_intervalIntegrable
        4
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        hA
        hU₀
        hq.1
        hqR
        j

  · intro j
    exact
      h3SelectedDuhamelTailRadialRawFourierL2Integrand_intervalIntegrable
        5
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        hA
        hU₀
        hq.1
        hqR
        j

end

end Euclidean
end Bridge
end PrimeTensor
