import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Tail.Fifth.Radial.L2.Bound

/-!
# Uniform fifth-radial Fourier L² bound for the selected velocity

The three pieces of the positive-time selected mild state are now all
quantitatively controlled on a compact slab `[a,b]`:

* the free initial heat has fifth-radial `L²` norm bounded by the fixed-lag
  heat coefficient at lag `a`;
* the midpoint Duhamel head has fifth-radial `L²` norm bounded by the fixed-lag
  coefficient at lag `a/2` times the complete Duhamel `3A` bound;
* the terminal Duhamel tail has one slab-uniform fifth-radial norm-square
  bound.

This file assembles those pieces at the quotient-safe `L²` level.  We retain
norm squares throughout, because the fourth-radial difference estimate uses
exactly

    ‖F₅(s)‖² + ‖F₅(t)‖².

The elementary Hilbert estimate

    ‖x - y - z‖² ≤ 3 * (‖x‖² + ‖y‖² + ‖z‖²)

avoids introducing square roots of the terminal-tail constant.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityFifthRadialL2CompactBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2000000

/-! ## Free heat fifth-radial package -/

/-- Fifth-radial quotient-safe free-heat coordinate, using the lower endpoint
of the compact target slab as the fixed positive heat lag. -/
noncomputable def h3SelectedInitialHeatFifthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3HeatRadialFourierL2OfLowerLag
    hν ha q.property.1 5
    (h3SpectralScalarRawFourierL2 (U₀ i))

/-- The compact-slab free-heat package is the literal fifth radial weight of
the named selected initial heat almost everywhere. -/
theorem h3SelectedInitialHeatFifthRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3SelectedInitialHeatFifthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 5 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
            hν U₀
            (lt_of_lt_of_le ha q.property.1)
            i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  have hWeighted :=
    h3HeatRadialFourierL2OfLowerLag_ae
      hν ha q.property.1 5
      (h3SpectralScalarRawFourierL2 (U₀ i))

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae
      (U₀ i)

  have hq0 :
      0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hHeat :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hq0 i

  unfold h3SelectedInitialHeatFifthRadialFourierL2OnCompact

  filter_upwards [hWeighted, hRaw, hHeat] with ξ hWeightedξ hRawξ hHeatξ

  rw [hWeightedξ, hHeatξ]
  unfold h3SpectralScalarHeatRawRepresentative
  rw [hRawξ]

/-- Fixed-lag fifth-radial free heat is bounded uniformly over the compact
target slab. -/
theorem norm_h3SelectedInitialHeatFifthRadialFourierL2OnCompact_le
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ‖h3SelectedInitialHeatFifthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i‖
      ≤
    h3HeatNatMomentCoefficient 5 ν a * A := by

  have hHeat :=
    norm_h3HeatRadialFourierL2OfLowerLag_le
      hν ha q.property.1 5
      (h3SpectralScalarRawFourierL2 (U₀ i))

  have hRaw :
      ‖h3SpectralScalarRawFourierL2 (U₀ i)‖
        ≤
      A := by
    calc
      ‖h3SpectralScalarRawFourierL2 (U₀ i)‖
          ≤ ‖U₀ i‖ :=
        norm_h3SpectralScalarRawFourierL2_le
          (U₀ i)
      _ ≤ ‖U₀‖ :=
        h3SpectralVelocity_coordinate_norm_le U₀ i
      _ ≤ A :=
        hU₀

  have hCoeff0 :
      0 ≤ h3HeatNatMomentCoefficient 5 ν a :=
    h3HeatNatMomentCoefficient_nonneg 5 ν a

  unfold h3SelectedInitialHeatFifthRadialFourierL2OnCompact

  exact
    hHeat.trans
      (mul_le_mul_of_nonneg_left hRaw hCoeff0)

/-! ## Exact fifth-radial mild assembly -/

/-- On a positive compact target slab, the canonical selected fifth-radial
velocity package is exactly free heat minus midpoint head minus terminal tail
in Fourier `L²`. -/
theorem h3PreterminalSelectedVelocityFifthRadialFourierL2_eq_partsOnCompact
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc a b)
    (j : Fin 3) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail
    let qOpen :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨(q : ℝ),
        lt_of_lt_of_le ha q.property.1,
        lt_of_le_of_lt q.property.2 hbR⟩
    h3PreterminalSelectedVelocityFifthRadialFourierL2
        hNS ht₀ hE hTail qOpen j
      =
    h3SelectedInitialHeatFifthRadialFourierL2OnCompact
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ ha q j
      -
    h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ ha q j
      -
    h3SelectedDuhamelTailFifthRadialFourierL2
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        (lt_of_lt_of_le ha q.property.1)
        (le_trans q.property.2 hbR.le)
        j := by

  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let qOpen :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨(q : ℝ),
      lt_of_lt_of_le ha q.property.1,
      lt_of_le_of_lt q.property.2 hbR⟩

  let F5 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2
      hNS ht₀ hE hTail qOpen j

  let H5 : H3FourierComplexL2 :=
    h3SelectedInitialHeatFifthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha q j

  let D5head : H3FourierComplexL2 :=
    h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha q j

  let D5tail : H3FourierComplexL2 :=
    h3SelectedDuhamelTailFifthRadialFourierL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      j

  let W0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ (q : ℝ) j

  let H0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      (one_pos : (0 : ℝ) < 1)
      U₀
      (lt_of_lt_of_le ha q.property.1)
      j

  let D0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ))
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ j

  let Dh0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      j

  let Dt0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := (q : ℝ))
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ j

  have hF5 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2_ae
      hNS ht₀ hE hTail qOpen j
  dsimp only at hF5

  have hWraw :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := (q : ℝ))
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ j

  have hMild :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      j

  have hDsplit :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      j

  have hH5 :=
    h3SelectedInitialHeatFifthRadialFourierL2OnCompact_ae
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha q j

  have hDh5 :=
    h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact_ae
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha q j

  have hDt5 :=
    h3SelectedDuhamelTailFifthRadialFourierL2_ae
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      j

  change F5 = H5 - D5head - D5tail

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hF5,
    hWraw,
    hMild,
    hDsplit,
    hH5,
    hDh5,
    hDt5,
    MeasureTheory.Lp.coeFn_sub H5 D5head,
    MeasureTheory.Lp.coeFn_sub (H5 - D5head) D5tail
  ] with ξ hF5ξ hWrawξ hMildξ hDsplitξ hH5ξ hDh5ξ hDt5ξ hSub1 hSub2

  rw [hSub2]
  simp only [Pi.sub_apply] at hSub1 ⊢
  rw [hSub1]

  rw [hF5ξ]
  unfold h3SelectedRawFourierFifthRadialWeight
  rw [← hWrawξ]
  rw [hMildξ, hDsplitξ]
  rw [hH5ξ, hDh5ξ, hDt5ξ]

  ring

/-! ## Uniform compact fifth-radial selected velocity bound -/

/-- One fifth-radial norm-square constant works for every selected coordinate
and every target time in a positive compact restart slab. -/
theorem exists_norm_sq_bound_h3PreterminalSelectedVelocityFifthRadialFourierL2OnCompact
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    ∃ B5 : ℝ,
      0 ≤ B5 ∧
      ∀ q : Set.Icc a b,
        ∀ j : Fin 3,
          ‖h3PreterminalSelectedVelocityFifthRadialFourierL2
              hNS ht₀ hE hTail
              ⟨(q : ℝ),
                lt_of_lt_of_le ha q.property.1,
                lt_of_le_of_lt q.property.2 hbR⟩
              j‖ ^ 2
            ≤
          B5 := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  obtain ⟨BTail, hBTail0, hBTail⟩ :=
    exists_norm_sq_bound_h3SelectedDuhamelTailFifthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      ha hab hbR

  let Cfree : ℝ :=
    h3HeatNatMomentCoefficient 5 (1 : ℝ) a * E

  let Chead : ℝ :=
    h3HeatNatMomentCoefficient 5 (1 : ℝ) (a / 2) * (3 * E)

  let B5 : ℝ :=
    3 * (Cfree ^ 2 + Chead ^ 2 + BTail)

  have hCfree0 : 0 ≤ Cfree := by
    dsimp only [Cfree]
    exact
      mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg 5 (1 : ℝ) a)
        (le_trans zero_le_one hE)

  have hChead0 : 0 ≤ Chead := by
    dsimp only [Chead]
    exact
      mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg 5 (1 : ℝ) (a / 2))
        (mul_nonneg (by norm_num) (le_trans zero_le_one hE))

  have hB50 : 0 ≤ B5 := by
    dsimp only [B5]
    positivity

  refine ⟨B5, hB50, ?_⟩

  intro q j

  let qOpen :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨(q : ℝ),
      lt_of_lt_of_le ha q.property.1,
      lt_of_le_of_lt q.property.2 hbR⟩

  let F5 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityFifthRadialFourierL2
      hNS ht₀ hE hTail qOpen j

  let H5 : H3FourierComplexL2 :=
    h3SelectedInitialHeatFifthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha q j

  let D5head : H3FourierComplexL2 :=
    h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ ha q j

  let D5tail : H3FourierComplexL2 :=
    h3SelectedDuhamelTailFifthRadialFourierL2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      j

  have hEq :
      F5 = H5 - D5head - D5tail := by
    dsimp only [F5, H5, D5head, D5tail, qOpen, U₀, hA, hU₀]
    exact
      h3PreterminalSelectedVelocityFifthRadialFourierL2_eq_partsOnCompact
        hNS ht₀ hE hTail ha hbR q j

  have hFree :
      ‖H5‖ ≤ Cfree := by
    dsimp only [H5, Cfree, U₀, hA, hU₀]
    exact
      norm_h3SelectedInitialHeatFifthRadialFourierL2OnCompact_le
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        ha q j

  have hHead :
      ‖D5head‖ ≤ Chead := by
    dsimp only [D5head, Chead, U₀, hA, hU₀]
    exact
      norm_h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact_le
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        ha hbR q j

  have hTailSq :
      ‖D5tail‖ ^ 2 ≤ BTail := by
    dsimp only [D5tail, U₀, hA, hU₀]
    exact
      hBTail q j

  have hFreeSq :
      ‖H5‖ ^ 2 ≤ Cfree ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg H5)
      hFree
      2

  have hHeadSq :
      ‖D5head‖ ^ 2 ≤ Chead ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg D5head)
      hHead
      2

  have hNorm :
      ‖H5 - D5head - D5tail‖
        ≤
      ‖H5‖ + ‖D5head‖ + ‖D5tail‖ := by
    calc
      ‖H5 - D5head - D5tail‖
          ≤
        ‖H5 - D5head‖ + ‖D5tail‖ :=
        norm_sub_le _ _
      _ ≤
        (‖H5‖ + ‖D5head‖) + ‖D5tail‖ :=
        add_le_add
          (norm_sub_le H5 D5head)
          (le_refl ‖D5tail‖)
      _ =
        ‖H5‖ + ‖D5head‖ + ‖D5tail‖ := by
        ring

  have hNormSq :
      ‖H5 - D5head - D5tail‖ ^ 2
        ≤
      (‖H5‖ + ‖D5head‖ + ‖D5tail‖) ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg (H5 - D5head - D5tail))
      hNorm
      2

  have hThree :
      (‖H5‖ + ‖D5head‖ + ‖D5tail‖) ^ 2
        ≤
      3 *
        (‖H5‖ ^ 2 +
          ‖D5head‖ ^ 2 +
          ‖D5tail‖ ^ 2) := by
    nlinarith [
      sq_nonneg (‖H5‖ - ‖D5head‖),
      sq_nonneg (‖H5‖ - ‖D5tail‖),
      sq_nonneg (‖D5head‖ - ‖D5tail‖)
    ]

  have hPieces :
      3 *
        (‖H5‖ ^ 2 +
          ‖D5head‖ ^ 2 +
          ‖D5tail‖ ^ 2)
        ≤
      B5 := by
    dsimp only [B5]
    exact
      mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add hFreeSq hHeadSq)
          hTailSq)
        (by norm_num)

  change ‖F5‖ ^ 2 ≤ B5

  rw [hEq]

  exact
    hNormSq.trans
      (hThree.trans hPieces)

end

end Euclidean
end Bridge
end PrimeTensor
