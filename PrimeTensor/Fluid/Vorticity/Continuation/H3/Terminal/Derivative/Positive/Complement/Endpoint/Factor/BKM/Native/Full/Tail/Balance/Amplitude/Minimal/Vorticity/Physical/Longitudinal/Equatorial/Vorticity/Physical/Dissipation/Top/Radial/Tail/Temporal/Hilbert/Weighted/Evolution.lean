import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Truncation.Selected
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Full weighted selected top-tail Hilbert evolution

The bounded truncation argument is now complete pointwise in time:

* the raw selected Fourier coordinate has a strong derivative;
* every bounded `q²` truncation transports that derivative;
* the truncated velocity converges strongly to the intrinsic `q² û` state;
* the truncated projected RHS converges strongly to the exact weighted RHS.

This file removes the cutoff at the level of the temporal integral equation.

For one positive compact restart slab `[Q/2,Q]`, the result is

    q² û_i(t) - q² û_i(s)
      =
    ∫_s^t (-q³ û_i(r) - q² F_i(r)) dr.

The proof uses only:

1. Banach-valued FTC for each bounded truncation;
2. the exact domination `‖T_R F‖ ≤ ‖G‖` whenever `G = q² F`;
3. continuity, hence interval integrability, of the weighted RHS;
4. interval dominated convergence.

No unbounded multiplier is ever applied directly to a derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedEvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2500000

/-! ## Generic norm domination for a weighted-domain element -/

/--
If `G = q² F` almost everywhere, every nonnegative bounded radial truncation
has norm at most the full weighted state:

    `‖T_R F‖ ≤ ‖G‖`.
-/
theorem norm_h3TopTailTruncatedQSqL2_le_of_ae_eq
    (F G : H3FourierComplexL2)
    (hFG :
      (
        (G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        F ξ))
    {R : ℝ}
    (hR : 0 ≤ R) :
    ‖h3TopTailTruncatedQSqL2 R hR F‖
      ≤
    ‖G‖ := by

  apply Lp.norm_le_norm_of_ae_le

  have hTrunc :=
    h3TopTailTruncatedQSqL2_ae
      R hR F

  filter_upwards [hTrunc, hFG]
    with ξ hTruncξ hFGξ

  rw [hTruncξ, hFGξ]

  unfold
    h3TopTailTruncatedQSqFunction
    h3TopTailTruncatedQSqMultiplier

  by_cases hLow :
      ξ ∈ h3TerminalRadialFrequencyBelow R

  · rw [Set.indicator_of_mem hLow]

  · rw [Set.indicator_of_notMem hLow]
    rw [zero_mul, norm_zero]
    exact norm_nonneg _

/-! ## Selected Fourier projected-RHS continuity -/

/--
One selected quotient-safe projected Fourier RHS coordinate is strongly
continuous on the whole closed restart radius.
-/
theorem continuous_h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_coordinate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (i : Fin 3) :
    Continuous
      (fun q :
          Set.Icc
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
          hNS ht₀ hE hTail q i) := by

  let W :
      Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail

  have hW : Continuous W := by
    dsimp only [W]
    unfold h3PreterminalSelectedUnitSpectralStateOnRadius
    exact
      (
        continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
      ).comp
        continuous_subtype_val

  have hCoord :
      Continuous
        (fun q :
            Set.Icc
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          W q i) :=
    (continuous_apply i).comp hW

  have hLap :
      Continuous
        (fun q :
            Set.Icc
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
            hNS ht₀ hE hTail q i) := by
    unfold
      h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
    exact
      continuous_h3SpectralScalarLaplacianRawFourierL2.comp
        hCoord

  let D :
      Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        H3SpectralFinVectorState × H3SpectralFinVectorState :=
    fun q => (W q, W q)

  have hD : Continuous D := by
    dsimp only [D]
    exact Continuous.prodMk hW hW

  have hForce :
      Continuous
        (fun q :
            Set.Icc
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
            hNS ht₀ hE hTail q i) := by

    have hComp :=
      (continuous_h3RawFinLerayOuterProductDivergenceFourierL2 i).comp
        hD

    have hEq :
        (fun q :
            Set.Icc
              (0 : ℝ)
              (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
            hNS ht₀ hE hTail q i)
          =
        (fun q =>
          h3RawFinLerayOuterProductDivergenceFourierL2
            (W q) (W q) i) := by
      funext q
      rfl

    rw [hEq]

    exact hComp

  unfold
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius

  exact hLap.sub hForce

/-! ## Exact q² relation for the selected RHS -/

/--
On a positive terminal-half slab, the exact weighted PDE RHS is almost
everywhere `q²` times the selected unweighted projected Fourier RHS.
-/
theorem h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_eq_qsq_projectedRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q) :
    let qRadius :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨
        (s : ℝ),
        (
          lt_of_lt_of_le
            (by positivity : 0 < Q / 2)
            s.property.1
        ).le,
        (
          lt_of_le_of_lt
            s.property.2
            hQR
        ).le
      ⟩
    (
      (
        h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i s :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
        *
      (
        (
          h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
            hNS ht₀ hE hTail qRadius i :
          H3FourierComplexL2
        ) ξ
      )) := by

  dsimp only

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      (s : ℝ),
      (
        lt_of_lt_of_le
          (by positivity : 0 < Q / 2)
          s.property.1
      ).le,
      (
        lt_of_le_of_lt
          s.property.2
          hQR
      ).le
    ⟩

  let U : H3SpectralFinVectorState :=
    h3PreterminalSelectedUnitSpectralStateOnRadius
      hNS ht₀ hE hTail qRadius

  have hProjected :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_ae_eq_unitPDE
      hNS ht₀ hE hTail qRadius i

  have hWeighted :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_gradientSquare
      hNS ht₀ hE hTail hQ hQR i s

  filter_upwards [hProjected, hWeighted]
    with ξ hProjectedξ hWeightedξ

  rw [hWeightedξ, hProjectedξ]

  dsimp only [U, qRadius] at *

  unfold
    h3PreterminalSelectedUnitSpectralStateOnRadius
    at *

  simp only [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2,
    h3SpectralFinCoordinateRawFourierL2CLM_apply,
    Complex.ofReal_neg,
    Complex.ofReal_mul,
    Complex.ofReal_pow
  ] at *

  ring

/-! ## Selected truncation norm domination -/

/--
At each slab time, a natural truncated selected projected RHS has norm at
most the full weighted PDE RHS.
-/
theorem norm_h3TopTailTruncatedQSqL2_selectedProjectedRHSOnSlab_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s : Set.Icc (Q / 2) Q)
    (n : ℕ) :
    let qRadius :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨
        (s : ℝ),
        (
          lt_of_lt_of_le
            (by positivity : 0 < Q / 2)
            s.property.1
        ).le,
        (
          lt_of_le_of_lt
            s.property.2
            hQR
        ).le
      ⟩
    ‖(
      h3TopTailTruncatedQSqL2
        ((n : ℝ) + 1)
        (by positivity)
        (
          h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
            hNS ht₀ hE hTail qRadius i
        )
    )‖
      ≤
    ‖(
      h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR i s
    )‖ := by

  dsimp only

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨
      (s : ℝ),
      (
        lt_of_lt_of_le
          (by positivity : 0 < Q / 2)
          s.property.1
      ).le,
      (
        lt_of_le_of_lt
          s.property.2
          hQR
      ).le
    ⟩

  let F : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNS ht₀ hE hTail qRadius i

  let G : H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i s

  have hFG :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_eq_qsq_projectedRHS
      hNS ht₀ hE hTail hQ hQR i s

  have h :=
    norm_h3TopTailTruncatedQSqL2_le_of_ae_eq
      F G hFG
      (R := ((n : ℝ) + 1))
      (by positivity)

  dsimp only [F, G, qRadius] at h ⊢

  exact h

/-! ## Full compact-slab weighted evolution -/

/--
Exact selected top-tail weighted Hilbert evolution on one positive compact
restart slab.
-/
theorem h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_intervalEvolution
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (s t : Set.Icc (Q / 2) Q) :
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i t
      -
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR i s
      =
    ∫ r in (s : ℝ)..(t : ℝ),
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        (
          h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR i
        )
        r := by

  let Rstar : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  let tau : ℝ :=
    (Q + Rstar) / 2

  have hQhalf : 0 < Q / 2 := by
    positivity

  have hHalfLe : Q / 2 ≤ Q := by
    linarith

  have hQtau : Q < tau := by
    dsimp only [tau, Rstar]
    linarith

  have htau : 0 < tau :=
    hQ.trans hQtau

  have htauR : tau ≤ Rstar := by
    dsimp only [tau, Rstar]
    linarith

  let toRadius :
      Set.Icc (Q / 2) Q →
        Set.Icc (0 : ℝ) Rstar :=
    fun r =>
      ⟨
        (r : ℝ),
        (
          lt_of_lt_of_le
            hQhalf
            r.property.1
        ).le,
        (
          lt_of_le_of_lt
            r.property.2
            hQR
        ).le
      ⟩

  have hToRadius :
      Continuous toRadius := by
    exact
      continuous_subtype_val.subtype_mk _

  let rawRHS :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    fun r =>
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
        hNS ht₀ hE hTail
        (toRadius r)
        i

  have hRawRHS :
      Continuous rawRHS := by
    dsimp only [rawRHS]
    exact
      (
        continuous_h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_coordinate
          hNS ht₀ hE hTail i
      ).comp
        hToRadius

  let weightedRHS :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR i

  have hWeightedRHS :
      Continuous weightedRHS := by
    dsimp only [weightedRHS]
    exact
      continuous_h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR i

  let weightedRHSExt :
      ℝ → H3FourierComplexL2 :=
    Set.IccExtend
      hHalfLe
      weightedRHS

  have hWeightedRHSExt :
      Continuous weightedRHSExt := by
    dsimp only [weightedRHSExt]
    exact
      (continuous_IccExtend_iff).2
        hWeightedRHS

  let rawVelocity :
      ℝ → H3FourierComplexL2 :=
    fun r =>
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        r
        i

  let truncPath :
      ℕ → ℝ → H3FourierComplexL2 :=
    fun n r =>
      h3TopTailTruncatedQSqL2
        ((n : ℝ) + 1)
        (by positivity)
        (rawVelocity r)

  let truncRHS :
      ℕ →
        Set.Icc (Q / 2) Q →
          H3FourierComplexL2 :=
    fun n r =>
      h3TopTailTruncatedQSqL2
        ((n : ℝ) + 1)
        (by positivity)
        (rawRHS r)

  have hTruncRHS
      (n : ℕ) :
      Continuous (truncRHS n) := by

    have hComp :=
      (
        h3TopTailTruncatedQSqRealCLM
          ((n : ℝ) + 1)
          (by positivity)
      ).continuous.comp
        hRawRHS

    change
      Continuous
        (fun r : Set.Icc (Q / 2) Q =>
          h3TopTailTruncatedQSqRealCLM
            ((n : ℝ) + 1)
            (by positivity)
            (rawRHS r))
      at hComp

    simpa only [
      h3TopTailTruncatedQSqRealCLM_apply
    ] using hComp

  let truncRHSExt :
      ℕ → ℝ → H3FourierComplexL2 :=
    fun n =>
      Set.IccExtend
        hHalfLe
        (truncRHS n)

  have hTruncRHSExt
      (n : ℕ) :
      Continuous (truncRHSExt n) := by
    dsimp only [truncRHSExt]
    exact
      (continuous_IccExtend_iff).2
        (hTruncRHS n)

  have hUccSubset
      {x : ℝ}
      (hx :
        x ∈ Set.uIcc (s : ℝ) (t : ℝ)) :
      x ∈ Set.Icc (Q / 2) Q := by

    have hLower :
        Q / 2
          ≤
        min (s : ℝ) (t : ℝ) := by
      exact
        le_min s.property.1 t.property.1

    have hUpper :
        max (s : ℝ) (t : ℝ)
          ≤
        Q := by
      exact
        max_le s.property.2 t.property.2

    exact
      ⟨
        hLower.trans hx.1,
        hx.2.trans hUpper
      ⟩

  have hDeriv
      (n : ℕ)
      (x : ℝ)
      (hx :
        x ∈ Set.uIcc (s : ℝ) (t : ℝ)) :
      HasDerivAt
        (truncPath n)
        (truncRHSExt n x)
        x := by

    have hxSlab :=
      hUccSubset hx

    let xs : Set.Icc (Q / 2) Q :=
      ⟨x, hxSlab⟩

    have hx0 : 0 < x :=
      lt_of_lt_of_le
        hQhalf
        hxSlab.1

    have hxtau : x < tau :=
      lt_of_le_of_lt
        hxSlab.2
        hQtau

    have hBase :=
      h3SelectedRestartVelocityRawFourierL2_truncatedQSq_hasDerivAt_unit
        hNS ht₀ htau hE hTail
        (by
          dsimp only [Rstar] at htauR ⊢
          exact htauR)
        ⟨hx0, hxtau⟩
        (by positivity : 0 ≤ (n : ℝ) + 1)
        i

    let xClosedTau : Set.Icc (0 : ℝ) tau :=
      ⟨x, hx0.le, hxtau.le⟩

    let xRadiusTau :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      h3PreterminalElapsedToSelectedUnitRadius
        (by
          dsimp only [Rstar] at htauR ⊢
          exact htauR)
        xClosedTau

    have hRadius :
        xRadiusTau
          =
        toRadius xs := by
      apply Subtype.ext
      rfl

    have hExt :
        truncRHSExt n x
          =
        truncRHS n xs := by
      dsimp only [truncRHSExt]
      rw [
        Set.IccExtend_of_mem
          hHalfLe
          (truncRHS n)
          hxSlab
      ]

    dsimp only [truncPath, rawVelocity] at hBase ⊢

    rw [hExt]

    dsimp only [truncRHS, rawRHS]

    rw [← hRadius]

    exact hBase

  have hFTC
      (n : ℕ) :
      (∫ r in (s : ℝ)..(t : ℝ),
          truncRHSExt n r)
        =
      truncPath n (t : ℝ)
        -
      truncPath n (s : ℝ) := by

    exact
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx =>
          hDeriv n x hx)
        ((hTruncRHSExt n).intervalIntegrable
          (s : ℝ)
          (t : ℝ))

  have hVelocityT :=
    tendsto_h3TopTailTruncatedQSqL2_selectedVelocityOnSlab
      hNS ht₀ hE hTail hQ hQR i t

  have hVelocityS :=
    tendsto_h3TopTailTruncatedQSqL2_selectedVelocityOnSlab
      hNS ht₀ hE hTail hQ hQR i s

  have hEndpoint :
      Tendsto
        (fun n : ℕ =>
          truncPath n (t : ℝ)
            -
          truncPath n (s : ℝ))
        atTop
        (
          𝓝
            (
              h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
                  hNS ht₀ hE hTail hQ hQR i t
                -
              h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
                  hNS ht₀ hE hTail hQ hQR i s
            )
        ) := by

    dsimp only [truncPath, rawVelocity]

    exact hVelocityT.sub hVelocityS

  have hBoundIntegrable :
      IntervalIntegrable
        (fun r : ℝ =>
          ‖weightedRHSExt r‖)
        volume
        (s : ℝ)
        (t : ℝ) :=
    hWeightedRHSExt.norm.intervalIntegrable
      (s : ℝ)
      (t : ℝ)

  have hIntegral :
      Tendsto
        (fun n : ℕ =>
          ∫ r in (s : ℝ)..(t : ℝ),
            truncRHSExt n r)
        atTop
        (
          𝓝
            (
              ∫ r in (s : ℝ)..(t : ℝ),
                weightedRHSExt r
            )
        ) := by

    apply
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun r : ℝ =>
          ‖weightedRHSExt r‖)

    · exact
        Eventually.of_forall
          (fun n =>
            (hTruncRHSExt n).aestronglyMeasurable)

    · exact
        Eventually.of_forall
          (fun n => by
            filter_upwards with x
            intro hxIoc

            have hxUcc :
                x ∈
                  Set.uIcc
                    (s : ℝ)
                    (t : ℝ) :=
              Set.uIoc_subset_uIcc hxIoc

            have hxSlab :=
              hUccSubset hxUcc

            let xs :
                Set.Icc (Q / 2) Q :=
              ⟨x, hxSlab⟩

            have hTruncExt :
                truncRHSExt n x
                  =
                truncRHS n xs := by
              dsimp only [truncRHSExt]
              rw [
                Set.IccExtend_of_mem
                  hHalfLe
                  (truncRHS n)
                  hxSlab
              ]

            have hWeightedExt :
                weightedRHSExt x
                  =
                weightedRHS xs := by
              dsimp only [weightedRHSExt]
              rw [
                Set.IccExtend_of_mem
                  hHalfLe
                  weightedRHS
                  hxSlab
              ]

            rw [
              hTruncExt,
              hWeightedExt
            ]

            dsimp only [truncRHS, rawRHS, weightedRHS, toRadius, xs]

            exact
              norm_h3TopTailTruncatedQSqL2_selectedProjectedRHSOnSlab_le
                hNS ht₀ hE hTail
                hQ hQR i
                ⟨x, hxSlab⟩
                n)

    · exact hBoundIntegrable

    · filter_upwards with x
      intro hxIoc

      have hxUcc :
          x ∈
            Set.uIcc
              (s : ℝ)
              (t : ℝ) :=
        Set.uIoc_subset_uIcc hxIoc

      have hxSlab :=
        hUccSubset hxUcc

      let xs :
          Set.Icc (Q / 2) Q :=
        ⟨x, hxSlab⟩

      have hTruncExt
          (n : ℕ) :
          truncRHSExt n x
            =
          truncRHS n xs := by
        dsimp only [truncRHSExt]
        rw [
          Set.IccExtend_of_mem
            hHalfLe
            (truncRHS n)
            hxSlab
        ]

      have hWeightedExt :
          weightedRHSExt x
            =
          weightedRHS xs := by
        dsimp only [weightedRHSExt]
        rw [
          Set.IccExtend_of_mem
            hHalfLe
            weightedRHS
            hxSlab
        ]

      have hPoint :=
        tendsto_h3TopTailTruncatedQSqL2_selectedProjectedRHSOnSlab
          hNS ht₀ hE hTail
          hQ hQR i xs

      have hPoint' :
          Tendsto
            (fun n : ℕ =>
              truncRHS n xs)
            atTop
            (
              𝓝
                (
                  weightedRHS xs
                )
            ) := by

        dsimp only [truncRHS, rawRHS, weightedRHS, toRadius, xs]

        simpa using hPoint

      have hPoint'' :
          Tendsto
            (fun n : ℕ =>
              truncRHSExt n x)
            atTop
            (
              𝓝
                (
                  weightedRHS xs
                )
            ) := by

        apply
          hPoint'.congr'

        filter_upwards with n

        exact
          (hTruncExt n).symm

      simpa only [hWeightedExt] using hPoint''

  have hEndpointAsIntegral :
      Tendsto
        (fun n : ℕ =>
          ∫ r in (s : ℝ)..(t : ℝ),
            truncRHSExt n r)
        atTop
        (
          𝓝
            (
              h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
                  hNS ht₀ hE hTail hQ hQR i t
                -
              h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
                  hNS ht₀ hE hTail hQ hQR i s
            )
        ) := by

    apply
      hEndpoint.congr'

    filter_upwards with n

    exact
      (hFTC n).symm

  have hLimit :
      (∫ r in (s : ℝ)..(t : ℝ),
          weightedRHSExt r)
        =
      h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR i t
        -
      h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR i s :=
    tendsto_nhds_unique
      hIntegral
      hEndpointAsIntegral

  exact hLimit.symm

end

end Euclidean
end Bridge
end PrimeTensor
