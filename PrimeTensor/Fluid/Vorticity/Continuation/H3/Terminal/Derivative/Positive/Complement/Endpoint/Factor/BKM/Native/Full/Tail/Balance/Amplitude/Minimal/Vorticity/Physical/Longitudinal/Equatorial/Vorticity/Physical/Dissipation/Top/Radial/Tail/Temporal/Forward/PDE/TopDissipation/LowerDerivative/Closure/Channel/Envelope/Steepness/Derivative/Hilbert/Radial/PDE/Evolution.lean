import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Truncation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Evolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Cutoff-free q³ selected Hilbert evolution

The preceding checkpoint completed the bounded `q³` cutoff layer:

* the raw selected Fourier coordinate has a strong derivative;
* every bounded `q³` truncation transports that derivative;
* the truncated velocity converges strongly to `q³ û_j`;
* the truncated projected RHS converges strongly to
  `-q⁴ û_j - q³ F_j`;
* every truncated RHS is norm-dominated by the full higher weighted RHS.

This file passes the bounded FTC identities to the cutoff-free limit on one
positive compact restart slab:

    q³ û_j(t) - q³ û_j(s)
      =
    ∫_s^t (-q⁴ û_j(r) - q³ F_j(r)) dr.

Since the higher weighted RHS is strongly continuous, the Banach-valued
fundamental theorem of calculus then gives the genuine strong derivative

    d/dt [q³ û_j]
      =
    -q⁴ û_j - q³ F_j

at every strict interior slab time.

This closes the selected analytic derivative needed for the sixth-diffusion
channel.  A later bridge transports the local selected derivative back to the
canonical terminal physical `q³ û_j` path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSixthDiffusionQCubeEvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/-! ## Cutoff-free interval evolution -/

theorem h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_intervalEvolution
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (s t : Set.Icc (Q / 2) Q) :
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR j t
      -
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR j s
      =
    ∫ r in (s : ℝ)..(t : ℝ),
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        (
          h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR j
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
        j

  have hRawRHS :
      Continuous rawRHS := by
    dsimp only [rawRHS]
    exact
      (
        continuous_h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius_coordinate
          hNS ht₀ hE hTail j
      ).comp
        hToRadius

  let weightedRHS :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j

  have hWeightedRHS :
      Continuous weightedRHS := by
    dsimp only [weightedRHS]
    exact
      continuous_h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR j

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
        j

  let truncPath :
      ℕ → ℝ → H3FourierComplexL2 :=
    fun n r =>
      h3SixthDiffusionTruncatedQCubeL2
        ((n : ℝ) + 1)
        (by positivity)
        (rawVelocity r)

  let truncRHS :
      ℕ →
        Set.Icc (Q / 2) Q →
          H3FourierComplexL2 :=
    fun n r =>
      h3SixthDiffusionTruncatedQCubeL2
        ((n : ℝ) + 1)
        (by positivity)
        (rawRHS r)

  have hTruncRHS
      (n : ℕ) :
      Continuous (truncRHS n) := by

    have hComp :=
      (
        h3SixthDiffusionTruncatedQCubeRealCLM
          ((n : ℝ) + 1)
          (by positivity)
      ).continuous.comp
        hRawRHS

    change
      Continuous
        (fun r : Set.Icc (Q / 2) Q =>
          h3SixthDiffusionTruncatedQCubeRealCLM
            ((n : ℝ) + 1)
            (by positivity)
            (rawRHS r))
      at hComp

    simpa only [
      h3SixthDiffusionTruncatedQCubeRealCLM_apply
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
      h3SelectedRestartVelocityRawFourierL2_truncatedQCube_hasDerivAt_unit
        hNS ht₀ htau hE hTail
        (by
          dsimp only [Rstar] at htauR ⊢
          exact htauR)
        ⟨hx0, hxtau⟩
        (by positivity : 0 ≤ (n : ℝ) + 1)
        j

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
    tendsto_h3SixthDiffusionTruncatedQCubeL2_selectedVelocityOnSlab
      hNS ht₀ hE hTail hQ hQR j t

  have hVelocityS :=
    tendsto_h3SixthDiffusionTruncatedQCubeL2_selectedVelocityOnSlab
      hNS ht₀ hE hTail hQ hQR j s

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
              h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
                  hNS ht₀ hE hTail hQ hQR j t
                -
              h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
                  hNS ht₀ hE hTail hQ hQR j s
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
              norm_h3SixthDiffusionTruncatedQCubeL2_selectedProjectedRHSOnSlab_le
                hNS ht₀ hE hTail
                hQ hQR j
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
        tendsto_h3SixthDiffusionTruncatedQCubeL2_selectedProjectedRHSOnSlab
          hNS ht₀ hE hTail
          hQ hQR j xs

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
              h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
                  hNS ht₀ hE hTail hQ hQR j t
                -
              h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
                  hNS ht₀ hE hTail hQ hQR j s
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
      h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR j t
        -
      h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
            hNS ht₀ hE hTail hQ hQR j s :=
    tendsto_nhds_unique
      hIntegral
      hEndpointAsIntegral

  exact hLimit.symm

/-! ## Strong q³ derivative on the selected slab -/

theorem h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_hasDerivAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    HasDerivAt
      (
        Set.IccExtend
          (by linarith : Q / 2 ≤ Q)
          (
            h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
              hNS ht₀ hE hTail hQ hQR j
          )
      )
      (
        h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR j
          ⟨x, hx.1.le, hx.2.le⟩
      )
      x := by

  have hHalfLe :
      Q / 2 ≤ Q := by
    linarith

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j

  let Gclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j

  let V : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Vclosed

  let G : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Gclosed

  have hGClosedContinuous :
      Continuous Gclosed := by
    dsimp only [Gclosed]
    exact
      continuous_h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR j

  have hGContinuous :
      Continuous G := by
    dsimp only [G]
    exact
      hGClosedContinuous.Icc_extend'

  have hGAt :
      ∀ y ∈ Set.Ioo (Q / 2) Q,
        ContinuousAt G y := by
    intro y hy
    exact hGContinuous.continuousAt

  have hGIntegrable :
      IntervalIntegrable G volume (Q / 2) x := by
    exact
      hGContinuous.intervalIntegrable
        (Q / 2)
        x

  have hGMeasurable :
      StronglyMeasurableAtFilter
        G
        (𝓝 x)
        (volume : Measure ℝ) := by
    exact
      ContinuousAt.stronglyMeasurableAtFilter
        (μ := (volume : Measure ℝ))
        isOpen_Ioo
        hGAt
        x
        hx

  have hIntegralDerivative :
      HasDerivAt
        (fun y : ℝ =>
          ∫ r in (Q / 2)..y, G r)
        (G x)
        x :=
    intervalIntegral.integral_hasDerivAt_right
      hGIntegrable
      hGMeasurable
      hGContinuous.continuousAt

  let left :
      Set.Icc (Q / 2) Q :=
    ⟨Q / 2, le_rfl, hHalfLe⟩

  let J : ℝ → H3FourierComplexL2 :=
    fun y =>
      V (Q / 2)
        +
      ∫ r in (Q / 2)..y, G r

  have hJDerivative :
      HasDerivAt J (G x) x := by
    dsimp only [J]
    exact
      hIntegralDerivative.const_add
        (V (Q / 2))

  have hJEq :
      ∀ y ∈ Set.Icc (Q / 2) Q,
        J y = V y := by

    intro y hy

    let yClosed :
        Set.Icc (Q / 2) Q :=
      ⟨y, hy⟩

    have hEvolution :=
      h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_intervalEvolution
        hNS ht₀ hE hTail
        hQ hQR j
        left yClosed

    have hVLeft :
        V (Q / 2)
          =
        Vclosed left := by
      dsimp only [V]
      rw [
        Set.IccExtend_of_mem
          hHalfLe
          Vclosed
          ⟨le_rfl, hHalfLe⟩
      ]

    have hVy :
        V y
          =
        Vclosed yClosed := by
      dsimp only [V]
      rw [
        Set.IccExtend_of_mem
          hHalfLe
          Vclosed
          hy
      ]

    dsimp only [J]

    rw [hVLeft, hVy]

    dsimp only [G, Gclosed, Vclosed, left, yClosed] at hEvolution ⊢

    rw [← hEvolution]

    abel

  have hNeighborhood :
      Set.Icc (Q / 2) Q ∈ 𝓝 x :=
    Icc_mem_nhds
      hx.1
      hx.2

  have hEventuallyEq :
      V =ᶠ[𝓝 x] J := by
    filter_upwards [hNeighborhood] with y hy
    exact
      (hJEq y hy).symm

  have hVDerivative :
      HasDerivAt V (G x) x :=
    hJDerivative.congr_of_eventuallyEq
      hEventuallyEq

  let xClosed :
      Set.Icc (Q / 2) Q :=
    ⟨x, hx.1.le, hx.2.le⟩

  have hGx :
      G x = Gclosed xClosed := by
    dsimp only [G]
    rw [
      Set.IccExtend_of_mem
        hHalfLe
        Gclosed
        ⟨hx.1.le, hx.2.le⟩
    ]

  dsimp only [V, Gclosed, xClosed] at hVDerivative ⊢

  exact
    hVDerivative.congr_deriv
      hGx

theorem h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_differentiableAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (j : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    DifferentiableAt ℝ
      (
        Set.IccExtend
          (by linarith : Q / 2 ≤ Q)
          (
            h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
              hNS ht₀ hE hTail hQ hQR j
          )
      )
      x :=
  (
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_hasDerivAt
      hNS ht₀ hE hTail hQ hQR j hx
  ).differentiableAt

end

end Euclidean
end Bridge
end PrimeTensor
