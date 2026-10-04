import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Velocity.Truncation.Convergence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Evolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Generic natural-radial selected velocity evolution and derivative

The generic natural-radial cutoff layer is now complete:

* `T[m,R]` is bounded on raw Fourier `L²`;
* `T[m,n+1]` converges strongly to the full radial state;
* the truncated projected RHS is norm-dominated by the full radial RHS.

This file closes the temporal argument for every natural order `m ≥ 2`.

For each positive compact selected restart slab `[Q/2,Q]`, each coordinate
`i`, and each radial order `m ≥ 2`, we prove

    |ξ|^m û_i(t) - |ξ|^m û_i(s)
      =
    ∫_s^t |ξ|^m R̂_i(r) dr,

where `R̂` is the exact selected projected Navier--Stokes RHS.

The proof is the order-generic version of the already successful intrinsic
`q²` argument:

1. transport the raw selected derivative through each bounded cutoff;
2. apply Banach-valued FTC at fixed cutoff;
3. remove the cutoff at both endpoints;
4. pass the RHS integrals to the limit by dominated convergence.

Strong continuity of the full radial RHS then upgrades the interval evolution
to a genuine `HasDerivAt` theorem for the full arbitrary-radial velocity path.

This is the strong topology needed by the selected nonlinear forcing
difference quotient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityNatRadialEvolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3200000

/-! ## Fixed bounded cutoff derivative -/

/--
For every fixed nonnegative Euclidean cutoff `R`, the bounded natural-radial
operator transports the strong selected raw-Fourier derivative.
-/
theorem h3SelectedRestartVelocityRawFourierL2_truncatedNatRadial_hasDerivAt_unit
    (m : ℕ)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ tau q R : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau)
    (hR : 0 ≤ R)
    (i : Fin 3) :
    HasDerivAt
      (fun r : ℝ =>
        h3SelectedTruncatedNatRadialL2
          m R hR
          (
            h3SpectralScalarRawFourierL2
              (
                (
                  h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    (one_pos : (0 : ℝ) < 1)
                    (h3PreterminalSelectedDecoderAnchorState
                      hNS ht₀ hTail)
                    (lt_of_lt_of_le zero_lt_one hE)
                    (norm_h3PreterminalSelectedDecoderAnchorState_le
                      hNS ht₀ hE hTail)
                    r
                ) i
              )
          ))
      (
        h3SelectedTruncatedNatRadialL2
          m R hR
          (
            h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
              hNS ht₀ hE hTail
              (
                h3PreterminalElapsedToSelectedUnitRadius
                  htauR
                  ⟨q, hq.1.le, hq.2.le⟩
              )
              i
          )
      )
      q := by

  have hRaw :=
    h3SelectedRestartVelocityRawFourierL2_hasDerivAt_unit
      hNS ht₀ htau hE hTail htauR hq i

  have h :=
    (
      h3SelectedTruncatedNatRadialRealCLM
        m R hR
    ).hasFDerivAt.comp_hasDerivAt
      q
      hRaw

  simpa only [
    Function.comp_def,
    h3SelectedTruncatedNatRadialRealCLM_apply
  ] using h

/-! ## Full radial compact-slab evolution -/

/--
Exact selected arbitrary-radial Fourier `L²` evolution on one positive compact
restart slab.
-/
theorem h3PreterminalSelectedVelocityNatRadialFourierL2OnSlab_intervalEvolution
    (m : ℕ)
    (hm : 2 ≤ m)
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
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
          m hm
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          (by positivity : 0 < Q / 2)
          hQR t i
      -
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
          m hm
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          (by positivity : 0 < Q / 2)
          hQR s i
      =
    ∫ r in (s : ℝ)..(t : ℝ),
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        (
          h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
            m hNS ht₀ hE hTail hQ hQR i
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

  let radialRHS :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i

  have hRadialRHS :
      Continuous radialRHS := by
    dsimp only [radialRHS]
    exact
      continuous_h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        m hNS ht₀ hE hTail hQ hQR i

  let radialRHSExt :
      ℝ → H3FourierComplexL2 :=
    Set.IccExtend
      hHalfLe
      radialRHS

  have hRadialRHSExt :
      Continuous radialRHSExt := by
    dsimp only [radialRHSExt]
    exact
      (continuous_IccExtend_iff).2
        hRadialRHS

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
      h3SelectedTruncatedNatRadialL2
        m
        ((n : ℝ) + 1)
        (by positivity)
        (rawVelocity r)

  let truncRHS :
      ℕ →
        Set.Icc (Q / 2) Q →
          H3FourierComplexL2 :=
    fun n r =>
      h3SelectedTruncatedNatRadialL2
        m
        ((n : ℝ) + 1)
        (by positivity)
        (rawRHS r)

  have hTruncRHS
      (n : ℕ) :
      Continuous (truncRHS n) := by

    have hComp :=
      (
        h3SelectedTruncatedNatRadialRealCLM
          m
          ((n : ℝ) + 1)
          (by positivity)
      ).continuous.comp
        hRawRHS

    change
      Continuous
        (fun r : Set.Icc (Q / 2) Q =>
          h3SelectedTruncatedNatRadialRealCLM
            m
            ((n : ℝ) + 1)
            (by positivity)
            (rawRHS r))
      at hComp

    simpa only [
      h3SelectedTruncatedNatRadialRealCLM_apply
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
      h3SelectedRestartVelocityRawFourierL2_truncatedNatRadial_hasDerivAt_unit
        m
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
    tendsto_h3SelectedTruncatedNatRadialL2_selectedVelocityOnSlab
      m hm
      hNS ht₀ hE hTail hQ hQR i t

  have hVelocityS :=
    tendsto_h3SelectedTruncatedNatRadialL2_selectedVelocityOnSlab
      m hm
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
              h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
                  m hm
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  hQhalf hQR t i
                -
              h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
                  m hm
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  hQhalf hQR s i
            )
        ) := by

    dsimp only [truncPath, rawVelocity]

    exact hVelocityT.sub hVelocityS

  have hBoundIntegrable :
      IntervalIntegrable
        (fun r : ℝ =>
          ‖radialRHSExt r‖)
        volume
        (s : ℝ)
        (t : ℝ) :=
    hRadialRHSExt.norm.intervalIntegrable
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
                radialRHSExt r
            )
        ) := by

    apply
      intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun r : ℝ =>
          ‖radialRHSExt r‖)

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

            have hRadialExt :
                radialRHSExt x
                  =
                radialRHS xs := by
              dsimp only [radialRHSExt]
              rw [
                Set.IccExtend_of_mem
                  hHalfLe
                  radialRHS
                  hxSlab
              ]

            rw [
              hTruncExt,
              hRadialExt
            ]

            dsimp only [
              truncRHS, rawRHS,
              radialRHS, toRadius, xs
            ]

            exact
              norm_h3SelectedTruncatedNatRadialL2_selectedProjectedRHSOnSlab_le
                m
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

      have hRadialExt :
          radialRHSExt x
            =
          radialRHS xs := by
        dsimp only [radialRHSExt]
        rw [
          Set.IccExtend_of_mem
            hHalfLe
            radialRHS
            hxSlab
        ]

      have hPoint :=
        tendsto_h3SelectedTruncatedNatRadialL2_selectedProjectedRHSOnSlab
          m
          hNS ht₀ hE hTail
          hQ hQR i xs

      have hRadius :
          h3SelectedProjectedRHSSlabRadius
              hE hQ hQR xs
            =
          toRadius xs := by
        apply Subtype.ext
        rfl

      have hPoint' :
          Tendsto
            (fun n : ℕ =>
              truncRHS n xs)
            atTop
            (
              𝓝
                (
                  radialRHS xs
                )
            ) := by

        dsimp only [
          truncRHS, rawRHS,
          radialRHS
        ]

        rw [← hRadius]

        simpa using hPoint

      have hPoint'' :
          Tendsto
            (fun n : ℕ =>
              truncRHSExt n x)
            atTop
            (
              𝓝
                (
                  radialRHS xs
                )
            ) := by

        apply
          hPoint'.congr'

        filter_upwards with n

        exact
          (hTruncExt n).symm

      simpa only [hRadialExt] using hPoint''

  have hEndpointAsIntegral :
      Tendsto
        (fun n : ℕ =>
          ∫ r in (s : ℝ)..(t : ℝ),
            truncRHSExt n r)
        atTop
        (
          𝓝
            (
              h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
                  m hm
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  hQhalf hQR t i
                -
              h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
                  m hm
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  hQhalf hQR s i
            )
        ) := by

    apply
      hEndpoint.congr'

    filter_upwards with n

    exact
      (hFTC n).symm

  have hLimit :
      (∫ r in (s : ℝ)..(t : ℝ),
          radialRHSExt r)
        =
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
            m hm
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            hQhalf hQR t i
        -
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
            m hm
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            hQhalf hQR s i :=
    tendsto_nhds_unique
      hIntegral
      hEndpointAsIntegral

  exact hLimit.symm

/-! ## Strong arbitrary-radial derivative -/

/--
On every positive selected compact restart slab, the full order-`m` natural
radial velocity state has strong Fourier `L²` derivative equal to the exact
order-`m` projected RHS at every strict interior slab time.
-/
theorem h3PreterminalSelectedVelocityNatRadialFourierL2OnSlab_hasDerivAt
    (m : ℕ)
    (hm : 2 ≤ m)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ Q x : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3)
    (hx : x ∈ Set.Ioo (Q / 2) Q) :
    HasDerivAt
      (
        Set.IccExtend
          (by linarith : Q / 2 ≤ Q)
          (
            fun s : Set.Icc (Q / 2) Q =>
              h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
                m hm
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                (by positivity : 0 < Q / 2)
                hQR s i
          )
      )
      (
        h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
          m hNS ht₀ hE hTail hQ hQR i
          ⟨x, hx.1.le, hx.2.le⟩
      )
      x := by

  have hHalfLe :
      Q / 2 ≤ Q := by
    linarith

  have hHalfPos :
      0 < Q / 2 := by
    positivity

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    fun s =>
      h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        m hm
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        hHalfPos hQR s i

  let Gclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
      m hNS ht₀ hE hTail hQ hQR i

  let V : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Vclosed

  let G : ℝ → H3FourierComplexL2 :=
    Set.IccExtend hHalfLe Gclosed

  have hGClosedContinuous :
      Continuous Gclosed := by
    dsimp only [Gclosed]
    exact
      continuous_h3PreterminalSelectedProjectedRHSNatRadialFourierL2OnSlab
        m hNS ht₀ hE hTail hQ hQR i

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
      h3PreterminalSelectedVelocityNatRadialFourierL2OnSlab_intervalEvolution
        m hm
        hNS ht₀ hE hTail
        hQ hQR i
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

end

end Euclidean
end Bridge
end PrimeTensor
