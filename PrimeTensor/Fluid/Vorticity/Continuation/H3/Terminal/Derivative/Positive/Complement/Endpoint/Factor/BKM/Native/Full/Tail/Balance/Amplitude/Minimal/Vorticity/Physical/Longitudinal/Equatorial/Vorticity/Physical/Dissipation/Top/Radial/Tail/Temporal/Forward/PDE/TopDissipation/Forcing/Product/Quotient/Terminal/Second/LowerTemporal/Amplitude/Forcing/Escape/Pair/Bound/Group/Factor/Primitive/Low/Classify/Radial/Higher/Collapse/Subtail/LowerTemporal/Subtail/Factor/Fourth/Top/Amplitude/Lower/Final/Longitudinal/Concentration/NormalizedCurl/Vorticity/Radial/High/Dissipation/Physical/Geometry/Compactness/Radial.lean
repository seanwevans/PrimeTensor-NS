import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry.Compactness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Radial.Uniform.Absolute.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Bad.Cone.Volume.Vanishing

/-!
# Force the canonical physical witness into radial escape

The canonical single-time witness carries a fixed positive amount of physical
H³ dissipation in

    badCone(i, κ_n) \ {|ξ| < 1},

with `κ_n -> 0`.

Raw-Fourier `L²` Cauchy already gives uniform absolute continuity of physical
dissipation on every fixed bounded radial region.  For a target radius
`R = n+1`, choose a sufficiently late canonical index so that

* the selected time is within `1/(n+1)` of `T`;
* the bad-cone aperture is thin enough that its portion below `R` has volume
  smaller than the absolute-continuity threshold.

The bounded part then carries arbitrarily little dissipation mass, while the
whole canonical localized region carries a fixed positive mass.  A fixed
positive remainder is therefore forced outside radius `R`.

This diagonal argument produces radial escape on a subsequence of the exact
canonical `σ` witness.  It eliminates the small-volume branch without any
pointwise choice of an `Lp` representative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalCanonicalRadialEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalCanonicalRadialEscape :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 2400000

/--
A positive canonical bad-cone mass with shrinking aperture, together with raw
Fourier `L²` Cauchy, forces radial escape on a subsequence of the same
single-time sequence.
-/
theorem physicalDissipationRadialEscapeSubsequenceOf_of_singleTimeBadConeMass_of_velocityRawFourierL2Cauchy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (i : Fin 3)
    (σ : ℕ → ℝ)
    (hσ :
      ∀ n : ℕ,
        σ n ∈ Set.Ioo a T)
    (hSigma :
      Tendsto σ atTop (𝓝 T))
    (κ : ℕ → ℝ)
    (hκPos :
      ∀ n : ℕ,
        0 < κ n)
    (hKappa :
      Tendsto κ atTop (𝓝 0))
    {ε : ℝ}
    (hε : 0 < ε)
    (hLocal :
      ∀ n : ℕ,
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        16 *
          h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3
            i
            (κ n)
            1
            (σ n)
            ⟨
              lt_trans hClass.terminal_start.1
                (hσ n).1,
              (hσ n).2
            ⟩) :
    H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
      hH3 hClass σ := by

  let δ : ℝ :=
    ε ^ 2 / 4096

  have hδ :
      0 < δ := by
    dsimp only [δ]
    positivity

  have hLocalReal :
      ∀ n : ℕ,
        ε ^ 2 / 1024
          <
        h3TerminalPhysicalDissipationBadConeHighRadialRealMass
          hH3
          i
          (κ n)
          1
          (σ n)
          ⟨
            lt_trans hClass.terminal_start.1
              (hσ n).1,
            (hσ n).2
          ⟩ := by

    intro n

    let M : ℝ :=
      h3TerminalPhysicalDissipationBadConeHighRadialRealMass
        hH3
        i
        (κ n)
        1
        (σ n)
        ⟨
          lt_trans hClass.terminal_start.1
            (hσ n).1,
          (hσ n).2
        ⟩

    have hMNonneg :
        0 ≤ M := by

      dsimp only [M]

      exact
        h3TerminalPhysicalDissipationBadConeHighRadialRealMass_nonneg
          hH3
          i
          (κ n)
          1
          (σ n)
          ⟨
            lt_trans hClass.terminal_start.1
              (hσ n).1,
            (hσ n).2
          ⟩

    have hBridge :=
      ofReal_physicalDissipationBadConeHighRadialRealMass_eq_mass
        hH3
        hClass
        (hσ n)
        i
        (κ n)
        1

    have hScaled :
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        ENNReal.ofReal (16 * M) := by

      calc
        ENNReal.ofReal (ε ^ 2 / 64)
            <
          16 *
            h3TerminalPhysicalDissipationBadConeHighRadialMass
              hH3
              i
              (κ n)
              1
              (σ n)
              ⟨
                lt_trans hClass.terminal_start.1
                  (hσ n).1,
                (hσ n).2
              ⟩ :=
          hLocal n

        _ =
          16 * ENNReal.ofReal M := by

          dsimp only [M] at hBridge

          rw [hBridge]

        _ =
          ENNReal.ofReal (16 * M) := by

          rw [
            ENNReal.ofReal_mul
              (by norm_num : (0 : ℝ) ≤ 16)
          ]

          norm_num

    have hMPos :
        0 < M := by

      by_contra hNotPos

      have hMLe :
          M ≤ 0 :=
        le_of_not_gt hNotPos

      have hMZero :
          M = 0 :=
        le_antisymm hMLe hMNonneg

      rw [hMZero] at hScaled
      norm_num at hScaled

    have hReal :
        ε ^ 2 / 64
          <
        16 * M :=
      (
        ENNReal.ofReal_lt_ofReal_iff
          (
            mul_pos
              (by norm_num : (0 : ℝ) < 16)
              hMPos
          )
      ).1
        hScaled

    dsimp only [M] at hReal ⊢

    nlinarith

  have hSigmaMetric := hSigma
  rw [Metric.tendsto_atTop] at hSigmaMetric

  have hChoice :
      ∀ n : ℕ,
        ∃ d : ℕ,
          n ≤ d
            ∧
          dist (σ d) T
            <
          (1 : ℝ) / ((n : ℝ) + 1)
            ∧
          MeasurableSet
            (
              (
                h3TerminalLongitudinalAngularBadCone
                    i
                    (κ d)
                  \
                h3TerminalRadialFrequencyBelow 1
              )
                \
              h3TerminalRadialFrequencyBelow
                ((n : ℝ) + 1)
            )
            ∧
          (
            (
              h3TerminalLongitudinalAngularBadCone
                  i
                  (κ d)
                \
              h3TerminalRadialFrequencyBelow 1
            )
              \
            h3TerminalRadialFrequencyBelow
              ((n : ℝ) + 1)
          )
            ⊆
          (h3TerminalRadialFrequencyBelow
              ((n : ℝ) + 1))ᶜ
            ∧
          δ
            ≤
          h3TerminalPhysicalDissipationSetMassAt
            hH3
            hClass
            (σ d)
            (hσ d)
            (
              (
                h3TerminalLongitudinalAngularBadCone
                    i
                    (κ d)
                  \
                h3TerminalRadialFrequencyBelow 1
              )
                \
              h3TerminalRadialFrequencyBelow
                ((n : ℝ) + 1)
            ) := by

    intro n

    let R : ℝ :=
      (n : ℝ) + 1

    have hR :
        0 < R := by
      dsimp only [R]
      positivity

    have hUAC :=
      physicalDissipationUniformAbsoluteContinuityBelowRadialCutoffAtEndpoint_of_velocityRawFourierL2Cauchy
        hH3
        hClass
        hCauchy
        hR

    obtain
      ⟨
        α,
        hα,
        η,
        hη,
        hSmall
      ⟩ :=
      hUAC
        δ
        hδ

    obtain
      ⟨
        κ₀,
        hκ₀,
        hConeVolume
      ⟩ :=
      longitudinalBoundedBadConeVolumeVanishingAtCutoff
        i
        1
        R
        α
        hα

    have hKappaSmall :
        ∀ᶠ d : ℕ in atTop,
          κ d < κ₀ :=
      (tendsto_order.1 hKappa).2
        κ₀
        hκ₀

    obtain
      ⟨Nη, hNearη⟩ :=
      hSigmaMetric
        η
        hη

    have hScale :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      positivity

    obtain
      ⟨Ns, hNearScale⟩ :=
      hSigmaMetric
        ((1 : ℝ) / ((n : ℝ) + 1))
        hScale

    obtain
      ⟨
        d,
        hnd,
        hNηd,
        hNsd,
        hκd
      ⟩ :=
      (
        (eventually_ge_atTop n).and
          (
            (eventually_ge_atTop Nη).and
              (
                (eventually_ge_atTop Ns).and
                  hKappaSmall
              )
          )
      ).exists

    have hTimeNearη :
        dist (σ d) T < η :=
      hNearη
        d
        hNηd

    have hTimeNearScale :
        dist (σ d) T
          <
        (1 : ℝ) / ((n : ℝ) + 1) :=
      hNearScale
        d
        hNsd

    let htAbs :
        σ d ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans hClass.terminal_start.1
          (hσ d).1,
        (hσ d).2
      ⟩

    let F : H3FourierPoint3 → ℝ :=
      fun ξ =>
        h3TerminalSpectralDissipationSingleDensity
          (h3TerminalVelocitySpectralStateAt
            hH3
            (σ d)
            htAbs)
          ξ

    let B : Set H3FourierPoint3 :=
      h3TerminalRadialFrequencyBelow R

    let S : Set H3FourierPoint3 :=
      h3TerminalLongitudinalAngularBadCone
          i
          (κ d)
        \
      h3TerminalRadialFrequencyBelow 1

    let P : Set H3FourierPoint3 :=
      S ∩ B

    let Q : Set H3FourierPoint3 :=
      S \ B

    have hBMeas :
        MeasurableSet B := by
      dsimp only [B]
      exact
        measurableSet_h3TerminalRadialFrequencyBelow R

    have hSMeas :
        MeasurableSet S := by
      dsimp only [S]
      exact
        (
          measurableSet_h3TerminalLongitudinalAngularBadCone
            i
            (κ d)
        ).diff
          (
            measurableSet_h3TerminalRadialFrequencyBelow
              1
          )

    have hPMeas :
        MeasurableSet P :=
      hSMeas.inter
        hBMeas

    have hQMeas :
        MeasurableSet Q :=
      hSMeas.diff
        hBMeas

    have hPVolume :
        volume P < α := by

      dsimp only [P, S, B]

      exact
        hConeVolume
          (κ d)
          (hκPos d)
          hκd

    have hInsideRaw :=
      hSmall
        (σ d)
        (hσ d)
        hTimeNearη
        P
        hPMeas
        hPVolume

    have hPSubsetB :
        P ⊆ B := by
      intro ξ hξ
      exact hξ.2

    have hPInter :
        P ∩ B = P :=
      inter_eq_left.2
        hPSubsetB

    have hInside :
        (∫ ξ in P, F ξ ∂volume)
          <
        δ := by

      change
        (∫ ξ in P ∩ B, F ξ ∂volume)
          <
        δ
        at hInsideRaw

      rw [hPInter] at hInsideRaw

      exact
        hInsideRaw

    have hFInt :
        Integrable F volume := by

      dsimp only [F, htAbs]

      simpa only using
        (
          h3TerminalSpectralDissipationSingleDensity_integrable
            hH3
            hClass
            (hσ d)
        )

    have hSplit :
        (∫ ξ in S, F ξ ∂volume)
          =
        (∫ ξ in P, F ξ ∂volume)
          +
        (∫ ξ in Q, F ξ ∂volume) := by

      have hRaw :=
        integral_inter_add_sdiff₀
          (μ := volume)
          (s := S)
          hBMeas.nullMeasurableSet
          hFInt.integrableOn

      simpa only [P, Q] using
        hRaw.symm

    have hTotal :
        ε ^ 2 / 1024
          <
        (∫ ξ in S, F ξ ∂volume) := by

      have hRaw :=
        hLocalReal d

      simpa only [
        S,
        F,
        htAbs,
        h3TerminalPhysicalDissipationBadConeHighRadialRealMass
      ] using
        hRaw

    have hOuter :
        δ
          <
        (∫ ξ in Q, F ξ ∂volume) := by

      rw [hSplit] at hTotal

      have hConst :
          4 * δ = ε ^ 2 / 1024 := by
        dsimp only [δ]
        ring

      have hTotal' :
          4 * δ
            <
          (∫ ξ in P, F ξ ∂volume)
            +
          (∫ ξ in Q, F ξ ∂volume) := by

        simpa only [hConst] using
          hTotal

      linarith

    have hQSubset :
        Q ⊆ Bᶜ := by
      intro ξ hξ
      exact hξ.2

    have hMass :
        δ
          ≤
        h3TerminalPhysicalDissipationSetMassAt
          hH3
          hClass
          (σ d)
          (hσ d)
          Q := by

      dsimp only [
        h3TerminalPhysicalDissipationSetMassAt,
        Q,
        F,
        htAbs
      ]

      exact
        hOuter.le

    refine
      ⟨
        d,
        hnd,
        hTimeNearScale,
        ?_,
        ?_,
        ?_
      ⟩

    · simpa only [Q, S, B, R] using
        hQMeas

    · simpa only [Q, S, B, R] using
        hQSubset

    · simpa only [Q, S, B, R] using
        hMass

  choose
    m
    hnm
    hNear
    hMeas
    hSubset
    hMass
    using hChoice

  have hmTop :
      Tendsto m atTop atTop := by

    refine
      tendsto_atTop.2 ?_

    intro N

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    exact
      hn.trans
        (hnm n)

  let S : ℕ → Set H3FourierPoint3 :=
    fun n =>
      (
        (
          h3TerminalLongitudinalAngularBadCone
              i
              (κ (m n))
            \
          h3TerminalRadialFrequencyBelow 1
        )
          \
        h3TerminalRadialFrequencyBelow
          ((n : ℝ) + 1)
      )

  have hData :
      ∀ n : ℕ,
        ∃ ht :
          σ (m n) ∈ Set.Ioo a T,
          dist (σ (m n)) T
              <
            (1 : ℝ) / ((n : ℝ) + 1)
            ∧
          MeasurableSet (S n)
            ∧
          S n
              ⊆
            (h3TerminalRadialFrequencyBelow
                ((n : ℝ) + 1))ᶜ
            ∧
          δ
              ≤
            h3TerminalPhysicalDissipationSetMassAt
              hH3 hClass (σ (m n)) ht (S n) := by

    intro n

    refine
      ⟨
        hσ (m n),
        hNear n,
        ?_,
        ?_,
        ?_
      ⟩

    · simpa only [S] using
        hMeas n

    · simpa only [S] using
        hSubset n

    · simpa only [S] using
        hMass n

  have hSigmaM :
      Tendsto
        (fun n : ℕ => σ (m n))
        atTop
        (𝓝 T) :=
    hSigma.comp
      hmTop

  exact
    ⟨
      δ,
      hδ,
      m,
      hmTop,
      S,
      hData,
      hSigmaM
    ⟩

/--
The final resolved-PDE witness can be chosen so that its canonical single-time
physical dissipation sequence itself has a radial-escape subsequence.

This removes the small-volume branch from the synchronized final witness using
only the already-retained raw-Fourier `L²` Cauchy hypothesis.
-/
theorem exists_fixed_terminalSequence_with_canonicalPhysicalDissipationRadialEscape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
        )
        atTop
        (𝓝 0)
        ∧
      ∃ σ : ℕ → ℝ,
        ∃ hσ :
          ∀ n : ℕ,
            σ n ∈ Set.Ioo a T,
          Tendsto σ atTop (𝓝 T)
            ∧
          (
            ∀ n : ℕ,
              ENNReal.ofReal (ε ^ 2 / 64)
                <
              16 *
                h3TerminalPhysicalDissipationBadConeHighRadialMass
                  hH3
                  i
                  ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                  1
                  (σ n)
                  ⟨
                    lt_trans hClass.terminal_start.1
                      (hσ n).1,
                    (hσ n).2
                  ⟩
          )
            ∧
          H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
            hH3 hClass σ := by

  obtain
    ⟨
      _j₀,
      _τ,
      _hτ,
      _p,
      _q,
      _hnp,
      _hpq,
      _hTau,
      _hEnergyTop,
      _hLongTop,
      _r,
      _hrNe,
      k,
      hKMono,
      _hTauPK,
      _hTauQK,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      _hScalar,
      _hPolarization,
      _hNotVanishing
    ⟩ :=
    exists_fixed_terminalSequence_with_singleTimePhysicalDissipationGeometry_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  let κ : ℕ → ℝ :=
    fun n =>
      (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)

  have hκPos :
      ∀ n : ℕ,
        0 < κ n := by

    intro n

    dsimp only [κ]

    positivity

  have hKappa :
      Tendsto κ atTop (𝓝 0) := by

    simpa only [κ] using
      hAperture

  have hEscape :
      H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
        hH3 hClass σ :=
    physicalDissipationRadialEscapeSubsequenceOf_of_singleTimeBadConeMass_of_velocityRawFourierL2Cauchy
      hH3
      hClass
      hCauchy
      i
      σ
      hσ
      hSigma
      κ
      hκPos
      hKappa
      hε
      (by
        intro n
        dsimp only [κ]
        exact hLocal n)

  exact
    ⟨
      k,
      hKMono,
      hAperture,
      σ,
      hσ,
      hSigma,
      hLocal,
      hEscape
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
