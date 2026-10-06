import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation.Physical.Geometry
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Concentration.Compactness.Dichotomy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Bad.Cone.Volume.Vanishing

/-!
# Synchronize concentration--compactness with the final physical witness

The final resolved-PDE witness now contains a single-time sequence `σ n -> T`
with fixed positive physical H³ dissipation mass in

    badCone(i, κ_n) \ {|ξ| < 1},

where `κ_n -> 0`.

This file performs concentration--compactness directly on that exact sequence.

At stage `n`, reindex far enough along `σ` that the bounded part of the bad
cone inside radius `n+1` has Fourier volume below `1/(n+1)`.  Split the
already-positive localized dissipation mass at that radius.  One of the two
pieces carries a fixed fraction of the mass:

* the outer piece lies beyond radius `n+1`; or
* the bounded piece has volume below `1/(n+1)`.

A binary subsequence extraction freezes one alternative.  Thus radial escape
or small-volume concentration occurs on a subsequence of the canonical
single-time physical dissipation witness itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFinalWitnessCompactness
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFinalWitnessCompactness :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 2400000

/--
Radial escape realized on a subsequence of a prescribed terminal time
sequence.
-/
def H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ m : ℕ → ℕ,
      Tendsto m atTop atTop
        ∧
      ∃ S : ℕ → Set H3FourierPoint3,
        (
          ∀ n : ℕ,
            ∃ ht : σ (m n) ∈ Set.Ioo a T,
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
                  hH3 hClass (σ (m n)) ht (S n)
        )
          ∧
        Tendsto
          (fun n : ℕ => σ (m n))
          atTop
          (𝓝 T)

/--
Small-volume concentration realized on a subsequence of a prescribed terminal
time sequence.
-/
def H3TerminalPhysicalDissipationSmallVolumeConcentrationSubsequenceOf
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (σ : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ m : ℕ → ℕ,
      Tendsto m atTop atTop
        ∧
      ∃ S : ℕ → Set H3FourierPoint3,
        (
          ∀ n : ℕ,
            ∃ ht : σ (m n) ∈ Set.Ioo a T,
              dist (σ (m n)) T
                  <
                (1 : ℝ) / ((n : ℝ) + 1)
                ∧
              MeasurableSet (S n)
                ∧
              volume (S n)
                  <
                ENNReal.ofReal
                  ((1 : ℝ) / ((n : ℝ) + 1))
                ∧
              δ
                  ≤
                h3TerminalPhysicalDissipationSetMassAt
                  hH3 hClass (σ (m n)) ht (S n)
        )
          ∧
        Tendsto
          (fun n : ℕ => σ (m n))
          atTop
          (𝓝 T)

private theorem exists_strictMono_subsequence_all_left_or_all_right_finalCompactness
    (P Q : ℕ → Prop)
    (hPQ : ∀ n : ℕ, P n ∨ Q n) :
    (
      ∃ s : ℕ → ℕ,
        StrictMono s
          ∧
        ∀ n : ℕ, P (s n)
    )
      ∨
    (
      ∃ s : ℕ → ℕ,
        StrictMono s
          ∧
        ∀ n : ℕ, Q (s n)
    ) := by

  classical

  by_cases hP :
      ∀ N : ℕ,
        ∃ n > N,
          P n

  · exact
      Or.inl
        (Nat.exists_strictMono_subsequence hP)

  · push Not at hP

    obtain ⟨N, hN⟩ :=
      hP

    let s : ℕ → ℕ :=
      fun n => N + n + 1

    have hSMono :
        StrictMono s := by

      intro x y hxy

      dsimp only [s]

      omega

    refine
      Or.inr
        ⟨
          s,
          hSMono,
          ?_
        ⟩

    intro n

    have hNS :
        N < s n := by

      dsimp only [s]

      omega

    exact
      (hPQ (s n)).resolve_left
        (hN (s n) hNS)

private theorem id_le_of_strictMono_finalCompactness
    {s : ℕ → ℕ}
    (hs : StrictMono s) :
    ∀ n : ℕ, n ≤ s n := by

  intro n

  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      exact
        Nat.succ_le_of_lt
          (
            lt_of_le_of_lt
              ih
              (hs (Nat.lt_succ_self n))
          )

/--
Direct same-witness concentration--compactness.

A positive single-time dissipation mass in shrinking equatorial bad cones
forces, on a subsequence of the prescribed `σ`, either radial escape or
small-volume concentration.
-/
theorem physicalDissipationRadialEscape_or_smallVolumeConcentration_subsequence_of_singleTimeBadConeMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (σ : ℕ → ℝ)
    (hσ :
      ∀ n : ℕ,
        σ n ∈ Set.Ioo a T)
    (hSigma :
      Tendsto σ atTop (𝓝 T))
    (κ : ℕ → ℝ)
    (hκPos :
      ∀ n : ℕ, 0 < κ n)
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
        hH3 hClass σ
      ∨
    H3TerminalPhysicalDissipationSmallVolumeConcentrationSubsequenceOf
        hH3 hClass σ := by

  classical

  let δ : ℝ :=
    ε ^ 2 / 2048

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

      by_contra hNot

      have hMLe :
          M ≤ 0 :=
        le_of_not_gt
          hNot

      have hMZero :
          M = 0 :=
        le_antisymm
          hMLe
          hMNonneg

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
          volume
              (
                (
                  h3TerminalLongitudinalAngularBadCone
                      i
                      (κ d)
                    \
                  h3TerminalRadialFrequencyBelow 1
                )
                  ∩
                h3TerminalRadialFrequencyBelow
                  ((n : ℝ) + 1)
              )
            <
          ENNReal.ofReal
            ((1 : ℝ) / ((n : ℝ) + 1)) := by

    intro n

    let R : ℝ :=
      (n : ℝ) + 1

    let α : ℝ≥0∞ :=
      ENNReal.ofReal
        ((1 : ℝ) / ((n : ℝ) + 1))

    have hR :
        0 < R := by
      dsimp only [R]
      positivity

    have hScale :
        0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      positivity

    have hα :
        0 < α := by
      dsimp only [α]
      exact
        ENNReal.ofReal_pos.2
          hScale

    obtain
      ⟨κ₀, hκ₀, hConeSmall⟩ :=
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
      ⟨Nσ, hNear⟩ :=
      hSigmaMetric
        ((1 : ℝ) / ((n : ℝ) + 1))
        hScale

    obtain
      ⟨d, hnd, hNσd, hκSmall⟩ :=
      (
        (eventually_ge_atTop n).and
          (
            (eventually_ge_atTop Nσ).and
              hKappaSmall
          )
      ).exists

    have hDist :
        dist (σ d) T
          <
        (1 : ℝ) / ((n : ℝ) + 1) :=
      hNear
        d
        hNσd

    have hVolume :
        volume
            (
              (
                h3TerminalLongitudinalAngularBadCone
                    i
                    (κ d)
                  \
                h3TerminalRadialFrequencyBelow 1
              )
                ∩
              h3TerminalRadialFrequencyBelow
                ((n : ℝ) + 1)
            )
          <
        ENNReal.ofReal
          ((1 : ℝ) / ((n : ℝ) + 1)) := by

      dsimp only [R, α] at hConeSmall

      exact
        hConeSmall
          (κ d)
          (hκPos d)
          hκSmall

    exact
      ⟨
        d,
        hnd,
        hDist,
        hVolume
      ⟩

  choose m hnm hNear hVolume using hChoice

  have hmTop :
      Tendsto m atTop atTop := by

    refine
      tendsto_atTop.2 ?_

    intro N

    filter_upwards [eventually_ge_atTop N] with n hn

    exact
      hn.trans
        (hnm n)

  let P : ℕ → Prop :=
    fun n =>
      δ
        <
      h3TerminalPhysicalDissipationSetMassAt
        hH3
        hClass
        (σ (m n))
        (hσ (m n))
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

  let Q : ℕ → Prop :=
    fun n =>
      δ
        <
      h3TerminalPhysicalDissipationSetMassAt
        hH3
        hClass
        (σ (m n))
        (hσ (m n))
        (
          (
            h3TerminalLongitudinalAngularBadCone
                i
                (κ (m n))
              \
            h3TerminalRadialFrequencyBelow 1
          )
            ∩
          h3TerminalRadialFrequencyBelow
            ((n : ℝ) + 1)
        )

  have hPQ :
      ∀ n : ℕ,
        P n ∨ Q n := by

    intro n

    let htAbs :
        σ (m n) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans hClass.terminal_start.1
          (hσ (m n)).1,
        (hσ (m n)).2
      ⟩

    let f : H3FourierPoint3 → ℝ :=
      fun ξ =>
        h3TerminalSpectralDissipationSingleDensity
          (h3TerminalVelocitySpectralStateAt
            hH3
            (σ (m n))
            htAbs)
          ξ

    let S : Set H3FourierPoint3 :=
      h3TerminalLongitudinalAngularBadCone
          i
          (κ (m n))
        \
      h3TerminalRadialFrequencyBelow 1

    let B : Set H3FourierPoint3 :=
      h3TerminalRadialFrequencyBelow
        ((n : ℝ) + 1)

    have hFInt :
        Integrable f volume := by

      dsimp only [f, htAbs]

      simpa only using
        (
          h3TerminalSpectralDissipationSingleDensity_integrable
            hH3
            hClass
            (hσ (m n))
        )

    have hBMeas :
        MeasurableSet B := by

      dsimp only [B]

      exact
        measurableSet_h3TerminalRadialFrequencyBelow
          ((n : ℝ) + 1)

    have hSplit :
        (∫ ξ in S, f ξ ∂volume)
          =
        (∫ ξ in S ∩ B, f ξ ∂volume)
          +
        (∫ ξ in S \ B, f ξ ∂volume) := by

      have hSplit' :=
        integral_inter_add_sdiff₀
          (μ := volume)
          (s := S)
          hBMeas.nullMeasurableSet
          hFInt.integrableOn

      exact
        hSplit'.symm

    have hTotal :
        2 * δ
          <
        (∫ ξ in S, f ξ ∂volume) := by

      have hRaw :=
        hLocalReal
          (m n)

      have hRaw' :
          ε ^ 2 / 1024
            <
          (∫ ξ in S, f ξ ∂volume) := by

        simpa only [
          S,
          f,
          htAbs,
          h3TerminalPhysicalDissipationBadConeHighRadialRealMass
        ] using
          hRaw

      have hConst :
          2 * δ = ε ^ 2 / 1024 := by

        dsimp only [δ]

        ring

      rw [hConst]

      exact hRaw'

    by_cases hMiddle :
        δ
          <
        (∫ ξ in S ∩ B, f ξ ∂volume)

    · exact
        Or.inr
          (by
            change
              δ
                <
              (∫ ξ in S ∩ B, f ξ ∂volume)
            exact hMiddle)

    · have hMiddleLe :
          (∫ ξ in S ∩ B, f ξ ∂volume)
            ≤
          δ :=
        le_of_not_gt
          hMiddle

      have hTail :
          δ
            <
          (∫ ξ in S \ B, f ξ ∂volume) := by

        rw [hSplit] at hTotal

        linarith

      exact
        Or.inl
          (by
            change
              δ
                <
              (∫ ξ in S \ B, f ξ ∂volume)
            exact hTail)

  have hFrozen :=
    exists_strictMono_subsequence_all_left_or_all_right_finalCompactness
      P
      Q
      hPQ

  rcases hFrozen with hRadial | hSmall

  · obtain
      ⟨s, hSMono, hSP⟩ :=
      hRadial

    have hSTop :
        Tendsto s atTop atTop :=
      hSMono.tendsto_atTop

    have hSGe :
        ∀ n : ℕ,
          n ≤ s n :=
      id_le_of_strictMono_finalCompactness
        hSMono

    let r : ℕ → ℕ :=
      fun n =>
        m (s n)

    have hrTop :
        Tendsto r atTop atTop := by

      simpa only [r, Function.comp_def] using
        hmTop.comp hSTop

    have hSigmaR :
        Tendsto
          (fun n : ℕ => σ (r n))
          atTop
          (𝓝 T) := by

      exact
        hSigma.comp
          hrTop

    let Srad : ℕ → Set H3FourierPoint3 :=
      fun n =>
        (
          (
            h3TerminalLongitudinalAngularBadCone
                i
                (κ (m (s n)))
              \
            h3TerminalRadialFrequencyBelow 1
          )
            \
          h3TerminalRadialFrequencyBelow
            (((s n : ℕ) : ℝ) + 1)
        )

    have hRadData :
        ∀ n : ℕ,
          ∃ ht :
            σ (r n) ∈ Set.Ioo a T,
            dist (σ (r n)) T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
              ∧
            MeasurableSet (Srad n)
              ∧
            Srad n
                ⊆
              (h3TerminalRadialFrequencyBelow
                  ((n : ℝ) + 1))ᶜ
              ∧
            δ
                ≤
              h3TerminalPhysicalDissipationSetMassAt
                hH3 hClass (σ (r n)) ht (Srad n) := by

      intro n

      have hNS :
          (n : ℝ) ≤ (s n : ℝ) := by
        exact_mod_cast
          (hSGe n)

      have hScaleLe :
          (1 : ℝ) / (((s n : ℕ) : ℝ) + 1)
            ≤
          (1 : ℝ) / ((n : ℝ) + 1) := by

        exact
          one_div_le_one_div_of_le
            (by positivity)
            (by linarith)

      have hDist :
          dist (σ (r n)) T
            <
          (1 : ℝ) / ((n : ℝ) + 1) := by

        dsimp only [r]

        exact
          (hNear (s n)).trans_le
            hScaleLe

      have hMeas :
          MeasurableSet (Srad n) := by

        dsimp only [Srad]

        exact
          (
            (
              measurableSet_h3TerminalLongitudinalAngularBadCone
                i
                (κ (m (s n)))
            ).diff
              (
                measurableSet_h3TerminalRadialFrequencyBelow
                  1
              )
          ).diff
            (
              measurableSet_h3TerminalRadialFrequencyBelow
                (((s n : ℕ) : ℝ) + 1)
            )

      have hSubset :
          Srad n
            ⊆
          (h3TerminalRadialFrequencyBelow
              ((n : ℝ) + 1))ᶜ := by

        intro ξ hξ

        have hNotOuter :
            ξ
              ∉
            h3TerminalRadialFrequencyBelow
              (((s n : ℕ) : ℝ) + 1) := by

          exact
            hξ.2

        intro hSmall

        apply hNotOuter

        change
          h3FourierGradientMagnitude ξ
            <
          ((s n : ℕ) : ℝ) + 1

        change
          h3FourierGradientMagnitude ξ
            <
          (n : ℝ) + 1
          at hSmall

        linarith

      have hMass :
          δ
            <
          h3TerminalPhysicalDissipationSetMassAt
            hH3
            hClass
            (σ (r n))
            (hσ (r n))
            (Srad n) := by

        dsimp only [r, Srad]

        simpa only [P] using
          hSP n

      exact
        ⟨
          hσ (r n),
          hDist,
          hMeas,
          hSubset,
          hMass.le
        ⟩

    exact
      Or.inl
        ⟨
          δ,
          hδ,
          r,
          hrTop,
          Srad,
          hRadData,
          hSigmaR
        ⟩

  · obtain
      ⟨s, hSMono, hSQ⟩ :=
      hSmall

    have hSTop :
        Tendsto s atTop atTop :=
      hSMono.tendsto_atTop

    have hSGe :
        ∀ n : ℕ,
          n ≤ s n :=
      id_le_of_strictMono_finalCompactness
        hSMono

    let r : ℕ → ℕ :=
      fun n =>
        m (s n)

    have hrTop :
        Tendsto r atTop atTop := by

      simpa only [r, Function.comp_def] using
        hmTop.comp hSTop

    have hSigmaR :
        Tendsto
          (fun n : ℕ => σ (r n))
          atTop
          (𝓝 T) := by

      exact
        hSigma.comp
          hrTop

    let Ssmall : ℕ → Set H3FourierPoint3 :=
      fun n =>
        (
          (
            h3TerminalLongitudinalAngularBadCone
                i
                (κ (m (s n)))
              \
            h3TerminalRadialFrequencyBelow 1
          )
            ∩
          h3TerminalRadialFrequencyBelow
            (((s n : ℕ) : ℝ) + 1)
        )

    have hSmallData :
        ∀ n : ℕ,
          ∃ ht :
            σ (r n) ∈ Set.Ioo a T,
            dist (σ (r n)) T
                <
              (1 : ℝ) / ((n : ℝ) + 1)
              ∧
            MeasurableSet (Ssmall n)
              ∧
            volume (Ssmall n)
                <
              ENNReal.ofReal
                ((1 : ℝ) / ((n : ℝ) + 1))
              ∧
            δ
                ≤
              h3TerminalPhysicalDissipationSetMassAt
                hH3 hClass (σ (r n)) ht (Ssmall n) := by

      intro n

      have hNS :
          (n : ℝ) ≤ (s n : ℝ) := by
        exact_mod_cast
          (hSGe n)

      have hScaleLe :
          (1 : ℝ) / (((s n : ℕ) : ℝ) + 1)
            ≤
          (1 : ℝ) / ((n : ℝ) + 1) := by

        exact
          one_div_le_one_div_of_le
            (by positivity)
            (by linarith)

      have hDist :
          dist (σ (r n)) T
            <
          (1 : ℝ) / ((n : ℝ) + 1) := by

        dsimp only [r]

        exact
          (hNear (s n)).trans_le
            hScaleLe

      have hMeas :
          MeasurableSet (Ssmall n) := by

        dsimp only [Ssmall]

        exact
          (
            (
              measurableSet_h3TerminalLongitudinalAngularBadCone
                i
                (κ (m (s n)))
            ).diff
              (
                measurableSet_h3TerminalRadialFrequencyBelow
                  1
              )
          ).inter
            (
              measurableSet_h3TerminalRadialFrequencyBelow
                (((s n : ℕ) : ℝ) + 1)
            )

      have hVolumeStage :=
        hVolume
          (s n)

      have hVolumeTarget :
          volume (Ssmall n)
            <
          ENNReal.ofReal
            ((1 : ℝ) / ((n : ℝ) + 1)) := by

        have hOfRealLe :
            ENNReal.ofReal
                ((1 : ℝ) / (((s n : ℕ) : ℝ) + 1))
              ≤
            ENNReal.ofReal
                ((1 : ℝ) / ((n : ℝ) + 1)) :=
          ENNReal.ofReal_le_ofReal
            hScaleLe

        change
          volume (Ssmall n)
            <
          ENNReal.ofReal
            ((1 : ℝ) / (((s n : ℕ) : ℝ) + 1))
          at hVolumeStage

        exact
          hVolumeStage.trans_le
            hOfRealLe

      have hMass :
          δ
            <
          h3TerminalPhysicalDissipationSetMassAt
            hH3
            hClass
            (σ (r n))
            (hσ (r n))
            (Ssmall n) := by

        dsimp only [r, Ssmall]

        simpa only [Q] using
          hSQ n

      exact
        ⟨
          hσ (r n),
          hDist,
          hMeas,
          hVolumeTarget,
          hMass.le
        ⟩

    exact
      Or.inr
        ⟨
          δ,
          hδ,
          r,
          hrTop,
          Ssmall,
          hSmallData,
          hSigmaR
        ⟩

/--
Apply the direct same-witness concentration--compactness split to the canonical
single-time physical dissipation witness produced by the resolved-PDE closure.
The inherited selector `k` is exposed explicitly, so the shrinking aperture is
kept exactly as it occurs in the canonical witness.
-/
theorem exists_fixed_terminalSequence_with_physicalDissipationConcentrationCompactnessDichotomy_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
          (
            H3TerminalPhysicalDissipationRadialEscapeSubsequenceOf
                hH3 hClass σ
              ∨
            H3TerminalPhysicalDissipationSmallVolumeConcentrationSubsequenceOf
                hH3 hClass σ
          ) := by

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

  have hDichotomy :=
    physicalDissipationRadialEscape_or_smallVolumeConcentration_subsequence_of_singleTimeBadConeMass
      hH3
      hClass
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
      hDichotomy
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
