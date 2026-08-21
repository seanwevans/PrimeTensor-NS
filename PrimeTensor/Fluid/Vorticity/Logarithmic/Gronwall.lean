import PrimeTensor.Fluid.Vorticity.BKM.Growth.Frontier

/-!
# Closing the logarithmic Grönwall step

This file proves the pure scalar proposition
`LogarithmicGronwallClosesEnergy`.

Starting from

    E'(t) ≤ C (1 + |g(t)|) E(t) (1 + log E(t)),
    E(t) ≥ 1,

set

    W(t) = log (1 + log E(t)).

On the terminal tail, both logarithms are legitimate and

    W'(t)
      = E'(t) / (E(t) (1 + log E(t)))
      ≤ C (1 + |g(t)|).

Mathlib's
`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`
then integrates this variable-coefficient inequality directly.  Because
`g` is integrable on `(a,T)`, the nonnegative coefficient
`C * (1 + |g|)` has a finite integral on `a..T`, giving one bound valid for
every `t ∈ [a,T)`.

Exponentiating twice recovers a uniform bound for `E`.

No Navier--Stokes fact is used in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

/--
The scalar logarithmic Grönwall/Osgood proposition required by the BKM
factorization is true.
-/
theorem logarithmicGronwallClosesEnergy :
    LogarithmicGronwallClosesEnergy := by

  intro
    a T g E C
    haT
    hg
    hC
    hEOne
    hC1
    hGrowth

  let k : ℝ → ℝ :=
    fun s =>
      C * (1 + |g s|)

  let W : ℝ → ℝ :=
    fun s =>
      Real.log
        (
          1 + Real.log (E s)
        )

  have hgInterval :
      IntervalIntegrable
        g
        MeasureTheory.volume
        a T := by
    apply
      (
        intervalIntegrable_iff_integrableOn_Ioo_of_le
          (le_of_lt haT)
      ).2
    exact hg

  have hkInterval :
      IntervalIntegrable
        k
        MeasureTheory.volume
        a T := by

    have hOne :
        IntervalIntegrable
          (fun _ : ℝ => (1 : ℝ))
          MeasureTheory.volume
          a T :=
      intervalIntegrable_const

    have hAbs :
        IntervalIntegrable
          (fun s : ℝ => |g s|)
          MeasureTheory.volume
          a T :=
      hgInterval.abs

    have hSum :
        IntervalIntegrable
          (fun s : ℝ => 1 + |g s|)
          MeasureTheory.volume
          a T :=
      hOne.add hAbs

    simpa only [k] using
      hSum.const_mul C

  have hkNonnegative :
      0 ≤ᵐ[
        MeasureTheory.volume.restrict
          (Set.Ioc a T)
      ] k := by

    filter_upwards [] with s

    dsimp only [k]

    have hOneAbs :
        0 ≤ 1 + |g s| := by
      positivity

    exact
      mul_nonneg
        hC
        hOneAbs

  let K : ℝ :=
    ∫ s : ℝ in a..T, k s

  let B : ℝ :=
    W a + K

  let M : ℝ :=
    Real.exp
      (
        Real.exp B - 1
      )

  refine
    ⟨
      M,
      ?_,
      ?_
    ⟩

  · exact
      le_of_lt
        (Real.exp_pos _)

  · intro t ht

    have hat :
        a ≤ t :=
      ht.1

    have htT :
        t ≤ T :=
      le_of_lt ht.2

    have hIccSubset :
        Set.uIcc a t
          ⊆
        Set.uIcc a T := by

      intro s hs

      rw [
        Set.uIcc_of_le hat
      ] at hs

      rw [
        Set.uIcc_of_le
          (le_of_lt haT)
      ]

      exact
        ⟨
          hs.1,
          hs.2.trans htT
        ⟩

    have hkIntervalAt :
        IntervalIntegrable
          k
          MeasureTheory.volume
          a t :=
      hkInterval.mono_set
        hIccSubset

    have hkIntegrableOnIcc :
        MeasureTheory.IntegrableOn
          k
          (Set.Icc a t)
          MeasureTheory.volume := by

      apply
        (
          intervalIntegrable_iff_integrableOn_Icc_of_le
            hat
        ).1

      exact hkIntervalAt

    have hEC1 :
        ContDiffOn
          ℝ 1 E
          (Set.Icc a t) :=
      hC1
        t
        ht

    have hEOneIcc :
        ∀ s : ℝ,
          s ∈ Set.Icc a t →
            1 ≤ E s := by

      intro s hs

      apply
        hEOne
          s

      exact
        ⟨
          hs.1,
          lt_of_le_of_lt
            hs.2
            ht.2
        ⟩

    have hEPosIcc :
        ∀ s : ℝ,
          s ∈ Set.Icc a t →
            0 < E s := by

      intro s hs

      exact
        lt_of_lt_of_le
          zero_lt_one
          (hEOneIcc s hs)

    have hENeIcc :
        ∀ s : ℝ,
          s ∈ Set.Icc a t →
            E s ≠ 0 := by

      intro s hs

      exact
        ne_of_gt
          (hEPosIcc s hs)

    have hLogEC1 :
        ContDiffOn
          ℝ 1
          (
            fun s : ℝ =>
              Real.log (E s)
          )
          (Set.Icc a t) :=
      hEC1.log
        hENeIcc

    have hYC1 :
        ContDiffOn
          ℝ 1
          (
            fun s : ℝ =>
              1 + Real.log (E s)
          )
          (Set.Icc a t) := by

      exact
        contDiffOn_const.add
          hLogEC1

    have hYPosIcc :
        ∀ s : ℝ,
          s ∈ Set.Icc a t →
            0 < 1 + Real.log (E s) := by

      intro s hs

      have hLogNonnegative :
          0 ≤ Real.log (E s) :=
        Real.log_nonneg
          (hEOneIcc s hs)

      linarith

    have hYNeIcc :
        ∀ s : ℝ,
          s ∈ Set.Icc a t →
            1 + Real.log (E s) ≠ 0 := by

      intro s hs

      exact
        ne_of_gt
          (hYPosIcc s hs)

    have hWC1 :
        ContDiffOn
          ℝ 1 W
          (Set.Icc a t) := by

      dsimp only [W]

      exact
        hYC1.log
          hYNeIcc

    let w' : ℝ → ℝ :=
      fun s =>
        (
          deriv E s / E s
        )
          /
        (
          1 + Real.log (E s)
        )

    have hWDeriv :
        ∀ s : ℝ,
          s ∈ Set.Ioo a t →
            HasDerivWithinAt
              W
              (w' s)
              (Set.Ioi s)
              s := by

      intro s hs

      have hsTail :
          s ∈ Set.Ico a T := by
        exact
          ⟨
            le_of_lt hs.1,
            lt_trans hs.2 ht.2
          ⟩

      have hEsOne :
          1 ≤ E s :=
        hEOne
          s
          hsTail

      have hEsPos :
          0 < E s :=
        lt_of_lt_of_le
          zero_lt_one
          hEsOne

      have hEsNe :
          E s ≠ 0 :=
        ne_of_gt hEsPos

      have hLogEsNonnegative :
          0 ≤ Real.log (E s) :=
        Real.log_nonneg
          hEsOne

      have hYsPos :
          0 < 1 + Real.log (E s) := by
        linarith

      have hYsNe :
          1 + Real.log (E s) ≠ 0 :=
        ne_of_gt hYsPos

      have hIccNhds :
          Set.Icc a t ∈ nhds s :=
        Icc_mem_nhds
          hs.1
          hs.2

      have hEAt :
          ContDiffAt
            ℝ 1 E s :=
        hEC1.contDiffAt
          hIccNhds

      have hEDiff :
          DifferentiableAt
            ℝ E s :=
        hEAt.differentiableAt_one

      have hEHas :
          HasDerivAt
            E
            (deriv E s)
            s :=
        hEDiff.hasDerivAt

      have hLogEHas :
          HasDerivAt
            (
              fun r : ℝ =>
                Real.log (E r)
            )
            (
              deriv E s / E s
            )
            s :=
        hEHas.log
          hEsNe

      have hYHas :
          HasDerivAt
            (
              fun r : ℝ =>
                1 + Real.log (E r)
            )
            (
              deriv E s / E s
            )
            s :=
        hLogEHas.const_add
          1

      have hWHas :
          HasDerivAt
            W
            (
              (
                deriv E s / E s
              )
                /
              (
                1 + Real.log (E s)
              )
            )
            s := by

        dsimp only [W]

        exact
          hYHas.log
            hYsNe

      dsimp only [w']

      exact
        hWHas.hasDerivWithinAt

    have hwLe :
        ∀ s : ℝ,
          s ∈ Set.Ioo a t →
            w' s ≤ k s := by

      intro s hs

      have hsGrowth :
          s ∈ Set.Ioo a T :=
        ⟨
          hs.1,
          lt_trans hs.2 ht.2
        ⟩

      have hsTail :
          s ∈ Set.Ico a T :=
        ⟨
          le_of_lt hs.1,
          hsGrowth.2
        ⟩

      have hEsOne :
          1 ≤ E s :=
        hEOne
          s
          hsTail

      have hEsPos :
          0 < E s :=
        lt_of_lt_of_le
          zero_lt_one
          hEsOne

      have hLogEsNonnegative :
          0 ≤ Real.log (E s) :=
        Real.log_nonneg
          hEsOne

      have hYsPos :
          0 < 1 + Real.log (E s) := by
        linarith

      have hDenPos :
          0 <
            E s
              *
            (
              1 + Real.log (E s)
            ) :=
        mul_pos
          hEsPos
          hYsPos

      have hGrowthAt :=
        hGrowth
          s
          hsGrowth

      have hDiv :
          deriv E s
              /
            (
              E s
                *
              (
                1 + Real.log (E s)
              )
            )
            ≤
          C * (1 + |g s|) := by

        apply
          (
            div_le_iff₀
              hDenPos
          ).2

        calc
          deriv E s
              ≤
            C
              * (1 + |g s|)
              * E s
              * (1 + Real.log (E s)) :=
            hGrowthAt

          _ =
            (
              C * (1 + |g s|)
            )
              *
            (
              E s
                *
              (
                1 + Real.log (E s)
              )
            ) := by
              ring

      dsimp only [w', k]

      simpa only [div_div] using
        hDiv

    have hWSubIntegral :
        W t - W a
          ≤
        ∫ s : ℝ in a..t, k s := by

      apply
        intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
          hat
          hWC1.continuousOn
          hWDeriv
          hkIntegrableOnIcc
          hwLe

    have hIntegralMono :
        (∫ s : ℝ in a..t, k s)
          ≤
        ∫ s : ℝ in a..T, k s := by

      exact
        intervalIntegral.integral_mono_interval
          le_rfl
          hat
          htT
          hkNonnegative
          hkInterval

    have hWt :
        W t ≤ B := by

      dsimp only [B, K]

      linarith

    have hEtOne :
        1 ≤ E t :=
      hEOne
        t
        ht

    have hEtPos :
        0 < E t :=
      lt_of_lt_of_le
        zero_lt_one
        hEtOne

    have hLogEtNonnegative :
        0 ≤ Real.log (E t) :=
      Real.log_nonneg
        hEtOne

    have hYtPos :
        0 < 1 + Real.log (E t) := by
      linarith

    have hYtLe :
        1 + Real.log (E t)
          ≤
        Real.exp B := by

      have hExp :=
        Real.exp_le_exp.mpr
          hWt

      dsimp only [W] at hExp

      simpa only [
        Real.exp_log
          hYtPos
      ] using
        hExp

    have hLogEtLe :
        Real.log (E t)
          ≤
        Real.exp B - 1 := by
      linarith

    have hEtLe :
        E t
          ≤
        Real.exp
          (
            Real.exp B - 1
          ) := by

      have hExp :=
        Real.exp_le_exp.mpr
          hLogEtLe

      simpa only [
        Real.exp_log
          hEtPos
      ] using
        hExp

    dsimp only [M]

    exact hEtLe

/--
The BKM factorization no longer needs an abstract scalar assumption.
-/
theorem vorticityL1LinfProducesH3Control_of_BKMGrowth_closedScalar
    (
      hGrowth :
        VorticityEnvelopeProducesBKMH3Growth
    ) :
    VorticityL1LinfProducesH3Control :=
  PrimeTensor.Bridge.Euclidean.vorticityL1LinfProducesH3Control_of_BKMGrowth
    hGrowth
    logarithmicGronwallClosesEnergy

/--
Consequently, after the scalar step is discharged, the seeded continuation
criterion depends only on the PDE/harmonic-analysis BKM growth estimate and the
standard tail-H³ restart/extension theorem.
-/
theorem seededVorticityL1LinfProducesExtension_of_BKMGrowth_closedScalar
    (
      hGrowth :
        VorticityEnvelopeProducesBKMH3Growth
    )
    (
      hH3ToExtension :
        H3ControlProducesExtension
    ) :
    SeededVorticityL1LinfProducesExtension :=
  PrimeTensor.Bridge.Euclidean.seededVorticityL1LinfProducesExtension_of_BKMGrowth
    hGrowth
    logarithmicGronwallClosesEnergy
    hH3ToExtension

end Euclidean
end Bridge
end PrimeTensor
