import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComponentSequences
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Energy.Envelope

/-!
# Synchronized terminal vorticity / gradient blowup sequence

The preceding component-sequence theorem gives a terminal sequence carrying
unbounded actual vorticity amplitude.  The elementary curl-to-gradient
relation already formalized by

    vorticityEnvelope_two_mul_of_velocityGradientEnvelope

shows that this same time sequence must also carry an unbounded actual first
velocity derivative.

Indeed, if every first derivative at a fixed time were bounded by `M`, then
every vorticity component would be bounded by `2 * M`.  Therefore

    2 * M < max(|ωₓ|, |ωᵧ|, |ω_z|)

forces at least one first derivative to exceed `M`.

Consequently, under hypothetical nonextension there is one sequence `τₙ → T`
such that

    n < max(|ωₓ|, |ωᵧ|, |ω_z|)

and, at the same time `τₙ`,

    n / 2 < |∂_{iₙ} u_{jₙ}|.

Both amplitudes tend to `+∞`.  The spatial points need not coincide.

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise curl-to-gradient contrapositive -/

/--
If the maximum actual vorticity-component amplitude at a spacetime point is
strictly larger than `2 * M`, then at that same time some actual first
velocity derivative exceeds `M` somewhere in space.
-/
theorem exists_velocityGradientComponent_gt_of_vorticityComponentMax_gt_two_mul
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t M : ℝ}
    {x : Point3}
    (hOmega :
      2 * M
        <
      max
        (
          abs
            (
              realVorticityX
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                t x
            )
        )
        (
          max
            (
              abs
                (
                  realVorticityY
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t x
                )
            )
            (
              abs
                (
                  realVorticityZ
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t x
                )
            )
        )) :
    ∃
      i j : PrimeTensor.Axis Depth.three,
      ∃ y : Point3,
        M
          <
        abs
          (
            spatial3.d
              i
              (
                fun z =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t z
                  ).component j
              )
              y
          ) := by

  by_contra hNoGradient

  have hGradient :
      VelocityGradientEnvelope
        u
        (fun _ : ℝ => M)
        t := by

    unfold VelocityGradientEnvelope

    intro i j y

    by_contra hNotLe

    have hGt :
        M
          <
        abs
          (
            spatial3.d
              i
              (
                fun z =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t z
                  ).component j
              )
              y
          ) :=
      lt_of_not_ge
        hNotLe

    exact
      hNoGradient
        ⟨
          i,
          j,
          y,
          hGt
        ⟩

  have hVorticity :
      VorticityEnvelope
        u
        (fun _ : ℝ => 2 * M)
        t := by

    simpa only [] using
      vorticityEnvelope_two_mul_of_velocityGradientEnvelope
        hGradient

  have hAt :=
    hVorticity x

  have hMaxLe :
      max
        (
          abs
            (
              realVorticityX
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                t x
            )
        )
        (
          max
            (
              abs
                (
                  realVorticityY
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t x
                )
            )
            (
              abs
                (
                  realVorticityZ
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t x
                )
            )
        )
        ≤
      2 * M := by

    exact
      max_le
        hAt.1
        (
          max_le
            hAt.2.1
            hAt.2.2
        )

  exact
    (not_lt_of_ge hMaxLe)
      hOmega

/-! ## Synchronized terminal sequence -/

/--
Hypothetical nonextension admits one terminal time sequence carrying both
unbounded actual vorticity amplitude and unbounded actual first-derivative
amplitude.

The vorticity and gradient spatial points may differ, but the times are the
same.
-/
theorem exists_synchronized_vorticityGradient_blowupSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃
      τ : ℕ → ℝ,
      ∃
        y : ℕ → Point3,
        ∃
          i j : ℕ → PrimeTensor.Axis Depth.three,
          ∃ z : ℕ → Point3,
            (
              ∀ n : ℕ,
                τ n ∈ Set.Ioo a T
                  ∧
                τ n ∈
                  Set.Ioo
                    (T - (1 : ℝ) / ((n : ℝ) + 1))
                    T
                  ∧
                (n : ℝ)
                  <
                max
                  (
                    abs
                      (
                        realVorticityX
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (τ n)
                          (y n)
                      )
                  )
                  (
                    max
                      (
                        abs
                          (
                            realVorticityY
                              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                              (τ n)
                              (y n)
                          )
                      )
                      (
                        abs
                          (
                            realVorticityZ
                              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                              (τ n)
                              (y n)
                          )
                      )
                  )
                  ∧
                (n : ℝ) / 2
                  <
                abs
                  (
                    spatial3.d
                      (i n)
                      (
                        fun x =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u (τ n) x
                          ).component (j n)
                      )
                      (z n)
                  )
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  max
                    (
                      abs
                        (
                          realVorticityX
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            (τ n)
                            (y n)
                        )
                    )
                    (
                      max
                        (
                          abs
                            (
                              realVorticityY
                                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                (τ n)
                                (y n)
                            )
                        )
                        (
                          abs
                            (
                              realVorticityZ
                                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                (τ n)
                                (y n)
                            )
                        )
                    )
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  abs
                    (
                      spatial3.d
                        (i n)
                        (
                          fun x =>
                            (
                              PrimeTensor.Bridge.logSpaceTimeVectorField
                                u (τ n) x
                            ).component (j n)
                        )
                        (z n)
                    )
              )
              atTop
              atTop := by

  obtain
    ⟨
      τ,
      y,
      hτ,
      hTauTendsto,
      hOmegaTendsto
    ⟩ :=
    exists_vorticityComponentMax_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hGradientChoice :
      ∀ n : ℕ,
        ∃
          i j : PrimeTensor.Axis Depth.three,
          ∃ z : Point3,
            (n : ℝ) / 2
              <
            abs
              (
                spatial3.d
                  i
                  (
                    fun x =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u (τ n) x
                      ).component j
                  )
                  z
              ) := by

    intro n

    have hOmega :
        2 * ((n : ℝ) / 2)
          <
        max
          (
            abs
              (
                realVorticityX
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  (τ n)
                  (y n)
              )
          )
          (
            max
              (
                abs
                  (
                    realVorticityY
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      (τ n)
                      (y n)
                  )
              )
              (
                abs
                  (
                    realVorticityZ
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      (τ n)
                      (y n)
                  )
              )
          ) := by

      convert
        (hτ n).2.2
        using 1 <;> ring

    exact
      exists_velocityGradientComponent_gt_of_vorticityComponentMax_gt_two_mul
        hOmega

  choose i j z hGradient using
    hGradientChoice

  have hGradientTendsto :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                spatial3.d
                  (i n)
                  (
                    fun x =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u (τ n) x
                      ).component (j n)
                  )
                  (z n)
              )
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        (2 * M)

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    have hCast :
        (N : ℝ) ≤ n := by
      exact_mod_cast hn

    have hNat :
        M < (n : ℝ) / 2 := by
      linarith [hN]

    exact
      le_of_lt
        (
          lt_trans
            hNat
            (hGradient n)
        )

  exact
    ⟨
      τ,
      y,
      i,
      j,
      z,
      (fun n =>
        ⟨
          (hτ n).1,
          (hτ n).2.1,
          (hτ n).2.2,
          hGradient n
        ⟩),
      hTauTendsto,
      hOmegaTendsto,
      hGradientTendsto
    ⟩

/-! ## Neutral package -/

/--
Neutral synchronized terminal formulation.
-/
theorem smoothContinuationExtension_or_synchronized_vorticityGradient_blowupSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃
        τ : ℕ → ℝ,
        ∃
          y : ℕ → Point3,
          ∃
            i j : ℕ → PrimeTensor.Axis Depth.three,
            ∃ z : ℕ → Point3,
              (
                ∀ n : ℕ,
                  τ n ∈ Set.Ioo a T
                    ∧
                  τ n ∈
                    Set.Ioo
                      (T - (1 : ℝ) / ((n : ℝ) + 1))
                      T
                    ∧
                  (n : ℝ)
                    <
                  max
                    (
                      abs
                        (
                          realVorticityX
                            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                            (τ n)
                            (y n)
                        )
                    )
                    (
                      max
                        (
                          abs
                            (
                              realVorticityY
                                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                (τ n)
                                (y n)
                            )
                        )
                        (
                          abs
                            (
                              realVorticityZ
                                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                (τ n)
                                (y n)
                            )
                        )
                    )
                    ∧
                  (n : ℝ) / 2
                    <
                  abs
                    (
                      spatial3.d
                        (i n)
                        (
                          fun x =>
                            (
                              PrimeTensor.Bridge.logSpaceTimeVectorField
                                u (τ n) x
                            ).component (j n)
                        )
                        (z n)
                    )
              )
                ∧
              Tendsto τ atTop (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    max
                      (
                        abs
                          (
                            realVorticityX
                              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                              (τ n)
                              (y n)
                          )
                      )
                      (
                        max
                          (
                            abs
                              (
                                realVorticityY
                                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                  (τ n)
                                  (y n)
                              )
                          )
                          (
                            abs
                              (
                                realVorticityZ
                                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                  (τ n)
                                  (y n)
                              )
                          )
                      )
                )
                atTop
                atTop
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    abs
                      (
                        spatial3.d
                          (i n)
                          (
                            fun x =>
                              (
                                PrimeTensor.Bridge.logSpaceTimeVectorField
                                  u (τ n) x
                              ).component (j n)
                          )
                          (z n)
                      )
                )
                atTop
                atTop
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_synchronized_vorticityGradient_blowupSequence_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
