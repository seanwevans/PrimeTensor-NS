import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.VorticityGradientSynchronizedSequence

/-!
# Same-point terminal vorticity / gradient blowup sequence

The synchronized terminal sequence already forces vorticity and a first
velocity derivative to diverge at the same times.  The spatial witnesses can
be synchronized as well.

At a fixed spacetime point, the three vorticity components are the differences

    ωₓ = ∂y u_z - ∂z u_y,
    ωᵧ = ∂z u_x - ∂x u_z,
    ω_z = ∂x u_y - ∂y u_x.

Hence if every first derivative at that point has magnitude at most `M`, then
every vorticity component has magnitude at most `2 * M`.

Contrapositively,

    2 * M < max(|ωₓ|, |ωᵧ|, |ω_z|)

forces some first velocity derivative at the very same point to exceed `M`.

Applying this to the terminal vorticity sequence yields one sequence of
spacetime points `(τₙ, yₙ)` for which both the actual vorticity amplitude and
an actual first velocity derivative diverge.

This is still only a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Same-point curl-to-gradient contrapositive -/

/--
Large vorticity at one spacetime point forces a large first velocity derivative
at that same spacetime point.
-/
theorem exists_velocityGradientComponentAtPoint_gt_of_vorticityComponentMax_gt_two_mul
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
        M
          <
        abs
          (
            spatial3.d
              i
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component j
              )
              x
          ) := by

  by_contra hNoGradient

  have hBound :
      ∀
        i j : PrimeTensor.Axis Depth.three,
          abs
            (
              spatial3.d
                i
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component j
                )
                x
            )
            ≤
          M := by

    intro i j

    by_contra hNotLe

    have hGt :
        M
          <
        abs
          (
            spatial3.d
              i
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component j
              )
              x
          ) :=
      lt_of_not_ge
        hNotLe

    exact
      hNoGradient
        ⟨
          i,
          j,
          hGt
        ⟩

  have hyz :=
    hBound yAxis zAxis

  have hzy :=
    hBound zAxis yAxis

  have hzx :=
    hBound zAxis xAxis

  have hxz :=
    hBound xAxis zAxis

  have hxy :=
    hBound xAxis yAxis

  have hyx :=
    hBound yAxis xAxis

  have hX :
      abs
        (
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      2 * M := by

    unfold realVorticityX

    calc
      abs
          (
            spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
                x
              -
            spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
                x
          )
          ≤
        abs
            (
              spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
                x
            )
          +
        abs
            (
              spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
                x
            ) :=
        abs_sub _ _

      _ ≤
        M + M :=
        add_le_add hyz hzy

      _ =
        2 * M := by
        ring

  have hY :
      abs
        (
          realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      2 * M := by

    unfold realVorticityY

    calc
      abs
          (
            spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
              -
            spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
                x
          )
          ≤
        abs
            (
              spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
            )
          +
        abs
            (
              spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
                x
            ) :=
        abs_sub _ _

      _ ≤
        M + M :=
        add_le_add hzx hxz

      _ =
        2 * M := by
        ring

  have hZ :
      abs
        (
          realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      2 * M := by

    unfold realVorticityZ

    calc
      abs
          (
            spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
                x
              -
            spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
          )
          ≤
        abs
            (
              spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
                x
            )
          +
        abs
            (
              spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
            ) :=
        abs_sub _ _

      _ ≤
        M + M :=
        add_le_add hxy hyx

      _ =
        2 * M := by
        ring

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
        hX
        (
          max_le
            hY
            hZ
        )

  exact
    (not_lt_of_ge hMaxLe)
      hOmega

/-! ## Same-point terminal sequence -/

/--
Under hypothetical nonextension, one terminal sequence of spacetime points
carries both diverging actual vorticity amplitude and diverging actual
first-velocity-derivative amplitude.
-/
theorem exists_samePoint_vorticityGradient_blowupSequence_of_noH3PathExtension
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
                    (y n)
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
                      (y n)
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
                  (y n)
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
      exists_velocityGradientComponentAtPoint_gt_of_vorticityComponentMax_gt_two_mul
        hOmega

  choose i j hGradient using
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
                  (y n)
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
Neutral same-point terminal formulation.
-/
theorem smoothContinuationExtension_or_samePoint_vorticityGradient_blowupSequence
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
                      (y n)
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
                        (y n)
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
          exists_samePoint_vorticityGradient_blowupSequence_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
