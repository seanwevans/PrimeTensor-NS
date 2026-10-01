import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Same.Point.Vorticity.Gradient
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fixed gradient channel on the positive-growth same-point cascade

The preceding theorem gives one positive-growth terminal spacetime sequence

    (σ_n, y_n)

together with moving derivative axes `(i_n,j_n)` such that the same sequence
carries simultaneous divergence of

    E(σ_n),
    D(σ_n)/E(σ_n),
    (-T_H3(σ_n))/E(σ_n),
    Λ₃(σ_n),
    actual vorticity amplitude at (σ_n,y_n),
    |∂_{i_n} u_{j_n}(σ_n,y_n)|.

There are only finitely many derivative-axis pairs.  Hence one pair occurs
frequently.  `Filter.frequently_exists` isolates such a pair, and
`extraction_of_frequently_atTop` produces a strictly increasing subsequence
`φ : ℕ → ℕ` on which

    i_{φ(n)} = i_*,
    j_{φ(n)} = j_*.

All previously established `atTop` limits survive composition with the
strictly increasing subsequence.

Moreover `n ≤ φ(n)`, so the quantitative terminal localization and
positive-growth indexing survive in their standard form:

    σ_{φ(n)} ∈ (T - 1/(n+1), T),
    n < E'(σ_{φ(n)}).

Thus hypothetical nonextension forces one fixed physical first-derivative
entry to diverge at the same spatial points as actual vorticity, on a single
positive-growth sequence that also carries the full H³ scalar and frequency
cascade.

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Under hypothetical nonextension, one fixed first velocity derivative component
diverges at the same selected spatial points as actual vorticity on a
positive-growth subsequence carrying the full scalar/frequency cascade.
-/
theorem exists_terminal_positiveGrowth_fullCascade_samePoint_actualVorticity_fixedGradient_tendsto_atTop_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T) :
    ∃
      i₀ j₀ : PrimeTensor.Axis Depth.three,
      ∃
        τ : ℕ → ℝ,
        ∃
          y : ℕ → Point3,
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
              deriv (velocityH3EnergyAt u) (τ n)
          )
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3EnergyAt u (τ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3DissipationAt u (τ n)
                  /
                velocityH3EnergyAt u (τ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                (
                  - velocityH3TransportDerivativeAt u (τ n)
                )
                  /
                velocityH3EnergyAt u (τ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TopCharacteristicFrequencyAt
                  u
                  (τ n)
            )
            atTop
            atTop
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
                      i₀
                      (
                        fun x =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u (τ n) x
                          ).component j₀
                      )
                      (y n)
                  )
            )
            atTop
            atTop := by

  obtain
    ⟨
      σ,
      x,
      i,
      j,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto,
      hFrequencyTendsto,
      hOmegaTendsto,
      hGradientTendsto
    ⟩ :=
    exists_terminal_positiveGrowth_fullCascade_samePoint_actualVorticityGradient_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  let p :
      ℕ →
        (
          PrimeTensor.Axis Depth.three
            ×
          PrimeTensor.Axis Depth.three
        ) :=
    fun n =>
      (i n, j n)

  have hFrequentlySomePair :
      ∃ᶠ n : ℕ in atTop,
        ∃
          q :
            (
              PrimeTensor.Axis Depth.three
                ×
              PrimeTensor.Axis Depth.three
            ),
          p n = q :=
    Frequently.of_forall
      (
        fun n =>
          ⟨
            p n,
            rfl
          ⟩
      )

  obtain
    ⟨
      q,
      hPairFrequently
    ⟩ :=
    (
      Filter.frequently_exists
    ).1
      hFrequentlySomePair

  obtain
    ⟨
      φ,
      hPhiMono,
      hPair
    ⟩ :=
    extraction_of_frequently_atTop
      hPairFrequently

  have hPhiTendsto :
      Tendsto φ atTop atTop :=
    hPhiMono.tendsto_atTop

  let τ : ℕ → ℝ :=
    fun n =>
      σ (φ n)

  let y : ℕ → Point3 :=
    fun n =>
      x (φ n)

  have hFixedDerivativeAxis :
      ∀ n : ℕ,
        i (φ n) = q.1 := by

    intro n

    have h :=
      congrArg Prod.fst
        (hPair n)

    simpa only [p] using
      h

  have hFixedComponentAxis :
      ∀ n : ℕ,
        j (φ n) = q.2 := by

    intro n

    have h :=
      congrArg Prod.snd
        (hPair n)

    simpa only [p] using
      h

  have hTauData :
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
        deriv (velocityH3EnergyAt u) (τ n) := by

    intro n

    have hOld :=
      hσ (φ n)

    have hIndexLeNat :
        n ≤ φ n :=
      hPhiMono.le_apply

    have hIndexLe :
        (n : ℝ) ≤ (φ n : ℝ) := by
      exact_mod_cast
        hIndexLeNat

    have hDenPos :
        0 < (n : ℝ) + 1 := by
      positivity

    have hDenLe :
        (n : ℝ) + 1
          ≤
        (φ n : ℝ) + 1 := by
      linarith

    have hInv :
        (1 : ℝ) / ((φ n : ℝ) + 1)
          ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le
        hDenPos
        hDenLe

    have hNear :
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T := by

      constructor

      · dsimp only [τ]

        have hOldLower :=
          hOld.2.1.1

        linarith

      · dsimp only [τ]

        exact
          hOld.2.1.2

    have hDerivative :
        (n : ℝ)
          <
        deriv (velocityH3EnergyAt u) (τ n) := by

      dsimp only [τ]

      exact
        lt_of_le_of_lt
          hIndexLe
          hOld.2.2

    exact
      ⟨
        by
          dsimp only [τ]
          exact hOld.1,
        hNear,
        hDerivative
      ⟩

  have hTauTendsto :
      Tendsto τ atTop (𝓝 T) := by

    dsimp only [τ]

    exact
      hSigmaTendsto.comp
        hPhiTendsto

  have hEnergySubsequence :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop := by

    dsimp only [τ]

    change
      Tendsto
        (
          (fun n : ℕ =>
            velocityH3EnergyAt u (σ n))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hEnergyTendsto.comp
        hPhiTendsto

  have hDissSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3DissipationAt u (τ n)
              /
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop := by

    dsimp only [τ]

    change
      Tendsto
        (
          (fun n : ℕ =>
            velocityH3DissipationAt u (σ n)
              /
            velocityH3EnergyAt u (σ n))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hDissRatioTendsto.comp
        hPhiTendsto

  have hTransportSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (τ n)
            )
              /
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop := by

    dsimp only [τ]

    change
      Tendsto
        (
          (fun n : ℕ =>
            (
              - velocityH3TransportDerivativeAt u (σ n)
            )
              /
            velocityH3EnergyAt u (σ n))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hTransportRatioTendsto.comp
        hPhiTendsto

  have hFrequencySubsequence :
      Tendsto
        (
          fun n : ℕ =>
            h3TopCharacteristicFrequencyAt
              u
              (τ n)
        )
        atTop
        atTop := by

    dsimp only [τ]

    change
      Tendsto
        (
          (fun n : ℕ =>
            h3TopCharacteristicFrequencyAt
              u
              (σ n))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hFrequencyTendsto.comp
        hPhiTendsto

  have hOmegaSubsequence :
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
        atTop := by

    dsimp only [τ, y]

    change
      Tendsto
        (
          (fun n : ℕ =>
            max
              (
                abs
                  (
                    realVorticityX
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      (σ n)
                      (x n)
                  )
              )
              (
                max
                  (
                    abs
                      (
                        realVorticityY
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (σ n)
                          (x n)
                      )
                  )
                  (
                    abs
                      (
                        realVorticityZ
                          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                          (σ n)
                          (x n)
                      )
                  )
              ))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hOmegaTendsto.comp
        hPhiTendsto

  have hMovingGradientSubsequence :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                spatial3.d
                  (i (φ n))
                  (
                    fun z =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u (σ (φ n)) z
                      ).component (j (φ n))
                  )
                  (x (φ n))
              )
        )
        atTop
        atTop := by

    change
      Tendsto
        (
          (fun n : ℕ =>
            abs
              (
                spatial3.d
                  (i n)
                  (
                    fun z =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u (σ n) z
                      ).component (j n)
                  )
                  (x n)
              ))
              ∘
            φ
        )
        atTop
        atTop

    exact
      hGradientTendsto.comp
        hPhiTendsto

  have hFixedGradientFunction :
      (
        fun n : ℕ =>
          abs
            (
              spatial3.d
                q.1
                (
                  fun z =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u (τ n) z
                    ).component q.2
                )
                (y n)
            )
      )
        =
      (
        fun n : ℕ =>
          abs
            (
              spatial3.d
                (i (φ n))
                (
                  fun z =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u (σ (φ n)) z
                    ).component (j (φ n))
                )
                (x (φ n))
            )
      ) := by

    funext n

    have hi :=
      hFixedDerivativeAxis n

    have hj :=
      hFixedComponentAxis n

    dsimp only [τ, y]

    rw [
      ← hi,
      ← hj
    ]

  have hFixedGradientTendsto :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                spatial3.d
                  q.1
                  (
                    fun z =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u (τ n) z
                      ).component q.2
                  )
                  (y n)
              )
        )
        atTop
        atTop := by

    rw [
      hFixedGradientFunction
    ]

    exact
      hMovingGradientSubsequence

  exact
    ⟨
      q.1,
      q.2,
      τ,
      y,
      hTauData,
      hTauTendsto,
      hEnergySubsequence,
      hDissSubsequence,
      hTransportSubsequence,
      hFrequencySubsequence,
      hOmegaSubsequence,
      hFixedGradientTendsto
    ⟩

/--
Neutral fixed-gradient-channel formulation on the positive-growth same-point
cascade.
-/
theorem smoothContinuationExtension_or_terminal_positiveGrowth_fullCascade_samePoint_actualVorticity_fixedGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hb :
      b ∈ Set.Ioo a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T
    )
      ∨
    (
      ∃
        i₀ j₀ : PrimeTensor.Axis Depth.three,
        ∃
          τ : ℕ → ℝ,
          ∃
            y : ℕ → Point3,
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
                deriv (velocityH3EnergyAt u) (τ n)
            )
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3EnergyAt u (τ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3DissipationAt u (τ n)
                    /
                  velocityH3EnergyAt u (τ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  (
                    - velocityH3TransportDerivativeAt u (τ n)
                  )
                    /
                  velocityH3EnergyAt u (τ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TopCharacteristicFrequencyAt
                    u
                    (τ n)
              )
              atTop
              atTop
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
                        i₀
                        (
                          fun x =>
                            (
                              PrimeTensor.Bridge.logSpaceTimeVectorField
                                u (τ n) x
                            ).component j₀
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
        SmoothContinuationExtension
          u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_terminal_positiveGrowth_fullCascade_samePoint_actualVorticity_fixedGradient_tendsto_atTop_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

end

end Euclidean
end Bridge
end PrimeTensor
