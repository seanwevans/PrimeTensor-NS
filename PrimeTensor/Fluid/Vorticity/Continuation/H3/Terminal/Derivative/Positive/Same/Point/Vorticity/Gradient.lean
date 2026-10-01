import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Actual.Vorticity.Synchronization
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Vorticity.Gradient.Same.Point.Sequence

/-!
# Same-point actual vorticity / gradient synchronization on the positive-growth cascade

The preceding positive-growth synchronization theorem gives one terminal
sequence `σ_n` and spatial points `y_n` such that

    Ω_n :=
      max
        |ωₓ(σ_n,y_n)|
        (max |ωᵧ(σ_n,y_n)| |ω_z(σ_n,y_n)|)

satisfies

    Ω_n -> +∞,

while the same `σ_n` carries

    E(σ_n) -> +∞,
    D(σ_n)/E(σ_n) -> +∞,
    (-T_H3(σ_n))/E(σ_n) -> +∞,
    Λ₃(σ_n) -> +∞,

and positive H³ energy growth.

The already-closed pointwise curl-to-gradient contrapositive says that

    2 M < Ω_n

forces one first velocity derivative at the same spacetime point
`(σ_n,y_n)` to exceed `M`.

Choosing

    M = (Ω_n - 1) / 2

gives a derivative component at the same point with magnitude strictly larger
than `(Ω_n - 1)/2`.  Since `Ω_n -> +∞`, that derivative magnitude also tends
to `+∞`.

Thus one canonical positive-growth spacetime sequence simultaneously carries
the scalar H³ cascade, top-frequency divergence, actual vorticity divergence,
and actual first-gradient divergence at the same spatial points.

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Under hypothetical nonextension there is one positive-growth terminal
spacetime sequence carrying simultaneous divergence of full H³ energy,
normalized dissipation, normalized adverse transport, top characteristic
frequency, actual vorticity amplitude, and an actual first velocity derivative
at the same selected spatial points.
-/
theorem exists_terminal_positiveGrowth_fullCascade_samePoint_actualVorticityGradient_tendsto_atTop_of_noH3PathExtension
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
      σ : ℕ → ℝ,
      ∃
        y : ℕ → Point3,
        ∃
          i j : ℕ → PrimeTensor.Axis Depth.three,
          (
            ∀ n : ℕ,
              σ n ∈ Set.Ioo a T
                ∧
              σ n ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T
                ∧
              (n : ℝ)
                <
              deriv (velocityH3EnergyAt u) (σ n)
          )
            ∧
          Tendsto σ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3EnergyAt u (σ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3DissipationAt u (σ n)
                  /
                velocityH3EnergyAt u (σ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                (
                  - velocityH3TransportDerivativeAt u (σ n)
                )
                  /
                velocityH3EnergyAt u (σ n)
            )
            atTop
            atTop
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TopCharacteristicFrequencyAt
                  u
                  (σ n)
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
                          (σ n)
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
                              (σ n)
                              (y n)
                          )
                      )
                      (
                        abs
                          (
                            realVorticityZ
                              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                              (σ n)
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
                              u (σ n) x
                          ).component (j n)
                      )
                      (y n)
                  )
            )
            atTop
            atTop := by

  obtain
    ⟨
      σ,
      y,
      hσ,
      hSigmaTendsto,
      hEnergyTendsto,
      hDissRatioTendsto,
      hTransportRatioTendsto,
      hFrequencyTendsto,
      hOmegaTendsto
    ⟩ :=
    exists_terminal_positiveGrowth_fullCascade_actualVorticity_tendsto_atTop_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  let Ω : ℕ → ℝ :=
    fun n =>
      max
        (
          abs
            (
              realVorticityX
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (σ n)
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
                    (σ n)
                    (y n)
                )
            )
            (
              abs
                (
                  realVorticityZ
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    (σ n)
                    (y n)
                )
            )
        )

  have hOmegaTendsto' :
      Tendsto Ω atTop atTop := by
    simpa only [Ω] using
      hOmegaTendsto

  have hGradientChoice :
      ∀ n : ℕ,
        ∃
          i j : PrimeTensor.Axis Depth.three,
            (Ω n - 1) / 2
              <
            abs
              (
                spatial3.d
                  i
                  (
                    fun x =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u (σ n) x
                      ).component j
                  )
                  (y n)
              ) := by

    intro n

    have hOmega :
        2 * ((Ω n - 1) / 2)
          <
        Ω n := by
      linarith

    dsimp only [Ω] at hOmega

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
                          u (σ n) x
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

    have hOmegaEventually :
        ∀ᶠ n : ℕ in atTop,
          2 * M + 1
            ≤
          Ω n :=
      hOmegaTendsto'.eventually
        (eventually_ge_atTop (2 * M + 1))

    filter_upwards
      [
        hOmegaEventually
      ]
      with n hn

    have hThreshold :
        M
          ≤
        (Ω n - 1) / 2 := by
      linarith

    exact
      le_of_lt
        (
          lt_of_le_of_lt
            hThreshold
            (hGradient n)
        )

  exact
    ⟨
      σ,
      y,
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
    ⟩

/--
Neutral same-point positive-growth formulation.
-/
theorem smoothContinuationExtension_or_terminal_positiveGrowth_fullCascade_samePoint_actualVorticityGradient
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
        σ : ℕ → ℝ,
        ∃
          y : ℕ → Point3,
          ∃
            i j : ℕ → PrimeTensor.Axis Depth.three,
            (
              ∀ n : ℕ,
                σ n ∈ Set.Ioo a T
                  ∧
                σ n ∈
                  Set.Ioo
                    (T - (1 : ℝ) / ((n : ℝ) + 1))
                    T
                  ∧
                (n : ℝ)
                  <
                deriv (velocityH3EnergyAt u) (σ n)
            )
              ∧
            Tendsto σ atTop (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3EnergyAt u (σ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3DissipationAt u (σ n)
                    /
                  velocityH3EnergyAt u (σ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  (
                    - velocityH3TransportDerivativeAt u (σ n)
                  )
                    /
                  velocityH3EnergyAt u (σ n)
              )
              atTop
              atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TopCharacteristicFrequencyAt
                    u
                    (σ n)
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
                            (σ n)
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
                                (σ n)
                                (y n)
                            )
                        )
                        (
                          abs
                            (
                              realVorticityZ
                                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                                (σ n)
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
                                u (σ n) x
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
        SmoothContinuationExtension
          u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_terminal_positiveGrowth_fullCascade_samePoint_actualVorticityGradient_tendsto_atTop_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

end

end Euclidean
end Bridge
end PrimeTensor
