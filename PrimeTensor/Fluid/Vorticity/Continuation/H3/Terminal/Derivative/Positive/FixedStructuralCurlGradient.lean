import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ActualVorticitySynchronization
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedCurlGradientDoubleOrientation
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fixed structural curl / constituent-gradient pair on the positive-growth cascade

The positive-growth synchronization theorem gives one terminal sequence
`σ_n` and spatial points `y_n` for which the actual vorticity maximum tends to
`+∞`, while the same times carry the full H³ scalar and characteristic-
frequency cascade.

At one spacetime point, if

    M < max(|ωₓ|, |ωᵧ|, |ω_z|),

then one of the three curl components has magnitude greater than `M`.  Since

    ωₓ = ∂y u_z - ∂z u_y,
    ωᵧ = ∂z u_x - ∂x u_z,
    ω_z = ∂x u_y - ∂y u_x,

at least one of the two actual constituent derivatives of that large curl
component must have magnitude greater than `M/2`.

The six possibilities are exactly `H3TerminalCurlGradientPair`.  Applying the
pointwise statement with `M = Ω_n - 1` produces a structural pair `p_n` with

    Ω_n - 1 < |curl(p_n)|,
    (Ω_n - 1)/2 < |gradient(p_n)|.

Because the pair type is finite, one structural pair occurs frequently.  A
strictly increasing extraction freezes that pair while preserving every
`atTop` limit and the standard terminal localization / indexed positive-growth
lower bound.

Thus hypothetical nonextension forces one fixed, structurally coupled curl /
constituent-gradient channel to diverge at the same spacetime points on a
positive-growth sequence carrying the full scalar/frequency cascade.

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise six-channel structural selection -/

/--
If the maximum actual vorticity-component magnitude at one spacetime point
exceeds `M`, then one of the six structural curl / constituent-gradient pairs
has curl magnitude greater than `M` and constituent-gradient magnitude greater
than `M/2` at that same point.
-/
theorem exists_h3TerminalCurlGradientPair_of_vorticityComponentMax_gt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t M : ℝ}
    {x : Point3}
    (hOmega :
      M
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
    ∃ p : H3TerminalCurlGradientPair,
      M
        <
      abs
        (
          h3TerminalCurlFieldForPair
            u p t x
        )
        ∧
      M / 2
        <
      abs
        (
          h3TerminalGradientFieldForPair
            u p t x
        ) := by

  rcases
      (lt_max_iff.mp hOmega)
    with hX | hYZ

  · let a : ℝ :=
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

    let b : ℝ :=
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

    have hX' :
        M < abs (a - b) := by
      simpa only [a, b, realVorticityX] using
        hX

    by_cases ha :
        M / 2 < abs a

    · refine
        ⟨
          H3TerminalCurlGradientPair.x_yz,
          ?_,
          ?_
        ⟩

      · simpa only [
          h3TerminalCurlFieldForPair
        ] using
          hX

      · simpa only [
          h3TerminalGradientFieldForPair,
          h3TerminalGradientDerivativeAxisForPair,
          h3TerminalGradientComponentAxisForPair,
          a
        ] using
          ha

    · have haLe :
          abs a ≤ M / 2 :=
        le_of_not_gt
          ha

      have hb :
          M / 2 < abs b := by

        by_contra hbNo

        have hbLe :
            abs b ≤ M / 2 :=
          le_of_not_gt
            hbNo

        have hUpper :
            abs (a - b) ≤ M := by

          calc
            abs (a - b)
                ≤
              abs a + abs b :=
              abs_sub a b

            _ ≤
              M / 2 + M / 2 :=
              add_le_add
                haLe
                hbLe

            _ = M := by
              ring

        exact
          (not_lt_of_ge hUpper)
            hX'

      refine
        ⟨
          H3TerminalCurlGradientPair.x_zy,
          ?_,
          ?_
        ⟩

      · simpa only [
          h3TerminalCurlFieldForPair
        ] using
          hX

      · simpa only [
          h3TerminalGradientFieldForPair,
          h3TerminalGradientDerivativeAxisForPair,
          h3TerminalGradientComponentAxisForPair,
          b
        ] using
          hb

  · rcases
        (lt_max_iff.mp hYZ)
      with hY | hZ

    · let a : ℝ :=
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

      let b : ℝ :=
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

      have hY' :
          M < abs (a - b) := by
        simpa only [a, b, realVorticityY] using
          hY

      by_cases ha :
          M / 2 < abs a

      · refine
          ⟨
            H3TerminalCurlGradientPair.y_zx,
            ?_,
            ?_
          ⟩

        · simpa only [
            h3TerminalCurlFieldForPair
          ] using
            hY

        · simpa only [
            h3TerminalGradientFieldForPair,
            h3TerminalGradientDerivativeAxisForPair,
            h3TerminalGradientComponentAxisForPair,
            a
          ] using
            ha

      · have haLe :
            abs a ≤ M / 2 :=
          le_of_not_gt
            ha

        have hb :
            M / 2 < abs b := by

          by_contra hbNo

          have hbLe :
              abs b ≤ M / 2 :=
            le_of_not_gt
              hbNo

          have hUpper :
              abs (a - b) ≤ M := by

            calc
              abs (a - b)
                  ≤
                abs a + abs b :=
                abs_sub a b

              _ ≤
                M / 2 + M / 2 :=
                add_le_add
                  haLe
                  hbLe

              _ = M := by
                ring

          exact
            (not_lt_of_ge hUpper)
              hY'

        refine
          ⟨
            H3TerminalCurlGradientPair.y_xz,
            ?_,
            ?_
          ⟩

        · simpa only [
            h3TerminalCurlFieldForPair
          ] using
            hY

        · simpa only [
            h3TerminalGradientFieldForPair,
            h3TerminalGradientDerivativeAxisForPair,
            h3TerminalGradientComponentAxisForPair,
            b
          ] using
            hb

    · let a : ℝ :=
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

      let b : ℝ :=
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

      have hZ' :
          M < abs (a - b) := by
        simpa only [a, b, realVorticityZ] using
          hZ

      by_cases ha :
          M / 2 < abs a

      · refine
          ⟨
            H3TerminalCurlGradientPair.z_xy,
            ?_,
            ?_
          ⟩

        · simpa only [
            h3TerminalCurlFieldForPair
          ] using
            hZ

        · simpa only [
            h3TerminalGradientFieldForPair,
            h3TerminalGradientDerivativeAxisForPair,
            h3TerminalGradientComponentAxisForPair,
            a
          ] using
            ha

      · have haLe :
            abs a ≤ M / 2 :=
          le_of_not_gt
            ha

        have hb :
            M / 2 < abs b := by

          by_contra hbNo

          have hbLe :
              abs b ≤ M / 2 :=
            le_of_not_gt
              hbNo

          have hUpper :
              abs (a - b) ≤ M := by

            calc
              abs (a - b)
                  ≤
                abs a + abs b :=
                abs_sub a b

              _ ≤
                M / 2 + M / 2 :=
                add_le_add
                  haLe
                  hbLe

              _ = M := by
                ring

          exact
            (not_lt_of_ge hUpper)
              hZ'

        refine
          ⟨
            H3TerminalCurlGradientPair.z_yx,
            ?_,
            ?_
          ⟩

        · simpa only [
            h3TerminalCurlFieldForPair
          ] using
            hZ

        · simpa only [
            h3TerminalGradientFieldForPair,
            h3TerminalGradientDerivativeAxisForPair,
            h3TerminalGradientComponentAxisForPair,
            b
          ] using
            hb

/-! ## Fixed structural pair on the positive-growth cascade -/

local instance h3TerminalCurlGradientPairFintype :
    Fintype H3TerminalCurlGradientPair where

  elems :=
    {
      H3TerminalCurlGradientPair.x_yz,
      H3TerminalCurlGradientPair.x_zy,
      H3TerminalCurlGradientPair.y_zx,
      H3TerminalCurlGradientPair.y_xz,
      H3TerminalCurlGradientPair.z_xy,
      H3TerminalCurlGradientPair.z_yx
    }

  complete p := by
    cases p <;> simp

/--
Under hypothetical nonextension, one fixed structural curl /
constituent-gradient pair diverges at common spatial points on a positive-
growth subsequence carrying the full H³ scalar and top-frequency cascade.
-/
theorem exists_terminal_positiveGrowth_fullCascade_fixedStructuralCurlGradientPair_tendsto_atTop_of_noH3PathExtension
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
      p₀ : H3TerminalCurlGradientPair,
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
                abs
                  (
                    h3TerminalCurlFieldForPair
                      u p₀
                      (τ n)
                      (y n)
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
                    h3TerminalGradientFieldForPair
                      u p₀
                      (τ n)
                      (y n)
                  )
            )
            atTop
            atTop := by

  obtain
    ⟨
      σ,
      x,
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
        )

  have hOmegaTendsto' :
      Tendsto Ω atTop atTop := by
    simpa only [Ω] using
      hOmegaTendsto

  have hPairChoice :
      ∀ n : ℕ,
        ∃ p : H3TerminalCurlGradientPair,
          Ω n - 1
            <
          abs
            (
              h3TerminalCurlFieldForPair
                u p
                (σ n)
                (x n)
            )
            ∧
          (Ω n - 1) / 2
            <
          abs
            (
              h3TerminalGradientFieldForPair
                u p
                (σ n)
                (x n)
            ) := by

    intro n

    apply
      exists_h3TerminalCurlGradientPair_of_vorticityComponentMax_gt
        (
          u := u
        )
        (
          t := σ n
        )
        (
          x := x n
        )
        (
          M := Ω n - 1
        )

    dsimp only [Ω]

    linarith

  choose p hp using
    hPairChoice

  have hFrequentlySomePair :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : H3TerminalCurlGradientPair,
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
      p₀,
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
      hPairFixed
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
            Ω (φ n)
        )
        atTop
        atTop := by

    change
      Tendsto
        (Ω ∘ φ)
        atTop
        atTop

    exact
      hOmegaTendsto'.comp
        hPhiTendsto

  have hCurlTendsto :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                h3TerminalCurlFieldForPair
                  u p₀
                  (τ n)
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
          M + 1
            ≤
          Ω (φ n) :=
      hOmegaSubsequence.eventually
        (eventually_ge_atTop (M + 1))

    filter_upwards
      [
        hOmegaEventually
      ]
      with n hn

    have hThreshold :
        M
          ≤
        Ω (φ n) - 1 := by
      linarith

    have hPairN :=
      (hp (φ n)).1

    have hPairEq :
        p (φ n) = p₀ :=
      hPairFixed n

    rw [hPairEq] at hPairN

    dsimp only [τ, y]

    exact
      le_of_lt
        (
          lt_of_le_of_lt
            hThreshold
            hPairN
        )

  have hGradientTendsto :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                h3TerminalGradientFieldForPair
                  u p₀
                  (τ n)
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
          Ω (φ n) :=
      hOmegaSubsequence.eventually
        (eventually_ge_atTop (2 * M + 1))

    filter_upwards
      [
        hOmegaEventually
      ]
      with n hn

    have hThreshold :
        M
          ≤
        (Ω (φ n) - 1) / 2 := by
      linarith

    have hPairN :=
      (hp (φ n)).2

    have hPairEq :
        p (φ n) = p₀ :=
      hPairFixed n

    rw [hPairEq] at hPairN

    dsimp only [τ, y]

    exact
      le_of_lt
        (
          lt_of_le_of_lt
            hThreshold
            hPairN
        )

  exact
    ⟨
      p₀,
      τ,
      y,
      hTauData,
      hTauTendsto,
      hEnergySubsequence,
      hDissSubsequence,
      hTransportSubsequence,
      hFrequencySubsequence,
      hCurlTendsto,
      hGradientTendsto
    ⟩

/--
Neutral fixed structural-channel formulation.
-/
theorem smoothContinuationExtension_or_terminal_positiveGrowth_fullCascade_fixedStructuralCurlGradientPair
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
        p₀ : H3TerminalCurlGradientPair,
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
                  abs
                    (
                      h3TerminalCurlFieldForPair
                        u p₀
                        (τ n)
                        (y n)
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
                      h3TerminalGradientFieldForPair
                        u p₀
                        (τ n)
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
          exists_terminal_positiveGrowth_fullCascade_fixedStructuralCurlGradientPair_tendsto_atTop_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hb
        )

end

end Euclidean
end Bridge
end PrimeTensor
