import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualVelocityStrongH3Endpoint

/-!
# A fixed velocity component must escape in H³ under nonextension

The strong-endpoint contradiction can be sharpened into a positive necessary
condition without assuming any terminal limit.

Hypothetical nonextension already yields one fixed curl/constituent-gradient
pair `p`, one fixed gradient orientation, and one localized terminal sequence
`(τ n, x n)` along which the selected constituent gradient tends to `+∞`.

Swap the pair.  The selected gradient of `p` is exactly the complementary
derivative of `swap p`, and the complementary velocity component of `swap p`
is exactly the selected velocity component of `p`.

For the corresponding weighted scalar spectral H³ state `G_n`, the existing
uniform derivative-evaluation estimate gives

    |gradient_p(τ_n,x_n)| ≤ C₁ ‖G_n‖_{H³}.

Since one orientation of the left side tends to `+∞`, the norm `‖G_n‖` itself
must tend to `+∞`.

Thus a hypothetical nonextendible path does not merely have unbounded total H³
energy.  One fixed physical velocity component carries an H³ norm blowup along
a localized terminal sequence that is already synchronized with the fixed
curl/gradient structure.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalVelocityComponentEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Swap identities at the axis level -/

@[simp]
theorem h3TerminalComplementDerivativeAxisForPair_swap
    (p : H3TerminalCurlGradientPair) :
    h3TerminalComplementDerivativeAxisForPair
        (h3TerminalSwapCurlGradientPair p)
      =
    h3TerminalGradientDerivativeAxisForPair p := by
  cases p <;> rfl

@[simp]
theorem h3TerminalComplementComponentAxisForPair_swap
    (p : H3TerminalCurlGradientPair) :
    h3TerminalComplementComponentAxisForPair
        (h3TerminalSwapCurlGradientPair p)
      =
    h3TerminalGradientComponentAxisForPair p := by
  cases p <;> rfl

/-! ## Pointwise derivative bound by the swapped selected H³ state -/

/--
On any strict selected sequence, the selected constituent gradient of `p` is
bounded pointwise by the H³ norm of the complementary scalar state of
`swap p`.
-/
theorem norm_terminalGradientFieldForPair_le_swappedSelectedComplementSpectralNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (p : H3TerminalCurlGradientPair)
    (n : ℕ)
    (x : Point3) :
    norm
      (
        h3TerminalGradientFieldForPair
          u p
          (τ n)
          x
      )
      ≤
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
      *
    norm
      (
        h3TerminalSelectedComplementSpectralState
          hH3
          hTauStrict
          (h3TerminalSwapCurlGradientPair p)
          n
      ) := by

  let q : H3TerminalCurlGradientPair :=
    h3TerminalSwapCurlGradientPair p

  let G : H3SpectralScalarState :=
    h3TerminalSelectedComplementSpectralState
      hH3 hTauStrict q n

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementDerivativeAxisForPair q)

  have hAxis :
      h3AxisOfFin3 i
        =
      h3TerminalComplementDerivativeAxisForPair q := by

    dsimp only [i]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
        (h3TerminalComplementDerivativeAxisForPair q)

  have hRep :
      h3SpectralScalarRealC1RepresentativeOnPoint3 G
        =
      loggedVelocityComponent
        u
        (τ n)
        (h3TerminalComplementComponentAxisForPair q) := by

    dsimp only [G, q]

    exact
      h3TerminalSelectedComplementSpectralState_representative_eq_loggedVelocityComponent
        hH3
        hTauStrict
        (h3TerminalSwapCurlGradientPair p)
        n

  have hRaw :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
      G
      i
      x

  rw [hAxis] at hRaw

  have hDerivative :
      spatial3.d
          (h3TerminalComplementDerivativeAxisForPair q)
          (
            h3SpectralScalarRealC1RepresentativeOnPoint3
              G
          )
          x
        =
      h3TerminalComplementGradientFieldForPair
        u q
        (τ n)
        x := by

    rw [hRep]

    rfl

  have hComplement :
      norm
        (
          h3TerminalComplementGradientFieldForPair
            u q
            (τ n)
            x
        )
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
        *
      norm G := by

    rw [← hDerivative]

    exact
      hRaw

  have hSwap :
      h3TerminalComplementGradientFieldForPair
          u q
          (τ n)
          x
        =
      h3TerminalGradientFieldForPair
          u p
          (τ n)
          x := by

    dsimp only [q]

    exact
      h3TerminalComplementGradientFieldForPair_swap_eq_gradient
        u p (τ n) x

  rw [hSwap] at hComplement

  simpa only [G, q] using
    hComplement

/-! ## Fixed-component H³ escape -/

/--
Hypothetical nonextension forces one fixed physical velocity component to have
weighted spectral H³ norm tending to `+∞` along a localized terminal sequence.
-/
theorem exists_terminal_velocityComponentSpectralNorm_tendsto_atTop_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T) :
    ∃ j : Fin 3,
      ∃ τ : ℕ → ℝ,
        ∃ hTauStrict :
          ∀ n : ℕ,
            τ n ∈ Set.Ioo (0 : ℝ) T,
          (
            ∀ n : ℕ,
              τ n ∈ Set.Ioo a T
          )
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                norm
                  (
                    h3TerminalVelocityComponentSpectralStateAt
                      hH3
                      j
                      (τ n)
                      (hTauStrict n)
                  )
            )
            atTop
            atTop := by

  obtain
    ⟨
      p,
      _sCurl,
      sGradient,
      hBlowup
    ⟩ :=
    fixed_curl_constituentGradient_doubleOriented_samePoint_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTau,
      _hCurlTendsto,
      hGradientTendsto
    ⟩ :=
    hBlowup

  have hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T := by

    intro n

    have hTail :
        τ n ∈ Set.Ioo a T :=
      (hτ n).1

    exact
      ⟨
        lt_trans
          hClass.terminal_start.1
          hTail.1,
        hTail.2
      ⟩

  let q : H3TerminalCurlGradientPair :=
    h3TerminalSwapCurlGradientPair p

  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalGradientComponentAxisForPair p)

  let G : ℕ → H3SpectralScalarState :=
    fun n =>
      h3TerminalSelectedComplementSpectralState
        hH3 hTauStrict q n

  let K : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  have hKNonneg :
      0 ≤ K := by

    dsimp only [K]

    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg

  have hPoint :
      ∀ n : ℕ,
        norm
          (
            h3TerminalGradientFieldForPair
              u p
              (τ n)
              (x n)
          )
          ≤
        K * norm (G n) := by

    intro n

    dsimp only [G, K, q]

    exact
      norm_terminalGradientFieldForPair_le_swappedSelectedComplementSpectralNorm
        hH3
        hTauStrict
        p
        n
        (x n)

  have hKPos :
      0 < K := by

    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          1
            <
          h3TerminalOrientedValue
            sGradient
            (
              h3TerminalGradientFieldForPair
                u p
                (τ n)
                (x n)
            ) :=
      hGradientTendsto.eventually
        (eventually_gt_atTop 1)

    obtain
      ⟨
        n,
        hnLarge
      ⟩ :=
      hLarge.exists

    have hOrientedAbs :
        h3TerminalOrientedValue
            sGradient
            (
              h3TerminalGradientFieldForPair
                u p
                (τ n)
                (x n)
            )
          ≤
        abs
          (
            h3TerminalGradientFieldForPair
              u p
              (τ n)
              (x n)
          ) :=
      h3TerminalOrientedValue_le_abs
        sGradient
        (
          h3TerminalGradientFieldForPair
            u p
            (τ n)
            (x n)
        )

    have hAbsBound :
        abs
          (
            h3TerminalGradientFieldForPair
              u p
              (τ n)
              (x n)
          )
          ≤
        K * norm (G n) := by

      simpa only [Real.norm_eq_abs] using
        hPoint n

    have hPositiveProduct :
        0 < K * norm (G n) :=
      lt_of_lt_of_le
        (lt_trans zero_lt_one hnLarge)
        (
          hOrientedAbs.trans
            hAbsBound
        )

    exact
      pos_of_mul_pos_left
        hPositiveProduct
        (norm_nonneg (G n))

  have hGTendsto :
      Tendsto
        (
          fun n : ℕ =>
            norm (G n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    by_cases hM :
        M ≤ 0

    · exact
        Eventually.of_forall
          (
            fun n =>
              le_trans
                hM
                (norm_nonneg (G n))
          )

    · have hMPos :
          0 < M :=
        lt_of_not_ge
          hM

      have hGradientLarge :
          ∀ᶠ n : ℕ in atTop,
            K * M
              <
            h3TerminalOrientedValue
              sGradient
              (
                h3TerminalGradientFieldForPair
                  u p
                  (τ n)
                  (x n)
              ) :=
        hGradientTendsto.eventually
          (eventually_gt_atTop (K * M))

      filter_upwards
        [hGradientLarge]
        with n hnLarge

      have hOrientedAbs :
          h3TerminalOrientedValue
              sGradient
              (
                h3TerminalGradientFieldForPair
                  u p
                  (τ n)
                  (x n)
              )
            ≤
          abs
            (
              h3TerminalGradientFieldForPair
                u p
                (τ n)
                (x n)
            ) :=
        h3TerminalOrientedValue_le_abs
          sGradient
          (
            h3TerminalGradientFieldForPair
              u p
              (τ n)
              (x n)
          )

      have hAbsBound :
          abs
            (
              h3TerminalGradientFieldForPair
                u p
                (τ n)
                (x n)
            )
            ≤
          K * norm (G n) := by

        simpa only [Real.norm_eq_abs] using
          hPoint n

      have hScaled :
          K * M
            <
          K * norm (G n) :=
        lt_of_lt_of_le
          hnLarge
          (
            hOrientedAbs.trans
              hAbsBound
          )

      have hNormLarge :
          M < norm (G n) := by
        nlinarith

      exact
        le_of_lt
          hNormLarge

  have hStateEq :
      ∀ n : ℕ,
        G n
          =
        h3TerminalVelocityComponentSpectralStateAt
          hH3
          j
          (τ n)
          (hTauStrict n) := by

    intro n

    dsimp only [G, q, j]

    rw [
      h3TerminalSelectedComplementSpectralState_eq_at
        hH3
        hTauStrict
        (h3TerminalSwapCurlGradientPair p)
        n,
      h3TerminalComplementSpectralStateAt_eq_velocityComponent
        hH3
        (h3TerminalSwapCurlGradientPair p)
        (τ n)
        (hTauStrict n)
    ]

    simp only [
      h3TerminalComplementComponentAxisForPair_swap
    ]

  have hComponentEventuallyEq :
      (
        fun n : ℕ =>
          norm (G n)
      )
        =ᶠ[atTop]
      (
        fun n : ℕ =>
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                hH3
                j
                (τ n)
                (hTauStrict n)
            )
      ) :=
    Eventually.of_forall
      (
        fun n => by
          simpa using
            congrArg norm
              (hStateEq n)
      )

  have hComponentTendsto :
      Tendsto
        (
          fun n : ℕ =>
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                  hH3
                  j
                  (τ n)
                  (hTauStrict n)
              )
        )
        atTop
        atTop :=
    hGTendsto.congr'
      hComponentEventuallyEq

  exact
    ⟨
      j,
      τ,
      hTauStrict,
      (fun n => (hτ n).1),
      hTau,
      hComponentTendsto
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
