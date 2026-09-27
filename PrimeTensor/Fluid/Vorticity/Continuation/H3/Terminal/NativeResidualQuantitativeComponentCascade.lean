import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSynchronizedSpectralDissipationCascade

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalQuantitativeComponentCascade
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Hypothetical nonextension forces one fixed physical velocity component and one
localized terminal sequence satisfying

    n < C_H3,1 ‖U_j(τₙ)‖,

while the same sequence also carries the synchronized terminal cascade.
-/
theorem exists_terminal_velocityComponent_quantitativeSynchronizedCascade_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ j : Fin 3,
      ∃ τ : ℕ → ℝ,
        ∃ hTauStrict : ∀ n : ℕ, τ n ∈ Set.Ioo (0 : ℝ) T,
          (∀ n : ℕ, τ n ∈ Set.Ioo a T)
            ∧
          (∀ n : ℕ,
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T)
            ∧
          (∀ n : ℕ,
            (n : ℝ)
              <
            h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
              *
            norm
              (h3TerminalVelocityComponentSpectralStateAt
                hH3 j (τ n) (hTauStrict n)))
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (fun n : ℕ =>
              norm
                (h3TerminalVelocityComponentSpectralStateAt
                  hH3 j (τ n) (hTauStrict n)))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ => velocityH3EnergyAt u (τ n))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              velocityH3DissipationAt u (τ n)
                /
              velocityH3EnergyAt u (τ n))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              h3TopCharacteristicFrequencyAt u (τ n))
            atTop atTop
            ∧
          Tendsto
            (fun n : ℕ =>
              h3TopCharacteristicLengthAt u (τ n))
            atTop (𝓝 0) := by

  obtain ⟨p, _sCurl, sGradient, hBlowup⟩ :=
    fixed_curl_constituentGradient_doubleOriented_samePoint_blowupSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  obtain
    ⟨τ, x, hτ, hTau, _hCurlTendsto, hGradientTendsto⟩ :=
    hBlowup

  have hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T := by
    intro n
    have hTail : τ n ∈ Set.Ioo a T := (hτ n).1
    exact
      ⟨
        lt_trans hClass.terminal_start.1 hTail.1,
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

  have hPoint :
      ∀ n : ℕ,
        norm
          (h3TerminalGradientFieldForPair
            u p (τ n) (x n))
          ≤
        K * norm (G n) := by
    intro n
    dsimp only [G, K, q]
    exact
      norm_terminalGradientFieldForPair_le_swappedSelectedComplementSpectralNorm
        hH3 hTauStrict p n (x n)

  have hStateEq :
      ∀ n : ℕ,
        G n
          =
        h3TerminalVelocityComponentSpectralStateAt
          hH3 j (τ n) (hTauStrict n) := by
    intro n
    dsimp only [G, q, j]
    rw [
      h3TerminalSelectedComplementSpectralState_eq_at
        hH3 hTauStrict
        (h3TerminalSwapCurlGradientPair p) n,
      h3TerminalComplementSpectralStateAt_eq_velocityComponent
        hH3
        (h3TerminalSwapCurlGradientPair p)
        (τ n)
        (hTauStrict n)
    ]
    simp only [
      h3TerminalComplementComponentAxisForPair_swap
    ]

  have hQuant :
      ∀ n : ℕ,
        (n : ℝ)
          <
        K
          *
        norm
          (h3TerminalVelocityComponentSpectralStateAt
            hH3 j (τ n) (hTauStrict n)) := by
    intro n

    have hGradientLower :
        (n : ℝ)
          <
        h3TerminalOrientedValue
          sGradient
          (h3TerminalGradientFieldForPair
            u p (τ n) (x n)) :=
      (hτ n).2.2.2

    have hOrientedAbs :
        h3TerminalOrientedValue
            sGradient
            (h3TerminalGradientFieldForPair
              u p (τ n) (x n))
          ≤
        abs
          (h3TerminalGradientFieldForPair
            u p (τ n) (x n)) :=
      h3TerminalOrientedValue_le_abs
        sGradient
        (h3TerminalGradientFieldForPair
          u p (τ n) (x n))

    have hAbsBound :
        abs
          (h3TerminalGradientFieldForPair
            u p (τ n) (x n))
          ≤
        K * norm (G n) := by
      simpa only [Real.norm_eq_abs] using
        hPoint n

    have hQuantG :
        (n : ℝ) < K * norm (G n) :=
      lt_of_lt_of_le
        hGradientLower
        (hOrientedAbs.trans hAbsBound)

    have hNormEq :
        norm (G n)
          =
        norm
          (h3TerminalVelocityComponentSpectralStateAt
            hH3 j (τ n) (hTauStrict n)) :=
      congrArg norm (hStateEq n)

    calc
      (n : ℝ) < K * norm (G n) := hQuantG
      _ =
        K
          *
        norm
          (h3TerminalVelocityComponentSpectralStateAt
            hH3 j (τ n) (hTauStrict n)) := by
        rw [hNormEq]

  have hKPos : 0 < K := by
    have hLarge :
        ∀ᶠ n : ℕ in atTop,
          1
            <
          h3TerminalOrientedValue
            sGradient
            (h3TerminalGradientFieldForPair
              u p (τ n) (x n)) :=
      hGradientTendsto.eventually
        (eventually_gt_atTop 1)

    obtain ⟨n, hnLarge⟩ := hLarge.exists

    have hOrientedAbs :
        h3TerminalOrientedValue
            sGradient
            (h3TerminalGradientFieldForPair
              u p (τ n) (x n))
          ≤
        abs
          (h3TerminalGradientFieldForPair
            u p (τ n) (x n)) :=
      h3TerminalOrientedValue_le_abs
        sGradient
        (h3TerminalGradientFieldForPair
          u p (τ n) (x n))

    have hAbsBound :
        abs
          (h3TerminalGradientFieldForPair
            u p (τ n) (x n))
          ≤
        K * norm (G n) := by
      simpa only [Real.norm_eq_abs] using
        hPoint n

    have hPositiveProduct :
        0 < K * norm (G n) :=
      lt_of_lt_of_le
        (lt_trans zero_lt_one hnLarge)
        (hOrientedAbs.trans hAbsBound)

    exact
      pos_of_mul_pos_left
        hPositiveProduct
        (norm_nonneg (G n))

  have hGTendsto :
      Tendsto
        (fun n : ℕ => norm (G n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    by_cases hM : M ≤ 0
    · exact
        Eventually.of_forall
          (fun n =>
            le_trans hM (norm_nonneg (G n)))
    · have hGradientLarge :
          ∀ᶠ n : ℕ in atTop,
            K * M
              <
            h3TerminalOrientedValue
              sGradient
              (h3TerminalGradientFieldForPair
                u p (τ n) (x n)) :=
        hGradientTendsto.eventually
          (eventually_gt_atTop (K * M))

      filter_upwards [hGradientLarge] with n hnLarge

      have hOrientedAbs :
          h3TerminalOrientedValue
              sGradient
              (h3TerminalGradientFieldForPair
                u p (τ n) (x n))
            ≤
          abs
            (h3TerminalGradientFieldForPair
              u p (τ n) (x n)) :=
        h3TerminalOrientedValue_le_abs
          sGradient
          (h3TerminalGradientFieldForPair
            u p (τ n) (x n))

      have hAbsBound :
          abs
            (h3TerminalGradientFieldForPair
              u p (τ n) (x n))
            ≤
          K * norm (G n) := by
        simpa only [Real.norm_eq_abs] using
          hPoint n

      have hScaled :
          K * M < K * norm (G n) :=
        lt_of_lt_of_le
          hnLarge
          (hOrientedAbs.trans hAbsBound)

      have hNormLarge :
          M < norm (G n) := by
        nlinarith

      exact le_of_lt hNormLarge

  have hComponentEventuallyEq :
      (fun n : ℕ => norm (G n))
        =ᶠ[atTop]
      (fun n : ℕ =>
        norm
          (h3TerminalVelocityComponentSpectralStateAt
            hH3 j (τ n) (hTauStrict n))) :=
    Eventually.of_forall
      (fun n => by
        simpa using
          congrArg norm (hStateEq n))

  have hComponent :
      Tendsto
        (fun n : ℕ =>
          norm
            (h3TerminalVelocityComponentSpectralStateAt
              hH3 j (τ n) (hTauStrict n)))
        atTop atTop :=
    hGTendsto.congr'
      hComponentEventuallyEq

  have hTauLT :
      Tendsto τ atTop (𝓝[<] T) :=
    tendsto_nhdsLT_of_tendsto_nhds_of_strict_lt
      hTau
      (fun n => (hTauStrict n).2)

  have hEnergy :
      Tendsto
        (fun n : ℕ => velocityH3EnergyAt u (τ n))
        atTop atTop :=
    velocityH3EnergyAt_comp_tendsto_atTop_of_componentSpectralNorm_tendsto_atTop
      hH3 j hTauStrict hComponent

  have hDissipationRatio :
      Tendsto
        (fun n : ℕ =>
          velocityH3DissipationAt u (τ n)
            /
          velocityH3EnergyAt u (τ n))
        atTop atTop :=
    (velocityH3DissipationAt_div_energyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hFrequency :
      Tendsto
        (fun n : ℕ =>
          h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop :=
    (h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  have hLength :
      Tendsto
        (fun n : ℕ =>
          h3TopCharacteristicLengthAt u (τ n))
        atTop
        (𝓝 0) :=
    (h3TopCharacteristicLengthAt_tendsto_zero_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT

  exact
    ⟨
      j,
      τ,
      hTauStrict,
      (fun n => (hτ n).1),
      (fun n => (hτ n).2.1),
      hQuant,
      hTau,
      hComponent,
      hEnergy,
      hDissipationRatio,
      hFrequency,
      hLength
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
