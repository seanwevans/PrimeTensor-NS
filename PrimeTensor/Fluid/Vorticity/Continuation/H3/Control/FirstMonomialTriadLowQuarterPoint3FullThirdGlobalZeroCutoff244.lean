import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSignedExcessRadialTailLow244
import Mathlib.Tactic

/-!
# Global zero-cutoff heat/Leray identity for physical normalized Fourier variance

The previously closed fourth-radial PDE pairing works for *every* real radial
cutoff, not only the natural positive cutoffs used in terminal-tail arguments.
At radial cutoff zero the strict sublevel of the nonnegative Fourier gradient
magnitude is EMPTY. Restricting Fourier L² to its complement therefore
preserves the entire real Hilbert pairing.

Apply the previously proved coordinatewise sharp-tail heat-plus-Leray pairing
at zero cutoff. The empty-set identity eliminates all restricted measures and
produces the genuine GLOBAL time derivative

    D₃' = -2 ∑ⱼ ∫ q⁵ |ûⱼ|² - 2 ∑ⱼ ∫ q⁴ Re⟪ûⱼ,Fⱼ(U,U)⟫.

Thus the physical signed normalized variance source splits *exactly* into
lower-order plus top heat and into order-two transport plus top Leray transfer,
without a low-frequency remainder, an exchange of limit/derivative or a new
uniform spectral moment estimate. This identity alone does not bound the
nonlinear source or imply continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000

-- The Fourier carrier has a finite Euclidean coordinate axis. Several
-- Fourier measure instances depend on having this Fintype available locally.
noncomputable local instance axisFintypeH3GlobalZeroCutoff244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fourier radial magnitude has no points strictly below zero. -/
theorem h3Path_zeroRadialBelow_eq_empty244 :
    h3TerminalRadialFrequencyBelow (0 : ℝ) = ∅ := by
  ext ξ
  change (h3FourierGradientMagnitude ξ < 0) ↔ False
  constructor
  · intro h
    exact (not_lt_of_ge (h3FourierGradientMagnitude_nonneg ξ)) h
  · intro h
    exact False.elim h

/-- Restricting global Fourier L² states to the complement of the empty
zero-radius sublevel does not change their real Hilbert pairing. -/
theorem h3Path_zeroRadialRestrict_inner_eq_global244
    (F G : H3FourierComplexL2) :
    inner ℝ (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM 0 F)
      (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM 0 G) =
      inner ℝ F G := by
  have hRestricted :=
    inner_h3TerminalPhysicalTopDissipationRadialTailRestrictCLM_eq_integral_re_inner
      (0 : ℝ) F G
  -- Rewrite only the scalar measure, never the dependent codomain of
  -- the restriction map on the left of hRestricted.
  have hZeroMeasure :
      (volume : Measure H3FourierPoint3).restrict
          (h3TerminalRadialFrequencyBelow (0 : ℝ))ᶜ =
        (volume : Measure H3FourierPoint3) := by
    rw [h3Path_zeroRadialBelow_eq_empty244]
    simp only [Set.compl_empty, Measure.restrict_univ]
  have hRe :
      (∫ ξ : H3FourierPoint3, inner ℂ (F ξ) (G ξ)).re =
        ∫ ξ : H3FourierPoint3, (inner ℂ (F ξ) (G ξ)).re := by
    exact (Complex.reCLM.integral_comp_comm
      (MeasureTheory.L2.integrable_inner F G)).symm
  have hPolar : (inner ℂ F G).re = inner ℝ F G := by
    change RCLike.re (inner ℂ F G) = inner ℝ F G
    rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four]
    simpa using
      (re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
        (𝕜 := ℝ) F G).symm
  calc
    inner ℝ (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM 0 F)
        (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM 0 G) =
        ∫ ξ : H3FourierPoint3, (inner ℂ (F ξ) (G ξ)).re
          ∂((volume : Measure H3FourierPoint3).restrict
            (h3TerminalRadialFrequencyBelow (0 : ℝ))ᶜ) := hRestricted
    _ = ∫ ξ : H3FourierPoint3, (inner ℂ (F ξ) (G ξ)).re := by
        rw [hZeroMeasure]
    _ = (∫ ξ : H3FourierPoint3, inner ℂ (F ξ) (G ξ)).re := hRe.symm
    _ = (inner ℂ F G).re := by rw [MeasureTheory.L2.inner_def]
    _ = inner ℝ F G := hPolar

/-- The unrestricted fifth radial spectral moment, with its true dissipative
negative coefficient, for the actual terminal spectral state. -/
noncomputable def h3PathTopFourierGlobalHeatRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) : ℝ :=
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t ht
  ∑ j : Fin 3,
    (-2 : ℝ) * ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 5 *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2

/-- The actual global top-order signed nonlinear Leray transfer, without any
frequency cutoff or unnamed low-frequency derivative correction. -/
noncomputable def h3PathTopFourierGlobalLerayRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) : ℝ :=
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t ht
  ∑ j : Fin 3,
    (-2 : ℝ) * ∫ ξ : H3FourierPoint3,
      h3FourierGradientSquare ξ ^ 4 *
        (inner ℂ
          (h3SpectralScalarRawFourierL2 (U j) ξ)
          (h3RawFinLerayOuterProductDivergence U U j ξ)).re

/-- The global heat contribution to fourth-radial dissipation has the
correct (nonpositive) sign. No sign is inferred for the signed Leray rate. -/
theorem h3Path_globalHeatRate_nonpos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3PathTopFourierGlobalHeatRate244 hH3 t ht ≤ 0 := by
  unfold h3PathTopFourierGlobalHeatRate244
  apply Finset.sum_nonpos
  intro j hj
  apply mul_nonpos_of_nonpos_of_nonneg (by norm_num)
  apply integral_nonneg
  intro ξ
  exact mul_nonneg
    (pow_nonneg (h3FourierGradientSquare_nonneg ξ) 5)
    (sq_nonneg _)

/-- THE cutoff-free identity for the global fourth-radial Hilbert derivative.
All integrals and strong derivatives are justified by the earlier strict-time
weighted Hilbert PDE pairing. No limit of finite-frequency cutoff derivatives
is taken. -/
theorem h3Path_fourthRadialPairing_eq_globalHeat_add_Leray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t =
      h3PathTopFourierGlobalHeatRate244 hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ +
      h3PathTopFourierGlobalLerayRate244 hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hEach : ∀ j : Fin 3,
      2 * inner ℝ
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j t)
        (deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j) t) =
        (-2 : ℝ) * (∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5 *
            ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2)
        + (-2 : ℝ) * (∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 4 *
            (inner ℂ
              (h3SpectralScalarRawFourierL2 (U j) ξ)
              (h3RawFinLerayOuterProductDivergence U U j ξ)).re) := by
    intro j
    let V : ℝ → H3FourierComplexL2 :=
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j
    have hW : HasDerivAt V (deriv V t) t := by
      exact
        ((h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_contDiffAt_one
          hH3 hClass ht j).differentiableAt_one).hasDerivAt
    have hPair :=
      h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path_two_mul_inner_derivativeValue_eq_diffusion_plus_nonlinearCoordinate
        (R := (0 : ℝ)) hH3 hClass ht j (deriv V t) hW
    have hInner :
        inner ℝ
          (h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
            hH3 hClass 0 j t)
          (h3TerminalPhysicalTopDissipationRadialTailRestrictCLM
            0 (deriv V t)) =
        inner ℝ (V t) (deriv V t) := by
      unfold h3TerminalPhysicalTopDissipationRadialTailRestrictedComponentL2Path
      exact h3Path_zeroRadialRestrict_inner_eq_global244 _ _
    dsimp only at hPair
    rw [hInner] at hPair
    unfold h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt at hPair
    dsimp only at hPair
    rw [h3Path_zeroRadialBelow_eq_empty244] at hPair
    simp only [Set.compl_empty, Measure.restrict_univ] at hPair
    simpa only [htAbs, U, V] using hPair
  change
    (∑ j : Fin 3,
      2 * inner ℝ
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j t)
        (deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j) t)) =
      (∑ j : Fin 3,
        (-2 : ℝ) * (∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5 *
            ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2)) +
      (∑ j : Fin 3,
        (-2 : ℝ) * (∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 4 *
            (inner ℂ
              (h3SpectralScalarRawFourierL2 (U j) ξ)
              (h3RawFinLerayOuterProductDivergence U U j ξ)).re))
  calc
    (∑ j : Fin 3,
      2 * inner ℝ
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j t)
        (deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j) t)) =
      ∑ j : Fin 3,
        ((-2 : ℝ) * (∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 5 *
            ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2) +
        (-2 : ℝ) * (∫ ξ : H3FourierPoint3,
          h3FourierGradientSquare ξ ^ 4 *
            (inner ℂ
              (h3SpectralScalarRawFourierL2 (U j) ξ)
              (h3RawFinLerayOuterProductDivergence U U j ξ)).re)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hEach j
    _ = (∑ j : Fin 3,
          (-2 : ℝ) * (∫ ξ : H3FourierPoint3,
            h3FourierGradientSquare ξ ^ 5 *
              ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2)) +
        (∑ j : Fin 3,
          (-2 : ℝ) * (∫ ξ : H3FourierPoint3,
            h3FourierGradientSquare ξ ^ 4 *
              (inner ℂ
                (h3SpectralScalarRawFourierL2 (U j) ξ)
                (h3RawFinLerayOuterProductDivergence U U j ξ)).re)) := by
        rw [Finset.sum_add_distrib]

/-- The genuinely linear heat source includes BOTH lower-order dissipation
pairings and the exact global fifth radial dissipation. -/
noncomputable def h3PathTopFourierGlobalDiffusionExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  2 * velocityH3Energy2At u t * velocityH3DiffusionDerivative2At u t *
      (velocityH3Energy0At u t * h3TerminalPhysicalTopDissipation3Path hClass t) -
    velocityH3Energy2At u t ^ 2 *
      (velocityH3DiffusionDerivative0At u t *
        h3TerminalPhysicalTopDissipation3Path hClass t +
       velocityH3Energy0At u t *
         h3PathTopFourierGlobalHeatRate244 hH3 t htAbs)

/-- All genuine nonlinear terms: order-two transport and global Leray
transfer from the fourth-radial derivative. -/
noncomputable def h3PathTopFourierGlobalNonlinearExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  (0 : ℝ) - (
    2 * velocityH3Energy2At u t * velocityH3TransportDerivative2At u t *
      (velocityH3Energy0At u t * h3TerminalPhysicalTopDissipation3Path hClass t) +
    velocityH3Energy2At u t ^ 2 * velocityH3Energy0At u t *
      h3PathTopFourierGlobalLerayRate244 hH3 t htAbs
  )

/-- Global signed physical Fourier concentration contains precisely the
viscous heat source plus both nonlinear transfers. In particular there is NO
low-radial complement derivative at zero cutoff. -/
theorem h3Path_signedExcess_eq_globalHeat_add_Leray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass t =
      h3PathTopFourierGlobalDiffusionExcess244 hH3 hClass t ht +
      h3PathTopFourierGlobalNonlinearExcess244 hH3 hClass t ht := by
  have hOld := h3Path_signedExcess_eq_diffusionHilbert_add_transport244
    hH3 hClass ht
  have hTransport := h3Path_nonlinearTransportExcess_eq_orderTwo244
    hH3 hClass ht
  have hTop := h3Path_fourthRadialPairing_eq_globalHeat_add_Leray244
    hH3 hClass ht
  rw [hOld, hTransport]
  unfold h3PathTopFourierDiffusionHilbertBackground244
    h3PathTopFourierGlobalDiffusionExcess244
    h3PathTopFourierGlobalNonlinearExcess244
  dsimp only
  rw [hTop]
  ring

/-- An exact normalized global heat/nonlinearity decomposition with no
cutoff remainder and no unproved sign or transport estimate. -/
theorem h3Path_normalizedExcessRate_eq_globalHeat_add_Leray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass t =
      (h3PathTopFourierGlobalDiffusionExcess244 hH3 hClass t ht +
       h3PathTopFourierGlobalNonlinearExcess244 hH3 hClass t ht) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2 := by
  unfold h3PathTopFourierNormalizedSignedExcessRate244
  rw [h3Path_signedExcess_eq_globalHeat_add_Leray244 hH3 hClass ht]

/-- A small Young gap forces global heat plus actual nonlinear transfer to
supply the exact physical normalized-variance secant at some interior time. -/
theorem h3Path_nearYoung_forces_globalHeat_Leray_secant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    ∃ r : ℝ, ∃ hr : r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
          (t - s) ≤
        (h3PathTopFourierGlobalDiffusionExcess244 hH3 hClass r
           ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ +
         h3PathTopFourierGlobalNonlinearExcess244 hH3 hClass r
           ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩) /
          (velocityH3Energy0At u r *
            h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_normalizedVariance_exists_exactSignedExcessSecant244
      hH3 hClass hs ht hst hMass hD
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  rw [h3Path_normalizedExcessRate_eq_globalHeat_add_Leray244
    hH3 hClass hrClass] at hRate
  have hYoung := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩)
    hK (hD t ⟨hst.le, le_refl t⟩) hNear
  refine ⟨r, hr, ?_⟩
  rw [hRate]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr hst)).2
  linarith only [hYoung]

end
end PrimeTensor.FirstMonomialTriad
