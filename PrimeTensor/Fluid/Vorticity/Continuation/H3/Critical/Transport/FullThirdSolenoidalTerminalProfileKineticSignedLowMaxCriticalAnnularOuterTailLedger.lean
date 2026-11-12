import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungGapL2Integrability
import Mathlib.Tactic

/-!
# Actual sharp-annulus Young-gap ledger with its uncompensated outer tail

The actual sharp highpass above rho splits into the finite annulus
rho <= 2*pi*|xi| < sigma and the outer tail 2*pi*|xi| >= sigma.
The accepted q-cubic Young-gap theorem pays the constant-rate error on
that finite annulus; its outer-tail error remains EXACTLY on the right.
Neither a moving-radius bound nor a terminal estimate is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularOuterTailLedger244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularOuterTailLedger244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The genuine radial highpass is the disjoint union of a bounded
annulus and its outer tail, provided the radii are ordered. -/
theorem thirdFullKinetic_sharpRadialHighpass_annulusOuter_partition244
    (rho sigma : ℝ) (hOrder : rho ≤ sigma) :
    (h3TerminalRadialFrequencyBelow rho)ᶜ =
      (((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
        h3TerminalRadialFrequencyBelow sigma) ∪
      (h3TerminalRadialFrequencyBelow sigma)ᶜ := by
  have hSubset : h3TerminalRadialFrequencyBelow rho ⊆
      h3TerminalRadialFrequencyBelow sigma := by
    intro ξ hξ
    change h3FourierGradientMagnitude ξ < rho at hξ
    change h3FourierGradientMagnitude ξ < sigma
    exact lt_of_lt_of_le hξ hOrder
  ext ξ
  constructor
  · intro hOutside
    by_cases hSigma : ξ ∈ h3TerminalRadialFrequencyBelow sigma
    · exact Or.inl ⟨hOutside, hSigma⟩
    · exact Or.inr hSigma
  · intro hEither
    rcases hEither with hAnn | hTail
    · exact hAnn.1
    · intro hInside
      exact hTail (hSubset hInside)

/-- The two terms in the partition do not overlap. -/
theorem thirdFullKinetic_sharpRadialAnnulus_outer_disjoint244
    (rho sigma : ℝ) :
    Disjoint
      (((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
        h3TerminalRadialFrequencyBelow sigma)
      ((h3TerminalRadialFrequencyBelow sigma)ᶜ) := by
  apply Set.disjoint_left.mpr
  intro ξ hAnn hTail
  exact hTail hAnn.2

/-- The physical square-gradient frequency on the actual annulus lies
between the squares of its two gradient-frequency radii. -/
theorem thirdFullKinetic_sharpRadialAnnulus_qBand244
    (rho sigma : ℝ) (hRho : 0 ≤ rho)
    (ξ : H3FourierPoint3)
    (hξ : ξ ∈ ((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
      h3TerminalRadialFrequencyBelow sigma) :
    rho ^ 2 ≤ h3FourierGradientSquare ξ ∧
      h3FourierGradientSquare ξ ≤ sigma ^ 2 := by
  have hLower : rho ≤ h3FourierGradientMagnitude ξ := by
    have hx : ¬ h3FourierGradientMagnitude ξ < rho := hξ.1
    exact le_of_not_gt hx
  have hUpper : h3FourierGradientMagnitude ξ ≤ sigma :=
    (show h3FourierGradientMagnitude ξ < sigma from hξ.2).le
  have hMag : 0 ≤ h3FourierGradientMagnitude ξ :=
    h3FourierGradientMagnitude_nonneg ξ
  have hSquare : h3FourierGradientSquare ξ =
      h3FourierGradientMagnitude ξ ^ 2 := by
    dsimp only [h3FourierGradientSquare, h3FourierGradientMagnitude]
    ring
  rw [hSquare]
  exact ⟨pow_le_pow_left₀ hRho hLower 2,
    pow_le_pow_left₀ hMag hUpper 2⟩

/-- For the ACTUAL physical Navier--Stokes Fourier momentum source, the
unweighted highpass constant-rate mismatch has an exact finite-annulus
plus outer-tail partition. The finite annulus is paid by the q-cubic
Young-gap, while the outer tail is kept as an explicit, nonnegative cost.
The time is a genuine strict H3 physical time. -/
theorem thirdFullPhysical_actualHighpass_YoungGap_outerTailLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) (rho sigma : ℝ)
    (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) :
    let ann : Set H3FourierPoint3 :=
      ((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
        h3TerminalRadialFrequencyBelow sigma
    let rate : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    let R := (h3CriticalActualProjectedFourierSource hH3 j t :
      H3FourierPoint3 → ℂ)
    let Z := h3SpectralScalarRawFourierL2
      ((h3AuditActualSpectralVelocityTotal hH3 t) j)
    let N := h3RawFinLerayOuterProductDivergence
      (h3AuditActualSpectralVelocityTotal hH3 t)
      (h3AuditActualSpectralVelocityTotal hH3 t) j
    (rho ^ 2) ^ 3 *
      (∫ ξ in (h3TerminalRadialFrequencyBelow rho)ᶜ,
        ‖R ξ - (rate : ℂ) * Z ξ‖ ^ 2 ∂volume) ≤
      2 * (∫ ξ in ann,
        h3FourierGradientSquare ξ ^ 3 *
          ‖N ξ + 2 * ((h3FourierGradientSquare ξ : ℂ) * Z ξ)‖ ^ 2
          ∂volume) +
      (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
        (∫ ξ in ann, ‖Z ξ‖ ^ 2 ∂volume) +
      (rho ^ 2) ^ 3 *
        (∫ ξ in (h3TerminalRadialFrequencyBelow sigma)ᶜ,
          ‖R ξ - (rate : ℂ) * Z ξ‖ ^ 2 ∂volume) := by
  dsimp only
  let ann : Set H3FourierPoint3 :=
    ((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
      h3TerminalRadialFrequencyBelow sigma
  let tail : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow sigma)ᶜ
  let high : Set H3FourierPoint3 :=
    (h3TerminalRadialFrequencyBelow rho)ᶜ
  let R : H3FourierComplexL2 :=
    h3CriticalActualProjectedFourierSource hH3 j t
  let Z : H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2
      ((h3AuditActualSpectralVelocityTotal hH3 t) j)
  let rate : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let E : H3FourierComplexL2 := R - (rate : ℂ) • Z
  let e : H3FourierPoint3 → ℝ := fun ξ =>
    ‖(R : H3FourierPoint3 → ℂ) ξ -
      (rate : ℂ) * (Z : H3FourierPoint3 → ℂ) ξ‖ ^ 2
  have hEInt : Integrable e (volume : Measure H3FourierPoint3) := by
    have hBase : Integrable
        (fun ξ : H3FourierPoint3 => ‖(E : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
      (MeasureTheory.Lp.memLp E).integrable_norm_pow (by norm_num)
    apply hBase.congr
    filter_upwards [MeasureTheory.Lp.coeFn_sub R ((rate : ℂ) • Z),
      MeasureTheory.Lp.coeFn_smul (rate : ℂ) Z] with ξ hSub hSmul
    dsimp only [E, e]
    rw [hSub]
    simp only [Pi.sub_apply]
    rw [hSmul]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hDisj : Disjoint ann tail :=
    thirdFullKinetic_sharpRadialAnnulus_outer_disjoint244 rho sigma
  have hAnn : MeasurableSet ann :=
    (measurableSet_h3TerminalRadialFrequencyBelow rho).compl.inter
      (measurableSet_h3TerminalRadialFrequencyBelow sigma)
  have hTail : MeasurableSet tail :=
    (measurableSet_h3TerminalRadialFrequencyBelow sigma).compl
  have hUnion : high = ann ∪ tail :=
    thirdFullKinetic_sharpRadialHighpass_annulusOuter_partition244
      rho sigma hOrder
  have hSplit : (∫ ξ in high, e ξ ∂volume) =
      (∫ ξ in ann, e ξ ∂volume) +
        (∫ ξ in tail, e ξ ∂volume) := by
    rw [hUnion]
    exact setIntegral_union (s := ann) (t := tail)
      hDisj hTail hEInt.integrableOn hEInt.integrableOn
  have hBand : ∀ ξ ∈ ann,
      rho ^ 2 ≤ h3FourierGradientSquare ξ ∧
        h3FourierGradientSquare ξ ≤ sigma ^ 2 := by
    intro ξ hξ
    exact thirdFullKinetic_sharpRadialAnnulus_qBand244
      rho sigma hRho ξ hξ
  have hAnnular :=
    thirdFullPhysical_actualAnnularYoungGap_integral_auto244
      hH3 t ht j (rho ^ 2) (sigma ^ 2) (sq_nonneg rho)
      ann hAnn hBand
  change (rho ^ 2) ^ 3 * (∫ ξ in high, e ξ ∂volume) ≤
    2 * (∫ ξ in ann,
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 t) j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ)‖ ^ 2
        ∂volume) +
    (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
      (∫ ξ in ann,
        ‖h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2
        ∂volume) +
    (rho ^ 2) ^ 3 * (∫ ξ in tail, e ξ ∂volume)
  rw [hSplit]
  nlinarith only [hAnnular]

/-- The same exact outer-tail accounting holds after summing all three
physical solenoidal coordinates. This is the scalar Fourier ledger summed
on the ACTUAL vector state, not a synthetic vector field. -/
theorem thirdFullPhysical_actualThreeAxisHighpass_YoungGap_outerTailLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) :
    let ann : Set H3FourierPoint3 :=
      ((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
        h3TerminalRadialFrequencyBelow sigma
    let rate : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    let U : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 t
    (rho ^ 2) ^ 3 *
      (∑ j : Fin 3, ∫ ξ in (h3TerminalRadialFrequencyBelow rho)ᶜ,
        ‖(h3CriticalActualProjectedFourierSource hH3 j t :
          H3FourierPoint3 → ℂ) ξ -
          (rate : ℂ) * h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
        ∂volume) ≤
      2 * (∑ j : Fin 3, ∫ ξ in ann,
        h3FourierGradientSquare ξ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U j ξ +
            2 * ((h3FourierGradientSquare ξ : ℂ) *
              h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) +
      (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
        (∑ j : Fin 3, ∫ ξ in ann,
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) +
      (rho ^ 2) ^ 3 *
        (∑ j : Fin 3, ∫ ξ in (h3TerminalRadialFrequencyBelow sigma)ᶜ,
          ‖(h3CriticalActualProjectedFourierSource hH3 j t :
            H3FourierPoint3 → ℂ) ξ -
            (rate : ℂ) * h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2
          ∂volume) := by
  dsimp only
  let ann : Set H3FourierPoint3 :=
    ((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
      h3TerminalRadialFrequencyBelow sigma
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let rate : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let A : Fin 3 → ℝ := fun j =>
    ∫ ξ in (h3TerminalRadialFrequencyBelow rho)ᶜ,
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
        H3FourierPoint3 → ℂ) ξ -
        (rate : ℂ) * h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume
  let B : Fin 3 → ℝ := fun j =>
    ∫ ξ in ann,
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence U U j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume
  let C : Fin 3 → ℝ := fun j =>
    ∫ ξ in ann, ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume
  let D : Fin 3 → ℝ := fun j =>
    ∫ ξ in (h3TerminalRadialFrequencyBelow sigma)ᶜ,
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
        H3FourierPoint3 → ℂ) ξ -
        (rate : ℂ) * h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume
  have hEach (j : Fin 3) :
      (rho ^ 2) ^ 3 * A j ≤
        2 * B j +
          (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) * C j +
          (rho ^ 2) ^ 3 * D j := by
    simpa only [A, B, C, D, U, rate, ann] using
      (thirdFullPhysical_actualHighpass_YoungGap_outerTailLedger244
        hH3 t ht j rho sigma hRho hOrder)
  have hSum := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin 3) _ => hEach j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hSum
  simpa only [A, B, C, D, U, rate, ann, add_assoc] using hSum

end
end PrimeTensor.FirstMonomialTriad
