import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxViscousGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileAnchoredPDEClock
import Mathlib.Tactic

/-!
# Adverse signed sixth flux: PDE-certified finite-annulus viscous persistence

The signed low-maximum flux viscous gate singles out one of two ORIGINAL
observation times. Here the high-radial Fourier norm at that exact time pays
actual HIGH-RADIAL physical H3 dissipation, not only full dissipation.

The preexisting anchored finite-annulus PDE theorem then supplies a positive,
explicitly selected forward time width and a genuine integrated physical
annular dissipation cost. The height is chosen unconditionally, with its
cubic recovery-amplitude coefficient retained in the denominator.

The forward interval may extend past the ORIGINAL kinetic gap's right
endpoint. It is not asserted to lie in a previously selected disjoint window.
No lower bound uniform in moving cutoffs or terminal time is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev WA3 := PrimeTensor.Axis Depth.three
private abbrev WV3 := H3FourierPoint3

noncomputable local instance axisFintypeKineticSignedPDEWindow244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A strictly positive, explicitly calibrated annular viscous height.
The `1` in the denominator prevents any division by a possibly zero flux
amplitude coefficient. The cutoff and cubic amplitude are not discarded. -/
noncomputable def thirdFullKineticSignedLowMaxPDEViscousHeight244
    (R : ℕ) (V W : H3SpectralVelocityState) (η : ℝ) : ℝ :=
  (((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2) /
    (2 * ((thirdFullKineticSignedLowMaxFluxClockWeight244 R V W) ^ 2 + 1))

/-- The chosen height is positive and strictly below the signed flux
quadratic high-radial charge after multiplying by the amplitude square. -/
theorem thirdFullKineticSignedLowMaxPDEViscousHeight_budget244
    (R : ℕ) (V W : H3SpectralVelocityState)
    (η : ℝ) (hη : 0 < η) :
    0 < thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η ∧
    (thirdFullKineticSignedLowMaxFluxClockWeight244 R V W) ^ 2 *
        thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η <
      ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 := by
  let A : ℝ := thirdFullKineticSignedLowMaxFluxClockWeight244 R V W
  let Q : ℝ := ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  have hDen : 0 < 2 * (A ^ 2 + 1) := by positivity
  have hRatio : A ^ 2 / (2 * (A ^ 2 + 1)) < 1 := by
    apply (div_lt_iff₀ hDen).mpr
    nlinarith only [sq_nonneg A]
  constructor
  · change 0 < Q / (2 * (A ^ 2 + 1))
    exact div_pos hQ hDen
  · change A ^ 2 * (Q / (2 * (A ^ 2 + 1))) < Q
    calc
      A ^ 2 * (Q / (2 * (A ^ 2 + 1))) =
          (A ^ 2 / (2 * (A ^ 2 + 1))) * Q := by ring
      _ < 1 * Q := mul_lt_mul_of_pos_right hRatio hQ
      _ = Q := one_mul Q

/-- The positive-width, PDE-certified annular window attached to a
particular ACTUAL strict physical time. The same cutoff, anchor, source
ceiling, width formula and integrated charge all refer to this one time. -/
def ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (H z : ℝ) : Prop :=
  ∃ (N : ℕ) (K C δ : ℝ),
    R ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ z + δ < T ∧
    (∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 z) j‖ ≤ K) ∧
    (∀ r : ℝ, r ∈ Set.Icc z (z + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) ∧
    (H / 2 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 z) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 z)) ∧
    (δ = thirdFullProfileAnchoredPDEWidth244 hH3 z R N K C H) ∧
    (∀ r : ℝ, r ∈ Set.Icc z (z + δ) →
      H / 4 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
    δ * (H / 4) ≤
      ∫ r in z..(z + δ),
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r)

/-- The signed LOW-MAX high-tail charge upgrades to a STRICTLY POSITIVE
physical high-radial viscous height at the SAME actual observation time.
No pointwise continuity of the full viscous density is used. -/
private theorem thirdFullKinetic_signedLowMax_tail_to_highViscousHeight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo a T)
    (η A H : ℝ) (hη : 0 < η)
    (hBudget : A ^ 2 * H < ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2)
    (hTail : η / 4 ≤ A *
      ‖thirdFullSpectralVelocityHighRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 z)‖) :
    H < h3PathActualHighRadialDissipation244 ((R : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 z) := by
  let U := h3AuditActualSpectralVelocityTotal hH3 z
  let P := thirdFullSpectralVelocityHighRadialApply244 R U
  have hApos : 0 < A := by
    by_contra hn
    have hAle : A ≤ 0 := le_of_not_gt hn
    have hProd : A * ‖P‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hAle (norm_nonneg P)
    change η / 4 ≤ A * ‖P‖ at hTail
    linarith only [hProd, hTail, hη]
  have hTailSq : (η / 4) ^ 2 ≤ (A * ‖P‖) ^ 2 :=
    (sq_le_sq₀ (by positivity : 0 ≤ η / 4)
      (mul_nonneg hApos.le (norm_nonneg P))).mpr hTail
  have hViscous := thirdFullPhysical_highRadialViscousCoercivity244
    hH3 hClass z hz R
  have hCharge : ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
      A ^ 2 * h3PathActualHighRadialDissipation244 ((R : ℝ) + 1) U := by
    calc
      ((R : ℝ) + 1) ^ 2 * (η / 4) ^ 2 ≤
          ((R : ℝ) + 1) ^ 2 * (A * ‖P‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hTailSq (sq_nonneg _)
      _ = A ^ 2 * (((R : ℝ) + 1) ^ 2 * ‖P‖ ^ 2) := by ring
      _ ≤ A ^ 2 * h3PathActualHighRadialDissipation244
          ((R : ℝ) + 1) U :=
        mul_le_mul_of_nonneg_left hViscous (sq_nonneg A)
  have hScaled : A ^ 2 * H < A ^ 2 *
      h3PathActualHighRadialDissipation244 ((R : ℝ) + 1) U :=
    lt_of_lt_of_le hBudget hCharge
  exact lt_of_mul_lt_mul_left hScaled (sq_nonneg A)

/-- An actual positive high-radial physical viscous height carries the
preexisting physical-PDE-certified finite-annulus persistence, including
its EXACT chosen width and real integrated annular charge. -/
theorem thirdFullPhysical_highRadialHeight_to_signedCertifiedWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (z : ℝ) (hz : z ∈ Set.Ioo a T) (R : ℕ)
    (H : ℝ) (hH : 0 < H)
    (hHigh : H < h3PathActualHighRadialDissipation244 ((R : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 z)) :
    ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244 hH3 R H z := by
  obtain ⟨N, K, C, δ, hnN, hK, hC, hδ, hδone, hEnd,
    hState, hSource, hHalf, hWidth, _hVariation, hFloor, hCost⟩ :=
    thirdFullPhysical_highRadialSnapshot_profileAnchoredPDEClock244
      hH3 hClass z hz R H hH hHigh
  exact ⟨N, K, C, δ, hnN, hK, hC, hδ, hδone, hEnd,
    hState, hSource, hHalf, hWidth, hFloor, hCost⟩

/-- A signed imaginary LowMax(R) excursion at two actual times in a strict
physical gap has a CERTIFIED physical alternative: either the correctly
weighted recovery + projected-source clock pays half the excursion, or ONE
of those SAME observation times anchors a genuine positive-width annular
H3 viscous window with its own integrated charge.

The positive annular height is the explicit `...PDEViscousHeight244` and
is valid even when the cubic flux Lipschitz weight vanishes. No disjointness
or inclusion of the new forward window in the original gap is asserted. -/
theorem thirdFullPhysical_strictGap_signedLowMax_clockOrPDEAnnularWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (v w : WA3 → SchwartzMap WV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : WA3,
      (V (h3ClassicalizationFinOfAxis j) : WV3 → ℂ) =ᵐ[volume]
        (fun ξ : WV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : WA3,
      (W (h3ClassicalizationFinOfAxis j) : WV3 → ℂ) =ᵐ[volume]
        (fun ξ : WV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (η : ℝ) (hη : 0 < η)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|) :
    η / 2 < thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
        thirdFullFiniteBandH3WeightCeiling244 R *
          (∫ r in x..y,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖) ∨
    ∃ z : ℝ, (z = t ∨ z = s) ∧
      ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244 hH3 R
        (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η) z := by
  let A : ℝ := thirdFullKineticSignedLowMaxFluxClockWeight244 R V W
  let H : ℝ := thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η
  let E : ℝ :=
    ‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
      thirdFullFiniteBandH3WeightCeiling244 R *
        (∫ r in x..y,
          ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
      ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖
  obtain ⟨hH, hBudget⟩ :=
    thirdFullKineticSignedLowMaxPDEViscousHeight_budget244 R V W η hη
  have hx0 : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hx.1, hx.2⟩
  have hy0 : y ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hy.1, hy.2⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  by_cases hSmall : A * E ≤ η / 2
  · right
    have hTail := thirdFullPhysical_strictGap_signedLowMax_oneHighTail244
      hH3 R x y hx0 hy0 hxy s t hs ht v w V W hv hw
      η hη hAdverse (by simpa only [A, E] using hSmall)
    rcases hTail with hAtT | hAtS
    · refine ⟨t, Or.inl rfl, ?_⟩
      have hHigh : H < h3PathActualHighRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) :=
        thirdFullKinetic_signedLowMax_tail_to_highViscousHeight244
          hH3 hClass R t htClass η A H hη hBudget
          (by simpa only [A] using hAtT)
      exact thirdFullPhysical_highRadialHeight_to_signedCertifiedWindow244
        hH3 hClass t htClass R H hH hHigh
    · refine ⟨s, Or.inr rfl, ?_⟩
      have hHigh : H < h3PathActualHighRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) :=
        thirdFullKinetic_signedLowMax_tail_to_highViscousHeight244
          hH3 hClass R s hsClass η A H hη hBudget
          (by simpa only [A] using hAtS)
      exact thirdFullPhysical_highRadialHeight_to_signedCertifiedWindow244
        hH3 hClass s hsClass R H hH hHigh
  · left
    change η / 2 < A * E
    exact lt_of_not_ge hSmall

end
end PrimeTensor.FirstMonomialTriad
