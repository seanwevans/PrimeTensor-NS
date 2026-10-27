import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceRadialTemporalClock244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralHighRadialIntegral244
import Mathlib.Tactic

/-!
# Canonical source maxima: genuine high-radial Fourier concentration

There are two distinct conclusions on the same canonical source-maximizing
physical time sequence.

(1) In the conditional critical-width PDE regime the weighted H³ spectral
state diverges at the selected source maxima. Physical kinetic monotonicity
bounds its weighted spectral mass inside every fixed radial ball. The actual
integrated spectral mass in the complement therefore diverges, WITHOUT a
source-exposure hypothesis.

(2) For a temporal difference, the FULL squared spectral mass splits exactly
into the weighted finite-radial difference defect and the integrated
complementary difference density. Vanishing canonical source exposure makes
the low-radial term vanish. If the spectral state is eventually bounded at
the original disjoint-window anchors, the complementary difference density
must diverge. All estimates refer to the SAME source maxima and anchors.

The spectral state is a Fin-3 product with the SUP norm, whereas the Fourier
square energy is the sum of the three squared coordinate norms: they are not
identified as equal. Only the valid inequality norm² <= total square energy
is used. This is spatial concentration, not yet a lower time-integrated H³
dissipation estimate or unconditional Navier--Stokes continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeCanonicalHighRadialTemporal244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The finite product of spectral components carries the SUP norm, not a
PiLp-2 norm. Its square is nonetheless bounded by the exact sum-of-squares
Fourier energy. -/
theorem h3Path_spectralSupNorm_sq_le_squareEnergy244
    (G : H3SpectralVelocityState) :
    ‖G‖ ^ 2 ≤ h3SpectralVelocitySquareEnergy G := by
  have hE : 0 ≤ h3SpectralVelocitySquareEnergy G := by
    unfold h3SpectralVelocitySquareEnergy
    positivity
  have hNorm : ‖G‖ ≤ Real.sqrt (h3SpectralVelocitySquareEnergy G) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro j
    have hj := h3Path_spectralCoordinateSquare_le_totalSquareEnergy244 G j
    have hSq : ‖G j‖ ^ 2 ≤
        (Real.sqrt (h3SpectralVelocitySquareEnergy G)) ^ 2 := by
      simpa only [Real.sq_sqrt hE] using hj
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 hSq
  have hSq := pow_le_pow_left₀ (norm_nonneg G) hNorm 2
  simpa only [Real.sq_sqrt hE] using hSq

/-- Genuine integrated high-frequency squared *temporal displacement*.
Unlike the preexisting high-radial remainder for an individual state, the
integrand here is the difference of the two physical spectral snapshots. -/
noncomputable def h3Path_spectralTemporalHighRadialIntegral244
    (ρ : ℝ) (G H : H3SpectralVelocityState) : ℝ :=
  ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity G H ξ
      ∂volume

/-- Exact sum-of-three-squares integral for the difference of two weighted
states. Fourier L² subtraction holds a.e.; no fixed-frequency evaluation
is invoked. -/
theorem h3Path_spectralDifference_squareEnergy_eq_integral244
    (G H : H3SpectralVelocityState) :
    h3SpectralVelocitySquareEnergy (G - H) =
      ∫ ξ : H3FourierPoint3,
        h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity G H ξ
        ∂volume := by
  rw [h3Path_spectralSquareEnergy_eq_totalFourierIntegral244]
  apply integral_congr_ae
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub (G 0) (H 0),
    MeasureTheory.Lp.coeFn_sub (G 1) (H 1),
    MeasureTheory.Lp.coeFn_sub (G 2) (H 2)
  ] with ξ h0 h1 h2
  simp only [h3TerminalSpectralStateSquareAmplitude,
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity,
    h3TerminalSpectralDifferenceAt, Pi.sub_apply, h0, h1, h2]

/-- Interchanging the two snapshots preserves the integrated radial
spectral square difference, since norms of Hilbert-space differences are
symmetric. -/
theorem h3Path_radialSpectralTemporalDefect_symm244
    (ρ : ℝ) (G H : H3SpectralVelocityState) :
    h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ G H =
      h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ H G := by
  unfold h3TerminalWeightedSpectralVelocityRadialSquareDefect
  apply integral_congr_ae
  filter_upwards with ξ
  change
    ‖(G 0) ξ - (H 0) ξ‖ ^ 2 +
      ‖(G 1) ξ - (H 1) ξ‖ ^ 2 +
      ‖(G 2) ξ - (H 2) ξ‖ ^ 2 =
    ‖(H 0) ξ - (G 0) ξ‖ ^ 2 +
      ‖(H 1) ξ - (G 1) ξ‖ ^ 2 +
      ‖(H 2) ξ - (G 2) ξ‖ ^ 2
  rw [norm_sub_rev ((H 0) ξ) ((G 0) ξ),
    norm_sub_rev ((H 1) ξ) ((G 1) ξ),
    norm_sub_rev ((H 2) ξ) ((G 2) ξ)]

/-- Exact low/high decomposition of the SQUARED temporal displacement.
The high term is a genuine complementary-frequency Fourier integral. -/
theorem h3Path_spectralTemporal_low_add_high_eq_total244
    (ρ : ℝ) (G H : H3SpectralVelocityState) :
    h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ G H +
      h3Path_spectralTemporalHighRadialIntegral244 ρ G H =
        h3SpectralVelocitySquareEnergy (G - H) := by
  have hPartition := setIntegral_compl
    (measurableSet_h3TerminalRadialFrequencyBelow ρ)
    (h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_integrable G H)
  dsimp only [h3TerminalWeightedSpectralVelocityRadialSquareDefect,
    h3Path_spectralTemporalHighRadialIntegral244]
  rw [h3Path_spectralDifference_squareEnergy_eq_integral244]
  linarith only [hPartition]

/-- Complementary temporal spectral mass is nonnegative, being the actual
integral of a sum of three squared L² differences. -/
theorem h3Path_spectralTemporalHighRadialIntegral_nonneg244
    (ρ : ℝ) (G H : H3SpectralVelocityState) :
    0 ≤ h3Path_spectralTemporalHighRadialIntegral244 ρ G H := by
  unfold h3Path_spectralTemporalHighRadialIntegral244
  exact integral_nonneg (fun ξ =>
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_nonneg G H ξ)

/-- Divergent full spectral displacement plus an EVENTUAL finite-radial
square-defect ceiling forces divergence of the ACTUAL complementary Fourier
square-difference integral. The needed norm/energy comparison is valid for
the sup-norm spectral product. -/
theorem h3Path_spectralEscape_boundedLow_forces_highTemporalIntegral244
    (G H : ℕ → H3SpectralVelocityState) (ρ E : ℝ)
    (hEscape : Tendsto (fun k : ℕ => ‖G k - H k‖) atTop atTop)
    (hLow : ∀ᶠ k : ℕ in atTop,
      h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ (G k) (H k) ≤ E) :
    Tendsto (fun k : ℕ =>
      h3Path_spectralTemporalHighRadialIntegral244 ρ (G k) (H k))
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop,
      max (M + E + 1) 1 ≤ ‖G k - H k‖ :=
    hEscape.eventually (eventually_ge_atTop (max (M + E + 1) 1))
  filter_upwards [hLarge, hLow] with k hk hL
  have hOne : 1 ≤ ‖G k - H k‖ :=
    (le_max_right _ _).trans hk
  have hBig : M + E + 1 ≤ ‖G k - H k‖ :=
    (le_max_left _ _).trans hk
  have hPow : ‖G k - H k‖ ≤ ‖G k - H k‖ ^ 2 := by
    nlinarith only [hOne, sq_nonneg (‖G k - H k‖ - 1)]
  have hEnergy := h3Path_spectralSupNorm_sq_le_squareEnergy244
    (G k - H k)
  have hSplit := h3Path_spectralTemporal_low_add_high_eq_total244
    ρ (G k) (H k)
  linarith only [hBig, hPow, hEnergy, hSplit, hL]

/-- Vanishing low-radial temporal defect supplies the uniform upper bound
required by the preceding exact high-frequency escape theorem. -/
theorem h3Path_spectralEscape_lowVanish_forces_highTemporalIntegral244
    (G H : ℕ → H3SpectralVelocityState) (ρ : ℝ)
    (hEscape : Tendsto (fun k : ℕ => ‖G k - H k‖) atTop atTop)
    (hLow : Tendsto (fun k : ℕ =>
      h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ (G k) (H k))
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k : ℕ =>
      h3Path_spectralTemporalHighRadialIntegral244 ρ (G k) (H k))
      atTop atTop := by
  have hEventually : ∀ᶠ k : ℕ in atTop,
      h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ (G k) (H k) ≤ 1 := by
    have hSmall := (tendsto_order.1 hLow).2 (1 : ℝ) (by norm_num)
    filter_upwards [hSmall] with k hk
    exact hk.le
  exact h3Path_spectralEscape_boundedLow_forces_highTemporalIntegral244
    G H ρ 1 hEscape hEventually

/-- Divergence of spectral SUP norm and a uniform low-radial mass ceiling
force divergence of the integrated HIGH-radial mass of one actual state. -/
theorem h3Path_spectralNormEscape_boundedLow_forces_highMass244
    (G : ℕ → H3SpectralVelocityState) (ρ E : ℝ)
    (hEscape : Tendsto (fun k : ℕ => ‖G k‖) atTop atTop)
    (hLow : ∀ᶠ k : ℕ in atTop,
      h3PathActualSpectralLowRadialSquareMass244 ρ (G k) ≤ E) :
    Tendsto (fun k : ℕ =>
      h3PathActualSpectralHighRadialRemainder244 ρ (G k))
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop,
      max (M + E + 1) 1 ≤ ‖G k‖ :=
    hEscape.eventually (eventually_ge_atTop (max (M + E + 1) 1))
  filter_upwards [hLarge, hLow] with k hk hL
  have hOne : 1 ≤ ‖G k‖ := (le_max_right _ _).trans hk
  have hBig : M + E + 1 ≤ ‖G k‖ := (le_max_left _ _).trans hk
  have hPow : ‖G k‖ ≤ ‖G k‖ ^ 2 := by
    nlinarith only [hOne, sq_nonneg (‖G k‖ - 1)]
  have hEnergy := h3Path_spectralSupNorm_sq_le_squareEnergy244 (G k)
  dsimp only [h3PathActualSpectralHighRadialRemainder244]
  linarith only [hBig, hPow, hEnergy, hL]

/-- The same exact canonical maximizing-time sequence exhibits growing
ACTUAL high-frequency H³ Fourier mass for every fixed radius, without any
vanishing-source-exposure premise. If source exposure ALSO vanishes and the
original disjoint-window anchors have bounded spectral norm, the high-
frequency *temporal difference* integral diverges on this same sequence. -/
theorem h3Path_noL2Trace_canonicalWidth_highRadialPeaksAndTemporal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ ρ : ℝ, 0 ≤ ρ → ∀ k : ℕ,
        h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
          (h3AuditActualSpectralVelocityTotal hH3 (s k)) ≤
        (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
          (C (v k) * ((T - τ (v k)) / 2)) ^ 2) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        (∀ ρ : ℝ, 0 ≤ ρ →
          Tendsto (fun k : ℕ =>
            ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
              h3TerminalSpectralStateSquareAmplitude
                (h3AuditActualSpectralVelocityTotal hH3 (s k)) ξ ∂volume)
            atTop atTop) ∧
        (∀ ρ : ℝ, 0 ≤ ρ →
          Tendsto (fun k : ℕ => C (v k) * ((T - τ (v k)) / 2))
            atTop (𝓝 (0 : ℝ)) →
          ∀ E : ℝ,
          (∀ᶠ k : ℕ in atTop,
            ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ≤ E) →
          Tendsto (fun k : ℕ =>
            h3Path_spectralTemporalHighRadialIntegral244 ρ
              (h3AuditActualSpectralVelocityTotal hH3 (s k))
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
            atTop atTop)) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hMass hNoTrace hDInt
  have hAT : a < T := lt_trans (hTime 0).1 (hTime 0).2
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [hAT]
  have hLate : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hCofinal.eventually (Ioi_mem_nhds hb.2)
  have hτAbs (k : ℕ) : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (hTime (v k)).1,
      (hTime (v k)).2⟩
  have hsAbs (k : ℕ) : s k ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · exact lt_of_lt_of_le
        (hτAbs k).1 (hPeak k).1.1
    · have hEnd : τ (v k) + (T - τ (v k)) / 2 < T := by
        have ht := (hTime (v k)).2
        linarith only [ht]
      exact lt_of_le_of_lt (hPeak k).1.2 hEnd
  have hRadial (ρ : ℝ) (hρ : 0 ≤ ρ) (k : ℕ) :
      h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
        (h3AuditActualSpectralVelocityTotal hH3 (s k)) ≤
      (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
        (C (v k) * ((T - τ (v k)) / 2)) ^ 2 := by
    have hBound := h3Path_canonicalSourceHalfTerminal_radialExposure_le244
      hH3 (τ (v k)) (hτAbs k) (s k) (hPeak k).1 ρ hρ
    simpa only [← (hCanonical k).2] using hBound
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, hRadial, ?_⟩
  intro η B D hη hB hD hRegime
  have hSpectral : Tendsto (fun k : ℕ =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop :=
    (hJoint η B D hη hB hD hRegime).2
  constructor
  · intro ρ hρ
    have hLow : ∀ᶠ k : ℕ in atTop,
        h3PathActualSpectralLowRadialSquareMass244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 (s k)) ≤
        h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b := by
      filter_upwards [hLate] with k hk
      exact h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
        hH3 hClass b hb ρ hρ (s k)
        ⟨lt_of_lt_of_le hk (hPeak k).1.1, (hsAbs k).2⟩
    have hHigh := h3Path_spectralNormEscape_boundedLow_forces_highMass244
      (fun k => h3AuditActualSpectralVelocityTotal hH3 (s k))
      ρ (h3TerminalRadialSobolevWeightSquareCeiling ρ *
        velocityH3Energy0At u b) hSpectral hLow
    simpa only [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
      using hHigh
  · intro ρ hρ hFast E hAnchor
    let peak : ℕ → H3SpectralVelocityState := fun k =>
      h3AuditActualSpectralVelocityTotal hH3 (s k)
    let anchor : ℕ → H3SpectralVelocityState := fun k =>
      h3AuditActualSpectralVelocityTotal hH3 (τ (v k))
    have hAnchor' : ∀ᶠ k : ℕ in atTop, ‖anchor k‖ ≤ E := by
      simpa only [anchor] using hAnchor
    have hDifference : Tendsto (fun k : ℕ => ‖peak k - anchor k‖)
        atTop atTop :=
      h3Path_boundedSpectralAnchor_forces_displacementEscape244
        peak anchor (by simpa only [peak] using hSpectral) E hAnchor'
    have hEq : (fun k : ℕ =>
        h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) *
            ((T - τ (v k)) / 2)) =
        (fun k : ℕ => C (v k) * ((T - τ (v k)) / 2)) := by
      funext k
      rw [← (hCanonical k).2]
    have hFast' : Tendsto (fun k : ℕ =>
        h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) *
            ((T - τ (v k)) / 2)) atTop (𝓝 (0 : ℝ)) := by
      rw [hEq]
      exact hFast
    have hLow := h3Path_canonicalHalfTerminal_radialDefect_tendsto_zero244
      hH3 (fun k => τ (v k)) s hτAbs
      (fun k => (hPeak k).1) ρ hρ hFast'
    have hLow' : Tendsto (fun k : ℕ =>
        h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
          (peak k) (anchor k)) atTop (𝓝 (0 : ℝ)) := by
      have hSwap : (fun k : ℕ =>
          h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
            (peak k) (anchor k)) =
          (fun k : ℕ =>
          h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
            (anchor k) (peak k)) := by
        funext k
        exact h3Path_radialSpectralTemporalDefect_symm244 ρ
          (peak k) (anchor k)
      rw [hSwap]
      simpa only [peak, anchor] using hLow
    exact h3Path_spectralEscape_lowVanish_forces_highTemporalIntegral244
      peak anchor ρ hDifference hLow'

end
end PrimeTensor.FirstMonomialTriad
