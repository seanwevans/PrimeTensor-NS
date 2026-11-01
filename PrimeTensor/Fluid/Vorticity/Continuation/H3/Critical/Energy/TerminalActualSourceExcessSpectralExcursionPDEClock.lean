import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAnchorExcursionContinuityRadius
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFourierTransfer244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDropHighRadialTemporalTransfer
import Mathlib.Tactic

/-!
# Fivefold H³ source peaks: the genuine PDE finite-band excursion budget

Strong continuity alone gives no quantitative terminal-scale temporal rate.
The existing *physical* momentum FTC, however, gives a quadratic clock at
any fixed Fourier radius. We combine this with the exact low/high spectral
square-energy decomposition on the SAME selected fivefold source windows.

A large full spectral excursion must pay either a finite-frequency PDE
source-clock cost or a positive high-frequency spectral-temporal difference.
The spectral anchor, physical source anchor/excursion, Riccati, compression,
cutoff, viscosity and source-floor alternatives are never discarded.
Nothing bounds the high-radial remainder uniformly toward terminal time.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A genuine full H³ spectral excursion, measured between two physical
strict-time observations, has an exact low-band PDE clock plus high-radial
spectral-temporal cost. The coefficient C is an actual source ceiling on the
original physical window, not a spectral time-Lipschitz assumption. -/
theorem h3Critical_actualSpectralExcursion_lowPDEPlusHighRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R x w s C ε : ℝ)
    (hR : 0 ≤ R) (hx : 0 < x) (hw : 0 < w) (hEnd : x + w < T)
    (hs : s ∈ Set.Icc x (x + w)) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hSource : ∀ r : ℝ, r ∈ Set.Icc x (x + w) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hExc : ε ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s -
        h3AuditActualSpectralVelocityTotal hH3 x‖) :
    ε ^ 2 ≤
      (3 * h3TerminalRadialSobolevWeightSquareCeiling R) * (C * w) ^ 2 +
      h3Path_spectralTemporalHighRadialIntegral244 R
        (h3AuditActualSpectralVelocityTotal hH3 x)
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 x
  let V : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 s
  have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hx, lt_of_le_of_lt (le_add_of_nonneg_right hw.le) hEnd⟩
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hx hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hSourceShort : ∀ r : ℝ, r ∈ Set.Icc x s →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C := by
    intro r hr
    exact hSource r ⟨hr.1, le_trans hr.2 hs.2⟩
  have hLow : h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V ≤
      (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
        (C * (s - x)) ^ 2 :=
    h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244
      hH3 R hR x s C hxAbs hsAbs hs.1 hSourceShort
  have hDeltanonneg : 0 ≤ s - x := sub_nonneg.mpr hs.1
  have hDeltale : s - x ≤ w := by linarith only [hs.2]
  have hCw : C * (s - x) ≤ C * w :=
    mul_le_mul_of_nonneg_left hDeltale hC
  have hCS : 0 ≤ C * (s - x) := mul_nonneg hC hDeltanonneg
  have hSq : (C * (s - x)) ^ 2 ≤ (C * w) ^ 2 :=
    pow_le_pow_left₀ hCS hCw 2
  have hCoeff : 0 ≤ 3 * h3TerminalRadialSobolevWeightSquareCeiling R :=
    mul_nonneg (by norm_num) (h3TerminalRadialSobolevWeightSquareCeiling_pos R).le
  have hLowW : h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V ≤
      (3 * h3TerminalRadialSobolevWeightSquareCeiling R) * (C * w) ^ 2 :=
    hLow.trans (mul_le_mul_of_nonneg_left hSq hCoeff)
  have hNorm : ε ≤ ‖U - V‖ := by
    simpa only [U, V, norm_sub_rev] using hExc
  have hNormSq : ε ^ 2 ≤ ‖U - V‖ ^ 2 :=
    pow_le_pow_left₀ hε hNorm 2
  have hSplit : ‖U - V‖ ^ 2 ≤
      h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V +
        h3Path_spectralTemporalHighRadialIntegral244 R U V := by
    rw [h3Path_spectralTemporal_low_add_high_eq_total244]
    exact h3Path_spectralSupNorm_sq_le_squareEnergy244 (U - V)
  calc
    ε ^ 2 ≤ ‖U - V‖ ^ 2 := hNormSq
    _ ≤ h3TerminalWeightedSpectralVelocityRadialSquareDefect R U V +
        h3Path_spectralTemporalHighRadialIntegral244 R U V := hSplit
    _ ≤ (3 * h3TerminalRadialSobolevWeightSquareCeiling R) * (C * w) ^ 2 +
        h3Path_spectralTemporalHighRadialIntegral244 R U V :=
      add_le_add_left hLowW _

/-- If a positive full-state excursion cannot be covered by twice the
finite-band physical PDE clock, more than half its squared threshold must
be carried by genuinely high-frequency temporal spectral mass. -/
theorem h3Critical_actualSpectralExcursion_PDEClockOrHighRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R x w s C ε : ℝ)
    (hR : 0 ≤ R) (hx : 0 < x) (hw : 0 < w) (hEnd : x + w < T)
    (hs : s ∈ Set.Icc x (x + w)) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hSource : ∀ r : ℝ, r ∈ Set.Icc x (x + w) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hExc : ε ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s -
        h3AuditActualSpectralVelocityTotal hH3 x‖) :
    ε ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
        (C * w) ^ 2 ∨
    ε ^ 2 < 2 * h3Path_spectralTemporalHighRadialIntegral244 R
      (h3AuditActualSpectralVelocityTotal hH3 x)
      (h3AuditActualSpectralVelocityTotal hH3 s) := by
  have hBudget := h3Critical_actualSpectralExcursion_lowPDEPlusHighRadial
    hH3 R x w s C ε hR hx hw hEnd hs hC hε hSource hExc
  by_cases hClock : ε ^ 2 ≤
      2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling R) * (C * w) ^ 2
  · exact Or.inl hClock
  · right
    have hMiss : 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
        (C * w) ^ 2 < ε ^ 2 := lt_of_not_ge hClock
    linarith only [hBudget, hMiss]

/-- On any positive spectral factor threshold, the preexisting anchor vs.
excursion inequality forces a *strict* norm-increment threshold. -/
theorem h3Critical_scalar_spectralThreshold_forces_excursion
    (S CL ε N : ℝ) (hCL : 0 ≤ CL)
    (hThreshold : 3 + 4 * CL * ε ≤ S)
    (hExc : S < 3 + 4 * CL * N) :
    ε < N := by
  by_contra hNot
  have hN : N ≤ ε := le_of_not_gt hNot
  have hScale : 4 * CL * N ≤ 4 * CL * ε :=
    mul_le_mul_of_nonneg_left hN (mul_nonneg (by norm_num) hCL)
  linarith only [hThreshold, hExc, hScale]

/-- All already-certified *non-spectral-excursion* alternatives for a
fivefold source peak. This keeps the genuine physical source temporal
excursion separate: no time derivative of the projected source is assumed. -/
def h3Critical_fivefold_nonSpectralExcursionAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x w δ σ M q sSource : ℝ) : Prop :=
  (∃ s : ℝ, s ∈ Set.Icc x (x + δ) ∧
    h3CriticalSourceExcessEnhancedFloor M q <
      h3PathSqrtEnergyRiccatiCoefficient *
        Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
  w ≤ (velocityH3EnergyAt u x - 1) / h3CriticalSourceExcessEnhancedFloor M q ∨
  h3CriticalSourceExcessEnhancedFloor M q ≤
    16 * (velocityH3EnergyAt u x - 1) * (max 1 σ + 1) ^ 4 ∨
  max 1 σ + 1 < 3 + 4 * h3AuditInitialLerayEnergyCoefficient *
    ‖h3AuditActualSpectralVelocityTotal hH3 x‖ ∨
  (4 * q) ^ 2 < 96 * ‖h3PathActualProjectedMomentumSource244 hH3 x‖ ^ 2 ∨
  (4 * q) ^ 2 < 96 * ‖h3PathActualProjectedMomentumSource244 hH3 sSource -
    h3PathActualProjectedMomentumSource244 hH3 x‖ ^ 2 ∨
  (4 * q) ^ 2 < 8 * velocityH3DissipationAt u x ∨
  (4 * q) ^ 2 < 8 * h3CriticalSourceExcessEnhancedFloor M q

/-- Same accepted separated fivefold source windows, same attained source
and state maxima, same calibrated widths and full physical dissipation
charges. For EVERY fixed Fourier cutoff and EVERY attempted spectral
threshold, either an existing non-spectral-excursion obstruction survives,
or actual projected momentum PDE motion pays the finite-band clock, or a
strict positive *high-radial spectral temporal mass* pays the remainder.
The Fourier cutoff and local source ceiling may both grow toward T. -/
theorem h3Critical_noL2Trace_cofinalFivefold_spectralExcursionPDEClockGate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n) :
    ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState A B δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        sSource k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        sState k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        A k = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        B k = 12 * ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ^ 2 +
          2 * (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s)) ∧
      (∀ k : ℕ, ∀ R ε : ℝ, 0 ≤ R → 0 < ε →
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        ε ^ 2 < 2 * h3Path_spectralTemporalHighRadialIntegral244 R
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))
          (h3AuditActualSpectralVelocityTotal hH3 (sState k))) := by
  obtain ⟨i, t, w, v, sSource, sState, A, B, δ,
      hv, hLimit, hSep, hCosts, hWindows⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_anchoredTemporalExcursionGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨t, w, v, sSource, sState, A, B, δ,
    hv, hLimit, hSep, hCosts, ?_, ?_⟩
  · intro k
    obtain ⟨ht, hw, hEnd, hsSource, hsState, hMax,
      hA, hB, hδ, hδw, hWidth, hFloor, _hAlt⟩ := hWindows k
    exact ⟨ht, hw, hEnd, hsSource, hsState, hMax,
      hA, hB, hδ, hδw, hWidth, hFloor⟩
  · intro k R ε hR hε hThreshold
    obtain ⟨ht, hw, hEnd, hsSource, hsState, hMax,
      _hA, _hB, _hδ, _hδw, _hWidth, _hFloor, hAlt⟩ := hWindows k
    have hSource : ∀ r : ℝ, r ∈ Set.Icc (t (v k))
        (t (v k) + w (v k)) →
        ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
          ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ := by
      intro r hr
      exact (hMax r hr).1
    have hx : 0 < t (v k) :=
      lt_trans hClass.terminal_start.1
        (lt_trans hb.1 (lt_trans (hc (v k)).1 ht.1))
    rcases hAlt with hRiccati | hCompression | hCutoff | hSpec | hSrc | hD | hFloor
    · exact Or.inl (Or.inl hRiccati)
    · exact Or.inl (Or.inr (Or.inl hCompression))
    · exact Or.inl (Or.inr (Or.inr (Or.inl hCutoff)))
    · rcases hSpec with hStateAnchor | hExc
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hStateAnchor))))
      · have hNorm : ε < ‖h3AuditActualSpectralVelocityTotal hH3 (sState k) -
            h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ :=
          h3Critical_scalar_spectralThreshold_forces_excursion
            (max 1 (σ (v k)) + 1) h3AuditInitialLerayEnergyCoefficient
            ε _ h3AuditInitialLerayEnergyCoefficient_nonneg hThreshold hExc
        have hClock := h3Critical_actualSpectralExcursion_PDEClockOrHighRadial
          hH3 R (t (v k)) (w (v k)) (sState k)
          ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ε
          hR hx hw hEnd hsState (norm_nonneg _) hε.le hSource hNorm.le
        rcases hClock with hLow | hHigh
        · exact Or.inr (Or.inl hLow)
        · exact Or.inr (Or.inr hHigh)
    · rcases hSrc with hSrcAnchor | hSrcExc
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSrcAnchor)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSrcExc))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hD)))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hFloor)))))))

end
end PrimeTensor.Bridge.Euclidean
