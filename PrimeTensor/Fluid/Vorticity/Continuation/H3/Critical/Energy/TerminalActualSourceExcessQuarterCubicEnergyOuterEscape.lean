import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessNoncompressedCofinalPhysicalEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorEnergyFourth244
import Mathlib.Tactic

/-!
# Quarter-cubic annular crossing directly forces physical outer-frequency escape

The certified quarter-cubic annular gap is stronger than the earlier
noncompression/source-based frequency escape: at each selected first-crossing
annulus, the low-radial H3-gradient bound gives R^3 < 4 (Q+1)^2 E3(t).
If the physical H3 anchor energy is bounded on the selected cofinal sequence,
then (Q+1)/R tends to infinity. No source bound, noncompressed clock or
integrability of full terminal H3 dissipation is used. The spectral-energy
bound is necessary, not an assertion that H3 energy is uniformly bounded.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A strict quarter-cubic annular surplus, nonnegative inner dissipation,
and the genuine H3 anchor estimate force an absolute physical outer radius
burden. No source or clock premise is used. -/
theorem h3Critical_scalar_quarterCubicGap_forces_outerEnergy
    (R Q K E Lr Lq : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hKE : K ^ 2 ≤ E)
    (hLr : 0 ≤ Lr)
    (hGap : R ^ 3 / 4 < (Lq - Lr) - R ^ 3 / 2)
    (hLq : Lq ≤ 3 * (Q + 1) ^ 2 * K ^ 2) :
    R ^ 3 < 4 * (Q + 1) ^ 2 * E := by
  have hCross : 3 * R ^ 3 / 4 < Lq - Lr := by
    linarith only [hGap]
  have hScale : 3 * (Q + 1) ^ 2 * K ^ 2 ≤
      3 * (Q + 1) ^ 2 * E :=
    mul_le_mul_of_nonneg_left hKE (by positivity)
  linarith only [hCross, hLr, hLq, hScale]

/-- A relative outer cutoff Q+1 <= D*R forces physical H3 energy at the
anchor to exceed the inner radius divided by 4 D^2. -/
theorem h3Critical_scalar_quarterCubic_relativeOuter_forces_energyGrowth
    (R Q E D : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q) (hE : 0 ≤ E)
    (hCross : R ^ 3 < 4 * (Q + 1) ^ 2 * E)
    (hOuter : Q + 1 ≤ D * R) :
    R < 4 * D ^ 2 * E := by
  have hQ0 : 0 ≤ Q + 1 := by linarith only [hR, hRQ]
  have hPow : (Q + 1) ^ 2 ≤ (D * R) ^ 2 :=
    pow_le_pow_left₀ hQ0 hOuter 2
  have hScaled : (4 * E) * (Q + 1) ^ 2 ≤
      (4 * E) * (D * R) ^ 2 :=
    mul_le_mul_of_nonneg_left hPow (by positivity)
  have hUpper : R ^ 3 < (4 * D ^ 2 * E) * R ^ 2 := by
    calc
      R ^ 3 < 4 * (Q + 1) ^ 2 * E := hCross
      _ = (4 * E) * (Q + 1) ^ 2 := by ring
      _ ≤ (4 * E) * (D * R) ^ 2 := hScaled
      _ = (4 * D ^ 2 * E) * R ^ 2 := by ring
  by_contra hNot
  have hReverse : 4 * D ^ 2 * E ≤ R := le_of_not_gt hNot
  have hMult := mul_le_mul_of_nonneg_right hReverse (sq_nonneg R)
  have hUpperReverse : (4 * D ^ 2 * E) * R ^ 2 ≤ R ^ 3 := by
    calc
      _ ≤ R * R ^ 2 := hMult
      _ = R ^ 3 := by ring
  exact (not_lt_of_ge hUpperReverse) hUpper

/-- The actual three-component finite annulus at a strict preterminal
anchor obeys the energy/outer-radius crossing constraint. -/
theorem h3Critical_quarterCubicPhysicalAnchor_forces_energyOuter
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t R Q : ℝ) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQuarter : R ^ 3 / 4 <
      (h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
       h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)) - R ^ 3 / 2)
    (hKE : ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
      velocityH3EnergyAt u t) :
    R ^ 3 < 4 * (Q + 1) ^ 2 * velocityH3EnergyAt u t := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hQ0 : 0 ≤ Q := le_trans hR0 hRQ
  have hLr : 0 ≤ h3PathActualLowRadialDissipation244 R G := by
    rw [h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 R hR0 G]
    positivity
  have hLq := h3Path_actualLowRadialDissipation_le_threeSpectralSup244 Q hQ0 G
  exact h3Critical_scalar_quarterCubicGap_forces_outerEnergy
    R Q ‖G‖ (velocityH3EnergyAt u t)
    (h3PathActualLowRadialDissipation244 R G)
    (h3PathActualLowRadialDissipation244 Q G)
    hR hRQ (by simpa only [G] using hKE) hLr
    (by simpa only [G] using hQuarter) hLq

/-- The same selected non-L2-trace, strictly separated physical annuli
carry an unconditional pointwise energy/outer-cutoff constraint. If their
anchor physical H3 energies are eventually bounded, the outer-to-inner
frequency ratio escapes EVERY fixed bound EVENTUALLY (rather than only
along a further subsequence). No source or geometric noncompression bound. -/
theorem h3Critical_noL2Trace_disjointQuarterCubic_boundedEnergy_forces_outerEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N : ℕ → ℕ, ∃ C δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        v k ≤ N (v k) ∧ 0 ≤ C (v k) ∧ 0 < δ (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 t N (v k) ∧
        δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - t (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 t N (v k))
          (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ (C (v k)))
          (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))) ∧
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
          ∫ r in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        ((v k : ℝ) + 1) ^ 3 <
          4 * ((N (v k) : ℝ) + 2) ^ 2 *
            velocityH3EnergyAt u (t (v k))) ∧
      (∀ B : ℝ, 0 ≤ B →
        (∀ᶠ k : ℕ in atTop,
          velocityH3EnergyAt u (t (v k)) ≤ B) →
        ∀ D : ℝ, 1 ≤ D → ∀ᶠ k : ℕ in atTop,
          D * ((v k : ℝ) + 1) < ((N (v k) : ℝ) + 2)) := by
  obtain ⟨t, N, C, δ, v, hv, hCofinal, hSeparated,
      hSelected, _hCosts, _hAlternative⟩ :=
    h3Critical_noL2Trace_disjointQuarterCubicAnnuli_energySourceOuterBarrier
      hH3 hClass hNoTrace
  have hPhysical (k : ℕ) :
      ((v k : ℝ) + 1) ^ 3 <
        4 * ((N (v k) : ℝ) + 2) ^ 2 *
          velocityH3EnergyAt u (t (v k)) := by
    obtain ⟨_, hN, _, _, hEnergy, hGap, _, _, _⟩ := hSelected k
    let R : ℝ := (v k : ℝ) + 1
    let Q : ℝ := (N (v k) : ℝ) + 1
    have hR : 1 ≤ R := by
      dsimp only [R]
      have hn : 0 ≤ (v k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    have hRQ : R ≤ Q := by
      have hn : (v k : ℝ) ≤ (N (v k) : ℝ) := by
        exact_mod_cast hN
      dsimp only [R, Q]
      linarith only [hn]
    have hQuarter : R ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) -
         h3PathActualLowRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) - R ^ 3 / 2 := by
      simpa only [R, Q, h3PathCubicAnnulusActualGap244] using hGap
    have hOuter := h3Critical_quarterCubicPhysicalAnchor_forces_energyOuter
      hH3 (t (v k)) R Q hR hRQ hQuarter hEnergy
    simpa only [R, Q,
      show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
      using hOuter
  have hWindow (k : ℕ) :
      v k ≤ N (v k) ∧ 0 ≤ C (v k) ∧ 0 < δ (v k) ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
      ((v k : ℝ) + 1) ^ 3 / 4 <
        h3PathCubicAnnulusActualGap244 hH3 t N (v k) ∧
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - t (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 t N (v k))
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ (C (v k)))
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))) ∧
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
        ∫ r in t (v k)..(t (v k) + δ (v k)),
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) ∧
      ((v k : ℝ) + 1) ^ 3 <
        4 * ((N (v k) : ℝ) + 2) ^ 2 *
          velocityH3EnergyAt u (t (v k)) := by
    obtain ⟨_, hN, hC, hδ, _, hGap, hEnvelope, hWidth, hCost⟩ := hSelected k
    have hExact : δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - t (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 t N (v k))
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ (C (v k)))
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))) := by
      simpa only [h3PathCubicAnnulusActualGap244] using hWidth
    exact ⟨hN, hC, hδ, hEnvelope, hGap, hExact, hCost, hPhysical k⟩
  refine ⟨t, N, C, δ, v, hv, hCofinal, hSeparated, hWindow, ?_⟩
  intro B hB hEnergyBound D hD
  have hLarge := h3Critical_scalar_strictMono_innerRadius_eventually_exceeds
    v hv (4 * D ^ 2 * B)
  filter_upwards [hEnergyBound, hLarge] with k hkE hkLarge
  let R : ℝ := (v k : ℝ) + 1
  let Q : ℝ := (N (v k) : ℝ) + 1
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hn : 0 ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hRQ : R ≤ Q := by
    have hN : v k ≤ N (v k) := (hWindow k).1
    have hn : (v k : ℝ) ≤ (N (v k) : ℝ) := by
      exact_mod_cast hN
    dsimp only [R, Q]
    linarith only [hn]
  have hE : 0 ≤ velocityH3EnergyAt u (t (v k)) := by
    obtain ⟨_, _, _, _, hKE, _, _, _, _⟩ := hSelected k
    exact (sq_nonneg _).trans hKE
  have hCross : R ^ 3 <
      4 * (Q + 1) ^ 2 * velocityH3EnergyAt u (t (v k)) := by
    simpa only [R, Q,
      show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
      using hPhysical k
  have hThreshold : 4 * D ^ 2 * B < R := by
    simpa only [R] using hkLarge
  have hResult : D * R < Q + 1 := by
    by_contra hNot
    have hOuter : Q + 1 ≤ D * R := le_of_not_gt hNot
    have hPay := h3Critical_scalar_quarterCubic_relativeOuter_forces_energyGrowth
      R Q (velocityH3EnergyAt u (t (v k))) D
      hR hRQ hE hCross hOuter
    have hScale : 4 * D ^ 2 * velocityH3EnergyAt u (t (v k)) ≤
        4 * D ^ 2 * B :=
      mul_le_mul_of_nonneg_left hkE (by positivity)
    have hSmall : R ≤ 4 * D ^ 2 * B := (hPay.trans_le hScale).le
    exact False.elim ((not_lt_of_ge hSmall) hThreshold)
  simpa only [R, Q,
    show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
    using hResult

end
end PrimeTensor.Bridge.Euclidean
