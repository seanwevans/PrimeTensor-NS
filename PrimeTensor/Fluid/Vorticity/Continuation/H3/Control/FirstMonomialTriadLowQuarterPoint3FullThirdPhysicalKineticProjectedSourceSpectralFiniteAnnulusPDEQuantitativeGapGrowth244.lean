import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEVanishingCaps244
import Mathlib.Tactic

/-!
# Quarter-cubic annulus gaps and super-sixth anchored PDE concentration

The high-radial cubic snapshot lemma originally selects a finite annulus
carrying more than three quarters of the cubic height. That strict lower
bound is retained here alongside the *exact* anchored PDE width, before
cofinal and pairwise-disjoint selections are performed.

The conditional terminal obstruction becomes quantitative: if the scaled
terminal lag does not collapse, and full physical H³ terminal dissipation
is integrable, the sum of the anchored projected-source PDE variation
coefficients grows faster than the sixth power of the selected radius.

The geometric noncollapse and full terminal H³ integrability remain
explicit hypotheses; this theorem claims neither automatically.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Retain the quarter-cubic surplus already proved during the original
finite-annulus selection. It is not safe to infer this bound for an
arbitrary cutoff returned by a weaker existential theorem. -/
theorem h3Path_cubicHighSnapshot_has_quarterGapExactPDEClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ t + δ < T ∧
      (δ = h3PathCubicAnnulusExactPDEWidth244 ((T - t) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C)) ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ((n : ℝ) + 1) ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2 := by
  obtain ⟨N, hnN, hHeight⟩ :=
    h3Path_cubicHighSnapshot_has_finiteAnnularHeight244
      hH3 hClass t ht n hCube
  let R : ℝ := (n : ℝ) + 1
  let Q : ℝ := (N : ℝ) + 1
  let A : ℝ := R ^ 3 / 2
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let K : ℝ := ‖G‖
  let B : ℝ :=
    h3PathActualLowRadialDissipation244 Q G -
      h3PathActualLowRadialDissipation244 R G
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := norm_nonneg G
  have hBase : ∀ j : Fin 3, ‖G j‖ ≤ K := by
    intro j
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg G)).1 le_rfl j
  have hCubePos : 0 < R ^ 3 := by dsimp only [R]; positivity
  have hHeight' : 3 * R ^ 3 / 4 < B := by
    simpa only [R, Q, B, G] using hHeight
  have hQuarter : R ^ 3 / 4 < B - A := by
    dsimp only [A]
    linarith only [hHeight']
  have hGap : 0 < B - A := by
    linarith only [hQuarter, hCubePos]
  let b : ℝ := (T - t) / 2
  have hb : 0 < b := by dsimp only [b]; linarith only [ht.2]
  have ht0 : 0 < t := lt_trans hClass.terminal_start.1 ht.1
  have htb : t < t + b := by linarith only [hb]
  have hbT : t + b < T := by
    dsimp only [b]
    linarith only [ht.2]
  obtain ⟨C, hC, hSource⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnStrict244
      hH3 ht0 htb hbT
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C
  let Ξ : ℝ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C
  have hΛ : 0 ≤ Λ :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 R Q K C hK hC
  have hΞ : 0 ≤ Ξ :=
    h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244 R Q C
  obtain ⟨δ, hExact, hδ, hδb, _hδone, hBudget⟩ :=
    h3Path_cubicAnnulusExactPDEWidth_valid244
      b (B - A) Λ Ξ hb hGap hΛ hΞ
  have hEnd : t + δ < T := by linarith only [hδb, hbT]
  have hSourceWindow : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C := by
    intro s hs
    apply hSource s
    constructor
    · exact hs.1
    · linarith only [hs.2, hδb]
  have hFinal :=
    h3Path_actualFiniteAnnulus_integratedCost_of_anchoredPDE244
      hH3 hClass R Q K C A t δ hR hQ hK hA ht hδ hEnd
      hBase hSourceWindow (show A < B from sub_pos.mp hGap) hBudget
  refine ⟨N, K, C, δ, hnN, hK, hC, hδ, hEnd, ?_, hFinal.1, ?_⟩
  · change δ = h3PathCubicAnnulusExactPDEWidth244 b (B - A) Λ Ξ
    exact hExact
  · change R ^ 3 / 4 < B - A
    exact hQuarter

/-- A genuinely quantitative concentration statement. If an exact
cubic PDE width has vanishing weighted cost, the geometric cap has an
eventual positive floor, and the annular gap has a quarter-cubic floor,
then the anchored PDE coefficient is super-sixth on that same sequence. -/
theorem h3Path_exactCubicClocks_quarterGapNoncompression_forces_superSixth244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusExactPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0))
    (hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k))
    (hZPos : ∀ᶠ k : ℕ in atTop,
      0 < Λ (v k) + Ξ (v k) + 1)
    (η : ℝ) (hη : 0 < η)
    (hGeometry : ∀ᶠ k : ℕ in atTop,
      η ≤ ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2)) :
    Tendsto (fun k : ℕ =>
      (Λ (v k) + Ξ (v k) + 1) / ((v k : ℝ) + 1) ^ 6)
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro B
  let D : ℝ := max 1 B
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hEps : 0 < 1 / (8 * D) := by positivity
  have hCap :=
    h3Path_exactCubicClocks_geometricNoncollapse_forces_normalizedPDEGap244
      v δ b gap Λ Ξ hv hExact hCollapse η hη hGeometry
      (1 / (8 * D)) hEps
  filter_upwards [hCap, hQuarter, hZPos] with k hk hkGap hkZ
  let R : ℝ := (v k : ℝ) + 1
  let Z : ℝ := Λ (v k) + Ξ (v k) + 1
  have hRpos : 0 < R := by dsimp only [R]; positivity
  have hR3 : 0 ≤ R ^ 3 := pow_nonneg hRpos.le _
  have hR6 : 0 < R ^ 6 := pow_pos hRpos _
  have hZ : 0 < Z := by simpa only [Z] using hkZ
  have hGap : R ^ 3 / 4 ≤ gap (v k) := by
    simpa only [R] using hkGap
  have hSmall : (R ^ 3 * gap (v k)) / (2 * Z) ≤ 1 / (8 * D) := by
    calc
      (R ^ 3 * gap (v k)) / (2 * Z) =
          R ^ 3 * (gap (v k) / (2 * Z)) := by ring
      _ ≤ 1 / (8 * D) := by simpa only [R, Z] using hk
  have hCross : (R ^ 3 * gap (v k)) * (8 * D) ≤
      (1 : ℝ) * (2 * Z) :=
    (div_le_div_iff₀ (by positivity : 0 < 2 * Z)
      (by positivity : 0 < 8 * D)).mp hSmall
  have hQuarterScaled : R ^ 6 / 4 ≤ R ^ 3 * gap (v k) := by
    have hMult : R ^ 3 * (R ^ 3 / 4) ≤ R ^ 3 * gap (v k) :=
      mul_le_mul_of_nonneg_left hGap hR3
    nlinarith only [hMult]
  have hRate : D * R ^ 6 ≤ Z := by
    have hLeft : D * R ^ 6 ≤ (4 * D) * (R ^ 3 * gap (v k)) := by
      calc
        D * R ^ 6 = (4 * D) * (R ^ 6 / 4) := by ring
        _ ≤ (4 * D) * (R ^ 3 * gap (v k)) :=
          mul_le_mul_of_nonneg_left hQuarterScaled (by positivity)
    have hRight : (4 * D) * (R ^ 3 * gap (v k)) ≤ Z := by
      nlinarith only [hCross]
    exact le_trans hLeft hRight
  have hB : B * R ^ 6 ≤ Z := by
    calc
      B * R ^ 6 ≤ D * R ^ 6 :=
        mul_le_mul_of_nonneg_right (le_max_right 1 B) hR6.le
      _ ≤ Z := hRate
  have hRatio : B ≤ Z / R ^ 6 := (le_div_iff₀ hR6).2 hB
  simpa only [R, Z] using hRatio

/-- Retain the original three-quarter-cubic finite-annulus selection
through the complete cofinal no-terminal-L²-trace sequence. -/
theorem h3Path_noL2Trace_forces_quarterGapExactPDEClocks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        n ≤ N n ∧ 0 ≤ K n ∧ 0 ≤ C n ∧ 0 < δ n ∧
        τ n + δ n < T ∧
        δ n = h3PathCubicAnnulusExactPDEWidth244 ((T - τ n) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N n)
          (h3PathCubicAnnulusActualLinearRate244 N K C n)
          (h3PathCubicAnnulusActualQuadraticRate244 N C n) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        ((n : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N n) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hCube⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ τ n + δ < T ∧
      (δ = h3PathCubicAnnulusExactPDEWidth244 ((T - τ n) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C)) ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ((n : ℝ) + 1) ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2 :=
    h3Path_cubicHighSnapshot_has_quarterGapExactPDEClock244
      hH3 hClass (τ n) (hτ n) n (hCube n)
  choose N K C δ hAll using hChoice
  refine ⟨τ, N, K, C, δ, hτ, hLimit, ?_⟩
  intro n
  rcases hAll n with ⟨hnN, hK, hC, hδ, hEnd, hExact, hFloor, hGap⟩
  exact ⟨hnN, hK, hC, hδ, hEnd,
    (by simpa only [h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hExact),
    hFloor, (by simpa only [h3PathCubicAnnulusActualGap244] using hGap)⟩

/-- Physical super-sixth concentration is forced conditionally on a
noncompressed cubic terminal lag, along a single disjoint sequence
that preserves the *exact* PDE windows and quarter-cubic gaps. -/
theorem h3Path_noL2Trace_finiteDissipation_quarterGapSuperSixth244
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
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)) →
        Tendsto (fun k : ℕ =>
          (h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
            h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1) /
            ((v k : ℝ) + 1) ^ 6) atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_forces_quarterGapExactPDEClocks244
      hH3 hClass hMass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hAll n with ⟨_, _, _, hp, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hAll n with ⟨_, _, _, _, he, _, _, _⟩
    exact he
  obtain ⟨v, hv, hCofinal, hSeparate⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  let M : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  have hBound : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤ M := by
    have hFloor (k : ℕ) (r : ℝ)
        (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
        ((v k : ℝ) + 1) ^ 3 / 2 ≤ velocityH3DissipationAt u r := by
      rcases hAll (v k) with ⟨_, _, _, _, hb, _, hAnnulus, _⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
          lt_of_le_of_lt hr.2 hb⟩
      exact (hAnnulus r hr).le.trans
        (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
          hH3 hClass r hrClass ((v k : ℝ) + 1)
            ((N (v k) : ℝ) + 1))
    have hSum := h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      (fun k => ((v k : ℝ) + 1) ^ 3 / 2)
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt
      (fun k => (hTime (v k)).1.le)
      (fun k => (hδ (v k)).le)
      (fun k => (hEnd (v k)).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
      hFloor
    simpa only [M] using hSum
  have hΛ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C n := by
    unfold h3PathCubicAnnulusActualLinearRate244
    rcases hAll n with ⟨_, hK, hC, _, _, _, _, _⟩
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n) hK hC
  have hΞ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C n := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusExactPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    exact (hAll (v k)).2.2.2.2.2.1
  obtain ⟨hSummable, hCollapse, _⟩ :=
    h3Path_exactCubicClocks_finiteCosts_forces_alternative244
      v δ (fun n => (T - τ n) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N)
      (h3PathCubicAnnulusActualLinearRate244 N K C)
      (h3PathCubicAnnulusActualQuadraticRate244 N C)
      M hv (fun n => (hδ n).le) hΛ hΞ
      (fun n => (hAll n).2.2.2.2.2.1) hBound
  have hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤
        h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    apply Filter.Eventually.of_forall
    intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg.le
  have hZPos : ∀ᶠ k : ℕ in atTop,
      0 < h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
        h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1 := by
    apply Filter.Eventually.of_forall
    intro k
    have hL := hΛ (v k)
    have hQ := hΞ (v k)
    linarith only [hL, hQ]
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, ?_,
    hSummable, ?_⟩
  · intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg
  · intro η hη hGeom
    exact h3Path_exactCubicClocks_quarterGapNoncompression_forces_superSixth244
      v δ (fun n => (T - τ n) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N)
      (h3PathCubicAnnulusActualLinearRate244 N K C)
      (h3PathCubicAnnulusActualQuadraticRate244 N C)
      hv hExact hCollapse hQuarter hZPos η hη hGeom

end
end PrimeTensor.FirstMonomialTriad
