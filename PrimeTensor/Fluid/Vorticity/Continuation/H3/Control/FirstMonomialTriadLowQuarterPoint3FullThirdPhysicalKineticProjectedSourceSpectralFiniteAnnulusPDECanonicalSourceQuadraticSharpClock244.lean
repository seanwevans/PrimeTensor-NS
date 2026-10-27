import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceWindowEnvelope244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEMinimalOuterCutoff244
import Mathlib.Tactic

/-!
# Canonical actual projected-source ceiling in the minimal quadratic-sharp PDE clock

The original clock selected a convenient but arbitrary compact-interval bound
`C` for the actual physical projected momentum source. Such a bound can be
artificially inflated. Here the same first-crossing annulus and exact
quadratic-sharp width use the *least* bound instead: the attained source-norm
maximum on the fixed half-terminal interval `[t, t+(T-t)/2]`.

Both the source maximum and the exact quadratic-sharp clock follow from the
already-proved strict-time physical source continuity and PDE persistence
lemma. No terminal bounded source, width cap, or no-blowup conclusion is
smuggled into the construction. Later clock hypotheses remain conditional.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The minimal actual first-crossing spectral annulus admits an exact
quadratically-sharp persistence clock whose source coefficient is *defined*
by the attained physical projected source maximum on the fixed enclosing
half-terminal interval. The chosen `C` is canonical, not merely efficient
up to an unspecified error. -/
theorem h3Path_cubicHighSnapshot_has_canonicalSourceQuadraticSharpClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧
      C = h3PathActualProjectedSourceWindowEnvelope244 hH3
        t (t + (T - t) / 2) ∧
      (∃ s : ℝ, s ∈ Set.Icc t (t + (T - t) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C) ∧
      0 < δ ∧ t + δ < T ∧
      (δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - t) / 2)
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
          ((n : ℝ) + 1) ^ 3 / 2 ∧
      (∀ m : ℕ, n ≤ m → m < N →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) ≤
          3 * (((n : ℝ) + 1) ^ 3) / 4) := by
  obtain ⟨N, hnN, hHeight, hMinimal⟩ :=
    h3Path_cubicHighSnapshot_has_minimalOuterAnnulus244
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
  let C : ℝ := h3PathActualProjectedSourceWindowEnvelope244 hH3 t (t + b)
  obtain ⟨sMax, hsMax, _hMax, hMaxEq⟩ :=
    h3Path_actualSourceWindowEnvelope_attained244 hH3 ht0 htb hbT
  have hC : 0 ≤ C := by
    dsimp only [C]
    rw [hMaxEq]
    exact norm_nonneg _
  have hSource : ∀ s : ℝ, s ∈ Set.Icc t (t + b) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C := by
    intro s hs
    exact h3Path_actualSourceWindowEnvelope_pointwise_le244
      hH3 ht0 htb hbT s hs
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C
  let Ξ : ℝ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C
  have hΛ : 0 ≤ Λ :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 R Q K C hK hC
  have hΞ : 0 ≤ Ξ :=
    h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244 R Q C
  obtain ⟨δ, hExact, hδ, hδb, _hδone, hBudget⟩ :=
    h3Path_cubicAnnulusQuadraticSharpPDEWidth_valid244
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
  refine ⟨N, K, C, δ, hnN, hK, hC, rfl, ?_, hδ, hEnd, ?_,
    hFinal.1, ?_, hMinimal⟩
  · refine ⟨sMax, hsMax, ?_⟩
    exact hMaxEq.symm
  · change δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 b (B - A) Λ Ξ
    exact hExact
  · change R ^ 3 / 4 < B - A
    exact hQuarter


/-- No-strong-terminal-L²-trace cubic snapshots now carry a minimal first
crossing and an EXACT quadratic-sharp physical PDE clock constructed using
the attained canonical source envelope, rather than an arbitrarily enlarged
existential ceiling. All clocks use the same actual strict-time snapshots. -/
theorem h3Path_noL2Trace_forces_canonicalSourceQuadraticSharpClocks244
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
        n ≤ N n ∧ 0 ≤ K n ∧ 0 ≤ C n ∧
        C n = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ n) (τ n + (T - τ n) / 2) ∧
        (∃ s : ℝ, s ∈ Set.Icc (τ n) (τ n + (T - τ n) / 2) ∧
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C n) ∧
        0 < δ n ∧ τ n + δ n < T ∧
        δ n = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
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
          h3PathCubicAnnulusActualGap244 hH3 τ N n ∧
        (∀ m : ℕ, n ≤ m → m < N n →
          h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
            3 * (((n : ℝ) + 1) ^ 3) / 4)) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hCube⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧
      C = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (τ n) (τ n + (T - τ n) / 2) ∧
      (∃ s : ℝ, s ∈ Set.Icc (τ n) (τ n + (T - τ n) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C) ∧
      0 < δ ∧ τ n + δ < T ∧
      δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C) ∧
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
          ((n : ℝ) + 1) ^ 3 / 2 ∧
      (∀ m : ℕ, n ≤ m → m < N →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
          3 * (((n : ℝ) + 1) ^ 3) / 4) :=
    h3Path_cubicHighSnapshot_has_canonicalSourceQuadraticSharpClock244
      hH3 hClass (τ n) (hτ n) n (hCube n)
  classical
  choose N K C δ hAll using hChoice
  refine ⟨τ, N, K, C, δ, hτ, hLimit, ?_⟩
  intro n
  rcases hAll n with ⟨hnN, hK, hC, hCanon, hPeak, hδ, hEnd,
    hExact, hFloor, hGap, hMinimal⟩
  exact ⟨hnN, hK, hC, hCanon, hPeak, hδ, hEnd,
    (by simpa only [h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hExact),
    hFloor, (by simpa only [h3PathCubicAnnulusActualGap244] using hGap),
    hMinimal⟩

end
end PrimeTensor.FirstMonomialTriad
