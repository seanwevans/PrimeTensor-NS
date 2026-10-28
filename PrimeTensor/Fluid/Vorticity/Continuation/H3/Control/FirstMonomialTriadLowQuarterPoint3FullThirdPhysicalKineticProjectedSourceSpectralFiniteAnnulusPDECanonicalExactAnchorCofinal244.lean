import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorSource244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceDisjointThreeScale244
import Mathlib.Tactic

/-!
# Exact physical H³ anchor preserved through canonical cofinal annulus clocks

The old cofinal existential theorem retained `0 ≤ K(n)` but not its actual
construction `K(n)=‖U₃(τ(n))‖`. We therefore rebuild the witness selection
from the exact-anchor pointwise constructor rather than rewriting arbitrary
witnesses after selection. This retains the minimal first-crossing annuli,
exact quadratic-sharp windows, disjoint dissipative charging, and three-cap
alternative, now with the physical H³ anchor identity and its product bound.

The pointwise constructor has been strengthened to export the original
quarter-cubic gap and minimality, both already proved internally there.
No unproved cap, universal source bound, or terminal regularity is introduced.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Rebuild the same kind of canonical disjoint first-crossing windows with
K(n) *defined* as the actual weighted H³ spectral norm at each anchor.
The exact PDE clock, sharp persistence, gap, minimality and three-cap test
are transported through the SAME newly selected cofinal subsequence. -/
theorem h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k,
        K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        K (v k) ^ 2 ≤ velocityH3EnergyAt u (τ (v k)) ∧
        (K (v k) * C (v k)) ^ 2 ≤
          velocityH3EnergyAt u (τ (v k)) * C (v k) ^ 2 ∧
        v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        (∃ s : ℝ, s ∈ Set.Icc (τ (v k))
            (τ (v k) + (T - τ (v k)) / 2) ∧
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k)) ∧
        0 < δ (v k) ∧ τ (v k) + δ (v k) < T ∧
        δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - τ (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
          (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
          (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) →
          ((v k : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k) ∧
        (∀ m : ℕ, v k ≤ m → m < N (v k) →
          h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
            3 * (((v k : ℝ) + 1) ^ 3) / 4)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 6 ≤
          16 * ε * (h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1) ∨
        ((v k : ℝ) + 1) ^ 9 ≤
          16 * ε ^ 2 *
            (h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)) ∧
      (Tendsto (fun k => C (v k) ^ 2) atTop atTop →
        ∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          ∃ s : ℝ, s ∈ Set.Icc (τ (v k))
              (τ (v k) + (T - τ (v k)) / 2) ∧
            M ≤ ‖h3PathActualProjectedMomentumSource244 hH3 s‖) := by
  obtain ⟨τ, hTime, _hNear, hLimit, hCube⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ (N : ℕ) (C δ : ℝ),
      n ≤ N ∧ 0 ≤ C ∧
      C = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (τ n) (τ n + (T - τ n) / 2) ∧
      (∃ s : ℝ, s ∈ Set.Icc (τ n) (τ n + (T - τ n) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C) ∧
      0 < δ ∧ τ n + δ < T ∧
      δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ (fun _ => N) n)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 (τ n)‖ C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C) ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 (τ n)‖ ^ 2 ≤
        velocityH3EnergyAt u (τ n) ∧
      (‖h3AuditActualSpectralVelocityTotal hH3 (τ n)‖ * C) ^ 2 ≤
        velocityH3EnergyAt u (τ n) * C ^ 2 ∧
      ((n : ℝ) + 1) ^ 3 / 4 <
        h3PathCubicAnnulusActualGap244 hH3 τ (fun _ => N) n ∧
      (∀ m : ℕ, n ≤ m → m < N →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
          3 * (((n : ℝ) + 1) ^ 3) / 4) := by
    have hRaw := h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244
      hH3 hClass (τ n) (hTime n) n (hCube n)
    simpa only [h3PathCubicAnnulusActualGap244] using hRaw
  classical
  choose N C δ hAll using hChoice
  let K : ℕ → ℝ := fun n => ‖h3AuditActualSpectralVelocityTotal hH3 (τ n)‖
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hAll n with ⟨_, _, _, _, hp, _, _, _, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hAll n with ⟨_, _, _, _, _, he, _, _, _, _, _, _⟩
    exact he
  obtain ⟨v, hv, hCofinal, hSeparate⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  let Budget : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  have hBound : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤ Budget := by
    have hFloor (k : ℕ) (r : ℝ)
        (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
        ((v k : ℝ) + 1) ^ 3 / 2 ≤ velocityH3DissipationAt u r := by
      rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hAnnulus, _, _, _, _⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
          lt_of_le_of_lt hr.2 (hEnd (v k))⟩
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
    simpa only [Budget] using hSum
  let f : ℕ → ℝ := fun k =>
    δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)
  have hf (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact mul_nonneg (hδ (v k)).le (by positivity)
  have hSummable : Summable f :=
    h3Path_nonnegativeBoundedRangeSums_summable244 f Budget hf
      (by simpa only [f] using hBound)
  have hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) := by
    have hTwice := hSummable.tendsto_atTop_zero.const_mul (2 : ℝ)
    have hEq : (fun k : ℕ =>
        δ (v k) * ((v k : ℝ) + 1) ^ 3) =
        (fun k : ℕ => 2 * f k) := by
      funext k
      dsimp only [f]
      ring
    rw [hEq]
    simpa only [mul_zero] using hTwice
  have hLinear (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C n := by
    have hC : 0 ≤ C n := by
      rcases hAll n with ⟨_, hc, _, _, _, _, _, _, _, _, _, _⟩
      exact hc
    change 0 ≤ h3PathFiniteAnnulusPDEVariationCoefficient244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n)
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      _ _ _ _ (norm_nonneg _) hC
  have hQuadratic (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C n := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    rcases hAll (v k) with ⟨_, _, _, _, _, _, hx, _, _, _, _, _⟩
    simpa only [K, h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hx
  have hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤
        h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    apply Filter.Eventually.of_forall
    intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, _, _, _, hg, _⟩
    simpa only [h3PathCubicAnnulusActualGap244] using hg.le
  have hBarrier := h3Path_exactQuadraticSharpClocks_threeScaleBarrier244
    v δ (fun n => (T - τ n) / 2)
    (h3PathCubicAnnulusActualGap244 hH3 τ N)
    (h3PathCubicAnnulusActualLinearRate244 N K C)
    (h3PathCubicAnnulusActualQuadraticRate244 N C)
    hv hExact hCollapse hQuarter
    (Filter.Eventually.of_forall (fun k => hLinear (v k)))
    (Filter.Eventually.of_forall (fun k => hQuadratic (v k)))
  have hPeaks (k : ℕ) : ∃ s : ℝ,
      s ∈ Set.Icc (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k) := by
    rcases hAll (v k) with ⟨_, _, _, hp, _, _, _, _, _, _, _, _⟩
    exact hp
  have hCnonneg (k : ℕ) : 0 ≤ C (v k) := by
    rcases hAll (v k) with ⟨_, hc, _, _, _, _, _, _, _, _, _, _⟩
    exact hc
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, ?_, ?_, hBarrier, ?_⟩
  · simpa only [f] using hSummable
  · intro k
    rcases hAll (v k) with
      ⟨hnN, _, hc, _, hp, he, hx, hf, hE, hEC, hg, hm⟩
    refine ⟨rfl, hE, hEC, hnN, hc, hPeaks k,
      hp, he, ?_, hf, ?_, hm⟩
    · exact hExact k
    · simpa only [h3PathCubicAnnulusActualGap244] using hg
  · intro hSquare M
    exact h3Path_attainedSourceSquareEscape_forces_windowPeaks244
      (fun k => C (v k)) (fun k => τ (v k))
      (fun k => τ (v k) + (T - τ (v k)) / 2)
      (fun s => ‖h3PathActualProjectedMomentumSource244 hH3 s‖)
      hCnonneg hPeaks hSquare M


/-- Source–spectral amplification charged to actual physical H³ energy:
the eighth-power finite-annulus rate bound is now expressed entirely with
physical E₃ at the anchor and the canonical projected-source ceiling. -/
theorem h3Path_exactAnchorCriticalWidth_forces_physicalEnergySource244
    (R Q U D K C E : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKE : K ^ 2 ≤ E)
    (hWidth : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hRate : U * R ^ 6 <
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C) :
    U ^ 8 * R ^ 3 < 48 ^ 8 * E ^ 4 * C ^ 8 * D ^ 5 := by
  have hRaw := h3Path_scalarCriticalWidth_linearEscape_sourceSpectral244
    R Q U D K C hR hRQ hU hD hWidth hRate
  have hProduct : (K * C) ^ 2 ≤ E * C ^ 2 :=
    h3Path_exactAnchor_productSquare_le_physicalEnergySource244
      K C E hK hC hKE
  have hPow : ((K * C) ^ 2) ^ 4 ≤ (E * C ^ 2) ^ 4 :=
    pow_le_pow_left₀ (sq_nonneg (K * C)) hProduct 4
  have hFactor : 0 ≤ (48 : ℝ) ^ 8 * D ^ 5 := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hPow hFactor
  calc
    U ^ 8 * R ^ 3 < (48 * |K * C|) ^ 8 * D ^ 5 := hRaw
    _ = ((48 : ℝ) ^ 8 * D ^ 5) * ((K * C) ^ 2) ^ 4 := by
      rw [abs_of_nonneg (mul_nonneg hK hC)]
      ring
    _ ≤ ((48 : ℝ) ^ 8 * D ^ 5) * (E * C ^ 2) ^ 4 := hScaled
    _ = 48 ^ 8 * E ^ 4 * C ^ 8 * D ^ 5 := by ring

/-- The physical amplification law, indexed at one original canonical
minimal-annulus witness. The only extra assumptions are the specified
outer cutoff cap and linear-rate exceedance at that same index. -/
theorem h3Path_exactAnchorCanonicalIndex_physicalAmplification244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ) (U D : ℝ)
    (hN : v k ≤ N (v k))
    (hK : K (v k) =
      ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
    (hKE : K (v k) ^ 2 ≤ velocityH3EnergyAt u (τ (v k)))
    (hC : 0 ≤ C (v k))
    (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hWidth : (((N (v k) : ℝ) + 1) + 1) ^ 8 ≤
      D * (((v k : ℝ) + 1) ^ 9))
    (hRate : U * (((v k : ℝ) + 1) ^ 6) <
      h3PathCubicAnnulusActualLinearRate244 N K C (v k)) :
    U ^ 8 * (((v k : ℝ) + 1) ^ 3) <
      48 ^ 8 * (velocityH3EnergyAt u (τ (v k))) ^ 4 *
        (C (v k)) ^ 8 * D ^ 5 := by
  let R : ℝ := (v k : ℝ) + 1
  let Q : ℝ := (N (v k) : ℝ) + 1
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hNat]
  have hRQ : R ≤ Q := by
    have hCast : (v k : ℝ) ≤ (N (v k) : ℝ) := by
      exact_mod_cast hN
    dsimp only [R, Q]
    linarith only [hCast]
  have hK0 : 0 ≤ K (v k) := by
    rw [hK]
    exact norm_nonneg _
  have hWidth' : (Q + 1) ^ 8 ≤ D * R ^ 9 := by
    simpa only [Q, R] using hWidth
  have hRate' : U * R ^ 6 <
      h3PathFiniteAnnulusPDEVariationCoefficient244
        R Q (K (v k)) (C (v k)) := by
    simpa only [R, Q, h3PathCubicAnnulusActualLinearRate244] using hRate
  have hBound := h3Path_exactAnchorCriticalWidth_forces_physicalEnergySource244
    R Q U D (K (v k)) (C (v k)) (velocityH3EnergyAt u (τ (v k)))
    hR hRQ hU hD hK0 hC hKE hWidth' hRate'
  simpa only [R] using hBound

end
end PrimeTensor.FirstMonomialTriad
