import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessDisjointQuarterCubicPDEBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.AnnularGeometry.EnergyOuter
import Mathlib.Tactic

/-!
# Disjoint H3 quarter-cubic annuli: actual energy/source/cutoff barriers

Transfer the certified physical sixth- and ninth-order clock alternative to
actual H3 energy, the attained projected-source maximum, and the outer
Fourier radius. The frequency order and energy anchor are exported from the
same preterminal diagonal that supplies the disjoint windows.

No terminal H3-dissipation integrability is assumed. Unbounded annular
charges remain a separate possible arm and no regularity follows.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Replace the actual linear/square-root PDE coefficients in the
quarter-cubic rate alternative by physical H3 energy, actual projected
source amplitude and tenth/eighth outer frequency powers. -/
theorem h3Critical_scalar_quarterCubicRates_to_energySourceOuter
    (R Q K C E G ε : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hKE : K ^ 2 ≤ E)
    (hε : 0 ≤ ε)
    (hAlt : G ≤ ε ∨
      R ^ 6 ≤ 16 * ε *
        (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C + 1) ∨
      R ^ 9 ≤ 16 * ε ^ 2 *
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1)) :
    G ≤ ε ∨
      R ^ 12 ≤ 512 * ε ^ 2 *
        (2304 * E * C ^ 2 * (Q + 1) ^ 10 + 1) ∨
      R ^ 9 ≤ 16 * ε ^ 2 *
        (36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := by
  have hSplit := h3Path_scalar_higherBudget_sourceEnergyOrOuterEighth244
    R Q K C E C (R ^ 6) (R ^ 9) G ε
    hR hRQ hK hC hC hε hKE (by positivity) hAlt
  rcases hSplit with hSource | hTime | hLinear | hQuadratic
  · exact False.elim ((lt_irrefl C) hSource)
  · exact Or.inl hTime
  · exact Or.inr (Or.inl (by convert hLinear using 1; ring))
  · exact Or.inr (Or.inr hQuadratic)

/-- The original quarter-gap physical annuli, with preserved exact
quadratic PDE clocks, simultaneously carry the source maximum, anchor
energy bound and ordered outer cutoff. Either certified charges are
unbounded or the sixth-order rate becomes a twelfth-order energy/source
barrier, while the ninth-order quadratic rate charges eighth-power cutoffs.
No finite terminal full-H3 integral enters. -/
theorem h3Critical_noL2Trace_disjointQuarterCubicAnnuli_energySourceOuterBarrier
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
        k ≤ v k ∧ v k ≤ N (v k) ∧
        0 ≤ C (v k) ∧ 0 < δ (v k) ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ ^ 2 ≤
          velocityH3EnergyAt u (t (v k)) ∧
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 t N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
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
              (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
        ∑ k ∈ Finset.range m,
          (∫ r in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r))) ∧
      ((∀ M : ℝ, ∃ m : ℕ,
        M < ∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
       (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
         ((v k : ℝ) + 1) ^ 3 * ((T - t (v k)) / 4) ≤ ε ∨
         ((v k : ℝ) + 1) ^ 12 ≤
           512 * ε ^ 2 *
             (2304 * velocityH3EnergyAt u (t (v k)) * (C (v k)) ^ 2 *
               ((N (v k) : ℝ) + 2) ^ 10 + 1) ∨
         ((v k : ℝ) + 1) ^ 9 ≤
           16 * ε ^ 2 *
             (36 * (C (v k)) ^ 2 *
               (((N (v k) : ℝ) + 2) ^ 8 + ((v k : ℝ) + 2) ^ 8) + 1))) := by
  obtain ⟨t, N, C, δ, hTimes, _hDist, hLimit, hWindows⟩ :=
    h3Critical_noL2Trace_cofinalQuarterCubicAnnulusDiagonal
      hH3 hClass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    obtain ⟨_, _, _, hPositive, _, _, _, _, _, _⟩ := hWindows n
    exact hPositive
  have hEnd (n : ℕ) : t n + δ n < T := by
    obtain ⟨_, _, _, _, hBefore, _, _, _, _, _⟩ := hWindows n
    exact hBefore
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      t δ T hLimit hδ hEnd
  have hIndex (k : ℕ) : k ≤ v k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        exact Nat.succ_le_of_lt
          (lt_of_le_of_lt ih (hMono (Nat.lt_succ_self k)))
  let K : ℕ → ℝ := fun n =>
    ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖
  let b : ℕ → ℝ := fun n => (T - t n) / 2
  let gap : ℕ → ℝ := fun n => h3PathCubicAnnulusActualGap244 hH3 t N n
  let Λ : ℕ → ℝ := fun n => h3PathCubicAnnulusActualLinearRate244 N K C n
  let Ξ : ℕ → ℝ := fun n => h3PathCubicAnnulusActualQuadraticRate244 N C n
  have hSelected (k : ℕ) :
      k ≤ v k ∧ v k ≤ N (v k) ∧
      0 ≤ C (v k) ∧ 0 < δ (v k) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ ^ 2 ≤
        velocityH3EnergyAt u (t (v k)) ∧
      ((v k : ℝ) + 1) ^ 3 / 4 <
        h3PathCubicAnnulusActualGap244 hH3 t N (v k) ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
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
            (h3AuditActualSpectralVelocityTotal hH3 r) := by
    obtain ⟨hN, hC, hCEq, hPositive, _hEnd, hExact, hEnergy,
      hQuarter, _hFloor, hCost⟩ := hWindows (v k)
    refine ⟨hIndex k, hN, hC, hPositive, hEnergy, ?_, hCEq, ?_, hCost⟩
    · simpa only [h3PathCubicAnnulusActualGap244] using hQuarter
    · simpa only [h3PathCubicAnnulusActualGap244] using hExact
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)) := by
    obtain ⟨_, _, _, _, _, _, _, hWidth, _⟩ := hSelected k
    simpa only [b, gap, Λ, Ξ, K,
      h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hWidth
  have hQuarter (k : ℕ) :
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k) := by
    obtain ⟨_, _, _, _, _, hGap, _, _, _⟩ := hSelected k
    exact le_of_lt (by simpa only [gap] using hGap)
  have hLinearNonneg (k : ℕ) : 0 ≤ Λ (v k) := by
    obtain ⟨_, _, hC, _, _, _, _, _, _⟩ := hSelected k
    dsimp only [Λ, h3PathCubicAnnulusActualLinearRate244]
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (K (v k)) (C (v k)) (norm_nonneg _) hC
  have hQuadraticNonneg (k : ℕ) : 0 ≤ Ξ (v k) := by
    dsimp only [Ξ, h3PathCubicAnnulusActualQuadraticRate244]
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
  have hAlt := h3Critical_scalar_disjointQuadraticSharpCharges_unbounded_or_sixthNinth
    v δ b gap Λ Ξ hMono
    (fun k => (hδ (v k)).le)
    hExact (Filter.Eventually.of_forall hQuarter)
    (Filter.Eventually.of_forall hLinearNonneg)
    (Filter.Eventually.of_forall hQuadraticNonneg)
  let I : ℕ → ℝ := fun k =>
    ∫ r in t (v k)..(t (v k) + δ (v k)),
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) -
      h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r)
  have hCosts (k : ℕ) :
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤ I k := by
    obtain ⟨_, _, _, _, _, _, _, _, hCost⟩ := hSelected k
    exact hCost
  have hSum (m : ℕ) :
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
      ∑ k ∈ Finset.range m, I k :=
    h3Critical_scalar_finiteAnnularChargeSum_le_actualIntegralSum
      v δ I hCosts m
  refine ⟨t, N, C, δ, v,
    hMono, hCofinal, hSeparated, hSelected, ?_, ?_⟩
  · intro m
    simpa only [I] using hSum m
  · rcases hAlt with hUnbounded | hCaps
    · exact Or.inl hUnbounded
    · right
      intro ε hε
      filter_upwards [hCaps ε hε] with k hk
      let R : ℝ := (v k : ℝ) + 1
      let Q : ℝ := (N (v k) : ℝ) + 1
      let K₀ : ℝ := K (v k)
      let S : ℝ := C (v k)
      have hR : 1 ≤ R := by
        dsimp only [R]
        have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
        linarith only [hn]
      have hCut : v k ≤ N (v k) := by
        obtain ⟨_, hN, _, _, _, _, _, _, _⟩ := hSelected k
        exact hN
      have hRQ : R ≤ Q := by
        have hCast : (v k : ℝ) ≤ (N (v k) : ℝ) := by
          exact_mod_cast hCut
        dsimp only [R, Q]
        linarith only [hCast]
      have hK : 0 ≤ K₀ := by
        dsimp only [K₀, K]
        exact norm_nonneg _
      have hS : 0 ≤ S := by
        obtain ⟨_, _, hC, _, _, _, _, _, _⟩ := hSelected k
        exact hC
      have hKE : K₀ ^ 2 ≤ velocityH3EnergyAt u (t (v k)) := by
        obtain ⟨_, _, _, _, hE, _, _, _, _⟩ := hSelected k
        simpa only [K₀, K] using hE
      have hTimeCapEq :
          b (v k) / 2 = (T - t (v k)) / 4 := by
        dsimp only [b]
        ring
      have hPhysical := h3Critical_scalar_quarterCubicRates_to_energySourceOuter
        R Q K₀ S (velocityH3EnergyAt u (t (v k)))
        (R ^ 3 * ((T - t (v k)) / 4)) ε
        hR hRQ hK hS hKE hε.le
        (by simpa only [R, Q, K₀, K, S, Λ, Ξ, hTimeCapEq,
          h3PathCubicAnnulusActualLinearRate244,
          h3PathCubicAnnulusActualQuadraticRate244] using hk)
      rcases hPhysical with hTime | hLinear | hQuadratic
      · exact Or.inl (by simpa only [R] using hTime)
      · exact Or.inr (Or.inl (by
          simpa only [R, Q, S,
            show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
            using hLinear))
      · exact Or.inr (Or.inr (by
          simpa only [R, Q, S,
            show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring,
            show (v k : ℝ) + 1 + 1 = (v k : ℝ) + 2 by ring]
            using hQuadratic))

end
end PrimeTensor.Bridge.Euclidean
