import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceDisjointThreeScale244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalWidthSourceEscape244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEMinimalHighTailNinthEighth244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFixedFrequencyDissipationEvacuation244
import Mathlib.Tactic

/-!
# Canonical source: critical annular-width cap forces attained physical peaks

Unlike the earlier chosen source ceiling, the C of the canonical quadratic-sharp
clock is exactly the attained maximum norm of the physical Leray-projected
momentum source on the half-terminal interval. We work on precisely that
canonical disjoint sequence, NOT on the independent old arbitrary-ceiling
witnesses.

From the three-cap obstruction and the explicit eighth-power quadratic
source gain, eventual noncompression and a sixth-order linear-rate ceiling
force an arbitrarily large ninth-order rate if the source were bounded.
A fixed critical annular-width cap precludes that, so the canonical C²
must diverge. Attainment yields genuine physical source peaks at times in
shrinking terminal windows. Every geometric/rate/width test is conditional.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A ninth/eighth source-gain inequality on each sufficiently late time,
for every multiplier, cannot coexist with a uniform critical cutoff cap
and a bounded source-square sequence. This is a sequence-level analytic
lemma; it does NOT assume a bound on the source. -/
theorem h3Path_canonicalEighthGain_outerCap_forces_sourceSquareEscape244
    (R Q C G F : ℕ → ℝ) (η B D : ℝ)
    (hR : ∀ k, 1 ≤ R k) (hD : 0 ≤ D)
    (hGeom : ∀ᶠ k : ℕ in atTop, η ≤ G k)
    (hLinear : ∀ᶠ k : ℕ in atTop,
      F k ≤ B * (R k) ^ 6)
    (hOuterCap : ∀ᶠ k : ℕ in atTop,
      (Q k + 1) ^ 8 ≤ D * (R k) ^ 9)
    (hEighth : ∀ M S : ℝ, 0 ≤ M → ∀ᶠ k : ℕ in atTop,
      η ≤ G k → F k ≤ B * (R k) ^ 6 → C k ^ 2 ≤ S ^ 2 →
        M * (R k) ^ 9 <
          36 * S ^ 2 * ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1) :
    Tendsto (fun k : ℕ => C k ^ 2) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let S : ℝ := max A 0 + 1
  have hS : 1 ≤ S := by
    dsimp only [S]
    have hh : (0 : ℝ) ≤ max A 0 := le_max_right _ _
    linarith only [hh]
  have hAS : A ≤ S := by
    dsimp only [S]
    have hh : A ≤ max A 0 := le_max_left _ _
    linarith only [hh]
  have hASq : A ≤ S ^ 2 := by
    have hs : 0 ≤ S := le_trans (by norm_num) hS
    have hd : 0 ≤ S - 1 := by linarith only [hS]
    have hp := mul_nonneg hs hd
    nlinarith only [hAS, hp]
  let M : ℝ := 36 * S ^ 2 * (D + 256) + 2
  have hM : 0 ≤ M := by
    dsimp only [M]
    have hd : 0 ≤ D + 256 := by linarith only [hD]
    positivity
  filter_upwards [hGeom, hLinear, hOuterCap, hEighth M S hM]
    with k hg hl hc he
  have hRp : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
  have hR8 : (R k) ^ 8 ≤ (R k) ^ 9 := by
    calc
      _ = (R k) ^ 8 * 1 := by ring
      _ ≤ (R k) ^ 8 * R k :=
        mul_le_mul_of_nonneg_left (hR k) (by positivity)
      _ = (R k) ^ 9 := by ring
  have hR9 : 1 ≤ (R k) ^ 9 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) (hR k) 9)
  have hInner : (R k + 1) ^ 8 ≤ 256 * (R k) ^ 9 := by
    have hShift : R k + 1 ≤ 2 * R k := by linarith only [hR k]
    have hPow := pow_le_pow_left₀ (by positivity : 0 ≤ R k + 1) hShift 8
    calc
      _ ≤ (2 * R k) ^ 8 := hPow
      _ = 256 * (R k) ^ 8 := by ring
      _ ≤ 256 * (R k) ^ 9 :=
        mul_le_mul_of_nonneg_left hR8 (by norm_num)
  have hPair : (Q k + 1) ^ 8 + (R k + 1) ^ 8 ≤
      (D + 256) * (R k) ^ 9 := by
    nlinarith only [hc, hInner]
  have hScaled : 36 * S ^ 2 *
      ((Q k + 1) ^ 8 + (R k + 1) ^ 8) ≤
      36 * S ^ 2 * ((D + 256) * (R k) ^ 9) :=
    mul_le_mul_of_nonneg_left hPair (by positivity)
  have hBound : 36 * S ^ 2 *
      ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1 ≤
      (36 * S ^ 2 * (D + 256) + 1) * (R k) ^ 9 := by
    calc
      _ ≤ 36 * S ^ 2 * ((D + 256) * (R k) ^ 9) + 1 :=
        add_le_add hScaled (le_refl (1 : ℝ))
      _ ≤ 36 * S ^ 2 * ((D + 256) * (R k) ^ 9) + (R k) ^ 9 :=
        add_le_add (le_refl (36 * S ^ 2 * ((D + 256) * (R k) ^ 9))) hR9
      _ = (36 * S ^ 2 * (D + 256) + 1) * (R k) ^ 9 := by ring
  have hSmaller : (36 * S ^ 2 * (D + 256) + 1) * (R k) ^ 9 <
      M * (R k) ^ 9 := by
    apply mul_lt_mul_of_pos_right _ (pow_pos hRp 9)
    dsimp only [M]
    linarith
  have hSource : S ^ 2 < C k ^ 2 := by
    by_contra hNot
    have hCeiling : C k ^ 2 ≤ S ^ 2 := le_of_not_gt hNot
    have hSpike := he hg hl hCeiling
    exact (not_lt_of_ge (hBound.trans hSmaller.le)) hSpike
  exact hASq.trans hSource.le

/-- The canonical first-crossing snapshots admit a physically attained
projected-source blowup alternative. On persistent noncompressed clocks,
with controlled sixth-order linear PDE rate and bounded critical ninth/eighth
LITERAL annular width, actual projected-source norms cross every threshold
at points in the associated shrinking half-terminal windows.

Finite full H³ dissipation and absence of a strong terminal physical L²
trace remain inputs, as do the three conditional regime tests. -/
theorem h3Path_noL2Trace_finiteDissipation_canonicalCriticalWidth_physicalSourcePeaks244
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
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        (∃ s : ℝ, s ∈ Set.Icc (τ (v k))
            (τ (v k) + (T - τ (v k)) / 2) ∧
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k))) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        Tendsto (fun k : ℕ => C (v k) ^ 2) atTop atTop ∧
        (∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          ∃ s : ℝ,
            s ∈ Set.Icc (τ (v k))
              (τ (v k) + (T - τ (v k)) / 2) ∧
            M ≤ ‖h3PathActualProjectedMomentumSource244 hH3 s‖)) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hAll, hSummable, hThree, hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalSourceDisjointThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  let R : ℕ → ℝ := fun k => ((v k : ℝ) + 1)
  let Q : ℕ → ℝ := fun k => ((N (v k) : ℝ) + 1)
  let W : ℕ → ℝ := fun k => ((N (v k) - v k : ℕ) : ℝ)
  let G : ℕ → ℝ := fun k =>
    ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)
  let F : ℕ → ℝ := fun k =>
    h3PathCubicAnnulusActualLinearRate244 N K C (v k)
  let X : ℕ → ℝ := fun k =>
    h3PathCubicAnnulusActualQuadraticRate244 N C (v k)
  let Src : ℕ → ℝ := fun k => C (v k)
  have hR : ∀ k : ℕ, 1 ≤ R k := by
    intro k
    dsimp only [R]
    have hCast : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hCast]
  have hQ : ∀ k : ℕ, 0 ≤ Q k := by
    intro k
    dsimp only [Q]
    positivity
  have hW : ∀ k : ℕ, 0 ≤ W k := by
    intro k
    dsimp only [W]
    exact Nat.cast_nonneg _
  have hN (k : ℕ) : v k ≤ N (v k) := by
    by_contra hNot
    have hLess : N (v k) < v k := Nat.lt_of_not_ge hNot
    have hCast : Q k ≤ R k := by
      dsimp only [Q, R]
      have hNat : (N (v k) : ℝ) ≤ (v k : ℝ) := by
        exact_mod_cast hLess.le
      linarith only [hNat]
    have hMon := h3Path_actualLowRadialDissipation_mono_radius244
      hH3 hClass (τ (v k)) (hTime (v k)) hCast
    have hδ : 0 ≤ δ (v k) := (hAll k).2.2.1.le
    have hAt : τ (v k) ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) :=
      ⟨le_rfl, le_add_of_nonneg_right hδ⟩
    have hFloor := (hAll k).2.2.2.2.2.1 (τ (v k)) hAt
    have hPos : 0 < ((v k : ℝ) + 1) ^ 3 / 2 := by positivity
    linarith only [hFloor, hMon, hPos]
  have hOuterEq (k : ℕ) : R k + W k + 1 = Q k + 1 := by
    have hVN := hN k
    dsimp only [R, W, Q]
    rw [Nat.cast_sub hVN]
    ring
  have hThree' : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      G k ≤ ε ∨ R k ^ 6 ≤ 16 * ε * (F k + 1) ∨
        R k ^ 9 ≤ 16 * ε ^ 2 * (X k + 1) := by
    intro ε hε
    simpa only [R, G, F, X] using hThree ε hε
  have hQuadratic : ∀ k : ℕ,
      X k = h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
        (R k) (Q k) (Src k) := by
    intro k
    rfl
  have hEighth (η B M S : ℝ) (hη : 0 < η)
      (hB : 0 ≤ B) (hM : 0 ≤ M) :
      ∀ᶠ k : ℕ in atTop,
        η ≤ G k → F k + 1 ≤ B * R k ^ 6 →
          Src k ^ 2 ≤ S ^ 2 →
            M * R k ^ 9 <
              36 * S ^ 2 * ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1 :=
    h3Path_minimalQuadraticSharp_threeScale_forces_eighthGain244
      R Q G F X Src hR hQ hThree' hQuadratic
      η B M S hη hB hM
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_⟩
  · intro k
    exact ⟨hN k, (hAll k).1, (hAll k).2.1⟩
  · intro η B D hη hB hD hRegime
    have hGeom : ∀ᶠ k : ℕ in atTop, η ≤ G k := by
      filter_upwards [hRegime] with k hk
      exact hk.1
    have hLinear : ∀ᶠ k : ℕ in atTop,
        F k + 1 ≤ B * R k ^ 6 := by
      filter_upwards [hRegime] with k hk
      exact hk.2.1
    have hCap : ∀ᶠ k : ℕ in atTop,
        (Q k + 1) ^ 8 ≤ (256 * (D + 1)) * R k ^ 9 := by
      filter_upwards [hRegime] with k hk
      have hWidth : (W k + 1) ^ 8 ≤ D * R k ^ 9 := hk.2.2
      have hOuter := h3Path_criticalWidthCap_boundsOuter244
        (R k) (W k) D (hR k) (hW k) hD hWidth
      rw [hOuterEq k] at hOuter
      exact hOuter
    have hSquare : Tendsto (fun k : ℕ => C (v k) ^ 2) atTop atTop := by
      have hResult := h3Path_canonicalEighthGain_outerCap_forces_sourceSquareEscape244
        R Q Src G (fun k => F k + 1) η B (256 * (D + 1))
        hR (by positivity) hGeom hLinear hCap
        (fun M S hM => hEighth η B M S hη hB hM)
      simpa only [Src] using hResult
    exact ⟨hSquare, hPeaks hSquare⟩

end
end PrimeTensor.FirstMonomialTriad
