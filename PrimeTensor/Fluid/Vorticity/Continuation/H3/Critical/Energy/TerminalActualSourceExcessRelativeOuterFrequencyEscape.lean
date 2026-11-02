import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessDisjointEnergySourceOuterBarrier
import Mathlib.Tactic

/-!
# Exact disjoint annuli: bounded physical source and relative radius force time compression

The nonintegrable no-terminal-L²-trace branch already has a dichotomy:
unbounded certified annular charges, or eventual terminal-time compression /
R^12 linear-PDE rate / R^9 quadratic-PDE rate. We now exclude both PDE
rate arms under *explicit additional bounds*: bounded actual E₃*C² and C²,
and a relative outer cutoff Q+1 <= D R. The fifth-order linear rate gives
R^10, the quadratic rate gives R^8. These cannot pay R^12 or R^9 at
unbounded inner frequencies. The remaining nondivergent-charge arm MUST
therefore exhibit cubic terminal-time compression.

The source and relative frequency bounds are HYPOTHESES, not proved for
arbitrary Navier--Stokes solutions; this is a necessary-condition theorem,
not a terminal regularity or continuation result.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Under fixed relative outer radius Q+1 <= D*R, the physical
energy/source linear rate has at most tenth-order inner frequency growth,
and the source-quadratic rate at most eighth-order growth. -/
theorem h3Critical_scalar_relativeOuterCap_bounds_linearAndQuadraticBurdens
    (R Q E C B D : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q) (hD : 1 ≤ D)
    (hE : 0 ≤ E)
    (hES : E * C ^ 2 ≤ B) (hCS : C ^ 2 ≤ B)
    (hOuter : Q + 1 ≤ D * R) :
    E * C ^ 2 * (Q + 1) ^ 10 ≤ B * D ^ 10 * R ^ 10 ∧
    C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) ≤
      B * (D ^ 8 + 256) * R ^ 8 := by
  have hQpos : 0 ≤ Q + 1 := by linarith only [hR, hRQ]
  have hRpos : 0 ≤ R + 1 := by linarith only [hR]
  have hRtwo : R + 1 ≤ 2 * R := by linarith only [hR]
  have hQten : (Q + 1) ^ 10 ≤ D ^ 10 * R ^ 10 := by
    calc
      _ ≤ (D * R) ^ 10 := pow_le_pow_left₀ hQpos hOuter 10
      _ = D ^ 10 * R ^ 10 := by ring
  have hQeight : (Q + 1) ^ 8 ≤ D ^ 8 * R ^ 8 := by
    calc
      _ ≤ (D * R) ^ 8 := pow_le_pow_left₀ hQpos hOuter 8
      _ = D ^ 8 * R ^ 8 := by ring
  have hReight : (R + 1) ^ 8 ≤ 256 * R ^ 8 := by
    calc
      _ ≤ (2 * R) ^ 8 := pow_le_pow_left₀ hRpos hRtwo 8
      _ = 256 * R ^ 8 := by ring
  have hSum : (Q + 1) ^ 8 + (R + 1) ^ 8 ≤
      (D ^ 8 + 256) * R ^ 8 := by
    calc
      _ ≤ D ^ 8 * R ^ 8 + 256 * R ^ 8 := add_le_add hQeight hReight
      _ = (D ^ 8 + 256) * R ^ 8 := by ring
  have hEC : 0 ≤ E * C ^ 2 := mul_nonneg hE (sq_nonneg C)
  have hB : 0 ≤ B := (sq_nonneg C).trans hCS
  constructor
  · calc
      E * C ^ 2 * (Q + 1) ^ 10 ≤
          (E * C ^ 2) * (D ^ 10 * R ^ 10) :=
        mul_le_mul_of_nonneg_left hQten hEC
      _ ≤ B * (D ^ 10 * R ^ 10) :=
        mul_le_mul_of_nonneg_right hES (by positivity)
      _ = B * D ^ 10 * R ^ 10 := by ring
  · calc
      C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) ≤
          C ^ 2 * ((D ^ 8 + 256) * R ^ 8) :=
        mul_le_mul_of_nonneg_left hSum (sq_nonneg C)
      _ ≤ B * ((D ^ 8 + 256) * R ^ 8) :=
        mul_le_mul_of_nonneg_right hCS (by positivity)
      _ = B * (D ^ 8 + 256) * R ^ 8 := by ring

/-- The R^12 and R^9 arms impose an *upper* bound on R whenever
normalized tenth/eighth-order physical coefficient burdens are bounded.
Thus neither arm can survive along a cofinal increasing inner cutoff. -/
theorem h3Critical_scalar_normalizedPhysicalRates_force_boundedInnerRadius
    (R Q E C B₁ B₂ ε : ℝ)
    (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hLinearBurden : E * C ^ 2 * (Q + 1) ^ 10 ≤ B₁ * R ^ 10)
    (hQuadraticBurden : C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) ≤
      B₂ * R ^ 8)
    (hRates :
      R ^ 12 ≤ 512 * ε ^ 2 *
        (2304 * E * C ^ 2 * (Q + 1) ^ 10 + 1) ∨
      R ^ 9 ≤ 16 * ε ^ 2 *
        (36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1)) :
    R ^ 2 ≤ 512 * ε ^ 2 * (2304 * B₁ + 1) ∨
    R ≤ 16 * ε ^ 2 * (36 * B₂ + 1) := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRten : 1 ≤ R ^ 10 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hR 10)
  have hReight : 1 ≤ R ^ 8 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hR 8)
  rcases hRates with hLinear | hQuadratic
  · left
    have hScale := mul_le_mul_of_nonneg_left hLinearBurden
      (by norm_num : (0 : ℝ) ≤ 2304)
    have hCoeff : 2304 * E * C ^ 2 * (Q + 1) ^ 10 + 1 ≤
        (2304 * B₁ + 1) * R ^ 10 := by
      calc
        _ = 2304 * (E * C ^ 2 * (Q + 1) ^ 10) + 1 := by ring
        _ ≤ 2304 * (B₁ * R ^ 10) + R ^ 10 := add_le_add hScale hRten
        _ = (2304 * B₁ + 1) * R ^ 10 := by ring
    have hBound : R ^ 2 * R ^ 10 ≤
        (512 * ε ^ 2 * (2304 * B₁ + 1)) * R ^ 10 := by
      calc
        _ = R ^ 12 := by ring
        _ ≤ 512 * ε ^ 2 *
          (2304 * E * C ^ 2 * (Q + 1) ^ 10 + 1) := hLinear
        _ ≤ 512 * ε ^ 2 * ((2304 * B₁ + 1) * R ^ 10) :=
          mul_le_mul_of_nonneg_left hCoeff (by positivity)
        _ = _ := by ring
    by_contra hNot
    have hStrict : 512 * ε ^ 2 * (2304 * B₁ + 1) < R ^ 2 :=
      lt_of_not_ge hNot
    have hMult := mul_lt_mul_of_pos_right hStrict (pow_pos hRpos 10)
    exact (not_lt_of_ge hBound) hMult
  · right
    have hScale := mul_le_mul_of_nonneg_left hQuadraticBurden
      (by norm_num : (0 : ℝ) ≤ 36)
    have hCoeff : 36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1 ≤
        (36 * B₂ + 1) * R ^ 8 := by
      calc
        _ = 36 * (C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8)) + 1 := by ring
        _ ≤ 36 * (B₂ * R ^ 8) + R ^ 8 := add_le_add hScale hReight
        _ = (36 * B₂ + 1) * R ^ 8 := by ring
    have hBound : R * R ^ 8 ≤
        (16 * ε ^ 2 * (36 * B₂ + 1)) * R ^ 8 := by
      calc
        _ = R ^ 9 := by ring
        _ ≤ 16 * ε ^ 2 *
          (36 * C ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := hQuadratic
        _ ≤ 16 * ε ^ 2 * ((36 * B₂ + 1) * R ^ 8) :=
          mul_le_mul_of_nonneg_left hCoeff (by positivity)
        _ = _ := by ring
    by_contra hNot
    have hStrict : 16 * ε ^ 2 * (36 * B₂ + 1) < R :=
      lt_of_not_ge hNot
    have hMult := mul_lt_mul_of_pos_right hStrict (pow_pos hRpos 8)
    exact (not_lt_of_ge hBound) hMult

/-- An increasing subsequence of natural frequencies eventually exceeds
any fixed real bound. -/
theorem h3Critical_scalar_strictMono_innerRadius_eventually_exceeds
    (v : ℕ → ℕ) (hv : StrictMono v) (M : ℝ) :
    ∀ᶠ k : ℕ in atTop, M < (v k : ℝ) + 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt M
  apply Filter.eventually_atTop.2
  refine ⟨n, ?_⟩
  intro k hk
  have hIndex : n ≤ v k := le_trans hk hv.le_apply
  have hCast : (n : ℝ) ≤ (v k : ℝ) := by exact_mod_cast hIndex
  linarith only [hn, hCast]

/-- On the actual no-trace H3 annular witnesses, if the source square,
energy--source product, and relative outer cutoff are eventually bounded,
then either the certified annular charges diverge or the *geometric*
terminal slack must collapse at the inverse-cubic rate. This does not
assume global full-H3 dissipation integrability. -/
theorem h3Critical_noL2Trace_disjointActiveAnnuli_boundedSourceRelativeOuter_forces_compression
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
        ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ ^ 2 ≤
          velocityH3EnergyAt u (t (v k)) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t (v k)) (t (v k) + (T - t (v k)) / 2)) ∧
      ((∀ M : ℝ, ∃ m : ℕ,
        M < ∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
       (∀ B D : ℝ, 0 ≤ B → 1 ≤ D →
         (∀ᶠ k : ℕ in atTop,
           velocityH3EnergyAt u (t (v k)) * (C (v k)) ^ 2 ≤ B) →
         (∀ᶠ k : ℕ in atTop, (C (v k)) ^ 2 ≤ B) →
         (∀ᶠ k : ℕ in atTop,
           ((N (v k) : ℝ) + 2) ≤ D * ((v k : ℝ) + 1)) →
         ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
           ((v k : ℝ) + 1) ^ 3 * ((T - t (v k)) / 4) ≤ ε)) := by
  obtain ⟨t, N, C, δ, v, hv, hCofinal, hSeparated,
      hSelected, _hCosts, hAlternative⟩ :=
    h3Critical_noL2Trace_disjointQuarterCubicAnnuli_energySourceOuterBarrier
      hH3 hClass hNoTrace
  have hPhysical (k : ℕ) :
      v k ≤ N (v k) ∧ 0 ≤ C (v k) ∧ 0 < δ (v k) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ ^ 2 ≤
        velocityH3EnergyAt u (t (v k)) ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (t (v k)) (t (v k) + (T - t (v k)) / 2) := by
    obtain ⟨_, hN, hC, hδ, hE, _, hEnvelope, _, _⟩ := hSelected k
    exact ⟨hN, hC, hδ, hE, hEnvelope⟩
  refine ⟨t, N, C, δ, v, hv, hCofinal, hSeparated, hPhysical, ?_⟩
  rcases hAlternative with hUnbounded | hRates
  · exact Or.inl hUnbounded
  · right
    intro B D hB hD hEnergySource hSource hOuter ε hε
    let L : ℝ := 512 * ε ^ 2 * (2304 * (B * D ^ 10) + 1)
    let P : ℝ := 16 * ε ^ 2 * (36 * (B * (D ^ 8 + 256)) + 1)
    have hLarge := h3Critical_scalar_strictMono_innerRadius_eventually_exceeds
      v hv (max L P)
    filter_upwards [hRates ε hε, hEnergySource, hSource, hOuter, hLarge]
      with k hk hkES hkCS hkOuter hkLarge
    let R : ℝ := (v k : ℝ) + 1
    let Q : ℝ := (N (v k) : ℝ) + 1
    let E : ℝ := velocityH3EnergyAt u (t (v k))
    let S : ℝ := C (v k)
    have hR : 1 ≤ R := by
      dsimp only [R]
      have hNat : 0 ≤ (v k : ℝ) := Nat.cast_nonneg _
      linarith only [hNat]
    have hRQ : R ≤ Q := by
      have hn : v k ≤ N (v k) := (hPhysical k).1
      have hCast : (v k : ℝ) ≤ (N (v k) : ℝ) := by exact_mod_cast hn
      dsimp only [R, Q]
      linarith only [hCast]
    have hE : 0 ≤ E := by
      have hKE := (hPhysical k).2.2.2.1
      dsimp only [E]
      exact (sq_nonneg _).trans hKE
    have hES : E * S ^ 2 ≤ B := by
      simpa only [E, S] using hkES
    have hCS : S ^ 2 ≤ B := by
      simpa only [S] using hkCS
    have hOuter' : Q + 1 ≤ D * R := by
      simpa only [Q, R,
        show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
        using hkOuter
    obtain ⟨hLburden, hPburden⟩ :=
      h3Critical_scalar_relativeOuterCap_bounds_linearAndQuadraticBurdens
        R Q E S B D hR hRQ hD hE hES hCS hOuter'
    have hRBound : R ≤ R ^ 2 := by
      have hOne : 0 ≤ R - 1 := sub_nonneg.mpr hR
      have hNonneg : 0 ≤ R := by linarith only [hR]
      have hProd := mul_nonneg hNonneg hOne
      nlinarith only [hProd]
    have hLarge' : max L P < R := by simpa only [R] using hkLarge
    rcases hk with hTime | hLinear | hQuadratic
    · exact hTime
    · have hSmall :=
        h3Critical_scalar_normalizedPhysicalRates_force_boundedInnerRadius
          R Q E S (B * D ^ 10) (B * (D ^ 8 + 256)) ε
          hR hε.le hLburden hPburden (Or.inl (by
            simpa only [R, Q, E, S,
              show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring] using hLinear))
      rcases hSmall with hRadial | hImpossible
      · have hThreshold : L < R := lt_of_le_of_lt (le_max_left _ _) hLarge'
        have hContrary : R ^ 2 < R := lt_of_le_of_lt hRadial hThreshold
        exact False.elim ((not_lt_of_ge hRBound) hContrary)
      · have hThreshold : P < R := lt_of_le_of_lt (le_max_right _ _) hLarge'
        exact False.elim ((not_lt_of_ge hImpossible) hThreshold)
    · have hSmall :=
        h3Critical_scalar_normalizedPhysicalRates_force_boundedInnerRadius
          R Q E S (B * D ^ 10) (B * (D ^ 8 + 256)) ε
          hR hε.le hLburden hPburden (Or.inr (by
            simpa only [R, Q, S,
              show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring,
              show (v k : ℝ) + 1 + 1 = (v k : ℝ) + 2 by ring] using hQuadratic))
      rcases hSmall with hRadial | hImpossible
      · have hThreshold : L < R := lt_of_le_of_lt (le_max_left _ _) hLarge'
        have hContrary : R ^ 2 < R := lt_of_le_of_lt hRadial hThreshold
        exact False.elim ((not_lt_of_ge hRBound) hContrary)
      · have hThreshold : P < R := lt_of_le_of_lt (le_max_right _ _) hLarge'
        exact False.elim ((not_lt_of_ge hImpossible) hThreshold)

end
end PrimeTensor.Bridge.Euclidean
