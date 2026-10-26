import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEExactClockConcentration244
import Mathlib.Tactic

/-!
# Vanishing exact cubic PDE caps: the asymptotically sharp alternative

Under finite terminal H³ dissipation, disjoint cubic persistence costs are
summable. In particular their individual cubic-weighted widths vanish.
Unlike an alternative with a fixed total dissipation bound M, this gives a
family of terminal alternatives for *every* positive epsilon.

The exact selector is min(b/2, 1, gap/(2*(Λ+Ξ+1))). Once the cubic
height exceeds epsilon, the unit cap cannot account for a width of cost
at most epsilon. Hence the cubic-weighted geometric cap or the
cubic-weighted **normalized** PDE gap must be at most epsilon.

Crucially this conclusion needs no global or local uniform estimates for
the PDE coefficients. Geometric compression remains a genuine alternative.
Neither finite full H³ dissipation nor a noncompressed cubic terminal lag
is claimed to follow from preterminal admissibility.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A small cost for the literal three-cap minimum must be explained by
one of the two non-unit caps, once the unit cap itself is too costly.
This is algebraic and does not require positivity of the coefficients
hidden in the PDE cap. -/
theorem h3Path_exactMinWidth_smallCost_forces_twoCaps244
    (A M b q δ : ℝ)
    (hA : 0 < A) (hUnit : M < A)
    (hExact : δ = min (b / 2) (min (1 : ℝ) q))
    (hCost : A * δ ≤ M) :
    A * (b / 2) ≤ M ∨ A * q ≤ M := by
  by_contra hNot
  push_neg at hNot
  have hWidth : δ ≤ M / A := by
    apply (le_div_iff₀ hA).2
    calc
      δ * A = A * δ := by ring
      _ ≤ M := hCost
  have hTimeSmall : M / A < b / 2 := by
    apply (div_lt_iff₀ hA).2
    simpa only [mul_comm] using hNot.1
  have hUnitSmall : M / A < (1 : ℝ) := by
    apply (div_lt_iff₀ hA).2
    simpa only [one_mul] using hUnit
  have hPDESmall : M / A < q := by
    apply (div_lt_iff₀ hA).2
    simpa only [mul_comm] using hNot.2
  rw [hExact] at hWidth
  exact (not_lt_of_ge hWidth)
    (lt_min hTimeSmall (lt_min hUnitSmall hPDESmall))

/-- Sharp eventual alternative: for *each* epsilon>0, either the cubic
terminal-time cap or the cubic normalized anchored-PDE cap is at most
epsilon. The proof uses the vanishing actual costs, not their fixed
finite sum bound. Exactness of the selected widths is essential. -/
theorem h3Path_exactCubicClocks_vanishingCapAlternative244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusExactPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 3 *
          (gap (v k) /
            (2 * (Λ (v k) + Ξ (v k) + 1))) ≤ ε := by
  intro ε hε
  have hLarge :=
    h3Path_strictMonoCubicHeight_eventually_above_mass244
      v hv (ε / 2)
  have hSmall : ∀ᶠ k : ℕ in atTop,
      δ (v k) * ((v k : ℝ) + 1) ^ 3 < ε :=
    hCollapse.eventually (eventually_lt_nhds hε)
  filter_upwards [hLarge, hSmall] with k hkLarge hkSmall
  have hA : 0 < ((v k : ℝ) + 1) ^ 3 := by positivity
  have hUnit : ε < ((v k : ℝ) + 1) ^ 3 := by
    linarith only [hkLarge]
  have hCost : ((v k : ℝ) + 1) ^ 3 * δ (v k) ≤ ε := by
    calc
      ((v k : ℝ) + 1) ^ 3 * δ (v k) =
          δ (v k) * ((v k : ℝ) + 1) ^ 3 := by ring
      _ ≤ ε := le_of_lt hkSmall
  exact h3Path_exactMinWidth_smallCost_forces_twoCaps244
    (((v k : ℝ) + 1) ^ 3) ε (b (v k))
    (gap (v k) /
      (2 * (Λ (v k) + Ξ (v k) + 1))) (δ (v k))
    hA hUnit
    (by simpa only [h3PathCubicAnnulusExactPDEWidth244] using hExact k)
    hCost

/-- Conditional concentration theorem. If the cubic-scaled remaining
terminal time has an eventual positive floor, its geometric cap cannot
explain the vanishing exact-window cost. Thus the cubic-scaled normalized
PDE gap is eventually below *every* positive epsilon. In conjunction
with nonnegativity of the gap and of the PDE rate, this is its zero limit.
No geometric lower bound is deduced here. -/
theorem h3Path_exactCubicClocks_geometricNoncollapse_forces_normalizedPDEGap244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusExactPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η)
    (hGeometry : ∀ᶠ k : ℕ in atTop,
      η ≤ ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 *
          (gap (v k) /
            (2 * (Λ (v k) + Ξ (v k) + 1))) ≤ ε := by
  intro ε hε
  have hTest : 0 < min ε (η / 2) := by
    apply lt_min
    · exact hε
    · linarith only [hη]
  have hAlt := h3Path_exactCubicClocks_vanishingCapAlternative244
    v δ b gap Λ Ξ hv hExact hCollapse (min ε (η / 2)) hTest
  filter_upwards [hGeometry, hAlt] with k hkGeom hkAlt
  rcases hkAlt with hTime | hPDE
  · have hMin : min ε (η / 2) ≤ η / 2 := min_le_right _ _
    exact False.elim (by linarith only [hkGeom, hTime, hMin, hη])
  · exact le_trans hPDE (min_le_left _ _)

/-- Physical application of the sharp vanishing-cap alternative, using
actual cofinal no-L²-trace cubic annuli and *the same disjoint exact
windows* from the preceding synchronization theorem. No source ceiling
is assumed bounded independently of the selected cutoff. -/
theorem h3Path_noL2Trace_finiteDissipation_vanishingExactPDECaps244
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
      (∀ k : ℕ, 0 < δ (v k)) ∧
      (∀ k : ℕ,
        δ (v k) = h3PathCubicAnnulusExactPDEWidth244
          ((T - τ (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
          (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
          (h3PathCubicAnnulusActualQuadraticRate244 N C (v k))) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 3 *
          (h3PathCubicAnnulusActualGap244 hH3 τ N (v k) /
            (2 * (h3PathCubicAnnulusActualLinearRate244 N K C (v k) +
                  h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1))) ≤ ε) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate,
      hPositive, hExact, hSummable, hCollapse, _⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactPDEClockConcentration244
      hH3 hClass hMass hNoTrace hDInt
  have hSharp := h3Path_exactCubicClocks_vanishingCapAlternative244
    v δ (fun n => (T - τ n) / 2)
    (h3PathCubicAnnulusActualGap244 hH3 τ N)
    (h3PathCubicAnnulusActualLinearRate244 N K C)
    (h3PathCubicAnnulusActualQuadraticRate244 N C)
    hv hExact hCollapse
  exact ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate,
    hPositive, hExact, hSummable, hSharp⟩

end
end PrimeTensor.FirstMonomialTriad
