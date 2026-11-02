import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessDisjointAnnularChargeAlternative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticSharpClock244
import Mathlib.Tactic

/-!
# Nonintegrable-branch disjoint H³ annular charge and exact quadratic PDE clocks

The existing physical cubic-annulus diagonal has disjoint strictly preterminal
windows with exact unlinearized PDE persistence widths. Its charge alternative
is not conditional on finite terminal dissipation. Here we transport that
alternative through the exact minimum of four independent clock caps.

If the positive cubic charges have bounded partial sums, their heights times
widths vanish. Because the inner frequency tends to infinity, the unit cap
cannot account for that collapse. At every positive tolerance, the surviving
possibilities are compressed terminal slack, a small linear-rate cap, or a
small square-root quadratic-rate cap. No false terminal L¹ assumption is made.

A separate scalar lemma isolates the stronger sixth/ninth-order PDE obstruction
under an explicit quarter-cubic annular-gap bound. That extra gap hypothesis
is NOT inferred from the weaker existing disjoint-window certificate, which
retains only an annular floor. Establishing it for the selected exact-anchor
windows is the next physical selection problem.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A disjoint nonnegative cubic charge sequence either has unbounded partial
sums or its *literal quadratic-sharp* PDE selector eventually lies below one
of the three nontrivial scaled caps. No full dissipation integrability. -/
theorem h3Critical_scalar_disjointQuadraticSharpCharges_unbounded_or_threeCaps
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hδ : ∀ k : ℕ, 0 ≤ δ (v k))
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k))) :
    (∀ M : ℝ, ∃ m : ℕ,
      M < ∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) ≤ ε ∨
      ((v k : ℝ) + 1) ^ 3 *
        (gap (v k) / (4 * (Λ (v k) + 1))) ≤ ε ∨
      ((v k : ℝ) + 1) ^ 3 *
        Real.sqrt (gap (v k) / (4 * (Ξ (v k) + 1))) ≤ ε) := by
  rcases h3Critical_scalar_disjointCubicCharges_unbounded_or_widthCollapse
      v δ hδ with hUnbounded | hCollapse
  · exact Or.inl hUnbounded
  · exact Or.inr (h3Path_exactQuadraticSharpClocks_vanishingThreeCapAlternative244
      v δ b gap Λ Ξ hv hExact hCollapse)

/-- If the *same* selected exact-width annuli additionally have a quarter-
cubic physical gap, small cubic charges force geometric compression or a
sixth-order linear / ninth-order quadratic PDE coefficient barrier.
This is a separate conditional strengthening, not an assertion that the
current cofinal selection already exports the gap certificate. -/
theorem h3Critical_scalar_disjointQuadraticSharpCharges_unbounded_or_sixthNinth
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hδ : ∀ k : ℕ, 0 ≤ δ (v k))
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k))
    (hΛ : ∀ᶠ k : ℕ in atTop, 0 ≤ Λ (v k))
    (hΞ : ∀ᶠ k : ℕ in atTop, 0 ≤ Ξ (v k)) :
    (∀ M : ℝ, ∃ m : ℕ,
      M < ∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) ≤ ε ∨
      ((v k : ℝ) + 1) ^ 6 ≤ 16 * ε * (Λ (v k) + 1) ∨
      ((v k : ℝ) + 1) ^ 9 ≤ 16 * ε ^ 2 * (Ξ (v k) + 1)) := by
  rcases h3Critical_scalar_disjointCubicCharges_unbounded_or_widthCollapse
      v δ hδ with hUnbounded | hCollapse
  · exact Or.inl hUnbounded
  · exact Or.inr (h3Path_exactQuadraticSharpClocks_threeScaleBarrier244
      v δ b gap Λ Ξ hv hExact hCollapse hQuarter hΛ hΞ)

/-- Physical non-L²-trace endpoint: genuine, disjoint, cofinal cubic annuli
satisfy either unbounded *certified* charge sums, or the three precise
quadratic-sharp temporal/linear/quadratic caps. All source and spectral rates
are the actual PDE coefficients, with K fixed to the actual Fourier state
norm. There is no finite terminal dissipation premise. -/
theorem h3Critical_noL2Trace_disjointActiveAnnuli_unboundedCharge_or_quadraticSharpThreeCaps
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N : ℕ → ℕ, ∃ K C δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ n : ℕ, K n = ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖) ∧
      (∀ k : ℕ,
        k ≤ v k ∧ 0 < δ (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
        δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - t (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 t N (v k))
          (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
          (h3PathCubicAnnulusActualQuadraticRate244 N C (v k))) ∧
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
         ((v k : ℝ) + 1) ^ 3 *
           (h3PathCubicAnnulusActualGap244 hH3 t N (v k) /
             (4 * (h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1))) ≤ ε ∨
         ((v k : ℝ) + 1) ^ 3 *
           Real.sqrt (h3PathCubicAnnulusActualGap244 hH3 t N (v k) /
             (4 * (h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1))) ≤ ε)) := by
  obtain ⟨t, N, C, δ, v, hMono, hCofinal, hSeparated,
    hSelected, hSum, _hOldAlternative⟩ :=
    h3Critical_noL2Trace_disjointActiveAnnuli_unboundedCharge_or_cubicClockCollapse
      hH3 hClass hNoTrace
  let K : ℕ → ℝ := fun n =>
    ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖
  let b : ℕ → ℝ := fun n => (T - t n) / 2
  let gap : ℕ → ℝ := fun n => h3PathCubicAnnulusActualGap244 hH3 t N n
  let Λ : ℕ → ℝ := fun n => h3PathCubicAnnulusActualLinearRate244 N K C n
  let Ξ : ℕ → ℝ := fun n => h3PathCubicAnnulusActualQuadraticRate244 N C n
  have hPositive (k : ℕ) : 0 ≤ δ (v k) := (hSelected k).2.1.le
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)) := by
    obtain ⟨_, _, _, _, hWidth, _, _⟩ := hSelected k
    simpa only [b, gap, Λ, Ξ, K,
      h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hWidth
  have hAlternative :=
    h3Critical_scalar_disjointQuadraticSharpCharges_unbounded_or_threeCaps
      v δ b gap Λ Ξ hMono hPositive hExact
  have hSelected' (k : ℕ) :
      k ≤ v k ∧ 0 < δ (v k) ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - t (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 t N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    obtain ⟨hIndex, hδ, _hEnd, hEnvelope, hWidth, _, _⟩ := hSelected k
    exact ⟨hIndex, hδ, hEnvelope, by simpa only [K,
      h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hWidth⟩
  refine ⟨t, N, K, C, δ, v,
    hMono, hCofinal, hSeparated, (fun n => rfl), hSelected', hSum, ?_⟩
  rcases hAlternative with hUnbounded | hCaps
  · exact Or.inl hUnbounded
  · right
    intro ε hε
    filter_upwards [hCaps ε hε] with k hk
    rcases hk with hTime | hLinear | hQuadratic
    · left
      change ((v k : ℝ) + 1) ^ 3 * (((T - t (v k)) / 2) / 2) ≤ ε at hTime
      convert hTime using 1 <;> ring
    · exact Or.inr (Or.inl (by
        simpa only [gap, Λ, K,
          h3PathCubicAnnulusActualGap244,
          h3PathCubicAnnulusActualLinearRate244] using hLinear))
    · exact Or.inr (Or.inr (by
        simpa only [gap, Ξ,
          h3PathCubicAnnulusActualGap244,
          h3PathCubicAnnulusActualQuadraticRate244] using hQuadratic))

end
end PrimeTensor.Bridge.Euclidean
