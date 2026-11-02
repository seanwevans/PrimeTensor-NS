import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellEnergyBridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessDisjointEnergySourceOuterBarrier
import Mathlib.Tactic

/-!
# One canonical minimal-shell diagonal for the exact physical H3 rate barriers

The existing minimal first-crossing diagonal retains the last single integer
Fourier shell, its strictly positive raw kinetic mass, the exact quadratic
projected-source PDE window, the anchor H3 energy and the real annular cost.
We now charge the sixth/ninth PDE alternative to that SAME diagonal's physical
energy/source maximum and tenth/eighth powers of the outer cutoff.

No terminal full-H3 dissipation integrability, outer-frequency cap, or uniform
source/energy envelope is assumed. Divergent certified annular charges remain
an alternative. Last-shell positivity does not give a fixed cubic mass floor.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

-- Keep the raw Fourier kinetic mass's canonical physical measure instances.
noncomputable local instance axisFintypeMinimalShellEnergyRates
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalShellEnergyRates :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The exact minimum of the quadratic-sharp clock caps, coupled to a strict
quarter-cubic gap, has the charge-divergence / sixth-and-ninth PDE alternative
on any strictly increasing selected integer sequence. -/
theorem h3Critical_scalar_minimalShell_chargeOrSixthNinth
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hδ : ∀ k : ℕ, 0 ≤ δ (v k))
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hQuarter : ∀ k : ℕ,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k))
    (hΛ : ∀ k : ℕ, 0 ≤ Λ (v k))
    (hΞ : ∀ k : ℕ, 0 ≤ Ξ (v k)) :
    (∀ M : ℝ, ∃ q : ℕ,
      M < ∑ k ∈ Finset.range q,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) ≤ ε ∨
      ((v k : ℝ) + 1) ^ 6 ≤ 16 * ε * (Λ (v k) + 1) ∨
      ((v k : ℝ) + 1) ^ 9 ≤ 16 * ε ^ 2 * (Ξ (v k) + 1)) := by
  exact h3Critical_scalar_disjointQuadraticSharpCharges_unbounded_or_sixthNinth
    v δ b gap Λ Ξ hv hδ hExact
    (Filter.Eventually.of_forall hQuarter)
    (Filter.Eventually.of_forall hΛ)
    (Filter.Eventually.of_forall hΞ)

/-- The ORIGINAL disjoint minimal first-crossing windows have, at once:
(1) positive last-shell raw Fourier kinetic mass and an overshoot bound;
(2) their exact physical projected-source PDE widths and local integral costs;
(3) either unbounded certified cubic charges, or the physical terminal-clock,
H3 energy/source tenth-power linear rate, or source eighth-power quadratic
rate alternative. In particular no distinct nonminimal outer cutoff is used. -/
theorem h3Critical_noL2Trace_disjointMinimalShell_energySourceOuterRateBarrier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k))) ∧
      (∀ q : ℕ,
        (∑ k ∈ Finset.range q,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
        ∑ k ∈ Finset.range q,
          (∫ s in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s))) ∧
      ((∀ M : ℝ, ∃ q : ℕ,
        M < ∑ k ∈ Finset.range q,
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
               (((N (v k) : ℝ) + 2) ^ 8 +
                 ((v k : ℝ) + 2) ^ 8) + 1))) := by
  obtain ⟨t, N, m, C, δ, v, hv, hCofinal, hSeparated, hWindow⟩ :=
    h3Critical_noL2Trace_disjoint_minimalShellEnergyExactClock
      hH3 hClass hNoTrace
  let K : ℕ → ℝ := fun n =>
    ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖
  let b : ℕ → ℝ := fun n => (T - t n) / 2
  let gap : ℕ → ℝ := fun n => h3PathCubicAnnulusActualGap244 hH3 t N n
  let Λ : ℕ → ℝ := fun n => h3PathCubicAnnulusActualLinearRate244 N K C n
  let Ξ : ℕ → ℝ := fun n => h3PathCubicAnnulusActualQuadraticRate244 N C n
  have hPositive (k : ℕ) : 0 ≤ δ (v k) := by
    rcases hWindow k with ⟨_, _, _, _, hδ, _, _, _, _, _, _, _, _, _, _⟩
    exact hδ.le
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)) := by
    rcases hWindow k with ⟨_, _, _, _, _, _, hWidth, _, _, _, _, _, _, _, _⟩
    simpa only [b, gap, Λ, Ξ, K,
      h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hWidth
  have hQuarter (k : ℕ) :
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k) := by
    rcases hWindow k with ⟨_, _, _, _, _, _, _, _, hGap, _, _, _, _, _, _⟩
    exact le_of_lt (by
      simpa only [gap, h3PathCubicAnnulusActualGap244] using hGap)
  have hCnonneg (k : ℕ) : 0 ≤ C (v k) := by
    rcases hWindow k with ⟨_, _, hC, _, _, _, _, _, _, _, _, _, _, _, _⟩
    exact hC
  have hLinearNonneg (k : ℕ) : 0 ≤ Λ (v k) := by
    dsimp only [Λ, h3PathCubicAnnulusActualLinearRate244]
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (K (v k)) (C (v k)) (norm_nonneg _) (hCnonneg k)
  have hQuadraticNonneg (k : ℕ) : 0 ≤ Ξ (v k) := by
    dsimp only [Ξ, h3PathCubicAnnulusActualQuadraticRate244]
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
  have hAlternative := h3Critical_scalar_minimalShell_chargeOrSixthNinth
    v δ b gap Λ Ξ hv hPositive hExact hQuarter hLinearNonneg hQuadraticNonneg
  let I : ℕ → ℝ := fun k =>
    ∫ s in t (v k)..(t (v k) + δ (v k)),
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)
  have hCosts (k : ℕ) :
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤ I k := by
    rcases hWindow k with ⟨_, _, _, _, _, _, _, _, _, _, _, hCost, _, _, _⟩
    exact hCost
  have hSum (q : ℕ) :
      (∑ k ∈ Finset.range q,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
      ∑ k ∈ Finset.range q, I k :=
    h3Critical_scalar_finiteAnnularChargeSum_le_actualIntegralSum
      v δ I hCosts q
  refine ⟨t, N, m, C, δ, v, hv, hCofinal,
    hSeparated, hWindow, ?_, ?_⟩
  · intro q
    simpa only [I] using hSum q
  · rcases hAlternative with hUnbounded | hCaps
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
        rcases hWindow k with ⟨hNm, hnM, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
        omega
      have hRQ : R ≤ Q := by
        have hn : (v k : ℝ) ≤ (N (v k) : ℝ) := by
          exact_mod_cast hCut
        dsimp only [R, Q]
        linarith only [hn]
      have hK : 0 ≤ K₀ := by
        dsimp only [K₀, K]
        exact norm_nonneg _
      have hS : 0 ≤ S := hCnonneg k
      have hKE : K₀ ^ 2 ≤ velocityH3EnergyAt u (t (v k)) := by
        rcases hWindow k with ⟨_, _, _, _, _, _, _, hE, _, _, _, _, _, _, _⟩
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
