import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellEveryTailSignedReplenishment
import Mathlib.Tactic

/-!
# Minimal H3 first crossings: quadratic physical energy cost of a Riccati window

The previously established EVERY-TAIL signed-gap theorem distinguishes large
Riccati energy from cumulative viscous drains. Here the original Riccati
exception is quantified without resampling the physical PDE witnesses:

  R^3 / 2 < K sqrt(E) E  ==>  R^2 < (4 K^2 + 1) E.

Thus the exceptional windows necessarily contain H3 energy on the quadratic
inner-frequency scale. The precise physical consequence is CONDITIONAL on
both divergent cubic-window charges and bounded positive inter-window signed
transport, just as in the preceding accepted theorem. Neither condition is
inferred from Navier--Stokes, and no terminal full-H3 budget is added.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalRiccatiQuadratic
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalRiccatiQuadratic :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A strict cubic Riccati peak forces quadratic energy. The harmless +1
keeps the coefficient positive without requiring division by K. -/
theorem h3Critical_scalar_riccatiCubicPeak_forces_quadraticEnergy
    (R K E : ℝ) (hR : 0 < R) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hPeak : R ^ 3 / 2 < K * Real.sqrt E * E) :
    R ^ 2 < (4 * K ^ 2 + 1) * E := by
  have hRoot : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  have hLeft : 0 ≤ R ^ 3 / 2 := by positivity
  have hRight : 0 ≤ K * Real.sqrt E * E := by positivity
  have hSq : (R ^ 3 / 2) ^ 2 < (K * Real.sqrt E * E) ^ 2 :=
    (sq_lt_sq₀ hLeft hRight).2 hPeak
  have hSqEq : (K * Real.sqrt E * E) ^ 2 = K ^ 2 * E ^ 3 := by
    calc
      _ = K ^ 2 * (Real.sqrt E) ^ 2 * E ^ 2 := by ring
      _ = K ^ 2 * E ^ 3 := by rw [hRoot]; ring
  rw [hSqEq] at hSq
  have hCubic : R ^ 6 < 4 * K ^ 2 * E ^ 3 := by
    nlinarith only [hSq]
  let B : ℝ := 4 * K ^ 2 + 1
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    nlinarith only [sq_nonneg K]
  have hKB : 4 * K ^ 2 ≤ B := by
    dsimp only [B]
    linarith
  have hB0 : 0 ≤ B :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) hB1
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB1
  have hB3 : B ≤ B ^ 3 := by
    calc
      B = B * 1 := by ring
      _ ≤ B * B ^ 2 := mul_le_mul_of_nonneg_left hB2 hB0
      _ = B ^ 3 := by ring
  by_contra hNot
  have hBE : B * E ≤ R ^ 2 := le_of_not_gt hNot
  have hBE0 : 0 ≤ B * E := mul_nonneg hB0 hE
  have hCubeLe : (B * E) ^ 3 ≤ (R ^ 2) ^ 3 :=
    pow_le_pow_left₀ hBE0 hBE 3
  have hMass0 : 0 ≤ E ^ 3 := pow_nonneg hE 3
  have hCoeff : 4 * K ^ 2 ≤ B ^ 3 := hKB.trans hB3
  have hCoeffLe : 4 * K ^ 2 * E ^ 3 ≤ B ^ 3 * E ^ 3 :=
    mul_le_mul_of_nonneg_right hCoeff hMass0
  have hImpossible : R ^ 6 < R ^ 6 := by
    calc
      R ^ 6 < 4 * K ^ 2 * E ^ 3 := hCubic
      _ ≤ B ^ 3 * E ^ 3 := hCoeffLe
      _ = (B * E) ^ 3 := by ring
      _ ≤ (R ^ 2) ^ 3 := hCubeLe
      _ = R ^ 6 := by ring
  exact (lt_irrefl _) hImpossible

/-- A cubic Riccati exception on an original selected physical window has
a genuine physical time paying the quadratic H3 energy amplitude cost. -/
def h3CriticalMinimalShellQuadraticEnergyWindowAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ s : ℝ,
    s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) ∧
    ((v k : ℝ) + 1) ^ 2 <
      (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u s

/-- Transport the actual Riccati exception to its quadratic H3 amplitude;
no nondecreasing-energy assumption or terminal H3 ceiling is used. -/
theorem h3Critical_minimalShellRiccatiWindow_forces_quadraticEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ)
    (hRiccati : h3CriticalMinimalShellRiccatiWindowAt u t δ v k) :
    h3CriticalMinimalShellQuadraticEnergyWindowAt u t δ v k := by
  obtain ⟨s, hs, hPeak⟩ := hRiccati
  refine ⟨s, hs, ?_⟩
  have hR : 0 < (v k : ℝ) + 1 := by positivity
  have hE : 0 ≤ velocityH3EnergyAt u s :=
    (zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_velocityH3EnergyAt u s)
  exact h3Critical_scalar_riccatiCubicPeak_forces_quadraticEnergy
    ((v k : ℝ) + 1) h3PathSqrtEnergyRiccatiCoefficient
    (velocityH3EnergyAt u s) hR
    h3PathSqrtEnergyRiccatiCoefficient_nonneg hE hPeak

/-- The SAME minimal first-crossing physical PDE, positive raw shell,
actual width/energy constraints and sixth/ninth rates have the sharper
conditional cofinal alternative: recurrent Riccati windows exhibit H3
energy at least on the quadratic inner-frequency scale. -/
theorem h3Critical_noL2Trace_minimalShell_cofinalQuadraticEnergyWindows
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v j : ℕ → ℕ, ∃ k₁ : ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k))) ∧
      h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
        T t N C δ v ∧
      (∀ k : ℕ,
        1 < 4 * (velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1)) *
          (((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) ^ 2) ∧
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      (∀ k : ℕ, k₁ ≤ k →
        h3CriticalMinimalShellSignedTransportBudgetAt
          hH3 (t (v k)) (v k) (δ (v k))) ∧
      h3CriticalMinimalShellEveryTailSignedAccounting u t δ v k₁ ∧
      (h3CriticalMinimalShellEveryTailCubicChargeUnbounded δ v k₁ →
        h3CriticalMinimalShellEveryTailGapBudget u t δ v k₁ →
        ∀ b : ℕ, ∃ i : ℕ, b ≤ i ∧
          h3CriticalMinimalShellQuadraticEnergyWindowAt
            u t δ v (i + k₁)) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
      hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
      hRecurring⟩ :=
    h3Critical_noL2Trace_minimalShell_everyTailSignedRiccatiOrGap
      hH3 hClass hNoTrace
  refine ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
    hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting, ?_⟩
  intro hCharge hBudget b
  obtain ⟨i, hi, hRiccati⟩ := hRecurring hCharge hBudget b
  exact ⟨i, hi,
    h3Critical_minimalShellRiccatiWindow_forces_quadraticEnergy
      u t δ v (i + k₁) hRiccati⟩

end
end PrimeTensor.Bridge.Euclidean
