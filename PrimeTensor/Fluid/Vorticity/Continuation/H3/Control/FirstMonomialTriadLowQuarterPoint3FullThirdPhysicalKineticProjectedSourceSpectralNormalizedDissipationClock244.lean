import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralMovingRadialDominance244
import Mathlib.Tactic

/-!
# Dominant moving spectral mass forces normalized physical H³ dissipation clocks

The moving-cutoff theorem already supplies ONE terminal sequence, under
failure of a strong physical kinetic L² terminal trace, on which

  (R+1) High_R(S(t)) > R SpectralSquareEnergy(S(t)),
  D_H3(t) >= R² High_R(S(t)), and D_H3(t) > R³,

where R=n+1 and the true weighted spectral energy is E_H3(t)-1.

Combining the first two inequalities gives

  R³ (E_H3(t)-1) < (R+1) D_H3(t).

The third inequality absorbs the missing zeroth-order unit from the full
physical energy, giving a genuinely normalized PHYSICAL clock:

  R³ E_H3(t) < (R+2) D_H3(t).

For R>=2 this implies D_H3(t)/E_H3(t)>R. Thus the normalized physical
H³ dissipation diverges on the SAME terminal sequence, without assuming
smooth nonextension. The argument does NOT eliminate the no-kinetic-trace
branch: it constrains that branch quantitatively.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A high-radial fraction greater than R/(R+1), together with the actual
radial spectral dissipation bound, forces a cubic weighted-energy clock.
No spectral point evaluation or time regularity enters this algebraic step. -/
theorem h3Path_dominantRadialMass_forces_cubicDissipationEnergyClock244
    (E H D R : ℝ)
    (hR : 0 < R)
    (hDominant : R * E < (R + 1) * H)
    (hDissipation : R ^ 2 * H ≤ D) :
    R ^ 3 * E < (R + 1) * D := by
  calc
    R ^ 3 * E = R ^ 2 * (R * E) := by ring
    _ < R ^ 2 * ((R + 1) * H) :=
      mul_lt_mul_of_pos_left hDominant (pow_pos hR 2)
    _ = (R + 1) * (R ^ 2 * H) := by ring
    _ ≤ (R + 1) * D :=
      mul_le_mul_of_nonneg_left hDissipation (by linarith)

/-- The normalized cubic clock exceeds its frequency radius when R>=2.
The denominator is the positive genuine physical H³ energy. -/
theorem h3Path_cubicDissipationEnergyClock_forces_ratio_gt_radius244
    (E D R : ℝ)
    (hR : 2 ≤ R)
    (hE : 0 < E)
    (hClock : R ^ 3 * E < (R + 2) * D) :
    R < D / E := by
  have hPolynomial : R + 2 ≤ R ^ 2 := by
    have hProduct : 0 ≤ (R - 2) * (R + 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [hProduct]
  have hFactor : R * (R + 2) ≤ R ^ 3 := by
    calc
      R * (R + 2) ≤ R * R ^ 2 :=
        mul_le_mul_of_nonneg_left hPolynomial (by linarith)
      _ = R ^ 3 := by ring
  have hScaled : (R * (R + 2)) * E ≤ R ^ 3 * E :=
    mul_le_mul_of_nonneg_right hFactor hE.le
  have hProduct : (R + 2) * (R * E) < (R + 2) * D := by
    calc
      (R + 2) * (R * E) = (R * (R + 2)) * E := by ring
      _ ≤ R ^ 3 * E := hScaled
      _ < (R + 2) * D := hClock
  have hPositive : 0 < R + 2 := by linarith
  have hRE : R * E < D := by
    by_contra hNot
    have hReverse : D ≤ R * E := le_of_not_gt hNot
    have hScaledReverse :
        (R + 2) * D ≤ (R + 2) * (R * E) :=
      mul_le_mul_of_nonneg_left hReverse hPositive.le
    exact (not_lt_of_ge hScaledReverse) hProduct
  exact (lt_div_iff₀ hE).2 hRE

/-- The SAME moving-radial dominance witness has physical full-H³-energy
normalized dissipation above the quadratic intrinsic frequency scale.
The expression is deliberately cross-multiplied to preserve the exact clock
without concealing its positive denominator. -/
theorem h3Path_physicalNoL2Trace_forces_normalizedDissipationClockSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u (τ n) <
          ((n : ℝ) + 3) * velocityH3DissipationAt u (τ n)) := by
  obtain ⟨τ, hτ, hNear, hTendsto, hDominance, hCubic⟩ :=
    h3Path_physicalNoL2Trace_forces_movingRadialHighDominanceSequence244
      hH3 hClass hL hNoTrace
  refine ⟨τ, hτ, hNear, hTendsto, ?_⟩
  intro n
  let R : ℝ := (n : ℝ) + 1
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 (τ n)
  let H : ℝ := h3PathActualSpectralHighRadialRemainder244 R G
  let E : ℝ := h3SpectralVelocitySquareEnergy G
  let D : ℝ := velocityH3DissipationAt u (τ n)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hDom : R * E < (R + 1) * H := by
    dsimp only [R, G, E, H]
    simpa only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      using hDominance n
  have hRadial : R ^ 2 * H ≤ D := by
    dsimp only [H, G, D]
    rw [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
    exact h3Path_physicalDissipation_ge_highRadialSpectralMass244
      hH3 hClass (τ n) (hτ n) R hR.le
  have hSpectralClock : R ^ 3 * E < (R + 1) * D :=
    h3Path_dominantRadialMass_forces_cubicDissipationEnergyClock244
      E H D R hR hDom hRadial
  have hTime : τ n ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (hτ n).1, (hτ n).2⟩
  have hEnergy : 1 + E = velocityH3EnergyAt u (τ n) := by
    dsimp only [E, G]
    exact h3AuditActualSpectralVelocityTotal_energy_exact hH3 (τ n) hTime
  have hCube : R ^ 3 < D := by
    dsimp only [R, D]
    exact hCubic n
  have hFull : R ^ 3 * velocityH3EnergyAt u (τ n) < (R + 2) * D := by
    calc
      R ^ 3 * velocityH3EnergyAt u (τ n) = R ^ 3 * (E + 1) := by
        rw [← hEnergy]
        ring
      _ = R ^ 3 * E + R ^ 3 := by ring
      _ < (R + 1) * D + D := add_lt_add hSpectralClock hCube
      _ = (R + 2) * D := by ring
  simpa only [R, D, show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
    using hFull

/-- Failure of a strong physical kinetic trace forces the ACTUAL normalized
full H³ dissipation D_H3/E_H3 to tend to infinity along a terminal sequence.
Unlike analogous nonextension clocks, no failure-of-H³-extension premise is
required, and the conclusion is only along the selected sequence. -/
theorem h3Path_physicalNoL2Trace_forces_normalizedDissipationRatioDivergence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        velocityH3DissipationAt u (τ n) /
          velocityH3EnergyAt u (τ n)) atTop atTop := by
  obtain ⟨τ, hτ, _hNear, hTendsto, hClock⟩ :=
    h3Path_physicalNoL2Trace_forces_normalizedDissipationClockSequence244
      hH3 hClass hL hNoTrace
  refine ⟨τ, hTendsto, tendsto_atTop.2 ?_⟩
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hnOne : 1 ≤ n := (le_max_right N 1).trans hn
  let R : ℝ := (n : ℝ) + 1
  have hR : 2 ≤ R := by
    have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnOne
    dsimp only [R]
    linarith
  have hE : 0 < velocityH3EnergyAt u (τ n) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u (τ n))
  have hNorm : R < velocityH3DissipationAt u (τ n) /
      velocityH3EnergyAt u (τ n) := by
    apply h3Path_cubicDissipationEnergyClock_forces_ratio_gt_radius244
      (velocityH3EnergyAt u (τ n))
      (velocityH3DissipationAt u (τ n)) R hR hE
    simpa only [R, show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
      using hClock n
  have hMn : M < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hnN)
  have hnR : (n : ℝ) < R := by dsimp only [R]; linarith
  exact le_of_lt (lt_trans (lt_trans hMn hnR) hNorm)

end
end PrimeTensor.FirstMonomialTriad
