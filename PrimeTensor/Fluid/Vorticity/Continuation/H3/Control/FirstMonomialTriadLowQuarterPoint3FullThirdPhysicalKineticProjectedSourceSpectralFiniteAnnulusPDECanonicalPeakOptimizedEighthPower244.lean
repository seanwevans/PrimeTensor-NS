import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakFrequencyAmplification244
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Actual canonical source maxima: sharp sixth-root frequency optimization

From physical kinetic monotonicity and the exact H³ Fourier split, the
previous module proved, for any rho >= 1,

  8 * rho^6 * E₀(b) <= ‖U₃(t)‖²
    ==> (rho²/2) * ‖U₃(t)‖² <= D₃(t).

This file selects the radius from the ACTUAL peak amplitude and kinetic
anchor (without changing the physical observation time):

  rho^6 = ‖U₃(t)‖² / (8*(E₀(b)+1)).

When ‖U₃(t)‖² >= 8*(E₀(b)+1), the radius is >= 1 and the threshold holds.
Cubing the genuine dissipation estimate gives the explicit superquadratic
law

  ‖U₃(t)‖^8 <= 64*(E₀(b)+1)*D₃(t)^3.

It holds eventually along every cofinal spectrally divergent peak sequence,
and hence on the exact canonical physical projected-source maxima in the
already-explicit critical-width regime. No new times, terminal modulus,
source peak persistence lower bound, or contradiction with finite temporal
H³ dissipation are asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Construct the exact positive optimal sixth-root radius. The harmless
kinetic regularizer `E+1` ensures the denominator stays positive, including
when the physical kinetic mass at the chosen anchor is zero. -/
theorem h3Path_optimizedSixthRootRadius244
    (A E : ℝ) (hE : 0 ≤ E)
    (hLarge : 8 * (E + 1) ≤ A ^ 2) :
    ∃ ρ : ℝ, 1 ≤ ρ ∧
      8 * (E + 1) * ρ ^ 6 = A ^ 2 ∧
      8 * ρ ^ 6 * E ≤ A ^ 2 := by
  let B : ℝ := E + 1
  let x : ℝ := A ^ 2 / (8 * B)
  let ρ : ℝ := x ^ ((6 : ℝ)⁻¹)
  have hB : 0 < B := by dsimp only [B]; linarith only [hE]
  have h8B : 0 < 8 * B := by positivity
  have hxOne : 1 ≤ x := by
    dsimp only [x, B]
    exact (le_div_iff₀ (by positivity : 0 < 8 * (E + 1))).2
      (by simpa only [one_mul] using hLarge)
  have hxNonneg : 0 ≤ x := le_trans (by norm_num) hxOne
  have hρOne : 1 ≤ ρ := by
    dsimp only [ρ]
    exact Real.one_le_rpow hxOne (by positivity : (0 : ℝ) ≤ (6 : ℝ)⁻¹)
  have hρSix : ρ ^ 6 = x := by
    dsimp only [ρ]
    exact Real.rpow_inv_natCast_pow hxNonneg
      (by decide : (6 : ℕ) ≠ 0)
  have hRoot : 8 * (E + 1) * ρ ^ 6 = A ^ 2 := by
    calc
      8 * (E + 1) * ρ ^ 6 = (A ^ 2 / (8 * B)) * (8 * B) := by
        rw [hρSix]
        dsimp only [x, B]
        ring
      _ = A ^ 2 := div_mul_cancel₀ _ (ne_of_gt h8B)
  have hELeB : E ≤ E + 1 := by linarith
  have hThreshold : 8 * ρ ^ 6 * E ≤ A ^ 2 := by
    calc
      8 * ρ ^ 6 * E ≤ 8 * ρ ^ 6 * (E + 1) :=
        mul_le_mul_of_nonneg_left hELeB (by positivity)
      _ = 8 * (E + 1) * ρ ^ 6 := by ring
      _ = A ^ 2 := hRoot
  exact ⟨ρ, hρOne, hRoot, hThreshold⟩

/-- Pure sixth-root algebra: if the chosen radius has the stated exact
physical kinetic scaling, the half-mass dissipation inequality has an
unconditional eighth-power/cubic consequence, with explicit constant 64. -/
theorem h3Path_sixthRootCoercivity_algebraicEighthPower244
    (A D E ρ : ℝ) (hE : 0 ≤ E)
    (hRoot : 8 * (E + 1) * ρ ^ 6 = A ^ 2)
    (hCost : (ρ ^ 2 / 2) * A ^ 2 ≤ D) :
    A ^ 8 ≤ 64 * (E + 1) * D ^ 3 := by
  have hBase : 0 ≤ (ρ ^ 2 / 2) * A ^ 2 := by positivity
  have hCube : ((ρ ^ 2 / 2) * A ^ 2) ^ 3 ≤ D ^ 3 :=
    pow_le_pow_left₀ hBase hCost 3
  have hScaled := mul_le_mul_of_nonneg_left hCube
    (by positivity : 0 ≤ 64 * (E + 1))
  calc
    A ^ 8 = A ^ 2 * A ^ 6 := by ring
    _ = (8 * (E + 1) * ρ ^ 6) * A ^ 6 := by rw [hRoot]
    _ = (64 * (E + 1)) * (((ρ ^ 2 / 2) * A ^ 2) ^ 3) := by ring
    _ ≤ (64 * (E + 1)) * D ^ 3 := hScaled

/-- Sharp superquadratic physical consequence at a genuine strict-time
weighted H³ spectral state, with no time continuity or uniform PDE rate
hypothesis. The cutoff is a dependent real number; time is unchanged. -/
theorem h3Path_physicalSpectralPeak_optimizedEighthPower244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (hLarge : 8 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2) :
    ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 8 ≤
      64 * (velocityH3Energy0At u b + 1) *
        (velocityH3DissipationAt u t) ^ 3 := by
  have hE : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  obtain ⟨ρ, hρ, hRoot, hThreshold⟩ :=
    h3Path_optimizedSixthRootRadius244
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖
      (velocityH3Energy0At u b) hE hLarge
  have hCost := h3Path_physicalPeak_sixthThreshold_forces_dissipation244
    hH3 hClass b hb t ht ρ hρ hE hThreshold
  exact h3Path_sixthRootCoercivity_algebraicEighthPower244
    ‖h3AuditActualSpectralVelocityTotal hH3 t‖
    (velocityH3DissipationAt u t) (velocityH3Energy0At u b)
    ρ hE hRoot hCost

/-- The direct L¹-compatible normalization of the polynomial physical
coercivity estimate. No roots remain in the theorem statement. -/
theorem h3Path_physicalSpectralPeak_optimizedEighthPower_div244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (hLarge : 8 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2) :
    ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 8 /
        (64 * (velocityH3Energy0At u b + 1)) ≤
      (velocityH3DissipationAt u t) ^ 3 := by
  have hE : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hB : 0 < 64 * (velocityH3Energy0At u b + 1) := by
    positivity
  have hPower := h3Path_physicalSpectralPeak_optimizedEighthPower244
    hH3 hClass b hb t ht hLarge
  apply (div_le_iff₀ hB).2
  calc
    _ ≤ 64 * (velocityH3Energy0At u b + 1) *
        (velocityH3DissipationAt u t) ^ 3 := hPower
    _ = (velocityH3DissipationAt u t) ^ 3 *
        (64 * (velocityH3Energy0At u b + 1)) := by ring

/-- On ANY physical spectrally divergent sequence after a fixed kinetic
anchor, the exact eighth-power/cubic physical inequality holds eventually
at the SAME observation times; no spectral radius or subsequence is fixed. -/
theorem h3Path_cofinalSpectralPeaks_eventualOptimizedEighthPower244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ)
    (hs : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T)
    (hEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop) :
    ∀ᶠ k : ℕ in atTop,
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 8 ≤
        64 * (velocityH3Energy0At u b + 1) *
          (velocityH3DissipationAt u (s k)) ^ 3 := by
  let B : ℝ := 8 * (velocityH3Energy0At u b + 1)
  have hLarge : ∀ᶠ k : ℕ in atTop,
      max B 1 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hEscape.eventually (eventually_ge_atTop (max B 1))
  filter_upwards [hs, hLarge] with k ht hk
  have hOne : 1 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    (le_max_right _ _).trans hk
  have hBound : B ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    (le_max_left _ _).trans hk
  have hSq : ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 := by
    nlinarith only [hOne, sq_nonneg
      (‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ - 1)]
  apply h3Path_physicalSpectralPeak_optimizedEighthPower244
    hH3 hClass b hb (s k) ht
  exact le_trans (by simpa only [B] using hBound) hSq

/-- End-to-end conditional canonical source maximizer theorem. The EXACT
source-maximizing times from the disjoint quadratic-sharp construction obey
8/3-power physical coercivity eventually, under the unchanged noncompression,
linear-rate and annulus-width hypotheses. No new source observations are
chosen, and no lower persistence width is asserted. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakOptimizedEighthPower244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        ∃ b : ℝ, b ∈ Set.Ioo a T ∧
          ∀ᶠ k : ℕ in atTop,
            ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 8 ≤
              64 * (velocityH3Energy0At u b + 1) *
                (velocityH3DissipationAt u (s k)) ^ 3) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  have haT : a < T := lt_trans (hTime 0).1 (hTime 0).2
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [haT]
  have hLate : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hCofinal.eventually (Ioi_mem_nhds hb.2)
  have hsEventually : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T := by
    filter_upwards [hLate] with k hk
    have hMid : τ (v k) + (T - τ (v k)) / 2 < T := by
      have ht := (hTime (v k)).2
      linarith only [ht]
    exact ⟨lt_of_lt_of_le hk (hPeak k).1.1,
      lt_of_le_of_lt (hPeak k).1.2 hMid⟩
  intro η B D hη hB hD hRegime
  have hEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop :=
    (hJoint η B D hη hB hD hRegime).2
  exact ⟨b, hb,
    h3Path_cofinalSpectralPeaks_eventualOptimizedEighthPower244
      hH3 hClass b hb s hsEventually hEscape⟩

end
end PrimeTensor.FirstMonomialTriad
