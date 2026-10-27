import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalWidthPhysicalSource244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralStateEscape244
import Mathlib.Tactic

/-!
# Joint physical H³ and actual weighted spectral-state peaks on canonical source windows

On the same canonical quadratic-sharp first-crossing witnesses of the preceding
critical-width PDE theorem, the projected physical source maximum is attained
at an actual time in a shrinking half-terminal window. The existing physical
inverse-Fourier estimates say, for the actual weighted H³ spectral state U,
  ‖projected PDE source‖ ≤ (3 + C_L) * E₃,
  ‖projected PDE source‖ ≤ 3 * ‖U‖ + C_L * ‖U‖²,
where C_L >= 0 is the proven Leray Fourier constant.

Thus a single sufficiently large projected-source observation simultaneously
forces the actual normalized H³ energy and the actual H³ spectral-state norm
to be large. At the CANONICAL source-maximizing time, both obstructions occur
together, not at independent reselected times.

Geometric noncompression, sixth-order linear-rate control, and a bounded
critical ninth/eighth annular width remain eventual assumptions. No uniform
source modulus, temporal integrated H³-energy lower bound, or unconditional
Navier--Stokes continuation is inferred. The maximizing half-terminal time
need not belong to the shorter disjoint dissipation-charging window.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- One actual physical projected-source peak simultaneously enforces an
H³-energy peak and an actual weighted-spectral-state peak. The source
threshold is a concrete polynomial using only the proved Fourier constant. -/
theorem h3Path_projectedSourceThreshold_forces_jointH3Spectral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (A : ℝ) (hA : 0 ≤ A)
    (hLarge :
      (3 + h3AuditInitialLerayEnergyCoefficient) * A +
          (3 * A + h3AuditInitialLerayEnergyCoefficient * A ^ 2) + 1 ≤
        ‖h3PathActualProjectedMomentumSource244 hH3 t‖) :
    A < velocityH3EnergyAt u t ∧
      A < ‖h3AuditActualSpectralVelocityTotal hH3 t‖ := by
  let CL : ℝ := h3AuditInitialLerayEnergyCoefficient
  have hCL : 0 ≤ CL := h3AuditInitialLerayEnergyCoefficient_nonneg
  have hCoef : 0 ≤ 3 + CL := by linarith only [hCL]
  have hLarge' : (3 + CL) * A + (3 * A + CL * A ^ 2) + 1 ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ := by
    simpa only [CL] using hLarge
  have hE : A < velocityH3EnergyAt u t := by
    by_contra hNot
    have hEA : velocityH3EnergyAt u t ≤ A := le_of_not_gt hNot
    have hUpper : ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤
        (3 + CL) * A := by
      calc
        _ ≤ (3 + CL) * velocityH3EnergyAt u t := by
          simpa only [CL] using
            h3Path_physicalProjectedSource_norm_le_H3Energy244 hH3 t ht
        _ ≤ (3 + CL) * A :=
          mul_le_mul_of_nonneg_left hEA hCoef
    have hOther : 0 ≤ 3 * A + CL * A ^ 2 := by positivity
    linarith only [hLarge', hUpper, hOther]
  have hS : A < ‖h3AuditActualSpectralVelocityTotal hH3 t‖ := by
    by_contra hNot
    have hSA : ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ≤ A :=
      le_of_not_gt hNot
    have hSq : ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
        A ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hA).2 hSA
    have hUpper : ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤
        3 * A + CL * A ^ 2 := by
      calc
        _ ≤ 3 * ‖h3AuditActualSpectralVelocityTotal hH3 t‖ +
              CL * ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 := by
            simpa only [CL] using
              h3Path_physicalProjectedSource_norm_le_actualSpectralGrowth244
                hH3 t ht
        _ ≤ 3 * A + CL * A ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hSA (by norm_num))
            (mul_le_mul_of_nonneg_left hSq hCL)
    have hOther : 0 ≤ (3 + CL) * A := mul_nonneg hCoef hA
    linarith only [hLarge', hUpper, hOther]
  exact ⟨hE, hS⟩

/-- Under the canonical critical-width PDE regime, the ACTUAL source-
maximizing time in every sufficiently late half-terminal window is also a
simultaneous physical normalized-H³-energy and actual weighted H³ spectral-
velocity peak. The temporal and spectral witnesses are not reselected.
The geometric/rate/width conditions and finite H³ dissipation are explicit. -/
theorem h3Path_noL2Trace_finiteDissipation_canonicalWidth_jointH3StatePeaks244
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
            ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k) ∧
            M < velocityH3EnergyAt u s ∧
            M < ‖h3AuditActualSpectralVelocityTotal hH3 s‖)) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hEscape⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalCriticalWidth_physicalSourcePeaks244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, ?_⟩
  intro η B D hη hB hD hRegime
  obtain ⟨hSquare, _hPhysicalPeaks⟩ :=
    hEscape η B D hη hB hD hRegime
  refine ⟨hSquare, ?_⟩
  intro M
  let A : ℝ := max M 0
  let CL : ℝ := h3AuditInitialLerayEnergyCoefficient
  let H : ℝ := (3 + CL) * A + (3 * A + CL * A ^ 2) + 1
  have hA : 0 ≤ A := le_max_right M 0
  have hMA : M ≤ A := le_max_left M 0
  have hAbs := h3Path_sourceCeilingSquareEscape_forces_absEscape244
    (fun k => C (v k)) hSquare
  have hLarge : ∀ᶠ k : ℕ in atTop, H ≤ |C (v k)| :=
    hAbs.eventually (eventually_ge_atTop H)
  filter_upwards [hLarge] with k hk
  obtain ⟨s, hs, hPeak⟩ := (hCanonical k).2.2
  have hCNonneg : 0 ≤ C (v k) := by
    rw [← hPeak]
    exact norm_nonneg _
  have hC : H ≤ C (v k) := by
    simpa only [abs_of_nonneg hCNonneg] using hk
  have hSource : (3 + h3AuditInitialLerayEnergyCoefficient) * A +
        (3 * A + h3AuditInitialLerayEnergyCoefficient * A ^ 2) + 1 ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ := by
    change H ≤ ‖h3PathActualProjectedMomentumSource244 hH3 s‖
    rw [hPeak]
    exact hC
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · exact lt_of_lt_of_le
        (lt_trans hClass.terminal_start.1 (hTime (v k)).1) hs.1
    · have htEnd : τ (v k) + (T - τ (v k)) / 2 < T := by
        have ht := (hTime (v k)).2
        linarith only [ht]
      exact lt_of_le_of_lt hs.2 htEnd
  have hBoth := h3Path_projectedSourceThreshold_forces_jointH3Spectral244
    hH3 s hsAbs A hA hSource
  exact ⟨s, hs, hPeak, lt_of_le_of_lt hMA hBoth.1,
    lt_of_le_of_lt hMA hBoth.2⟩

/-- If a single predetermined sequence of actual positive times realizes
canonical source values whose squares escape, then BOTH actual physical
normalized H³ energies and spectral-state norms escape along THAT sequence.
Unlike `∀ M, ∀ᶠ k, ∃ s`, the choices do not depend on the threshold M. -/
theorem h3Path_fixedSourceMaximizers_forces_jointH3SpectralTendsto244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℕ → ℝ) (C : ℕ → ℝ)
    (hs : ∀ k, s k ∈ Set.Ioo (0 : ℝ) T)
    (hPeak : ∀ k, ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C k)
    (hSquare : Tendsto (fun k : ℕ => C k ^ 2) atTop atTop) :
    Tendsto (fun k : ℕ => velocityH3EnergyAt u (s k)) atTop atTop ∧
      Tendsto (fun k : ℕ =>
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop := by
  have hAbs := h3Path_sourceCeilingSquareEscape_forces_absEscape244 C hSquare
  have hSimultaneous (M : ℝ) : ∀ᶠ k : ℕ in atTop,
      M ≤ velocityH3EnergyAt u (s k) ∧
        M ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ := by
    let A : ℝ := max M 0
    let CL : ℝ := h3AuditInitialLerayEnergyCoefficient
    let H : ℝ := (3 + CL) * A + (3 * A + CL * A ^ 2) + 1
    have hA : 0 ≤ A := le_max_right M 0
    have hMA : M ≤ A := le_max_left M 0
    have hLarge : ∀ᶠ k : ℕ in atTop, H ≤ |C k| :=
      hAbs.eventually (eventually_ge_atTop H)
    filter_upwards [hLarge] with k hk
    have hCNonneg : 0 ≤ C k := by
      rw [← hPeak k]
      exact norm_nonneg _
    have hkC : H ≤ C k := by
      simpa only [abs_of_nonneg hCNonneg] using hk
    have hSource :
        (3 + h3AuditInitialLerayEnergyCoefficient) * A +
            (3 * A + h3AuditInitialLerayEnergyCoefficient * A ^ 2) + 1 ≤
          ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ := by
      change H ≤ ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖
      rw [hPeak k]
      exact hkC
    obtain ⟨hE, hS⟩ :=
      h3Path_projectedSourceThreshold_forces_jointH3Spectral244
        hH3 (s k) (hs k) A hA hSource
    exact ⟨(lt_of_le_of_lt hMA hE).le,
      (lt_of_le_of_lt hMA hS).le⟩
  constructor
  · apply Filter.tendsto_atTop.2
    intro M
    filter_upwards [hSimultaneous M] with k hk
    exact hk.1
  · apply Filter.tendsto_atTop.2
    intro M
    filter_upwards [hSimultaneous M] with k hk
    exact hk.2

/-- The synchronized physical canonical first-crossing PDE witnesses admit
ONE actual source-maximizing time sequence chosen before any eventual
noncompression, linear-rate or width-cap parameters. Under those conditional
PDE tests, both its physical H³ energies and its actual weighted spectral-
velocity norms tend to +∞ along this very same sequence. -/
theorem h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
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
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
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
        Tendsto (fun k : ℕ => velocityH3EnergyAt u (s k)) atTop atTop ∧
        Tendsto (fun k : ℕ =>
          ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hEscape⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalCriticalWidth_physicalSourcePeaks244
      hH3 hClass hMass hNoTrace hDInt
  classical
  have hChoice (k : ℕ) : ∃ s : ℝ,
      s ∈ Set.Icc (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k) :=
    (hCanonical k).2.2
  choose s hs hPeak using hChoice
  have hsAbs (k : ℕ) : s k ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · exact lt_of_lt_of_le
        (lt_trans hClass.terminal_start.1 (hTime (v k)).1) (hs k).1
    · have hUpper : τ (v k) + (T - τ (v k)) / 2 < T := by
        have ht := (hTime (v k)).2
        linarith only [ht]
      exact lt_of_le_of_lt (hs k).2 hUpper
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hCanonical k).1, (hCanonical k).2.1⟩
  · intro k
    exact ⟨hs k, hPeak k⟩
  · intro η B D hη hB hD hRegime
    have hSquare := (hEscape η B D hη hB hD hRegime).1
    exact h3Path_fixedSourceMaximizers_forces_jointH3SpectralTendsto244
      hH3 s (fun k => C (v k)) hsAbs hPeak hSquare

end
end PrimeTensor.FirstMonomialTriad
