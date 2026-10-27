import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourcePhysicalDifference244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFourierTransfer244
import Mathlib.Tactic

/-!
# Canonical physical source clock: finite-frequency spectral temporal modulus

The actual projected physical source maximum C on the strict half-terminal
window is an attained, minimal envelope.  The previous physical momentum
FTC and exact radial Plancherel theorem yield, without controlling the
full weighted H³ temporal displacement,

  LowRadialDefect_rho(S(t),S(s))
    <= 3 K(rho) (C (s-t))²
    <= 3 K(rho) (C (T-t)/2)².

The second bound holds at EVERY time in the half-terminal window, not just
at the arbitrarily selected maximum.  Thus a sequence whose exact source
exposure C_k (T-t_k)/2 tends to zero has vanishing low-frequency H³ temporal
defect at its predetermined source-maximizing times.  This is compatible
with a diverging full H³ spectral norm: high-frequency transport is NOT
bounded by the finite-frequency estimate.

No uniform H³ time derivative, bounded terminal source, or dissipation
upper bound is postulated.  Finite H³ dissipation alone is not used to
assert that the source exposure goes to zero.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The exact physical source envelope yields a sharp elapsed-time quadratic
modulus of the genuinely weighted H³ square defect at every fixed Fourier
radius.  Both endpoints are in the same positive strict physical window. -/
theorem h3Path_canonicalSourceWindow_radialTemporalDefect_le244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hs : s ∈ Set.Icc a b)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
      (h3AuditActualSpectralVelocityTotal hH3 a)
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤
      (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
        (h3PathActualProjectedSourceWindowEnvelope244 hH3 a b * (s - a)) ^ 2 := by
  have haT : a ∈ Set.Ioo (0 : ℝ) T := ⟨ha, lt_trans hab hb⟩
  have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  apply h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244
    hH3 ρ hρ a s
      (h3PathActualProjectedSourceWindowEnvelope244 hH3 a b)
      haT hsT hs.1
  intro r hr
  exact h3Path_actualSourceWindowEnvelope_pointwise_le244
    hH3 ha hab hb r ⟨hr.1, le_trans hr.2 hs.2⟩

/-- On a strict half-terminal window the canonical source envelope is
nonnegative and the finite-frequency spectral temporal square defect is
bounded by the square of the EXACT source exposure C (T-a)/2. -/
theorem h3Path_canonicalSourceHalfTerminal_radialExposure_le244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (s : ℝ)
    (hs : s ∈ Set.Icc a (a + (T - a) / 2))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
      (h3AuditActualSpectralVelocityTotal hH3 a)
      (h3AuditActualSpectralVelocityTotal hH3 s) ≤
      (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
        (h3PathActualProjectedSourceWindowEnvelope244 hH3
            a (a + (T - a) / 2) * ((T - a) / 2)) ^ 2 := by
  let b : ℝ := (T - a) / 2
  let C : ℝ := h3PathActualProjectedSourceWindowEnvelope244 hH3 a (a + b)
  have hb : 0 < b := by
    dsimp only [b]
    linarith only [ha.2]
  have hab : a < a + b := by linarith only [hb]
  have hbT : a + b < T := by
    dsimp only [b]
    linarith only [ha.2]
  have hs' : s ∈ Set.Icc a (a + b) := hs
  have hBase := h3Path_canonicalSourceWindow_radialTemporalDefect_le244
    hH3 ha.1 hab hbT hs' ρ hρ
  have hC : 0 ≤ C := by
    dsimp only [C]
    obtain ⟨r, _, _, hEq⟩ :=
      h3Path_actualSourceWindowEnvelope_attained244 hH3 ha.1 hab hbT
    rw [hEq]
    exact norm_nonneg _
  have hDistance : s - a ≤ b := by
    have h := hs'.2
    linarith only [h]
  have hMul : C * (s - a) ≤ C * b :=
    mul_le_mul_of_nonneg_left hDistance hC
  have hMulNonneg : 0 ≤ C * (s - a) :=
    mul_nonneg hC (sub_nonneg.mpr hs'.1)
  have hSq : (C * (s - a)) ^ 2 ≤ (C * b) ^ 2 :=
    pow_le_pow_left₀ hMulNonneg hMul 2
  have hCoeff : 0 ≤ 3 * h3TerminalRadialSobolevWeightSquareCeiling ρ :=
    mul_nonneg (by norm_num)
      (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le
  have hResult := hBase.trans (mul_le_mul_of_nonneg_left hSq hCoeff)
  simpa only [C, b] using hResult

/-- A nonnegative finite-radial square defect squeezed by a vanishing
quadratic source exposure must itself vanish; the radius stays FIXED. -/
theorem h3Path_radialDefect_vanishes_of_sourceExposure244
    (D exposure : ℕ → ℝ) (K : ℝ) (_hK : 0 ≤ K)
    (hD : ∀ k, 0 ≤ D k ∧ D k ≤ K * (exposure k) ^ 2)
    (hExposure : Tendsto exposure atTop (𝓝 (0 : ℝ))) :
    Tendsto D atTop (𝓝 (0 : ℝ)) := by
  have hSq : Tendsto (fun k => (exposure k) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hExposure.pow 2
  have hUpper : Tendsto (fun k => K * (exposure k) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hSq :
      Tendsto (fun k => K * (exposure k) ^ 2) atTop
        (𝓝 (K * (0 : ℝ))))
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun k => (hD k).1))
    (Filter.Eventually.of_forall (fun k => (hD k).2)) hUpper

/-- The EXACT canonical half-window source exposure, when it vanishes,
forces finite-radius weighted spectral displacement to vanish at any
preselected physical observation times within those windows. -/
theorem h3Path_canonicalHalfTerminal_radialDefect_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ s : ℕ → ℝ)
    (hτ : ∀ k, τ k ∈ Set.Ioo (0 : ℝ) T)
    (hs : ∀ k, s k ∈ Set.Icc (τ k) (τ k + (T - τ k) / 2))
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hExposure : Tendsto (fun k : ℕ =>
      h3PathActualProjectedSourceWindowEnvelope244 hH3
        (τ k) (τ k + (T - τ k) / 2) * ((T - τ k) / 2))
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k : ℕ =>
      h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
        (h3AuditActualSpectralVelocityTotal hH3 (τ k))
        (h3AuditActualSpectralVelocityTotal hH3 (s k)))
      atTop (𝓝 (0 : ℝ)) := by
  apply h3Path_radialDefect_vanishes_of_sourceExposure244
    (fun k => h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
      (h3AuditActualSpectralVelocityTotal hH3 (τ k))
      (h3AuditActualSpectralVelocityTotal hH3 (s k)))
    (fun k => h3PathActualProjectedSourceWindowEnvelope244 hH3
      (τ k) (τ k + (T - τ k) / 2) * ((T - τ k) / 2))
    (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ)
    (mul_nonneg (by norm_num)
      (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le)
  · intro k
    constructor
    · unfold h3TerminalWeightedSpectralVelocityRadialSquareDefect
      exact integral_nonneg (fun ξ =>
        h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_nonneg _ _ ξ)
    · exact h3Path_canonicalSourceHalfTerminal_radialExposure_le244
        hH3 (τ k) (hτ k) (s k) (hs k) ρ hρ
  · exact hExposure

/-- The original same-witness canonical disjoint PDE clocks inherit a
finite-frequency modulus at EVERY fixed radius and every selected source
maximizer.  The full state and source-jump barriers are still provided by
the parent construction, which does not make the extra exposure assumption.
In particular, no global spectral H³ modulus is inferred. -/
theorem h3Path_noL2Trace_canonicalWidth_radialSourceExposure244
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
      (∀ ρ : ℝ, 0 ≤ ρ → ∀ k : ℕ,
        h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
          (h3AuditActualSpectralVelocityTotal hH3 (s k)) ≤
        (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
          (C (v k) * ((T - τ (v k)) / 2)) ^ 2) ∧
      (∀ ρ : ℝ, 0 ≤ ρ →
        Tendsto (fun k => C (v k) * ((T - τ (v k)) / 2))
          atTop (𝓝 (0 : ℝ)) →
        Tendsto (fun k =>
          h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
            (h3AuditActualSpectralVelocityTotal hH3 (s k)))
          atTop (𝓝 (0 : ℝ))) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        (∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          M ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∨
          M ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k) -
            h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, _hBound, hAlternative⟩ :=
    h3Path_noL2Trace_canonicalWidth_physicalSourceSpectralTemporalBound244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_, ?_, ?_⟩
  · intro ρ hρ k
    have ht : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (hTime (v k)).1,
        (hTime (v k)).2⟩
    have hBound := h3Path_canonicalSourceHalfTerminal_radialExposure_le244
      hH3 (τ (v k)) ht (s k) (hPeak k).1 ρ hρ
    simpa only [← (hCanonical k).2] using hBound
  · intro ρ hρ hFast
    have ht : ∀ k : ℕ, τ (v k) ∈ Set.Ioo (0 : ℝ) T := by
      intro k
      exact ⟨lt_trans hClass.terminal_start.1 (hTime (v k)).1,
        (hTime (v k)).2⟩
    -- We rewrite the chosen clock's envelope equality at each index,
    -- avoiding any use of a fixed index to rewrite a sequence expression.
    have hEq : (fun k : ℕ =>
        h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) *
            ((T - τ (v k)) / 2)) =
        (fun k : ℕ => C (v k) * ((T - τ (v k)) / 2)) := by
      funext k
      rw [← (hCanonical k).2]
    have hFast'' : Tendsto (fun k =>
        h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) *
            ((T - τ (v k)) / 2)) atTop (𝓝 (0 : ℝ)) := by
      rw [hEq]
      exact hFast
    exact h3Path_canonicalHalfTerminal_radialDefect_tendsto_zero244
      hH3 (fun k => τ (v k)) s ht (fun k => (hPeak k).1)
      ρ hρ hFast''
  · intro η B D hη hB hD hRegime
    exact (hAlternative η B D hη hB hD hRegime).1

end
end PrimeTensor.FirstMonomialTriad
