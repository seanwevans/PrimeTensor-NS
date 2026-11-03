import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiSourceRateGate
import Mathlib.Tactic

/-!
# All-epsilon physical source-rate pressure on minimal Riccati windows

The existing sharp PDE alternative holds at EVERY positive epsilon, although
its first Riccati source-rate refinement fixed epsilon=1. The intrinsic
inverse-root clock excludes the terminal-compression cap for EVERY 0<epsilon<=1.
Consequently, a Riccati-heavy window with subquadratic anchor energy has
arbitrarily large *normalized* actual linear/quadratic PDE-rate expenditure,
in the precise eventually-for-each-multiplier sense.

The terminal tail depends on the prescribed multiplier; this is NOT a
pointwise assertion for all multipliers at one fixed selected window.
The unbounded-cubic-charge branch is retained, not discarded. No new PDE
regularity, terminal H3 integrability or source bounds are assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalQuantifiedPressure
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalQuantifiedPressure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The original intrinsic terminal clock excludes the compression cap for
all epsilon up to one, not just epsilon=1. -/
theorem h3Critical_scalar_intrinsicClock_excludes_smallEpsilonTimeCap
    (R d ε : ℝ) (hR : 1 ≤ R) (hClock : 16 < d * R)
    (hε : ε ≤ 1) :
    ¬ R ^ 3 * (d / 4) ≤ ε := by
  intro hCap
  exact (h3Critical_scalar_intrinsicClock_excludes_cubicTimeCap
    R d hR hClock) (hCap.trans hε)

/-- Exact epsilon-dependent physical linear and quadratic source cost at an
original minimal-shell Riccati window, or its quadratic H3 anchor cost. -/
def h3CriticalMinimalShellRiccatiEpsilonSourceRateAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℕ → ℝ) (N : ℕ → ℕ) (C : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ) (ε : ℝ) : Prop :=
  ((v k : ℝ) + 1) ^ 2 <
    4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
      velocityH3EnergyAt u (t (v k)) ∨
  ((v k : ℝ) + 1) ^ 12 ≤
    512 * ε ^ 2 * (2304 * velocityH3EnergyAt u (t (v k)) *
      (C (v k)) ^ 2 * ((N (v k) : ℝ) + 2) ^ 10 + 1) ∨
  ((v k : ℝ) + 1) ^ 9 ≤
    16 * ε ^ 2 * (36 * (C (v k)) ^ 2 *
      (((N (v k) : ℝ) + 2) ^ 8 +
        ((v k : ℝ) + 2) ^ 8) + 1)

/-- The rate gate at arbitrary epsilon (not just one) cannot realize its
compressed-time arm at a Riccati peak with a small quadratic anchor. -/
theorem h3Critical_minimalShellRiccatiClock_excludes_epsilonCompression
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (t : ℕ → ℝ) (N : ℕ → ℕ) (C : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ) (ε : ℝ)
    (hε : ε ≤ 1)
    (hAnchorClock :
      h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt u T t v k)
    (hRates :
      ((v k : ℝ) + 1) ^ 3 * ((T - t (v k)) / 4) ≤ ε ∨
      ((v k : ℝ) + 1) ^ 12 ≤
        512 * ε ^ 2 * (2304 * velocityH3EnergyAt u (t (v k)) *
          (C (v k)) ^ 2 * ((N (v k) : ℝ) + 2) ^ 10 + 1) ∨
      ((v k : ℝ) + 1) ^ 9 ≤
        16 * ε ^ 2 * (36 * (C (v k)) ^ 2 *
          (((N (v k) : ℝ) + 2) ^ 8 +
            ((v k : ℝ) + 2) ^ 8) + 1)) :
    h3CriticalMinimalShellRiccatiEpsilonSourceRateAt u t N C v k ε := by
  rcases hAnchorClock with hAnchor | hClock
  · exact Or.inl hAnchor
  · right
    rcases hRates with hCompress | hLinear | hQuadratic
    · have hR : (1 : ℝ) ≤ (v k : ℝ) + 1 := by
        have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
        linarith only [hNat]
      exact False.elim
        ((h3Critical_scalar_intrinsicClock_excludes_smallEpsilonTimeCap
          ((v k : ℝ) + 1) (T - t (v k)) ε hR hClock hε) hCompress)
    · exact Or.inl hLinear
    · exact Or.inr hQuadratic

/-- Unlike the former epsilon=1 refinement, this preserves the entire
quantifier on the sharp physical PDE source rates. Every positive epsilon
has its own eventual physical terminal tail. -/
theorem h3Critical_minimalShellPhysicalRates_refine_allEpsilonRiccatiPressure
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (t : ℕ → ℝ) (N : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ)
    (hRates : h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
      T t N C δ v)
    (hLocal : ∀ᶠ k : ℕ in atTop,
      h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
        h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt u T t v k) :
    (∀ M : ℝ, ∃ q : ℕ,
      M < ∑ k ∈ Finset.range q,
        h3CriticalMinimalShellCubicWindowCost δ v k) ∨
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiEpsilonSourceRateAt
            u t N C v k ε) := by
  rcases hRates with hDivergent | hQuantified
  · left
    intro M
    obtain ⟨q, hq⟩ := hDivergent M
    exact ⟨q, by
      simpa only [h3CriticalMinimalShellCubicWindowCost] using hq⟩
  · right
    intro ε hε hεOne
    have hGate := hQuantified ε hε
    filter_upwards [hLocal, hGate] with k hLocalK hGateK
    intro hRiccati
    exact h3Critical_minimalShellRiccatiClock_excludes_epsilonCompression
      u T t N C v k ε hεOne (hLocalK hRiccati) hGateK

/-- Given a prescribed nonnegative multiplier, construct one small positive
sharp-PDE epsilon whose squared factor absorbs both 512 M and 16 M. -/
theorem h3Critical_scalar_smallEpsilon_absorbs_normalizedRateMultiplier
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      512 * M * ε ^ 2 ≤ 1 ∧ 16 * M * ε ^ 2 ≤ 1 := by
  let D : ℝ := 512 * (M + 1)
  let ε : ℝ := 1 / D
  have hDPos : 0 < D := by
    dsimp only [D]
    positivity
  have hDOne : 1 ≤ D := by
    dsimp only [D]
    linarith only [hM]
  have hεPos : 0 < ε := by
    dsimp only [ε]
    positivity
  have hεOne : ε ≤ 1 := by
    dsimp only [ε]
    apply (div_le_iff₀ hDPos).2
    simpa only [one_mul] using hDOne
  have hDM : 512 * M ≤ D := by
    dsimp only [D]
    linarith only [hM]
  have hUnit : D * ε = 1 := by
    simpa [ε] using (mul_inv_cancel₀ (ne_of_gt hDPos))
  have hScaled := mul_le_mul_of_nonneg_right hDM hεPos.le
  rw [hUnit] at hScaled
  have hεSq : ε ^ 2 ≤ ε := by
    have hProd := mul_nonneg hεPos.le (sub_nonneg.mpr hεOne)
    nlinarith only [hProd]
  have h512 : 512 * M * ε ^ 2 ≤ 1 := by
    have hMult := mul_le_mul_of_nonneg_left hεSq
      (by positivity : 0 ≤ 512 * M)
    exact le_trans hMult hScaled
  have h16 : 16 * M * ε ^ 2 ≤ 1 := by
    have hNonneg : 0 ≤ M * ε ^ 2 := mul_nonneg hM (sq_nonneg _)
    nlinarith only [h512, hNonneg]
  exact ⟨ε, hεPos, hεOne, h512, h16⟩

/-- A prescribed multiplier M is paid by one of the ACTUAL normalized
source-rate densities, or else by the original quadratic anchor energy. -/
def h3CriticalMinimalShellRiccatiNormalizedSourcePressureAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℕ → ℝ) (N : ℕ → ℕ) (C : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ) (M : ℝ) : Prop :=
  ((v k : ℝ) + 1) ^ 2 <
    4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
      velocityH3EnergyAt u (t (v k)) ∨
  M * ((v k : ℝ) + 1) ^ 12 ≤
    2304 * velocityH3EnergyAt u (t (v k)) *
      (C (v k)) ^ 2 * ((N (v k) : ℝ) + 2) ^ 10 + 1 ∨
  M * ((v k : ℝ) + 1) ^ 9 ≤
    36 * (C (v k)) ^ 2 *
      (((N (v k) : ℝ) + 2) ^ 8 +
        ((v k : ℝ) + 2) ^ 8) + 1

/-- Epsilon-dependent terminal estimates imply a strong quantitative
pressure statement: for EACH nonnegative M, EVERY sufficiently late
Riccati peak either starts at quadratic H3 energy or pays at least M
units of one actual normalized PDE source-rate density. This does not
interchange the eventual quantifier and the multiplier quantifier. -/
theorem h3Critical_minimalShell_allEpsilon_forces_normalizedSourcePressure
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℕ → ℝ) (N : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ)
    (hAll : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiEpsilonSourceRateAt
            u t N C v k ε) :
    ∀ M : ℝ, 0 ≤ M →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiNormalizedSourcePressureAt
            u t N C v k M := by
  intro M hM
  obtain ⟨ε, hεPos, hεOne, h512, h16⟩ :=
    h3Critical_scalar_smallEpsilon_absorbs_normalizedRateMultiplier M hM
  have hEvent := hAll ε hεPos hεOne
  filter_upwards [hEvent] with k hEventK
  intro hRic
  rcases hEventK hRic with hAnchor | hLin | hQuad
  · exact Or.inl hAnchor
  · right
    left
    let A : ℝ :=
      2304 * velocityH3EnergyAt u (t (v k)) *
        (C (v k)) ^ 2 * ((N (v k) : ℝ) + 2) ^ 10 + 1
    have hE : 0 ≤ velocityH3EnergyAt u (t (v k)) :=
      (zero_le_one : (0 : ℝ) ≤ 1).trans
        (one_le_velocityH3EnergyAt u (t (v k)))
    have hA : 0 ≤ A := by
      dsimp only [A]
      positivity
    have hBound : ((v k : ℝ) + 1) ^ 12 ≤ 512 * ε ^ 2 * A := by
      simpa only [A] using hLin
    have hMult := mul_le_mul_of_nonneg_left hBound hM
    have hFactor := mul_le_mul_of_nonneg_right h512 hA
    calc
      M * ((v k : ℝ) + 1) ^ 12 ≤ M * (512 * ε ^ 2 * A) := hMult
      _ = (512 * M * ε ^ 2) * A := by ring
      _ ≤ 1 * A := hFactor
      _ = A := by ring
  · right
    right
    let A : ℝ :=
      36 * (C (v k)) ^ 2 *
        (((N (v k) : ℝ) + 2) ^ 8 + ((v k : ℝ) + 2) ^ 8) + 1
    have hA : 0 ≤ A := by
      dsimp only [A]
      positivity
    have hBound : ((v k : ℝ) + 1) ^ 9 ≤ 16 * ε ^ 2 * A := by
      simpa only [A] using hQuad
    have hMult := mul_le_mul_of_nonneg_left hBound hM
    have hFactor := mul_le_mul_of_nonneg_right h16 hA
    calc
      M * ((v k : ℝ) + 1) ^ 9 ≤ M * (16 * ε ^ 2 * A) := hMult
      _ = (16 * M * ε ^ 2) * A := by ring
      _ ≤ 1 * A := hFactor
      _ = A := by ring

/-- A useful closure criterion for the normalized-pressure arm. If the
physical anchor is eventually below the quadratic threshold and BOTH
actual normalized linear/quadratic source terms have a common finite upper
bound, then there can be no late Riccati-heavy minimal-shell windows.
This is a conditional test, not an assertion of such PDE rate bounds. -/
theorem h3Critical_minimalShell_boundedNormalizedPressure_excludes_lateRiccati
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℕ → ℝ) (N : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hPressure : ∀ M : ℝ, 0 ≤ M →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiNormalizedSourcePressureAt
            u t N C v k M)
    (hAnchor : ∀ᶠ k : ℕ in atTop,
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ≤ ((v k : ℝ) + 1) ^ 2)
    (hLinear : ∀ᶠ k : ℕ in atTop,
      2304 * velocityH3EnergyAt u (t (v k)) * (C (v k)) ^ 2 *
        ((N (v k) : ℝ) + 2) ^ 10 + 1 ≤
        L * ((v k : ℝ) + 1) ^ 12)
    (hQuadratic : ∀ᶠ k : ℕ in atTop,
      36 * (C (v k)) ^ 2 *
        (((N (v k) : ℝ) + 2) ^ 8 + ((v k : ℝ) + 2) ^ 8) + 1 ≤
        L * ((v k : ℝ) + 1) ^ 9) :
    ∀ᶠ k : ℕ in atTop,
      ¬ h3CriticalMinimalShellRiccatiWindowAt u t δ v k := by
  have hM : 0 ≤ L + 1 := by linarith only [hL]
  have hHigh := hPressure (L + 1) hM
  filter_upwards [hHigh, hAnchor, hLinear, hQuadratic] with
    k hk hAnchorK hLinearK hQuadraticK
  intro hRic
  rcases hk hRic with hAnchorLarge | hLinearLarge | hQuadraticLarge
  · exact (not_lt_of_ge hAnchorK) hAnchorLarge
  · have hRPos : 0 < ((v k : ℝ) + 1) ^ 12 := by positivity
    have hContr := le_trans hLinearLarge hLinearK
    nlinarith only [hRPos, hContr]
  · have hRPos : 0 < ((v k : ℝ) + 1) ^ 9 := by positivity
    have hContr := le_trans hQuadraticLarge hQuadraticK
    nlinarith only [hRPos, hContr]

/-- Same physical no-trace first crossings and kinetic shell witnesses:
either the selected cubic charges diverge, or at every late Riccati-heavy
window the ORIGINAL physical anchor or its normalized source coefficients
pay any fixed multiplier M. The terminal threshold may depend on M.
The existing signed-gap theorem independently handles the charge-divergence
branch under its explicit positive-gap budget. -/
theorem h3Critical_noL2Trace_minimalShell_quantifiedRiccatiSourcePressure
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
      (∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiAnchorOrTerminalClockAt u T t v k) ∧
      ((∀ M : ℝ, ∃ q : ℕ,
          M < ∑ k ∈ Finset.range q,
            h3CriticalMinimalShellCubicWindowCost δ v k) ∨
        (∀ M : ℝ, 0 ≤ M →
          ∀ᶠ k : ℕ in atTop,
            h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
              h3CriticalMinimalShellRiccatiNormalizedSourcePressureAt
                u t N C v k M)) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
      hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
      hLocal, _hRefined⟩ :=
    h3Critical_noL2Trace_minimalShell_riccatiClock_sourceRateDichotomy
      hH3 hClass hNoTrace
  have hAll := h3Critical_minimalShellPhysicalRates_refine_allEpsilonRiccatiPressure
    u T t N C δ v hRates hLocal
  refine ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
    hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
    hLocal, ?_⟩
  rcases hAll with hDivergent | hQuantified
  · exact Or.inl hDivergent
  · exact Or.inr (h3Critical_minimalShell_allEpsilon_forces_normalizedSourcePressure
      u t N C δ v hQuantified)

end
end PrimeTensor.Bridge.Euclidean
