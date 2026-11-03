import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiQuantifiedSourcePressure
import Mathlib.Tactic

/-!
# Minimal-shell Riccati pressure: outer cutoff escape or physical source-envelope escape

At an original minimal first-crossing window let R = v(k)+1, Q = N(v(k))+2,
E = actual anchor H3 energy, and C = actual physical PDE source envelope.
The accepted all-multiplier source-pressure theorem says that, when the
quadratic anchor alternative fails, arbitrary M must be paid by the actual
linear or quadratic source rate normalized by R^12 or R^9.

Here we prove directly that if E <= R^2, Q <= D*R and 0 <= C <= L, both
normalized rate densities have explicit finite ceilings depending only on
D and L. Hence for each fixed D,L, a sufficiently late Riccati-heavy window
with anchor energy below its established quadratic threshold must have
Q > D*R OR C > L. This is an eventual-for-each-(D,L) theorem, not a
simultaneous single-window statement and not an unconditional bound on C.

The original last-shell kinetic mass, exact physical PDE clocks, disjoint
windows, and signed-gap accounting are retained by the parent witness.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalOuterEnvelope
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalOuterEnvelope :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- With at most quadratic H3 anchor energy, a bounded outer/inner radius
ratio and a bounded physical source envelope force an actual finite ceiling
on BOTH normalized twelfth/ninth source-rate factors. No denominator, PDE
regularity assumption, or upper bound on the full H3 dissipation is used. -/
theorem h3Critical_scalar_boundedOuterAndEnvelope_bounds_normalizedSourceRates
    (R Q E C D L : ℝ)
    (hR : 1 ≤ R) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hER : E ≤ R ^ 2)
    (hC : 0 ≤ C) (hCL : C ≤ L)
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hQR : Q ≤ D * R) :
    2304 * E * C ^ 2 * Q ^ 10 + 1 ≤
      (2304 * L ^ 2 * D ^ 10 + 1) * R ^ 12 ∧
    36 * C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) + 1 ≤
      (36 * L ^ 2 * (D ^ 8 + 256) + 1) * R ^ 9 := by
  have hR0 : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) hR
  have hC2 : C ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hC hCL 2
  have hQ10 : Q ^ 10 ≤ (D * R) ^ 10 :=
    pow_le_pow_left₀ hQ hQR 10
  have hQ8 : Q ^ 8 ≤ (D * R) ^ 8 :=
    pow_le_pow_left₀ hQ hQR 8
  have hECL : E * C ^ 2 ≤ R ^ 2 * L ^ 2 := by
    calc
      E * C ^ 2 ≤ R ^ 2 * C ^ 2 :=
        mul_le_mul_of_nonneg_right hER (sq_nonneg C)
      _ ≤ R ^ 2 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hC2 (sq_nonneg R)
  have hLinBase : (E * C ^ 2) * Q ^ 10 ≤
      (R ^ 2 * L ^ 2) * (D * R) ^ 10 := by
    calc
      (E * C ^ 2) * Q ^ 10 ≤ (R ^ 2 * L ^ 2) * Q ^ 10 :=
        mul_le_mul_of_nonneg_right hECL (pow_nonneg hQ 10)
      _ ≤ (R ^ 2 * L ^ 2) * (D * R) ^ 10 :=
        mul_le_mul_of_nonneg_left hQ10
          (mul_nonneg (sq_nonneg R) (sq_nonneg L))
  have hLinFactor : 2304 * E * C ^ 2 * Q ^ 10 ≤
      (2304 * L ^ 2 * D ^ 10) * R ^ 12 := by
    calc
      2304 * E * C ^ 2 * Q ^ 10 = 2304 * ((E * C ^ 2) * Q ^ 10) := by ring
      _ ≤ 2304 * ((R ^ 2 * L ^ 2) * (D * R) ^ 10) :=
        mul_le_mul_of_nonneg_left hLinBase (by norm_num)
      _ = (2304 * L ^ 2 * D ^ 10) * R ^ 12 := by ring
  have hR12 : 1 ≤ R ^ 12 := one_le_pow₀ hR
  have hLinBound : 2304 * E * C ^ 2 * Q ^ 10 + 1 ≤
      (2304 * L ^ 2 * D ^ 10 + 1) * R ^ 12 := by
    calc
      2304 * E * C ^ 2 * Q ^ 10 + 1 ≤
          (2304 * L ^ 2 * D ^ 10) * R ^ 12 + R ^ 12 :=
        add_le_add hLinFactor hR12
      _ = (2304 * L ^ 2 * D ^ 10 + 1) * R ^ 12 := by ring
  have hRplus : R + 1 ≤ 2 * R := by linarith only [hR]
  have hRplus0 : 0 ≤ R + 1 := by linarith only [hR]
  have hRplus8 : (R + 1) ^ 8 ≤ (2 * R) ^ 8 :=
    pow_le_pow_left₀ hRplus0 hRplus 8
  have hSum8 : Q ^ 8 + (R + 1) ^ 8 ≤
      (D * R) ^ 8 + (2 * R) ^ 8 := add_le_add hQ8 hRplus8
  have hSum0 : 0 ≤ Q ^ 8 + (R + 1) ^ 8 :=
    add_nonneg (pow_nonneg hQ 8) (pow_nonneg hRplus0 8)
  have hQuadBase : C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) ≤
      L ^ 2 * ((D * R) ^ 8 + (2 * R) ^ 8) := by
    calc
      C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) ≤
          L ^ 2 * (Q ^ 8 + (R + 1) ^ 8) :=
        mul_le_mul_of_nonneg_right hC2 hSum0
      _ ≤ L ^ 2 * ((D * R) ^ 8 + (2 * R) ^ 8) :=
        mul_le_mul_of_nonneg_left hSum8 (sq_nonneg L)
  have hQuadFactor8 : 36 * C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) ≤
      (36 * L ^ 2 * (D ^ 8 + 256)) * R ^ 8 := by
    calc
      36 * C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) =
          36 * (C ^ 2 * (Q ^ 8 + (R + 1) ^ 8)) := by ring
      _ ≤ 36 * (L ^ 2 * ((D * R) ^ 8 + (2 * R) ^ 8)) :=
        mul_le_mul_of_nonneg_left hQuadBase (by norm_num)
      _ = (36 * L ^ 2 * (D ^ 8 + 256)) * R ^ 8 := by ring
  have hR89 : R ^ 8 ≤ R ^ 9 :=
    pow_le_pow_right₀ hR (by norm_num : (8 : ℕ) ≤ 9)
  have hQuadCoeff : 0 ≤ 36 * L ^ 2 * (D ^ 8 + 256) := by positivity
  have hQuadFactor9 : 36 * C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) ≤
      (36 * L ^ 2 * (D ^ 8 + 256)) * R ^ 9 :=
    hQuadFactor8.trans (mul_le_mul_of_nonneg_left hR89 hQuadCoeff)
  have hR9 : 1 ≤ R ^ 9 := one_le_pow₀ hR
  have hQuadBound : 36 * C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) + 1 ≤
      (36 * L ^ 2 * (D ^ 8 + 256) + 1) * R ^ 9 := by
    calc
      36 * C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) + 1 ≤
          (36 * L ^ 2 * (D ^ 8 + 256)) * R ^ 9 + R ^ 9 :=
        add_le_add hQuadFactor9 hR9
      _ = (36 * L ^ 2 * (D ^ 8 + 256) + 1) * R ^ 9 := by ring
  exact ⟨hLinBound, hQuadBound⟩

/-- Quantified source pressure cannot persist at arbitrarily large
multipliers if BOTH outer radius and true source envelope are bounded.
The only escape is Q > D R or C > L. -/
theorem h3Critical_scalar_highSourcePressure_forces_outerOrEnvelope
    (R Q E C D L : ℝ)
    (hR : 1 ≤ R) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hER : E ≤ R ^ 2)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hPressure :
      (2304 * L ^ 2 * D ^ 10 +
        36 * L ^ 2 * (D ^ 8 + 256) + 3) * R ^ 12 ≤
        2304 * E * C ^ 2 * Q ^ 10 + 1 ∨
      (2304 * L ^ 2 * D ^ 10 +
        36 * L ^ 2 * (D ^ 8 + 256) + 3) * R ^ 9 ≤
        36 * C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) + 1) :
    D * R < Q ∨ L < C := by
  by_cases hOuter : D * R < Q
  · exact Or.inl hOuter
  by_cases hEnvelope : L < C
  · exact Or.inr hEnvelope
  have hQR : Q ≤ D * R := le_of_not_gt hOuter
  have hCL : C ≤ L := le_of_not_gt hEnvelope
  obtain ⟨hLinearBound, hQuadraticBound⟩ :=
    h3Critical_scalar_boundedOuterAndEnvelope_bounds_normalizedSourceRates
      R Q E C D L hR hQ hE hER hC hCL hD hL hQR
  let M : ℝ := 2304 * L ^ 2 * D ^ 10 +
    36 * L ^ 2 * (D ^ 8 + 256) + 3
  have hLinearCoeff : 2304 * L ^ 2 * D ^ 10 + 1 < M := by
    have hPos : 0 ≤ 36 * L ^ 2 * (D ^ 8 + 256) := by positivity
    dsimp only [M]
    linarith only [hPos]
  have hQuadCoeff : 36 * L ^ 2 * (D ^ 8 + 256) + 1 < M := by
    have hPos : 0 ≤ 2304 * L ^ 2 * D ^ 10 := by positivity
    dsimp only [M]
    linarith only [hPos]
  have hRPos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  rcases hPressure with hLinear | hQuad
  · have hScaled := mul_lt_mul_of_pos_right hLinearCoeff (pow_pos hRPos 12)
    have hRate : M * R ^ 12 ≤
        (2304 * L ^ 2 * D ^ 10 + 1) * R ^ 12 := by
      exact (show M * R ^ 12 ≤ 2304 * E * C ^ 2 * Q ^ 10 + 1 from hLinear).trans
        hLinearBound
    exact False.elim ((not_lt_of_ge hRate) hScaled)
  · have hScaled := mul_lt_mul_of_pos_right hQuadCoeff (pow_pos hRPos 9)
    have hRate : M * R ^ 9 ≤
        (36 * L ^ 2 * (D ^ 8 + 256) + 1) * R ^ 9 := by
      exact (show M * R ^ 9 ≤
        36 * C ^ 2 * (Q ^ 8 + (R + 1) ^ 8) + 1 from hQuad).trans
        hQuadraticBound
    exact False.elim ((not_lt_of_ge hRate) hScaled)

/-- Arbitrary normalized PDE source pressure converts into an eventual
three-way physical alternative at EACH prescribed outer-radius and source
threshold: the original anchor carries quadratic energy, or the genuine
minimal outer cutoff escapes D*R, or the original physical source envelope
exceeds L. No anchor bound is assumed in this theorem. -/
theorem h3Critical_minimalShell_quantifiedPressure_forces_anchorOrOuterOrEnvelope
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℕ → ℝ) (N : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ)
    (hCNonneg : ∀ k : ℕ, 0 ≤ C (v k))
    (hPressure : ∀ M : ℝ, 0 ≤ M →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiNormalizedSourcePressureAt
            u t N C v k M) :
    ∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          ((v k : ℝ) + 1) ^ 2 <
              4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
                velocityH3EnergyAt u (t (v k)) ∨
          D * ((v k : ℝ) + 1) < ((N (v k) : ℝ) + 2) ∨
          L < C (v k) := by
  intro D L hD hL
  let M : ℝ := 2304 * L ^ 2 * D ^ 10 +
    36 * L ^ 2 * (D ^ 8 + 256) + 3
  have hMNonneg : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hLate := hPressure M hMNonneg
  filter_upwards [hLate] with k hk
  intro hRic
  by_cases hSmall :
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ≤ ((v k : ℝ) + 1) ^ 2
  · right
    let R : ℝ := (v k : ℝ) + 1
    let Q : ℝ := (N (v k) : ℝ) + 2
    let E : ℝ := velocityH3EnergyAt u (t (v k))
    let c : ℝ := C (v k)
    have hR : 1 ≤ R := by
      dsimp only [R]
      have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
    have hE : 0 ≤ E := by
      dsimp only [E]
      exact (zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_velocityH3EnergyAt u _)
    have hCoeff : 1 ≤ 4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) := by
      nlinarith only [sq_nonneg h3PathSqrtEnergyRiccatiCoefficient]
    have hSmall' : 4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) * E ≤
        R ^ 2 := by simpa only [E, R] using hSmall
    have hScaled := mul_le_mul_of_nonneg_right hCoeff hE
    have hER : E ≤ R ^ 2 := by
      linarith only [hScaled, hSmall']
    have hPressure' :
        M * R ^ 12 ≤ 2304 * E * c ^ 2 * Q ^ 10 + 1 ∨
        M * R ^ 9 ≤ 36 * c ^ 2 * (Q ^ 8 + (R + 1) ^ 8) + 1 := by
      rcases hk hRic with hLarge | hLinear | hQuadratic
      · exact False.elim ((not_lt_of_ge hSmall) hLarge)
      · exact Or.inl (by simpa only [R, Q, E, c] using hLinear)
      · right
        have hPlus : (v k : ℝ) + 1 + 1 = (v k : ℝ) + 2 := by ring
        simpa only [R, Q, c, hPlus] using hQuadratic
    have hEscape := h3Critical_scalar_highSourcePressure_forces_outerOrEnvelope
      R Q E c D L hR hQ hE hER (hCNonneg k) hD hL
      (by simpa only [M] using hPressure')
    simpa only [R, Q, c] using hEscape
  · left
    exact lt_of_not_ge hSmall

/-- Conditional two-way refinement: under an eventual subquadratic original
anchor bound, the anchor arm of the preceding unconditional trichotomy is
excluded. Neither a bound on the outer frequency nor a source-envelope
bound is assumed. -/
theorem h3Critical_minimalShell_quantifiedPressure_forces_outerOrSourceEnvelope
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℕ → ℝ) (N : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ)
    (hCNonneg : ∀ k : ℕ, 0 ≤ C (v k))
    (hPressure : ∀ M : ℝ, 0 ≤ M →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiNormalizedSourcePressureAt
            u t N C v k M)
    (hAnchor : ∀ᶠ k : ℕ in atTop,
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ≤ ((v k : ℝ) + 1) ^ 2) :
    ∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          D * ((v k : ℝ) + 1) < ((N (v k) : ℝ) + 2) ∨
          L < C (v k) := by
  intro D L hD hL
  have hThree := h3Critical_minimalShell_quantifiedPressure_forces_anchorOrOuterOrEnvelope
    u t N C δ v hCNonneg hPressure D L hD hL
  filter_upwards [hThree, hAnchor] with k hk hSmall
  intro hRic
  rcases hk hRic with hLarge | hOuter | hEnvelope
  · exact False.elim ((not_lt_of_ge hSmall) hLarge)
  · exact Or.inl hOuter
  · exact Or.inr hEnvelope

/-- If the relative outer radius and actual physical source envelope are
both eventually bounded, the all-multiplier source-pressure arm plus an
eventually subquadratic anchor excludes all sufficiently late Riccati peaks.
The two ceiling hypotheses are genuine additional PDE inputs. -/
theorem h3Critical_minimalShell_boundedOuterAndSource_excludes_lateRiccati
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℕ → ℝ) (N : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ) (D L : ℝ)
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hCNonneg : ∀ k : ℕ, 0 ≤ C (v k))
    (hPressure : ∀ M : ℝ, 0 ≤ M →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiNormalizedSourcePressureAt
            u t N C v k M)
    (hAnchor : ∀ᶠ k : ℕ in atTop,
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ≤ ((v k : ℝ) + 1) ^ 2)
    (hOuter : ∀ᶠ k : ℕ in atTop,
      (N (v k) : ℝ) + 2 ≤ D * ((v k : ℝ) + 1))
    (hEnvelope : ∀ᶠ k : ℕ in atTop, C (v k) ≤ L) :
    ∀ᶠ k : ℕ in atTop,
      ¬ h3CriticalMinimalShellRiccatiWindowAt u t δ v k := by
  have hEscape := h3Critical_minimalShell_quantifiedPressure_forces_outerOrSourceEnvelope
    u t N C δ v hCNonneg hPressure hAnchor D L hD hL
  filter_upwards [hEscape, hOuter, hEnvelope] with k hk hOuterK hEnvelopeK
  intro hRic
  rcases hk hRic with hFar | hSource
  · exact (not_lt_of_ge hOuterK) hFar
  · exact (not_lt_of_ge hEnvelopeK) hSource

/-- Same disjoint minimal-shell physical selectors as the accepted no-trace
source-pressure theorem. In its bounded-charge/source-pressure arm, a
subquadratic original anchor forces every late Riccati-heavy window to
escape each prescribed simultaneous outer-radius and source-envelope cap.
The unbounded-charge arm is retained unchanged. No bound on C or N is
assumed or claimed from the Navier--Stokes equations. -/
theorem h3Critical_noL2Trace_minimalShell_outerOrSourceEnvelopeEscape
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
                u t N C v k M) ∧
        (∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
          ∀ᶠ k : ℕ in atTop,
            h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
              ((v k : ℝ) + 1) ^ 2 <
                4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
                  velocityH3EnergyAt u (t (v k)) ∨
              D * ((v k : ℝ) + 1) < (N (v k) : ℝ) + 2 ∨
              L < C (v k)) ∧
        ((∀ᶠ k : ℕ in atTop,
            4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
              velocityH3EnergyAt u (t (v k)) ≤ ((v k : ℝ) + 1) ^ 2) →
          ∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
            ∀ᶠ k : ℕ in atTop,
              h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
                D * ((v k : ℝ) + 1) < (N (v k) : ℝ) + 2 ∨
                L < C (v k))) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
      hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
      hLocal, hAlt⟩ :=
    h3Critical_noL2Trace_minimalShell_quantifiedRiccatiSourcePressure
      hH3 hClass hNoTrace
  refine ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
    hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
    hLocal, ?_⟩
  rcases hAlt with hDivergent | hPressure
  · exact Or.inl hDivergent
  · right
    have hCNonneg (k : ℕ) : 0 ≤ C (v k) := by
      rcases hWindow k with ⟨_, _, hC, _⟩
      exact hC
    refine ⟨hPressure, ?_, ?_⟩
    · exact h3Critical_minimalShell_quantifiedPressure_forces_anchorOrOuterOrEnvelope
        u t N C δ v hCNonneg hPressure
    · intro hAnchor D L hD hL
      exact h3Critical_minimalShell_quantifiedPressure_forces_outerOrSourceEnvelope
        u t N C δ v hCNonneg hPressure hAnchor D L hD hL

end
end PrimeTensor.Bridge.Euclidean
