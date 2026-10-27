import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalShellNinthKinetic244
import Mathlib.Tactic

/-!
# Critical annular-width cap forces actual projected PDE source escape

The existing quadratic-sharp physical PDE clock gives the pointwise alternative
  M R^9 < (R+L+1)^8
whenever geometric noncompression, sixth-order linear-rate control, and a
bound C² ≤ S² on the selected projected source all hold.

Here the converse is made dynamical: if the geometric and linear-rate tests
persist and the *critical annular width* obeys (L+1)^8 ≤ D R^9 eventually,
then the actual source amplitude square C(v(k))² tends to +∞.
The width cap is an explicit additional condition. Neither it nor the
geometric/linear-rate conditions are claimed unconditionally.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A bounded critical ninth/eighth annular width bounds the full outer
frequency at the same critical scale. The universal factor 256 is enough
whether the width is smaller or larger than the inner radius. -/
theorem h3Path_criticalWidthCap_boundsOuter244
    (R L D : ℝ) (hR : 1 ≤ R) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hCap : (L + 1) ^ 8 ≤ D * R ^ 9) :
    (R + L + 1) ^ 8 ≤ (256 * (D + 1)) * R ^ 9 := by
  have hRnonneg : 0 ≤ R := le_trans (by norm_num) hR
  have hR8 : R ^ 8 ≤ R ^ 9 := by
    calc
      R ^ 8 = R ^ 8 * 1 := by ring
      _ ≤ R ^ 8 * R := mul_le_mul_of_nonneg_left hR (pow_nonneg hRnonneg 8)
      _ = R ^ 9 := by ring
  have hD9 : D * R ^ 9 ≤ (D + 1) * R ^ 9 :=
    mul_le_mul_of_nonneg_right (by linarith only [hD]) (pow_nonneg hRnonneg 9)
  by_cases hWide : R ≤ L + 1
  · have hUpper : R + L + 1 ≤ 2 * (L + 1) := by
      linarith only [hWide]
    have hNonneg : 0 ≤ R + L + 1 := by
      linarith only [hR, hL]
    have hPow := pow_le_pow_left₀ hNonneg hUpper 8
    calc
      (R + L + 1) ^ 8 ≤ (2 * (L + 1)) ^ 8 := hPow
      _ = 256 * (L + 1) ^ 8 := by ring
      _ ≤ 256 * (D * R ^ 9) :=
        mul_le_mul_of_nonneg_left hCap (by norm_num)
      _ ≤ 256 * ((D + 1) * R ^ 9) :=
        mul_le_mul_of_nonneg_left hD9 (by norm_num)
      _ = (256 * (D + 1)) * R ^ 9 := by ring
  · have hNarrow : L + 1 ≤ R := le_of_lt (lt_of_not_ge hWide)
    have hUpper : R + L + 1 ≤ 2 * R := by
      linarith only [hNarrow]
    have hNonneg : 0 ≤ R + L + 1 := by
      linarith only [hR, hL]
    have hPow := pow_le_pow_left₀ hNonneg hUpper 8
    have hFactor : R ^ 9 ≤ (D + 1) * R ^ 9 := by
      have hOne : (1 : ℝ) ≤ D + 1 := by linarith only [hD]
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hOne (pow_nonneg hRnonneg 9))
    calc
      (R + L + 1) ^ 8 ≤ (2 * R) ^ 8 := hPow
      _ = 256 * R ^ 8 := by ring
      _ ≤ 256 * R ^ 9 :=
        mul_le_mul_of_nonneg_left hR8 (by norm_num)
      _ ≤ 256 * ((D + 1) * R ^ 9) :=
        mul_le_mul_of_nonneg_left hFactor (by norm_num)
      _ = (256 * (D + 1)) * R ^ 9 := by ring

/-- Pointwise PDE certificate: under geometric and linear-rate control,
Either the critical width exceeds D R^9, or a proposed source ceiling S²
fails. Unlike the conditional width-gain theorem, the source is NOT assumed
bounded here. -/
theorem h3Path_criticalWidth_or_projectedSourceLarge244
    (R L C G F η B D S : ℝ)
    (hR : 1 ≤ R) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hGeom : η ≤ G) (hLinear : F ≤ B * R ^ 6)
    (hPDE : η ≤ G → F ≤ B * R ^ 6 → C ^ 2 ≤ S ^ 2 →
      (256 * (D + 1)) * R ^ 9 < (R + L + 1) ^ 8) :
    D * R ^ 9 < (L + 1) ^ 8 ∨ S ^ 2 < C ^ 2 := by
  by_cases hWidth : D * R ^ 9 < (L + 1) ^ 8
  · exact Or.inl hWidth
  · right
    have hCap : (L + 1) ^ 8 ≤ D * R ^ 9 := le_of_not_gt hWidth
    have hUpper := h3Path_criticalWidthCap_boundsOuter244 R L D hR hL hD hCap
    by_contra hNot
    have hSource : C ^ 2 ≤ S ^ 2 := le_of_not_gt hNot
    exact (not_lt_of_ge hUpper) (hPDE hGeom hLinear hSource)

/-- At fixed noncompressed PDE clocks with a controlled linear rate, a
uniform ninth/eighth width cap forces the *square* of the physical source
coefficient to diverge. The source ceiling is NOT an assumption. -/
theorem h3Path_criticalWidthCap_forces_sourceSquareEscape244
    (R L C G F : ℕ → ℝ) (η B D : ℝ)
    (hR : ∀ k, 1 ≤ R k) (hL : ∀ k, 0 ≤ L k) (hD : 0 ≤ D)
    (hGeom : ∀ᶠ k : ℕ in atTop, η ≤ G k)
    (hLinear : ∀ᶠ k : ℕ in atTop, F k ≤ B * (R k) ^ 6)
    (hWidth : ∀ᶠ k : ℕ in atTop,
      (L k + 1) ^ 8 ≤ D * (R k) ^ 9)
    (hPDE : ∀ S : ℝ, ∀ᶠ k : ℕ in atTop,
      η ≤ G k → F k ≤ B * (R k) ^ 6 → C k ^ 2 ≤ S ^ 2 →
        (256 * (D + 1)) * (R k) ^ 9 < (R k + L k + 1) ^ 8) :
    Tendsto (fun k : ℕ => C k ^ 2) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let S : ℝ := max A 0 + 1
  have hS : 1 ≤ S := by
    dsimp only [S]
    have hMax : (0 : ℝ) ≤ max A 0 := le_max_right _ _
    linarith only [hMax]
  have hAS : A ≤ S := by
    dsimp only [S]
    have hMax : A ≤ max A 0 := le_max_left _ _
    linarith only [hMax]
  have hASq : A ≤ S ^ 2 := by
    have hSNonneg : 0 ≤ S := le_trans (by norm_num) hS
    have hShift : 0 ≤ S - 1 := by linarith only [hS]
    have hProduct := mul_nonneg hSNonneg hShift
    nlinarith only [hAS, hProduct]
  filter_upwards [hGeom, hLinear, hWidth, hPDE S] with k hg hl hw hp
  have hUpper := h3Path_criticalWidthCap_boundsOuter244
    (R k) (L k) D (hR k) (hL k) hD hw
  have hSource : S ^ 2 < C k ^ 2 := by
    by_contra hNot
    have hBound : C k ^ 2 ≤ S ^ 2 := le_of_not_gt hNot
    exact (not_lt_of_ge hUpper) (hp hg hl hBound)
  exact hASq.trans hSource.le

/-- Physical terminal consequence on the SAME selected Fourier kinetic
shells and disjoint PDE windows. If noncompression, the sixth-order linear
rate bound, and a fixed critical ninth/eighth annular-width cap all persist,
then the actual projected-source coefficient square tends to +infinity.
This is an alternative to the conditional width-escape branch, not an
unconditional PDE source divergence statement. -/
theorem h3Path_noL2Trace_finiteDissipation_widthCap_sourceSquareEscape244
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
        (v m : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ m k ∧ m k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((m k : ℝ) + 1) ((m k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        Tendsto (fun k : ℕ => C (v k) ^ 2) atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime, hSeparate,
      _hGap, hSummable, _hMinimal, _hTail, _hBand, hShell,
      _hLast, hOuter⟩ :=
    h3Path_noL2Trace_finiteDissipation_minimalShellNinthEighth244
      hH3 hClass hMass hNoTrace hDInt
  let R : ℕ → ℝ := fun k => ((v k : ℝ) + 1)
  let L : ℕ → ℝ := fun k => ((N (v k) - v k : ℕ) : ℝ)
  let Src : ℕ → ℝ := fun k => C (v k)
  let G : ℕ → ℝ := fun k =>
    ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)
  let F : ℕ → ℝ := fun k =>
    h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1
  have hR : ∀ k, 1 ≤ R k := by
    intro k
    dsimp only [R]
    have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hNat]
  have hL : ∀ k, 0 ≤ L k := by
    intro k
    dsimp only [L]
    exact Nat.cast_nonneg _
  have hOuterEq (k : ℕ) :
      R k + L k + 1 = ((N (v k) : ℝ) + 2) := by
    have hVN : v k ≤ N (v k) :=
      (hShell k).1.trans (hShell k).2.1.le
    dsimp only [R, L]
    rw [Nat.cast_sub hVN]
    ring
  refine ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_⟩
  · intro k
    exact ⟨(hShell k).1, (hShell k).2.1, (hShell k).2.2.2.1⟩
  · intro η B D hη hB hD hRegime
    have hGeom : ∀ᶠ k : ℕ in atTop, η ≤ G k := by
      filter_upwards [hRegime] with k hk
      exact hk.1
    have hLinear : ∀ᶠ k : ℕ in atTop, F k ≤ B * (R k) ^ 6 := by
      filter_upwards [hRegime] with k hk
      exact hk.2.1
    have hWidth : ∀ᶠ k : ℕ in atTop,
        (L k + 1) ^ 8 ≤ D * (R k) ^ 9 := by
      filter_upwards [hRegime] with k hk
      exact hk.2.2
    have hPDE (S : ℝ) : ∀ᶠ k : ℕ in atTop,
        η ≤ G k → F k ≤ B * (R k) ^ 6 → Src k ^ 2 ≤ S ^ 2 →
          (256 * (D + 1)) * (R k) ^ 9 < (R k + L k + 1) ^ 8 := by
      have hFactor : 0 ≤ 256 * (D + 1) := by positivity
      have hImp := hOuter η B S (256 * (D + 1)) hη hB hFactor
      filter_upwards [hImp] with k hk
      intro hg hl hs
      have hG : η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) := by
        simpa only [G] using hg
      have hF : h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
          B * (((v k : ℝ) + 1) ^ 6) := by
        simpa only [F, R] using hl
      have hS : C (v k) ^ 2 ≤ S ^ 2 := by
        simpa only [Src] using hs
      have hPoint := (hk hG hF hS).1
      rw [hOuterEq k]
      dsimp only [R]
      convert hPoint using 1
      ring
    exact h3Path_criticalWidthCap_forces_sourceSquareEscape244
      R L Src G F η B D hR hL hD hGeom hLinear hWidth hPDE

end
end PrimeTensor.FirstMonomialTriad
