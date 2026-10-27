import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEMinimalOuterCutoff244
import Mathlib.Tactic

/-!
# Ninth-eighth separation for the actual first-crossing physical Fourier cutoff

The minimal-cutoff quadratic-sharp clocks carry the same three-scale PDE
alternative as the older arbitrary-cutoff witnesses. The eighth-order
quadratic spectral gain converts that alternative to intermittent ninth-eighth
separation for the *minimal* outer annular crossing radius.

Moreover, every candidate cutoff with shifted eighth power below an arbitrary
multiple of the inner ninth power lies strictly before the first crossing,
and hence has annular dissipation no greater than three quarters of the
inner cubic height. This is a spectral-mass consequence, not a new PDE
regularity estimate. The noncompression, linear-rate, source-ceiling and
terminal full-H3-integrability conditions remain explicit.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Combine a quadratic-sharp three-scale barrier with the exact physical
quadratic coefficient and the proved eighth-order radial Sobolev gain.
No outer-cutoff bound is assumed. -/
theorem h3Path_minimalQuadraticSharp_threeScale_forces_eighthGain244
    (R Q G L Ξ C : ℕ → ℝ)
    (hR : ∀ k : ℕ, 1 ≤ R k)
    (hQ : ∀ k : ℕ, 0 ≤ Q k)
    (hThree : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      G k ≤ ε ∨ R k ^ 6 ≤ 16 * ε * (L k + 1) ∨
        R k ^ 9 ≤ 16 * ε ^ 2 * (Ξ k + 1))
    (hQuadratic : ∀ k : ℕ,
      Ξ k = h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
        (R k) (Q k) (C k))
    (η B D S : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ k : ℕ in atTop,
      η ≤ G k → L k + 1 ≤ B * R k ^ 6 →
        C k ^ 2 ≤ S ^ 2 →
          D * R k ^ 9 <
            36 * S ^ 2 * ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1 := by
  have hJoint :=
    h3Path_quadraticSharpThreeScale_jointIntermittentEscape244
      R G L Ξ (fun k => lt_of_lt_of_le zero_lt_one (hR k))
      hThree η B D hη hB hD
  filter_upwards [hJoint] with k hk
  intro hkGeom hkLinear hkSource
  rcases hk hkGeom with hkL | hkXi
  · exact False.elim ((not_lt_of_ge hkLinear) hkL)
  · have hkRate : D * R k ^ 9 <
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          (R k) (Q k) (C k) + 1 := by
      simpa only [hQuadratic k] using hkXi
    exact h3Path_ninthQuadraticRate_boundedSource_forces_eighthCutoff244
      (R k) (Q k) (C k) S D (le_trans (by norm_num : (0 : ℝ) ≤ 1) (hR k)) (hQ k) hkSource hkRate

/-- The exterior eighth-power separation implies every smaller shifted
cutoff under that scale lies before the canonical first crossing. -/
theorem h3Path_eighthSeparation_forces_preFirstCrossing244
    (N m : ℕ) (R M : ℝ)
    (hCandidate : ((m : ℝ) + 2) ^ 8 ≤ M * R ^ 9)
    (hSeparated : M * R ^ 9 < (((N : ℝ) + 1) + 1) ^ 8) :
    m < N := by
  by_contra hNot
  have hNm : N ≤ m := Nat.le_of_not_gt hNot
  have hCast : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hNm
  have hOrder : (N : ℝ) + 2 ≤ (m : ℝ) + 2 := by
    linarith only [hCast]
  have hPow : ((N : ℝ) + 2) ^ 8 ≤ ((m : ℝ) + 2) ^ 8 :=
    pow_le_pow_left₀ (by positivity) hOrder 8
  have hSep' : M * R ^ 9 < ((N : ℝ) + 2) ^ 8 := by
    convert hSeparated using 1 <;> ring
  exact (not_lt_of_ge (le_trans hPow hCandidate)) hSep'

/-- The *minimal*, first-crossing physical outer cutoffs inherit the
intermittent ninth-eighth separation and the divergent outer/inner ratio.
Every lower candidate on that scale remains below the annular threshold.
The finite H3 terminal dissipation hypothesis is not discharged here. -/
theorem h3Path_noL2Trace_finiteDissipation_minimalOuterGrowth244
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
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k m : ℕ, v k ≤ m → m < N (v k) →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
            3 * (((v k : ℝ) + 1) ^ 3) / 4) ∧
      (∀ η B S M : ℝ, 0 < η → 0 ≤ B → 0 ≤ M →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) →
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
              B * ((v k : ℝ) + 1) ^ 6 →
            C (v k) ^ 2 ≤ S ^ 2 →
              M * ((v k : ℝ) + 1) ^ 9 <
                (((N (v k) : ℝ) + 1) + 1) ^ 8) ∧
      (∀ η B S : ℝ, 0 < η → 0 ≤ B →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
              B * ((v k : ℝ) + 1) ^ 6 ∧
            C (v k) ^ 2 ≤ S ^ 2) →
        Tendsto (fun k : ℕ =>
          (((N (v k) : ℝ) + 1) + 1) ^ 8 / ((v k : ℝ) + 1) ^ 9)
          atTop atTop) ∧
      (∀ η B S M : ℝ, 0 < η → 0 ≤ B → 0 ≤ M →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) →
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
              B * ((v k : ℝ) + 1) ^ 6 →
            C (v k) ^ 2 ≤ S ^ 2 →
            ∀ m : ℕ, v k ≤ m →
              ((m : ℝ) + 2) ^ 8 ≤ M * ((v k : ℝ) + 1) ^ 9 →
              h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
                  (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
                h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
                  (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
                3 * (((v k : ℝ) + 1) ^ 3) / 4) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparated, hGap,
      hSummable, hMinimal, hThree⟩ :=
    h3Path_noL2Trace_finiteDissipation_minimalQuadraticSharpThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  let R : ℕ → ℝ := fun k => ((v k : ℝ) + 1)
  let Q : ℕ → ℝ := fun k => ((N (v k) : ℝ) + 1)
  let G : ℕ → ℝ := fun k =>
    ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)
  let L : ℕ → ℝ := fun k =>
    h3PathCubicAnnulusActualLinearRate244 N K C (v k)
  let X : ℕ → ℝ := fun k =>
    h3PathCubicAnnulusActualQuadraticRate244 N C (v k)
  let Src : ℕ → ℝ := fun k => C (v k)
  have hR : ∀ k : ℕ, 1 ≤ R k := by
    intro k
    dsimp only [R]
    have hCast : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hCast]
  have hQ : ∀ k : ℕ, 0 ≤ Q k := by
    intro k
    dsimp only [Q]
    positivity
  have hThree' : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      G k ≤ ε ∨ R k ^ 6 ≤ 16 * ε * (L k + 1) ∨
        R k ^ 9 ≤ 16 * ε ^ 2 * (X k + 1) := by
    intro ε hε
    simpa only [R, G, L, X] using hThree ε hε
  have hQuadratic : ∀ k : ℕ,
      X k = h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
        (R k) (Q k) (Src k) := by
    intro k
    rfl
  have hEighth (η B D S : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) :
      ∀ᶠ k : ℕ in atTop,
        η ≤ G k → L k + 1 ≤ B * R k ^ 6 →
          Src k ^ 2 ≤ S ^ 2 →
            D * R k ^ 9 <
              36 * S ^ 2 * ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1 :=
    h3Path_minimalQuadraticSharp_threeScale_forces_eighthGain244
      R Q G L X Src hR hQ hThree' hQuadratic η B D S hη hB hD
  have hOuter (η B S M : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hM : 0 ≤ M) :
      ∀ᶠ k : ℕ in atTop,
        η ≤ G k → L k + 1 ≤ B * R k ^ 6 →
          Src k ^ 2 ≤ S ^ 2 →
            M * R k ^ 9 < (Q k + 1) ^ 8 :=
    h3Path_ninthEighthCutoff_intermit_forces_outerSeparation244
      R Q G L Src hR hEighth η B S M hη hB hM
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparated, hGap,
    hSummable, hMinimal, ?_, ?_, ?_⟩
  · intro η B S M hη hB hM
    simpa only [R, Q, G, L, Src] using hOuter η B S M hη hB hM
  · intro η B S hη hB hRegime
    have hReg : ∀ᶠ k : ℕ in atTop,
        η ≤ G k ∧ L k + 1 ≤ B * R k ^ 6 ∧ Src k ^ 2 ≤ S ^ 2 := by
      simpa only [R, G, L, Src] using hRegime
    simpa only [R, Q] using
      (h3Path_ninthEighthCutoff_uniformRegime_forces_outerRatioEscape244
        R Q G L Src hR hEighth η B S hη hB hReg)
  · intro η B S M hη hB hM
    filter_upwards [hOuter η B S M hη hB hM] with k hk
    intro hkGeom hkLinear hkSource m hvm hmCandidate
    have hSep : M * R k ^ 9 < (Q k + 1) ^ 8 :=
      hk hkGeom hkLinear hkSource
    have hSep' : M * R k ^ 9 < (((N (v k) : ℝ) + 1) + 1) ^ 8 := by
      simpa only [Q] using hSep
    have hCandidate : ((m : ℝ) + 2) ^ 8 ≤ M * R k ^ 9 := by
      simpa only [R] using hmCandidate
    have hmN : m < N (v k) :=
      h3Path_eighthSeparation_forces_preFirstCrossing244
        (N (v k)) m (R k) M hCandidate hSep'
    exact hMinimal k m hvm hmN

end
end PrimeTensor.FirstMonomialTriad
