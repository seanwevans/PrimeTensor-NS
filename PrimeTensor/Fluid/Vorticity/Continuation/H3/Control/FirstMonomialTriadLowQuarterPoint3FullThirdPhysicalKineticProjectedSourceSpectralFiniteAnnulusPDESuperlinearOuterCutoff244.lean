import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticEighthCutoff244
import Mathlib.Tactic

/-!
# Intermittent superlinear outer Fourier cutoff forced by ninth-order PDE concentration

The exact quadratic-sharp physical clock forces an arbitrarily high ninth-order
quadratic coefficient when the terminal lag remains noncompressed and the
linear sixth-order rate is bounded. The physical coefficient has already
been bounded by `36 * C^2 * ((Q+1)^8 + (R+1)^8)`.

We eliminate the lower-radius eighth-order contribution explicitly. For
any fixed source ceiling and any prescribed multiple `M` of `R^9`, the
selected *outer* cutoff obeys `(Q+1)^8 > M * R^9` on sufficiently late
noncompressed witnesses with bounded linear rate and source ceiling.

This is a conditional separation at the ninth-eighth scaling, not a bound
on the outer cutoff from above and not a terminal-regularity contradiction.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- At radii `R >= 1`, the inner eighth power costs at most `256 * R^9`.
Therefore a ninth-order quadratic PDE spike exceeding that contribution
and a proposed outer-radius allowance forces `(Q+1)^8 > M*R^9`. -/
theorem h3Path_ninthEighthCutoffCost_forces_superlinearOuter244
    (R Q S M D : ℝ)
    (hR : 1 ≤ R) (_hM : 0 ≤ M)
    (hSpike : D * R ^ 9 <
      36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1)
    (hThreshold : 36 * S ^ 2 * (M + 256) + 1 ≤ D) :
    M * R ^ 9 < (Q + 1) ^ 8 := by
  by_contra hNot
  have hOuter : (Q + 1) ^ 8 ≤ M * R ^ 9 := le_of_not_gt hNot
  have hR8 : R ^ 8 ≤ R ^ 9 := by
    calc
      R ^ 8 = R ^ 8 * 1 := by ring
      _ ≤ R ^ 8 * R := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = R ^ 9 := by ring
  have hR9One : (1 : ℝ) ≤ R ^ 9 := by
    have hp := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hR 9
    simpa only [one_pow] using hp
  have hInner : (R + 1) ^ 8 ≤ 256 * R ^ 9 := by
    calc
      (R + 1) ^ 8 ≤ (2 * R) ^ 8 :=
        pow_le_pow_left₀ (by linarith only [hR])
          (by linarith only [hR]) 8
      _ = 256 * R ^ 8 := by ring
      _ ≤ 256 * R ^ 9 :=
        mul_le_mul_of_nonneg_left hR8 (by norm_num)
  have hPair : (Q + 1) ^ 8 + (R + 1) ^ 8 ≤ (M + 256) * R ^ 9 := by
    calc
      _ ≤ M * R ^ 9 + 256 * R ^ 9 := add_le_add hOuter hInner
      _ = (M + 256) * R ^ 9 := by ring
  have hScaled :
      36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) ≤
        36 * S ^ 2 * ((M + 256) * R ^ 9) :=
    mul_le_mul_of_nonneg_left hPair (by positivity)
  have hCost :
      36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1 ≤
        (36 * S ^ 2 * (M + 256) + 1) * R ^ 9 := by
    calc
      _ ≤ 36 * S ^ 2 * ((M + 256) * R ^ 9) + R ^ 9 :=
        add_le_add hScaled hR9One
      _ = (36 * S ^ 2 * (M + 256) + 1) * R ^ 9 := by ring
  have hFinal :
      (36 * S ^ 2 * (M + 256) + 1) * R ^ 9 ≤ D * R ^ 9 :=
    mul_le_mul_of_nonneg_right hThreshold (by positivity)
  exact (not_lt_of_ge (hCost.trans hFinal)) hSpike

/-- An intermittent ninth-order physical barrier gives arbitrarily large
ninth-eighth outer-radius separation, without imposing an eventual branch
choice. The hypotheses encode the already-proved eighth-power PDE gain. -/
theorem h3Path_ninthEighthCutoff_intermit_forces_outerSeparation244
    (R Q G L C : ℕ → ℝ)
    (hR : ∀ k : ℕ, 1 ≤ R k)
    (hBarrier : ∀ η B D S : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
      ∀ᶠ k : ℕ in atTop,
        η ≤ G k →
          L k + 1 ≤ B * R k ^ 6 →
          C k ^ 2 ≤ S ^ 2 →
            D * R k ^ 9 <
              36 * S ^ 2 * ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1)
    (η B S M : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∀ᶠ k : ℕ in atTop,
      η ≤ G k →
        L k + 1 ≤ B * R k ^ 6 →
          C k ^ 2 ≤ S ^ 2 →
            M * R k ^ 9 < (Q k + 1) ^ 8 := by
  let D : ℝ := 36 * S ^ 2 * (M + 256) + 2
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hm : 0 ≤ M + 256 := by linarith only [hM]
    positivity
  have hThreshold : 36 * S ^ 2 * (M + 256) + 1 ≤ D := by
    dsimp only [D]
    linarith
  filter_upwards [hBarrier η B D S hη hB hD] with k hk
  intro hkGeom hkLinear hkSource
  exact h3Path_ninthEighthCutoffCost_forces_superlinearOuter244
    (R k) (Q k) S M D (hR k) hM
    (hk hkGeom hkLinear hkSource) hThreshold

/-- If the noncompression, linear-rate, and source-ceiling hypotheses all
hold eventually, the selected outer-radius eighth-power divided by the
inner ninth-power diverges to infinity. -/
theorem h3Path_ninthEighthCutoff_uniformRegime_forces_outerRatioEscape244
    (R Q G L C : ℕ → ℝ)
    (hR : ∀ k : ℕ, 1 ≤ R k)
    (hBarrier : ∀ η B D S : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
      ∀ᶠ k : ℕ in atTop,
        η ≤ G k →
          L k + 1 ≤ B * R k ^ 6 →
          C k ^ 2 ≤ S ^ 2 →
            D * R k ^ 9 <
              36 * S ^ 2 * ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1)
    (η B S : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (hRegime : ∀ᶠ k : ℕ in atTop,
      η ≤ G k ∧ L k + 1 ≤ B * R k ^ 6 ∧ C k ^ 2 ≤ S ^ 2) :
    Tendsto (fun k : ℕ => (Q k + 1) ^ 8 / R k ^ 9) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  let M : ℝ := max 0 (b + 1)
  have hM : 0 ≤ M := le_max_left _ _
  have hb : b < M := by
    dsimp only [M]
    exact lt_of_lt_of_le (by linarith : b < b + 1) (le_max_right _ _)
  have hGrowth := h3Path_ninthEighthCutoff_intermit_forces_outerSeparation244
    R Q G L C hR hBarrier η B S M hη hB hM
  filter_upwards [hGrowth, hRegime] with k hk hReg
  have hRpos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
  have hR9pos : 0 < R k ^ 9 := pow_pos hRpos _
  have hStrong : M * R k ^ 9 < (Q k + 1) ^ 8 :=
    hk hReg.1 hReg.2.1 hReg.2.2
  have hRatio : M < (Q k + 1) ^ 8 / R k ^ 9 :=
    (lt_div_iff₀ hR9pos).2 hStrong
  exact (lt_trans hb hRatio).le

/-- Physical no-terminal-strong-L²-trace witnesses inherit quantitative
ninth-eighth cutoff separation. Full terminal H³ dissipation remains an
explicit additional hypothesis; no eventual noncompression is asserted. -/
theorem h3Path_noL2Trace_finiteDissipation_superlinearOuterCutoff244
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
          atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparated,
      hGap, hSummable, hBarrier⟩ :=
    h3Path_noL2Trace_finiteDissipation_ninthRateEighthCutoff244
      hH3 hClass hMass hNoTrace hDInt
  let R : ℕ → ℝ := fun k => ((v k : ℝ) + 1)
  let Q : ℕ → ℝ := fun k => ((N (v k) : ℝ) + 1)
  let G : ℕ → ℝ := fun k =>
    ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)
  let L : ℕ → ℝ := fun k =>
    h3PathCubicAnnulusActualLinearRate244 N K C (v k)
  let Src : ℕ → ℝ := fun k => C (v k)
  have hR : ∀ k : ℕ, 1 ≤ R k := by
    intro k
    dsimp only [R]
    have hk : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hk]
  have hAbstract (η B D S : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) :
      ∀ᶠ k : ℕ in atTop,
        η ≤ G k → L k + 1 ≤ B * R k ^ 6 →
          Src k ^ 2 ≤ S ^ 2 →
            D * R k ^ 9 <
              36 * S ^ 2 * ((Q k + 1) ^ 8 + (R k + 1) ^ 8) + 1 := by
    simpa only [R, Q, G, L, Src] using hBarrier η B D S hη hB hD
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparated,
    hGap, hSummable, ?_, ?_⟩
  · intro η B S M hη hB hM
    simpa only [R, Q, G, L, Src] using
      (h3Path_ninthEighthCutoff_intermit_forces_outerSeparation244
        R Q G L Src hR hAbstract η B S M hη hB hM)
  · intro η B S hη hB hRegime
    have hReg : ∀ᶠ k : ℕ in atTop,
        η ≤ G k ∧ L k + 1 ≤ B * R k ^ 6 ∧ Src k ^ 2 ≤ S ^ 2 := by
      simpa only [R, G, L, Src] using hRegime
    simpa only [R, Q] using
      (h3Path_ninthEighthCutoff_uniformRegime_forces_outerRatioEscape244
        R Q G L Src hR hAbstract η B S hη hB hReg)

end
end PrimeTensor.FirstMonomialTriad
