import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceTemporalJump244
import Mathlib.Tactic

/-!
# Exact physical Laplacian-versus-Leray temporal splitting at canonical source peaks

At the canonical half-terminal source maximizers s_k and the disjoint cubic
PDE-window anchors t_k, the *actual* projected physical Hilbert source is

  P(r) = D(r) - L(r),

where D is the Fourier-reconstructed physical Laplacian and L is the actual
Fourier-reconstructed Leray transport. Thus

  ‖P(s_k)‖ ≤ ‖P(t_k)‖ + ‖D(s_k)-D(t_k)‖ + ‖L(s_k)-L(t_k)‖.

Under the previous CONDITIONAL canonical critical-width regime, ‖P(s_k)‖
escapes. This gives a three-channel obstruction on the SAME physical clocks:
source growth already at the anchor, a large diffusion temporal increment,
or a large Leray temporal increment. If the anchor source and either one of
the latter channels admit eventual uniform bounds, the other increment must
diverge on that original maximizing-time sequence.

Nothing here asserts a uniform source modulus or obtains a time-integrated
lower bound from a pointwise peak. The hypotheses enforcing canonical source
escape, in particular finite full H³ dissipation and the three critical
clock tests, are retained without weakening.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual projected source at a peak is controlled by its anchor
value and the two *distinct* physical PDE component increments. -/
theorem h3Path_physicalSourcePeak_le_anchor_diffusionJump_lerayJump244
    (Dpeak Danchor Lpeak Lanchor : H3PhysicalRealFinVectorL2Hilbert) :
    ‖Dpeak - Lpeak‖ ≤
      ‖Danchor - Lanchor‖ +
        ‖Dpeak - Danchor‖ + ‖Lpeak - Lanchor‖ := by
  have hIdentity :
      Dpeak - Lpeak =
        (Danchor - Lanchor) +
          ((Dpeak - Danchor) - (Lpeak - Lanchor)) := by
    abel
  rw [hIdentity]
  calc
    ‖(Danchor - Lanchor) +
        ((Dpeak - Danchor) - (Lpeak - Lanchor))‖ ≤
        ‖Danchor - Lanchor‖ +
          ‖(Dpeak - Danchor) - (Lpeak - Lanchor)‖ :=
      norm_add_le _ _
    _ ≤ ‖Danchor - Lanchor‖ +
          (‖Dpeak - Danchor‖ + ‖Lpeak - Lanchor‖) :=
      add_le_add (le_refl _) (norm_sub_le _ _)
    _ = ‖Danchor - Lanchor‖ +
          ‖Dpeak - Danchor‖ + ‖Lpeak - Lanchor‖ := by ring

/-- The source increment is bounded by the sum of its diffusion and
nonlinear Leray increments; the two endpoints are not reselected. -/
theorem h3Path_physicalSourceTemporalJump_le_componentJumps244
    (Dpeak Danchor Lpeak Lanchor : H3PhysicalRealFinVectorL2Hilbert) :
    ‖(Dpeak - Lpeak) - (Danchor - Lanchor)‖ ≤
      ‖Dpeak - Danchor‖ + ‖Lpeak - Lanchor‖ := by
  have hIdentity :
      (Dpeak - Lpeak) - (Danchor - Lanchor) =
        (Dpeak - Danchor) - (Lpeak - Lanchor) := by
    abel
  rw [hIdentity]
  exact norm_sub_le _ _

/-- Divergent physical projected source peaks demand at least one of three
PDE channels to cross every fixed threshold, eventually at EVERY selected
index. No single disjunct is chosen uniformly across the indices. -/
theorem h3Path_sourcePeaks_force_anchor_diffusionOrLerayTemporal244
    (Dpeak Danchor Lpeak Lanchor : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (hPeak : Tendsto (fun k : ℕ => ‖Dpeak k - Lpeak k‖) atTop atTop) :
    ∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
      M ≤ ‖Danchor k - Lanchor k‖ ∨
      M ≤ ‖Dpeak k - Danchor k‖ ∨
      M ≤ ‖Lpeak k - Lanchor k‖ := by
  intro M
  let A : ℝ := max M 0
  have hMA : M ≤ A := le_max_left M 0
  have hLarge : ∀ᶠ k : ℕ in atTop,
      3 * A ≤ ‖Dpeak k - Lpeak k‖ :=
    hPeak.eventually (eventually_ge_atTop (3 * A))
  filter_upwards [hLarge] with k hk
  have hEstimate := h3Path_physicalSourcePeak_le_anchor_diffusionJump_lerayJump244
    (Dpeak k) (Danchor k) (Lpeak k) (Lanchor k)
  by_cases hAnchor : A ≤ ‖Danchor k - Lanchor k‖
  · exact Or.inl (hMA.trans hAnchor)
  · by_cases hDiffusion : A ≤ ‖Dpeak k - Danchor k‖
    · exact Or.inr (Or.inl (hMA.trans hDiffusion))
    · right
      right
      have hAnchorSmall : ‖Danchor k - Lanchor k‖ < A := lt_of_not_ge hAnchor
      have hDiffSmall : ‖Dpeak k - Danchor k‖ < A := lt_of_not_ge hDiffusion
      have hLeray : A ≤ ‖Lpeak k - Lanchor k‖ := by
        linarith only [hk, hEstimate, hAnchorSmall, hDiffSmall]
      exact hMA.trans hLeray

/-- Once a physical source jump diverges, a fixed eventual bound on its
*diffusion* increment forces the Leray temporal increment to diverge.
This is the exact Fourier-Laplacian/Leray decomposition, not a postulated
norm bound for a source derivative. -/
theorem h3Path_boundedDiffusionJump_forces_lerayJumpEscape244
    (Dpeak Danchor Lpeak Lanchor : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (hJump : Tendsto (fun k : ℕ =>
      ‖(Dpeak k - Lpeak k) - (Danchor k - Lanchor k)‖) atTop atTop)
    (F : ℝ)
    (hDiff : ∀ᶠ k : ℕ in atTop, ‖Dpeak k - Danchor k‖ ≤ F) :
    Tendsto (fun k : ℕ => ‖Lpeak k - Lanchor k‖) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop,
      M + F ≤ ‖(Dpeak k - Lpeak k) - (Danchor k - Lanchor k)‖ :=
    hJump.eventually (eventually_ge_atTop (M + F))
  filter_upwards [hLarge, hDiff] with k hk hBound
  have hEstimate := h3Path_physicalSourceTemporalJump_le_componentJumps244
    (Dpeak k) (Danchor k) (Lpeak k) (Lanchor k)
  linarith only [hk, hBound, hEstimate]

/-- Dual branch: an eventual bound on the nonlinear Leray increment
forces a divergent physical diffusion temporal increment. -/
theorem h3Path_boundedLerayJump_forces_diffusionJumpEscape244
    (Dpeak Danchor Lpeak Lanchor : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (hJump : Tendsto (fun k : ℕ =>
      ‖(Dpeak k - Lpeak k) - (Danchor k - Lanchor k)‖) atTop atTop)
    (F : ℝ)
    (hLeray : ∀ᶠ k : ℕ in atTop, ‖Lpeak k - Lanchor k‖ ≤ F) :
    Tendsto (fun k : ℕ => ‖Dpeak k - Danchor k‖) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop,
      M + F ≤ ‖(Dpeak k - Lpeak k) - (Danchor k - Lanchor k)‖ :=
    hJump.eventually (eventually_ge_atTop (M + F))
  filter_upwards [hLarge, hLeray] with k hk hBound
  have hEstimate := h3Path_physicalSourceTemporalJump_le_componentJumps244
    (Dpeak k) (Danchor k) (Lpeak k) (Lanchor k)
  linarith only [hk, hBound, hEstimate]

/-- On one fixed cofinal disjoint PDE-window sequence and ONE previously
selected sequence of canonical source maximizers, retain the exact three
physical channels. Under the conditional critical-width regime, at every
late index either the anchor projected source, the physical Laplacian
increment or the physical Leray increment is large. If the anchor source
and diffusion increments are eventually bounded, the physical Leray
increment diverges; the converse holds if Leray increments are bounded.
All bounds are genuine additional inputs, not products of strict-time
continuity alone. -/
theorem h3Path_noL2Trace_canonicalWidth_diffusionLerayTemporalAlternative244
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
        (∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          M ≤ ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ∨
          M ≤ ‖h3AuditInitialActualSpectralLaplacianTotal hH3 (s k) -
            h3AuditInitialActualSpectralLaplacianTotal hH3 (τ (v k))‖ ∨
          M ≤ ‖h3AuditInitialActualSpectralLerayTotal hH3 (s k) -
            h3AuditInitialActualSpectralLerayTotal hH3 (τ (v k))‖) ∧
        (∀ E F : ℝ,
          (∀ᶠ k : ℕ in atTop,
            ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ≤ E) →
          (∀ᶠ k : ℕ in atTop,
            ‖h3AuditInitialActualSpectralLaplacianTotal hH3 (s k) -
              h3AuditInitialActualSpectralLaplacianTotal hH3 (τ (v k))‖ ≤ F) →
          Tendsto (fun k : ℕ =>
            ‖h3AuditInitialActualSpectralLerayTotal hH3 (s k) -
              h3AuditInitialActualSpectralLerayTotal hH3 (τ (v k))‖)
            atTop atTop) ∧
        (∀ E F : ℝ,
          (∀ᶠ k : ℕ in atTop,
            ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ≤ E) →
          (∀ᶠ k : ℕ in atTop,
            ‖h3AuditInitialActualSpectralLerayTotal hH3 (s k) -
              h3AuditInitialActualSpectralLerayTotal hH3 (τ (v k))‖ ≤ F) →
          Tendsto (fun k : ℕ =>
            ‖h3AuditInitialActualSpectralLaplacianTotal hH3 (s k) -
              h3AuditInitialActualSpectralLaplacianTotal hH3 (τ (v k))‖)
            atTop atTop)) := by
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
  let Dpeak : ℕ → H3PhysicalRealFinVectorL2Hilbert := fun k =>
    h3AuditInitialActualSpectralLaplacianTotal hH3 (s k)
  let Danchor : ℕ → H3PhysicalRealFinVectorL2Hilbert := fun k =>
    h3AuditInitialActualSpectralLaplacianTotal hH3 (τ (v k))
  let Lpeak : ℕ → H3PhysicalRealFinVectorL2Hilbert := fun k =>
    h3AuditInitialActualSpectralLerayTotal hH3 (s k)
  let Lanchor : ℕ → H3PhysicalRealFinVectorL2Hilbert := fun k =>
    h3AuditInitialActualSpectralLerayTotal hH3 (τ (v k))
  let peak : ℕ → H3PhysicalRealFinVectorL2Hilbert := fun k =>
    Dpeak k - Lpeak k
  let anchor : ℕ → H3PhysicalRealFinVectorL2Hilbert := fun k =>
    Danchor k - Lanchor k
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hCanonical k).1, (hCanonical k).2.1⟩
  · intro k
    exact ⟨hs k, hPeak k⟩
  · intro η B D hη hB hD hRegime
    have hSquare := (hEscape η B D hη hB hD hRegime).1
    have hAbs := h3Path_sourceCeilingSquareEscape_forces_absEscape244
      (fun k => C (v k)) hSquare
    have hCNonneg (k : ℕ) : 0 ≤ C (v k) := by
      rw [← hPeak k]
      exact norm_nonneg _
    have hEq : (fun k : ℕ => ‖peak k‖) =
        (fun k : ℕ => |C (v k)|) := by
      funext k
      change ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ =
        |C (v k)|
      rw [hPeak k]
      exact (abs_of_nonneg (hCNonneg k)).symm
    have hPeakEscape : Tendsto (fun k : ℕ => ‖peak k‖)
        atTop atTop := by
      rw [hEq]
      exact hAbs
    refine ⟨?_, ?_, ?_⟩
    · simpa only [peak, anchor, Dpeak, Danchor, Lpeak, Lanchor,
        h3PathActualProjectedMomentumSource244] using
        (h3Path_sourcePeaks_force_anchor_diffusionOrLerayTemporal244
          Dpeak Danchor Lpeak Lanchor hPeakEscape)
    · intro E F hBoundAnchor hBoundD
      have hAnchor' : ∀ᶠ k : ℕ in atTop, ‖anchor k‖ ≤ E := by
        simpa only [anchor, Danchor, Lanchor,
          h3PathActualProjectedMomentumSource244] using hBoundAnchor
      have hJump := h3Path_boundedAnchorSource_forces_temporalJumpEscape244
        peak anchor hPeakEscape E hAnchor'
      have hJump' : Tendsto (fun k : ℕ =>
          ‖(Dpeak k - Lpeak k) - (Danchor k - Lanchor k)‖)
          atTop atTop := by
        simpa only [peak, anchor] using hJump
      have hBoundD' : ∀ᶠ k : ℕ in atTop,
          ‖Dpeak k - Danchor k‖ ≤ F := by
        simpa only [Dpeak, Danchor] using hBoundD
      have hResult := h3Path_boundedDiffusionJump_forces_lerayJumpEscape244
        Dpeak Danchor Lpeak Lanchor hJump' F hBoundD'
      simpa only [Lpeak, Lanchor] using hResult
    · intro E F hBoundAnchor hBoundL
      have hAnchor' : ∀ᶠ k : ℕ in atTop, ‖anchor k‖ ≤ E := by
        simpa only [anchor, Danchor, Lanchor,
          h3PathActualProjectedMomentumSource244] using hBoundAnchor
      have hJump := h3Path_boundedAnchorSource_forces_temporalJumpEscape244
        peak anchor hPeakEscape E hAnchor'
      have hJump' : Tendsto (fun k : ℕ =>
          ‖(Dpeak k - Lpeak k) - (Danchor k - Lanchor k)‖)
          atTop atTop := by
        simpa only [peak, anchor] using hJump
      have hBoundL' : ∀ᶠ k : ℕ in atTop,
          ‖Lpeak k - Lanchor k‖ ≤ F := by
        simpa only [Lpeak, Lanchor] using hBoundL
      have hResult := h3Path_boundedLerayJump_forces_diffusionJumpEscape244
        Dpeak Danchor Lpeak Lanchor hJump' F hBoundL'
      simpa only [Dpeak, Danchor] using hResult

end
end PrimeTensor.FirstMonomialTriad
