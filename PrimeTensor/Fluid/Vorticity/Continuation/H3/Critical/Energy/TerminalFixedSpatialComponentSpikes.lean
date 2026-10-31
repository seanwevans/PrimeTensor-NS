import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedPhysicalSourceChannel
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-!
# A single physical coordinate carries cofinal terminal source spikes

The actual physical source Hilbert space is `PiLp 2 (Fin 3 → H3ScalarL2)`.
The exact PiLp norm-square identity and finite choice convert cofinal escape
of the FULL Hilbert norm into cofinal escape of ONE fixed physical coordinate.

The result applies both to the projected momentum source and, after the
fixed Laplacian/Leray source split, to one of SIX fixed (source, coordinate)
channels. Neither the coordinate nor the source can depend on the cutoff or
amplitude threshold.

IMPORTANT: Cofinal spikes do not imply temporal non-L¹ integrability of
that coordinate: spikes might become narrower. The previous theorem gives
fixed-channel nonintegrability only at the full vector level. A separate
finite-product Bochner integrability argument is needed to transfer this
stronger conclusion to a fixed coordinate.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology

noncomputable section
set_option maxHeartbeats 800000

/-- If the three physical scalar L² coordinate norms are at most `B`, then
    the physical vector L² norm is at most `3*B`. The factor three is
    deliberately coarse: it avoids any additional square-root machinery. -/
theorem h3Critical_fin3_hilbert_norm_le_three_mul_coordinate_ceiling
    (V : H3PhysicalRealFinVectorL2Hilbert)
    (B : ℝ) (hB : 0 ≤ B)
    (hCoord : ∀ j : Fin 3, ‖V.ofLp j‖ ≤ B) :
    ‖V‖ ≤ 3 * B := by
  have h0 : ‖V.ofLp (0 : Fin 3)‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hB).mpr (hCoord 0)
  have h1 : ‖V.ofLp (1 : Fin 3)‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hB).mpr (hCoord 1)
  have h2 : ‖V.ofLp (2 : Fin 3)‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hB).mpr (hCoord 2)
  have hNormSq : ‖V‖ ^ 2 = ∑ j : Fin 3, ‖V.ofLp j‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => H3ScalarL2) V
  have hBoundSq : ‖V‖ ^ 2 ≤ (3 * B) ^ 2 := by
    rw [hNormSq, Fin.sum_univ_three]
    nlinarith only [h0, h1, h2, sq_nonneg B]
  exact (sq_le_sq₀ (norm_nonneg V) (mul_nonneg (by norm_num) hB)).mp hBoundSq

/-- For a finite physical vector, cofinal unboundedness cannot migrate
    indefinitely between coordinates: ONE fixed coordinate has spikes on
    EVERY terminal subinterval and beyond EVERY prescribed threshold. -/
theorem h3Critical_fin3_fixed_component_spikes_of_vector_spikes
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (T : ℝ)
    (hSpikes : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ M < ‖F t‖) :
    ∃ j : Fin 3,
      ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧ M < ‖(F t).ofLp j‖ := by
  classical
  by_contra hMissing
  have hEach (j : Fin 3) :
      ∃ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T ∧
        ∃ M : ℝ, ∀ t : ℝ, t ∈ Set.Ioo b T →
          ‖(F t).ofLp j‖ ≤ M := by
    by_contra hAbsent
    apply hMissing
    refine ⟨j, ?_⟩
    intro b hb M
    by_contra hNoSpike
    apply hAbsent
    refine ⟨b, hb, M, ?_⟩
    intro t ht
    exact le_of_not_gt (fun hLarge => hNoSpike ⟨t, ht, hLarge⟩)
  obtain ⟨b0, hb0, M0, h0⟩ := hEach 0
  obtain ⟨b1, hb1, M1, h1⟩ := hEach 1
  obtain ⟨b2, hb2, M2, h2⟩ := hEach 2
  let b : ℝ := max b0 (max b1 b2)
  have hb : b ∈ Set.Ioo (0 : ℝ) T := by
    dsimp only [b]
    exact ⟨lt_of_lt_of_le hb0.1 (le_max_left _ _),
      max_lt hb0.2 (max_lt hb1.2 hb2.2)⟩
  let K : ℝ := max M0 (max M1 (max M2 0))
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact (le_max_right M2 (0 : ℝ)).trans
      ((le_max_right M1 (max M2 0)).trans
        (le_max_right M0 (max M1 (max M2 0))))
  have hM0 : M0 ≤ K := le_max_left _ _
  have hM1 : M1 ≤ K :=
    (le_max_left M1 (max M2 0)).trans (le_max_right _ _)
  have hM2 : M2 ≤ K :=
    (le_max_left M2 (0 : ℝ)).trans
      ((le_max_right M1 (max M2 0)).trans (le_max_right _ _))
  obtain ⟨t, ht, hLarge⟩ := hSpikes b hb (3 * K)
  have hComponent : ∀ j : Fin 3, ‖(F t).ofLp j‖ ≤ K := by
    intro j
    fin_cases j
    · have ht0 : t ∈ Set.Ioo b0 T :=
        ⟨lt_of_le_of_lt (le_max_left b0 (max b1 b2)) ht.1, ht.2⟩
      exact (h0 t ht0).trans hM0
    · have ht1 : t ∈ Set.Ioo b1 T :=
        ⟨lt_of_le_of_lt
          ((le_max_left b1 b2).trans (le_max_right b0 (max b1 b2)))
          ht.1, ht.2⟩
      exact (h1 t ht1).trans hM1
    · have ht2 : t ∈ Set.Ioo b2 T :=
        ⟨lt_of_le_of_lt
          ((le_max_right b1 b2).trans (le_max_right b0 (max b1 b2)))
          ht.1, ht.2⟩
      exact (h2 t ht2).trans hM2
  exact (not_le_of_gt hLarge)
    (h3Critical_fin3_hilbert_norm_le_three_mul_coordinate_ceiling
      (F t) K hK hComponent)

/-- Even with no terminal kinetic-mass assumption, absence of a physical
    L² velocity trace forces one fixed coordinate of the ACTUAL physical
    projected momentum source to have cofinal L²-norm spikes. -/
theorem h3Critical_noL2Trace_fixed_projected_source_coordinate_spikes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ j : Fin 3,
      ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖(h3PathActualProjectedMomentumSource244 hH3 t).ofLp j‖ := by
  exact h3Critical_fin3_fixed_component_spikes_of_vector_spikes
    (h3PathActualProjectedMomentumSource244 hH3) T
    (h3Critical_noL2Trace_projected_source_cofinally_unbounded hH3 hNoTrace)

/-- The fixed physical source channel itself can be localized to ONE of its
    three spatial coordinates. Thus a single pair (diffusion/transport, j)
    has arbitrarily large norm on every terminal tail; neither choice
    depends on the tail or threshold. -/
theorem h3Critical_noL2Trace_fixed_laplacian_or_leray_coordinate_spikes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    (∃ j : Fin 3,
      ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖(h3AuditInitialActualSpectralLaplacianTotal hH3 t).ofLp j‖) ∨
    (∃ j : Fin 3,
      ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖(h3AuditInitialActualSpectralLerayTotal hH3 t).ofLp j‖) := by
  rcases h3Critical_noL2Trace_fixed_physicalSource_nonintegrable_and_spikes
    hH3 hNoTrace with hD | hN
  · exact Or.inl
      (h3Critical_fin3_fixed_component_spikes_of_vector_spikes
        (h3AuditInitialActualSpectralLaplacianTotal hH3) T hD.2)
  · exact Or.inr
      (h3Critical_fin3_fixed_component_spikes_of_vector_spikes
        (h3AuditInitialActualSpectralLerayTotal hH3) T hN.2)

end
end PrimeTensor.Bridge.Euclidean
