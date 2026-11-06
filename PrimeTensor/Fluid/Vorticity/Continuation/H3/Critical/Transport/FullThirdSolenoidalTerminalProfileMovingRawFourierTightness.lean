import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileCriticalEighthPhysicalTransport
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalUniformHighRadialRecovery
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalCompactTimeRadialTightness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalFiniteBandPhysicalLowpass
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Genuine terminal L² Fourier tightness on moving physical bands

This is the missing compactness step in the critical-eighth kinetic-carrier
argument. The Fourier cutoff acts on *raw* physical L², not weighted H³.
For an L²-convergent moving sequence of genuine physical snapshots, every
radial cutoff tending to infinity has vanishing highpass norm. The exact
physical Fourier identification and the annulus/highpass inclusion transfer
that result to the physical kinetic mass in the minimal crossing annulus.

No H³ terminal trace, uniform H³ ceiling, or extra spectral compactness is
assumed. The proof does not assert that the critical-height profile exists.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeMovingRawTight244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMovingRawTight244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

private abbrev RawPhysicalFourier244 :=
  h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap

/-- Moving cutoffs do not lose the uniform tightness of a convergent physical
L² family. Unlike the analogous weighted H³ theorem, this is applied to the
raw Plancherel image of physical velocity, so it survives a possible H³
singularity at terminal time. -/
theorem thirdFullPhysical_movingRawHighpass_norm_tendsto_zero244
    (X : ℕ → H3PhysicalRealFinVectorL2Hilbert)
    (L : H3PhysicalRealFinVectorL2Hilbert) (n : ℕ → ℕ)
    (hX : Tendsto X atTop (𝓝 L))
    (hn : Tendsto n atTop atTop) :
    Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (n k)
        (RawPhysicalFourier244 (X k))‖) atTop (𝓝 (0 : ℝ)) := by
  let F : H3PhysicalRealFinVectorL2Hilbert → H3SpectralVelocityState :=
    RawPhysicalFourier244
  have hF : Tendsto (fun k : ℕ => F (X k)) atTop (𝓝 (F L)) :=
    (h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap.continuous.tendsto L).comp hX
  have hDiff : Tendsto (fun k : ℕ => ‖F (X k) - F L‖)
      atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mp hF
  have hTail : Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F L)‖)
      atTop (𝓝 (0 : ℝ)) :=
    (thirdFullSpectralVelocityHighRadialApply_norm_tendsto_zero244 (F L)).comp hn
  have hBound (k : ℕ) :
      ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F (X k))‖ ≤
      ‖F (X k) - F L‖ +
        ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F L)‖ := by
    calc
      ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F (X k))‖ =
          ‖thirdFullSpectralVelocityHighRadialApply244 (n k)
            ((F (X k) - F L) + F L)‖ := by rw [sub_add_cancel]
      _ = ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F (X k) - F L) +
            thirdFullSpectralVelocityHighRadialApply244 (n k) (F L)‖ := by
          rw [thirdFullSpectralVelocityHighRadialApply_add244]
      _ ≤ ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F (X k) - F L)‖ +
            ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F L)‖ :=
          norm_add_le _ _
      _ ≤ ‖F (X k) - F L‖ +
            ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F L)‖ :=
          add_le_add
            (thirdFullSpectralVelocityHighRadialApply_norm_le244 _ _)
            le_rfl
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hDiff) (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hTail) (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, ?_⟩
  intro k hk
  have hd := hN₁ k ((le_max_left N₁ N₂).trans hk)
  have ht := hN₂ k ((le_max_right N₁ N₂).trans hk)
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hd ht
  rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (norm_nonneg
        (thirdFullSpectralVelocityHighRadialApply244 (n k) (RawPhysicalFourier244 (X k))))]
  change ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (F (X k))‖ < ε
  exact lt_of_le_of_lt (hBound k) (by linarith only [hd, ht])

/-- The exact annular raw kinetic mass is bounded by three times the squared
raw highpass-vector norm, at the *same* inner cutoff. No assumption on the
outer radius is used, and the comparator is raw L² rather than H³. -/
theorem thirdFull_bandRawKineticMass_le_three_highpass244
    (n : ℕ) (Q : ℝ) (G : H3SpectralVelocityState) :
    h3PathActualBandRawKineticMass244 ((n : ℝ) + 1) Q G ≤
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 n
        (fun j : Fin 3 => h3TerminalRawVelocityFourierComponent G j)‖ ^ 2 := by
  let F : H3SpectralVelocityState :=
    fun j : Fin 3 => h3TerminalRawVelocityFourierComponent G j
  let A : Set H3FourierPoint3 :=
    h3TerminalRadialFrequencyBelow Q \
      h3TerminalRadialFrequencyBelow ((n : ℝ) + 1)
  let S : Set H3FourierPoint3 := h3TopTailNaturalHighRadialSet n
  let g : H3FourierPoint3 → ℝ :=
    h3TerminalRawVelocityFourierTotalSquareDensity G 0
  have hSubset : A ⊆ S := by
    intro ξ hξ
    exact hξ.2
  have hIntegrable : Integrable g volume :=
    rawVelocityFourierTotalSquareDensity_integrable G 0
  have hNonneg : 0 ≤ᵐ[volume] g := by
    filter_upwards with ξ
    dsimp only [g]
    unfold h3TerminalRawVelocityFourierTotalSquareDensity
    positivity
  have hMonotone : (∫ ξ in A, g ξ ∂volume) ≤
      ∫ ξ in S, g ξ ∂volume := by
    apply setIntegral_mono_set hIntegrable.integrableOn
    · exact ae_restrict_of_ae (s := S) hNonneg
    · filter_upwards with ξ
      intro hξ
      exact hSubset hξ
  have hZero (j : Fin 3) :
      h3TerminalRawVelocityFourierComponent (0 : H3SpectralVelocityState) j = 0 := by
    change h3SpectralScalarRawFourierL2 (0 : H3SpectralScalarState) = 0
    simp
  have hPoint (ξ : H3FourierPoint3) :
      g ξ = ‖F 0 ξ‖ ^ 2 + ‖F 1 ξ‖ ^ 2 + ‖F 2 ξ‖ ^ 2 := by
    simp [g, F, h3TerminalRawVelocityFourierTotalSquareDensity, hZero]
  have hInt (j : Fin 3) :
      Integrable (fun ξ : H3FourierPoint3 => ‖F j ξ‖ ^ 2)
        (volume.restrict S) :=
    ((MeasureTheory.Lp.memLp (F j)).norm.integrable_sq).mono_measure
      Measure.restrict_le_self
  have hSplit : (∫ ξ in S, g ξ ∂volume) =
      (∫ ξ in S, ‖F 0 ξ‖ ^ 2 ∂volume) +
      (∫ ξ in S, ‖F 1 ξ‖ ^ 2 ∂volume) +
      (∫ ξ in S, ‖F 2 ξ‖ ^ 2 ∂volume) := by
    calc
      (∫ ξ in S, g ξ ∂volume) =
        ∫ ξ in S, (‖F 0 ξ‖ ^ 2 + ‖F 1 ξ‖ ^ 2) +
          ‖F 2 ξ‖ ^ 2 ∂volume := by
            apply integral_congr_ae
            filter_upwards with ξ
            exact hPoint ξ
      _ = _ := by
        have h01 :
            (∫ ξ in S, ‖F 0 ξ‖ ^ 2 + ‖F 1 ξ‖ ^ 2 ∂volume) =
              (∫ ξ in S, ‖F 0 ξ‖ ^ 2 ∂volume) +
              (∫ ξ in S, ‖F 1 ξ‖ ^ 2 ∂volume) := by
          simpa only [Pi.add_apply] using
            (integral_add (hInt 0) (hInt 1))
        have h012 :
            (∫ ξ in S, (‖F 0 ξ‖ ^ 2 + ‖F 1 ξ‖ ^ 2) +
                ‖F 2 ξ‖ ^ 2 ∂volume) =
              (∫ ξ in S, ‖F 0 ξ‖ ^ 2 + ‖F 1 ξ‖ ^ 2 ∂volume) +
              (∫ ξ in S, ‖F 2 ξ‖ ^ 2 ∂volume) := by
          simpa only [Pi.add_apply] using
            (integral_add ((hInt 0).add (hInt 1)) (hInt 2))
        rw [h012, h01]
  have hId (j : Fin 3) :
      (∫ ξ in S, ‖F j ξ‖ ^ 2 ∂volume) =
      ‖thirdFullSpectralHighRadialApply244 n (F j)‖ ^ 2 := by
    change (∫ ξ in h3TopTailNaturalHighRadialSet n,
        ‖F j ξ‖ ^ 2 ∂volume) = _
    exact (thirdFullSpectralHighRadialApply_norm_sq244 n (F j)).symm
  have hCoord (j : Fin 3) :
      ‖thirdFullSpectralHighRadialApply244 n (F j)‖ ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 n F‖ :=
    h3SpectralFinVector_coordinate_norm_le
      (thirdFullSpectralVelocityHighRadialApply244 n F) j
  have hCoordSq (j : Fin 3) :
      ‖thirdFullSpectralHighRadialApply244 n (F j)‖ ^ 2 ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 n F‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hCoord j)
  have hThree : (∫ ξ in S, g ξ ∂volume) ≤
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 n F‖ ^ 2 := by
    rw [hSplit, hId 0, hId 1, hId 2]
    nlinarith only [hCoordSq 0, hCoordSq 1, hCoordSq 2]
  exact hMonotone.trans (by simpa only [A, F, g, S,
    h3PathActualBandRawKineticMass244] using hThree)

/-- At every positive time the actual raw Fourier vector of the weighted
H³ encoder is exactly the Plancherel image of the physical velocity. -/
theorem thirdFullPhysical_actualRawFourierVector_eq_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    (fun j : Fin 3 => h3TerminalRawVelocityFourierComponent
      (h3AuditActualSpectralVelocityTotal hH3 t) j) =
      RawPhysicalFourier244 (h3AuditInitialOldPhysicalHilbertTotal hH3 t) := by
  funext j
  change h3SpectralScalarRawFourierL2
      (h3AuditActualSpectralVelocityTotal hH3 t j) =
    h3ScalarFourierL2
      (h3AuditActualPhysicalZeroJetL2Total hH3 j t)
  exact h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2 hH3 j t ht

/-- The conditional vanishing premise of the critical-eighth gate is now a
THEOREM of genuine physical terminal L² convergence, independently of any
terminal H³ trace. The outer radius Q may move arbitrarily. -/
theorem thirdFullPhysical_movingBandRawMass_tendsto_zero_of_L2Trace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ) (n : ℕ → ℕ) (Q : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[<] T))
    (ht : ∀ᶠ k : ℕ in atTop, τ k ∈ Set.Ioo (0 : ℝ) T)
    (hn : Tendsto n atTop atTop)
    (hTrace : ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    Tendsto (fun k : ℕ =>
      h3PathActualBandRawKineticMass244 ((n k : ℝ) + 1) (Q k)
        (h3AuditActualSpectralVelocityTotal hH3 (τ k)))
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨L, hL⟩ := hTrace
  let X : ℕ → H3PhysicalRealFinVectorL2Hilbert :=
    fun k => h3AuditInitialOldPhysicalHilbertTotal hH3 (τ k)
  let V : ℕ → H3SpectralVelocityState :=
    fun k => RawPhysicalFourier244 (X k)
  have hX : Tendsto X atTop (𝓝 L) := hL.comp hτ
  have hTail : Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (V k)‖)
      atTop (𝓝 (0 : ℝ)) := by
    exact thirdFullPhysical_movingRawHighpass_norm_tendsto_zero244 X L n hX hn
  have hPow : Tendsto (fun k : ℕ =>
      ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (V k)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hTail.pow 2
  have hUpperLimit : Tendsto (fun k : ℕ =>
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (V k)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hPow.const_mul 3
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hSmall : ∀ᶠ k : ℕ in atTop,
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 (n k) (V k)‖ ^ 2 < ε :=
    hUpperLimit.eventually (eventually_lt_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.and hSmall)
  refine ⟨N, ?_⟩
  intro k hk
  obtain ⟨hkTime, hkSmall⟩ := hN k hk
  have hRaw := thirdFullPhysical_actualRawFourierVector_eq_physical244
    hH3 (τ k) hkTime
  have hMass := thirdFull_bandRawKineticMass_le_three_highpass244
    (n k) (Q k) (h3AuditActualSpectralVelocityTotal hH3 (τ k))
  rw [hRaw] at hMass
  have hNonneg := thirdFull_bandRawKineticMass_nonneg244
    ((n k : ℝ) + 1) (Q k)
    (h3AuditActualSpectralVelocityTotal hH3 (τ k))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg]
  exact lt_of_le_of_lt (by simpa only [V, X] using hMass) hkSmall

end
end PrimeTensor.FirstMonomialTriad
