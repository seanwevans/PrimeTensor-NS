import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRegularizedRadialStrongH3Convergence
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSpectralRealPhysicalDensity244
import Mathlib.Tactic

/-!
# Strong radial regularization along a moving solenoidal Hermitian H³ approximation

The two earlier density theorems produce (1) compact-Hermitian Schwartz
inputs whose bounded Leray images converge to any real solenoidal weighted H³
state, and (2) strong convergence of the origin-regularized radial multiplier
on every fixed weighted H³ state.  A fixed-state convergence theorem alone
DOES NOT justify applying the n-th multiplier to an independently moving
input G_n.  This file supplies the needed uniform contraction and then proves
that precise moving-diagonal statement.

The multiplier is real and even, so it preserves weighted Hermitian reality;
it is common to all three coordinates, so it preserves Fourier divergence.
Thus the moving diagonal is real-decodable and divergence-free at every step.

The resulting objects are still weighted L² spectral states, not yet actual
physical Schwartz velocities.  The remaining step is to identify their a.e.
representatives with the smooth origin-regularized inverse Fourier fields,
after *deweighting* the compact input and matching axis/Fin 3 coordinates.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean
open scoped BigOperators ENNReal ComplexConjugate SchwartzMap

noncomputable section
set_option maxHeartbeats 1600000

private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeRegularizedDiagonal244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Radial recovery is additive in its weighted Fourier input. This is an
identity of genuine `L²` classes, not just of formal representatives. -/
theorem h3FullThirdRadialRecoveryL2_sub244
    (n : ℕ) (F G : H3SpectralScalarState) :
    h3FullThirdRadialRecoveryL2244 n (F - G) =
      h3FullThirdRadialRecoveryL2244 n F -
        h3FullThirdRadialRecoveryL2244 n G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    MeasureTheory.MemLp.coeFn_toLp
      (h3FullThirdRadialRecoveryRaw_memLp244 n (F - G)),
    MeasureTheory.MemLp.coeFn_toLp
      (h3FullThirdRadialRecoveryRaw_memLp244 n F),
    MeasureTheory.MemLp.coeFn_toLp
      (h3FullThirdRadialRecoveryRaw_memLp244 n G),
    MeasureTheory.Lp.coeFn_sub F G,
    MeasureTheory.Lp.coeFn_sub
      (h3FullThirdRadialRecoveryL2244 n F)
      (h3FullThirdRadialRecoveryL2244 n G)
  ] with ξ hFG hF hG hSub hOutput
  have hFG' :
      (h3FullThirdRadialRecoveryL2244 n (F - G) : V3 → ℂ) ξ =
        h3FullThirdRadialRecoveryRaw244 n (F - G) ξ := hFG
  have hF' :
      (h3FullThirdRadialRecoveryL2244 n F : V3 → ℂ) ξ =
        h3FullThirdRadialRecoveryRaw244 n F ξ := hF
  have hG' :
      (h3FullThirdRadialRecoveryL2244 n G : V3 → ℂ) ξ =
        h3FullThirdRadialRecoveryRaw244 n G ξ := hG
  rw [hFG', hOutput]
  simp only [Pi.sub_apply]
  rw [hF', hG']
  simp only [h3FullThirdRadialRecoveryRaw244]
  rw [hSub]
  simp only [Pi.sub_apply]
  ring

/-- Uniform `L²` contraction of the nonsingular radial multiplier. -/
theorem norm_h3FullThirdRadialRecoveryL2_le244
    (n : ℕ) (F : H3SpectralScalarState) :
    ‖h3FullThirdRadialRecoveryL2244 n F‖ ≤ ‖F‖ := by
  have hBound :
      ‖h3FullThirdRadialRecoveryL2244 n F‖ ≤ 1 * ‖F‖ := by
    apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [
      MeasureTheory.MemLp.coeFn_toLp
        (h3FullThirdRadialRecoveryRaw_memLp244 n F)
    ] with ξ hRep
    have hRep' :
        (h3FullThirdRadialRecoveryL2244 n F : V3 → ℂ) ξ =
          h3FullThirdRadialRecoveryRaw244 n F ξ := hRep
    rw [hRep']
    have h0 := (h3FullThirdRadialRecoveryFactor_bounds244 n ξ).1
    have h1 := (h3FullThirdRadialRecoveryFactor_bounds244 n ξ).2
    change ‖(h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) * F ξ‖ ≤
      1 * ‖F ξ‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg (F ξ))
  simpa only [one_mul] using hBound

/-- A uniform Lipschitz estimate independent of the regularization scale. -/
theorem norm_h3FullThirdRadialRecoveryL2_sub_le244
    (n : ℕ) (F G : H3SpectralScalarState) :
    ‖h3FullThirdRadialRecoveryL2244 n F -
      h3FullThirdRadialRecoveryL2244 n G‖ ≤ ‖F - G‖ := by
  rw [← h3FullThirdRadialRecoveryL2_sub244]
  exact norm_h3FullThirdRadialRecoveryL2_le244 n (F - G)

/-- Uniform contraction in the actual finite three-component H³ norm. -/
theorem norm_h3FullThirdRadialRecoveryVelocity_le244
    (n : ℕ) (U : H3SpectralVelocityState) :
    ‖h3FullThirdRadialRecoveryVelocity244 n U‖ ≤ ‖U‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg U)).2
  intro j
  calc
    ‖h3FullThirdRadialRecoveryVelocity244 n U j‖ ≤ ‖U j‖ :=
      norm_h3FullThirdRadialRecoveryL2_le244 n (U j)
    _ ≤ ‖U‖ := h3SpectralFinVector_coordinate_norm_le U j

/-- The radial operator commutes with subtraction on the three-component
weighted state, which is the basis of its uniform error bound. -/
theorem h3FullThirdRadialRecoveryVelocity_sub244
    (n : ℕ) (U V : H3SpectralVelocityState) :
    h3FullThirdRadialRecoveryVelocity244 n (U - V) =
      h3FullThirdRadialRecoveryVelocity244 n U -
        h3FullThirdRadialRecoveryVelocity244 n V := by
  funext j
  change
    h3FullThirdRadialRecoveryL2244 n (U j - V j) =
      h3FullThirdRadialRecoveryL2244 n (U j) -
        h3FullThirdRadialRecoveryL2244 n (V j)
  exact h3FullThirdRadialRecoveryL2_sub244 n (U j) (V j)

/-- Uniform scale-independent contraction for differences. -/
theorem norm_h3FullThirdRadialRecoveryVelocity_sub_le244
    (n : ℕ) (U V : H3SpectralVelocityState) :
    ‖h3FullThirdRadialRecoveryVelocity244 n U -
      h3FullThirdRadialRecoveryVelocity244 n V‖ ≤ ‖U - V‖ := by
  rw [← h3FullThirdRadialRecoveryVelocity_sub244]
  exact norm_h3FullThirdRadialRecoveryVelocity_le244 n (U - V)

/-- The exact diagonal approximation estimate, separating the input error
from the regularization error on a FIXED target. -/
theorem norm_h3FullThirdRadialRecoveryVelocity_moving_error_le244
    (n : ℕ) (U V : H3SpectralVelocityState) :
    ‖h3FullThirdRadialRecoveryVelocity244 n V - U‖ ≤
      ‖V - U‖ + ‖h3FullThirdRadialRecoveryVelocity244 n U - U‖ := by
  calc
    ‖h3FullThirdRadialRecoveryVelocity244 n V - U‖ =
        ‖(h3FullThirdRadialRecoveryVelocity244 n V -
           h3FullThirdRadialRecoveryVelocity244 n U) +
          (h3FullThirdRadialRecoveryVelocity244 n U - U)‖ := by
          congr 1
          abel
    _ ≤ ‖h3FullThirdRadialRecoveryVelocity244 n V -
          h3FullThirdRadialRecoveryVelocity244 n U‖ +
        ‖h3FullThirdRadialRecoveryVelocity244 n U - U‖ := norm_add_le _ _
    _ ≤ ‖V - U‖ +
        ‖h3FullThirdRadialRecoveryVelocity244 n U - U‖ := by
      -- Fix both arguments before applying the ordered-addition lemma.
      -- An inferred trailing argument here can force expensive reduction
      -- of the full bundled Fourier multiplier during `isDefEq`.
      have hContract :
          ‖h3FullThirdRadialRecoveryVelocity244 n V -
            h3FullThirdRadialRecoveryVelocity244 n U‖ ≤ ‖V - U‖ :=
        norm_h3FullThirdRadialRecoveryVelocity_sub_le244 n V U
      exact add_le_add_left hContract
        (‖h3FullThirdRadialRecoveryVelocity244 n U - U‖)

/-- If the input itself converges, its simultaneously regularized image
converges to the SAME target. This is not implied by fixed-input convergence
without the preceding uniform contraction. -/
theorem h3FullThirdRadialRecoveryVelocity_moving_tendsto244
    (U : H3SpectralVelocityState)
    (V : ℕ → H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U)) :
    Tendsto
      (fun n => h3FullThirdRadialRecoveryVelocity244 n (V n))
      atTop (𝓝 U) := by
  have hInput : Tendsto (fun n => ‖V n - U‖) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 hV
  have hTarget : Tendsto
      (fun n => ‖h3FullThirdRadialRecoveryVelocity244 n U - U‖)
      atTop (𝓝 (0 : ℝ)) :=
    (tendsto_iff_norm_sub_tendsto_zero).1
      (h3FullThirdRadialRecoveryVelocity_tendsto244 U)
  have hUpper : Tendsto
      (fun n => ‖V n - U‖ +
        ‖h3FullThirdRadialRecoveryVelocity244 n U - U‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using hInput.add hTarget
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  apply squeeze_zero
  · intro n
    exact norm_nonneg _
  · intro n
    exact norm_h3FullThirdRadialRecoveryVelocity_moving_error_le244 n U (V n)
  · exact hUpper

/-- Consequently any moving regularized strongly convergent sequence is
Cauchy in the actual weighted H³ topology. -/
theorem h3FullThirdRadialRecoveryVelocity_moving_cauchy244
    (U : H3SpectralVelocityState)
    (V : ℕ → H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U)) :
    CauchySeq (fun n => h3FullThirdRadialRecoveryVelocity244 n (V n)) :=
  (h3FullThirdRadialRecoveryVelocity_moving_tendsto244 U V hV).cauchySeq

/-- The multiplier is even; its real Fourier radial value does not
introduce a conjugation or frequency-reflection error. -/
theorem h3FullThirdRadialRecoveryFactor_even244
    (n : ℕ) (ξ : V3) :
    h3FullThirdRadialRecoveryFactor244 n (-ξ) =
      h3FullThirdRadialRecoveryFactor244 n ξ := by
  simp only [h3FullThirdRadialRecoveryFactor244, norm_neg]

/-- The regularized Fourier `L²` state retains Hermitian symmetry. -/
theorem h3FullThirdRadialRecoveryL2_hermitian244
    (n : ℕ) (F : H3SpectralScalarState)
    (hF : H3FourierL2Hermitian F) :
    H3FourierL2Hermitian (h3FullThirdRadialRecoveryL2244 n F) := by
  unfold H3FourierL2Hermitian at hF ⊢
  have hRep := MeasureTheory.MemLp.coeFn_toLp
    (h3FullThirdRadialRecoveryRaw_memLp244 n F)
  have hRepNeg := h3Fourier_ae_neg hRep
  filter_upwards [hRepNeg, hRep, hF] with ξ hNeg hAt hHerm
  -- Make the packaged `L²` representative explicit before rewriting;
  -- Lean otherwise sees `MemLp.toLp ...`, not the named wrapper.
  have hNeg' :
      (h3FullThirdRadialRecoveryL2244 n F : V3 → ℂ) (-ξ) =
        h3FullThirdRadialRecoveryRaw244 n F (-ξ) := hNeg
  have hAt' :
      (h3FullThirdRadialRecoveryL2244 n F : V3 → ℂ) ξ =
        h3FullThirdRadialRecoveryRaw244 n F ξ := hAt
  rw [hNeg', hAt']
  change
    (h3FullThirdRadialRecoveryFactor244 n (-ξ) : ℂ) * F (-ξ) =
      conj ((h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) * F ξ)
  rw [h3FullThirdRadialRecoveryFactor_even244, hHerm, map_mul,
    Complex.conj_ofReal]

/-- Common real-even scalar multiplication preserves weighted-H³
raw-Hermitian reality on all three finite Fourier coordinates. -/
theorem h3FullThirdRadialRecoveryVelocity_rawHermitian244
    (n : ℕ) (U : H3SpectralVelocityState)
    (hU : H3SpectralVelocityRawHermitian U) :
    H3SpectralVelocityRawHermitian
      (h3FullThirdRadialRecoveryVelocity244 n U) := by
  apply h3SpectralVelocityHermitian_to_rawHermitian
  intro j
  exact h3FullThirdRadialRecoveryL2_hermitian244 n (U j)
    ((h3SpectralVelocityRawHermitian_to_hermitian hU) j)

/-- The radial recovery preserves Fourier incompressibility exactly, since
its frequency factor is shared by every velocity coordinate. -/
theorem h3FullThirdRadialRecoveryVelocity_divergenceFree244
    (n : ℕ) (U : H3SpectralVelocityState)
    (hU : H3SpectralFinDivergenceFree U) :
    H3SpectralFinDivergenceFree
      (h3FullThirdRadialRecoveryVelocity244 n U) := by
  have h0 := MeasureTheory.MemLp.coeFn_toLp
    (h3FullThirdRadialRecoveryRaw_memLp244 n (U 0))
  have h1 := MeasureTheory.MemLp.coeFn_toLp
    (h3FullThirdRadialRecoveryRaw_memLp244 n (U 1))
  have h2 := MeasureTheory.MemLp.coeFn_toLp
    (h3FullThirdRadialRecoveryRaw_memLp244 n (U 2))
  have hRep : ∀ᵐ ξ : V3 ∂volume, ∀ j : Fin 3,
      (h3FullThirdRadialRecoveryVelocity244 n U j : V3 → ℂ) ξ =
        (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) * (U j : V3 → ℂ) ξ := by
    filter_upwards [h0, h1, h2] with ξ he0 he1 he2
    intro j
    fin_cases j
    · exact he0
    · exact he1
    · exact he2
  filter_upwards [hU, hRep] with ξ hDiv hAt
  have hExpr :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ *
          (h3FullThirdRadialRecoveryVelocity244 n U j : V3 → ℂ) ξ) =
      (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) *
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * (U j : V3 → ℂ) ξ) := by
    simp only [hAt]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hExpr, hDiv, mul_zero]

/-- Real-decodable weighted-H³ states remain realizable after the radial
regularization. This uses the exact Fourier reality/decoder bridge. -/
theorem h3FullThirdRadialRecoveryVelocity_realizable244
    (n : ℕ) (U : H3SpectralVelocityState)
    (hU : H3SpectralVelocityRawHermitian U) :
    H3SpectralVelocityRealizable
      (h3FullThirdRadialRecoveryVelocity244 n U) :=
  h3SpectralVelocityRawHermitian_realizable
    (h3FullThirdRadialRecoveryVelocity_rawHermitian244 n U hU)

/-- Diagonalize the previously constructed compact Hermitian Schwartz-input
Leray approximants with the smooth origin regularizer. Every resulting
WEIGHTED SPECTRAL state is divergence-free, raw-Hermitian, realizable and
converges strongly/Cauchy to the exact given real solenoidal H³ target.

It is intentionally not claimed that these states have already been
identified with the Fourier transforms of real spatial Schwartz maps. -/
theorem exists_h3FullThirdRegularizedProjectedHermitianDiagonalSequence244
    (U : H3SpectralVelocityState)
    (hUdiv : H3SpectralFinDivergenceFree U)
    (hUreal : H3SpectralVelocityRawHermitian U) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap V3 ℂ,
      (∀ n j, HasCompactSupport (Φ n j : V3 → ℂ)) ∧
      (∀ n, H3SpectralFinDivergenceFree
        (h3FullThirdRadialRecoveryVelocity244 n
          (h3SchwartzSpectralLerayState244 (Φ n)))) ∧
      (∀ n, H3SpectralVelocityRawHermitian
        (h3FullThirdRadialRecoveryVelocity244 n
          (h3SchwartzSpectralLerayState244 (Φ n)))) ∧
      (∀ n, H3SpectralVelocityRealizable
        (h3FullThirdRadialRecoveryVelocity244 n
          (h3SchwartzSpectralLerayState244 (Φ n)))) ∧
      Tendsto (fun n => h3FullThirdRadialRecoveryVelocity244 n
          (h3SchwartzSpectralLerayState244 (Φ n))) atTop (𝓝 U) ∧
      CauchySeq (fun n => h3FullThirdRadialRecoveryVelocity244 n
          (h3SchwartzSpectralLerayState244 (Φ n))) := by
  obtain ⟨Φ, hCompact, hDiv, hRaw, _hRealize, hLimit, _hCauchy⟩ :=
    exists_h3RealSolenoidalProjectedCompactSpectralSequence244
      U hUdiv hUreal
  have hDiagonal :=
    h3FullThirdRadialRecoveryVelocity_moving_tendsto244 U
      (fun n => h3SchwartzSpectralLerayState244 (Φ n)) hLimit
  exact ⟨Φ, hCompact,
    (fun n => h3FullThirdRadialRecoveryVelocity_divergenceFree244
      n _ (hDiv n)),
    (fun n => h3FullThirdRadialRecoveryVelocity_rawHermitian244
      n _ (hRaw n)),
    (fun n => h3FullThirdRadialRecoveryVelocity_realizable244
      n _ (hRaw n)),
    hDiagonal, hDiagonal.cauchySeq⟩


/-- The SAME origin-regularized compact-Hermitian Leray diagonal also
converges after the canonical REAL physical L² decoder. No independent
physical approximation or new inverse Fourier convention is introduced. -/
theorem exists_h3FullThirdRegularizedProjectedHermitianDiagonalDecodedSequence244
    (U : H3SpectralVelocityState)
    (hUdiv : H3SpectralFinDivergenceFree U)
    (hUreal : H3SpectralVelocityRawHermitian U) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap V3 ℂ,
      Tendsto (fun n => h3FullThirdRadialRecoveryVelocity244 n
        (h3SchwartzSpectralLerayState244 (Φ n))) atTop (𝓝 U) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeRealL2
        (h3FullThirdRadialRecoveryVelocity244 n
          (h3SchwartzSpectralLerayState244 (Φ n))))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 U)) ∧
      CauchySeq (fun n => h3SpectralVelocityDecodeRealL2
        (h3FullThirdRadialRecoveryVelocity244 n
          (h3SchwartzSpectralLerayState244 (Φ n)))) := by
  obtain ⟨Φ, _hCompact, _hDiv, _hRaw, _hReal, hLimit, _hCauchy⟩ :=
    exists_h3FullThirdRegularizedProjectedHermitianDiagonalSequence244
      U hUdiv hUreal
  have hDecode :=
    h3SpectralVelocityDecodeRealL2_tendsto_of_weighted244 hLimit
  exact ⟨Φ, hLimit, hDecode, hDecode.cauchySeq⟩

end
end PrimeTensor.FirstMonomialTriad
