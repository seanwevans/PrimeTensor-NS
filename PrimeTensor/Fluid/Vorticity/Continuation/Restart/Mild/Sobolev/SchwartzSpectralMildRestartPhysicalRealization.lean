import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralMildPhysicalRealization
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayDuhamelTail
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayMildRestartTail

/-!
# Physical Schwartz realization after an interior mild restart

The origin-based selected mild solution now has a physical Schwartz
realization at every positive slice.  The existing restart-tail theory already
identifies

    ∫_a^{a+b} K_{a+b-s}(U(s),V(s)) ds

with an ordinary length-`b` Duhamel term for the translated paths
`q ↦ U(q+a)` and `q ↦ V(q+a)`.

This file combines those two facts.  First, any positive-length restart tail
of continuous globally bounded spectral paths decodes into the same physical
realization set used by a fresh length-`b` Duhamel problem.  Second, the
Banach-selected physical mild solution can therefore be re-anchored at every
interior time `a`:

    decode W(a+b) = H_b (decode W(a)) + realized restart remainder.

Thus the physical realization result is stable under the actual restart
operation rather than only at the original time zero.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- A positive-length Duhamel tail of continuous globally bounded paths has
exactly the same Schwartz physical realization as an origin-based Duhamel term
of that tail length. -/
theorem h3SpectralFinHeatLerayDuhamel_tail_decodeComplexL2_mem_physicalRealization_of_continuous
    {ν a b MU MV : ℝ}
    (hν : 0 < ν)
    (hb : 0 < b)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    h3SpectralFinVectorDecodeComplexL2
        (∫ s in a..(a + b),
          h3SpectralFinHeatLerayDuhamelIntegrand
            ν (a + b) hν U V s)
      ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
          ν b hν := by
  let Ua : ℝ → H3SpectralFinVectorState :=
    fun q => U (q + a)
  let Va : ℝ → H3SpectralFinVectorState :=
    fun q => V (q + a)

  have hUaCont : Continuous Ua := by
    dsimp [Ua]
    exact hUcont.comp (continuous_id.add continuous_const)

  have hVaCont : Continuous Va := by
    dsimp [Va]
    exact hVcont.comp (continuous_id.add continuous_const)

  have hUa : ∀ q : ℝ, ‖Ua q‖ ≤ MU := by
    intro q
    exact hU (q + a)

  have hVa : ∀ q : ℝ, ‖Va q‖ ≤ MV := by
    intro q
    exact hV (q + a)

  rw [h3SpectralFinHeatLerayDuhamel_tail_eq_shifted hν U V]
  exact
    h3SpectralFinHeatLerayDuhamel_decodeComplexL2_mem_physicalRealization_of_continuous
      hν hb hMU hMV Ua Va hUaCont hVaCont hUa hVa

/-- Every positive interior restart of the Banach-selected mild solution has
an exact physical decomposition into heat evolution from the restart state
plus a genuinely realized Schwartz heat--Leray tail remainder. -/
theorem h3SpectralFinHeatLerayPhysicalMildSolution_restart_decodeComplexL2_exists_realized_remainder
    {ν τ A a b : ℝ}
    (hν : 0 < ν)
    (hτ : 0 ≤ τ)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hsmall :
      8 * h3HeatLerayDuhamelPathCoefficient ν * A * Real.sqrt τ ≤ 1)
    (ha : 0 ≤ a)
    (hb : 0 < b)
    (hab : a + b ≤ τ) :
    ∃ R : H3ComplexPhysicalFinVectorL2,
      R ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
        ν b hν ∧
      h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
            hν hτ U₀ hA hU₀ hsmall (a + b))
        =
      h3ComplexPhysicalVelocityHeatApplyNN
          ν hν.le (NNReal.mk b hb.le)
          (h3SpectralFinHeatLerayMildSolutionPhysicalExtension
            hν hτ U₀ hA hU₀ hsmall a)
        + R := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension
      hν hτ U₀ hA hU₀ hsmall

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν hτ U₀ hA hU₀ hsmall
  have hWcont : Continuous W := by
    simpa only [W] using hWb.1
  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [W] using hWb.2 s

  have htwoA : 0 ≤ 2 * A :=
    mul_nonneg (by norm_num) hA.le
  have hab0 : 0 ≤ a + b :=
    add_nonneg ha hb.le
  have haτ : a ≤ τ := by
    exact le_trans (le_add_of_nonneg_right hb.le) hab

  let qa : Set.Icc (0 : ℝ) τ :=
    ⟨a, ha, haτ⟩
  let qab : Set.Icc (0 : ℝ) τ :=
    ⟨a + b, hab0, hab⟩

  have hMildA0 :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν hτ U₀ hA hU₀ hsmall qa
  have hqaNN :
      h3PhysicalTimePointNN qa = NNReal.mk a ha := by
    rfl
  rw [hqaNN] at hMildA0
  have hMildA :
      h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk a ha) U₀
        +
      h3SpectralFinHeatLerayDuhamel
          ν a hν W W
        =
      W a := by
    simpa only [W, qa,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply] using hMildA0

  have hMildAB0 :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν hτ U₀ hA hU₀ hsmall qab
  have hqabNN :
      h3PhysicalTimePointNN qab = NNReal.mk (a + b) hab0 := by
    rfl
  rw [hqabNN] at hMildAB0
  have hsumNN :
      NNReal.mk (a + b) hab0
        = NNReal.mk a ha + NNReal.mk b hb.le := by
    apply Subtype.ext
    simp
  rw [hsumNN] at hMildAB0
  have hMildAB :
      h3SpectralVelocityHeatApplyNN
          ν hν.le
          (NNReal.mk a ha + NNReal.mk b hb.le)
          U₀
        +
      h3SpectralFinHeatLerayDuhamel
          ν (a + b) hν W W
        =
      W (a + b) := by
    simpa only [W, qab,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply] using hMildAB0

  have hIntA :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν a hν W W)
        volume 0 a := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν ha htwoA htwoA W W hWcont hWcont
        (fun s _ => hWbound s)
        (fun s _ => hWbound s)

  have hIntAB :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν W W)
        volume 0 (a + b) := by
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν hab0 htwoA htwoA W W hWcont hWcont
        (fun s _ => hWbound s)
        (fun s _ => hWbound s)

  have hRestart :=
    h3SpectralFinHeatLerayMild_restart_tail
      hν ha hb.le U₀ W
      hMildA hMildAB hIntAB hIntA

  let R : H3ComplexPhysicalFinVectorL2 :=
    h3SpectralFinVectorDecodeComplexL2
      (∫ s in a..(a + b),
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν W W s)

  have hR :
      R ∈ H3SchwartzHeatLerayDuhamelPhysicalRealization
        ν b hν := by
    dsimp [R]
    exact
      h3SpectralFinHeatLerayDuhamel_tail_decodeComplexL2_mem_physicalRealization_of_continuous
        hν hb htwoA htwoA W W
        hWcont hWcont hWbound hWbound

  refine ⟨R, hR, ?_⟩

  have hDecoded :=
    congrArg h3SpectralFinVectorDecodeComplexL2 hRestart
  rw [h3SpectralFinVectorDecodeComplexL2_add] at hDecoded
  rw [h3SpectralFinVectorDecodeComplexL2_velocityHeatApplyNN] at hDecoded
  dsimp [R, W]
  exact hDecoded.symm

end

end Euclidean
end Bridge
end PrimeTensor
