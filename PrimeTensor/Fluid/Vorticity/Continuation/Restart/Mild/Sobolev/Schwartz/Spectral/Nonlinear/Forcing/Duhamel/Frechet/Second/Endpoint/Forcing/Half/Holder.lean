import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Integrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Bilinear
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1.Bound

/-!
# Transfer a path half-Hölder modulus to the nonlinear forcing

The second-Duhamel endpoint cancellation theorem isolates one remaining input:

    ‖N(W(s),W(s)) - N(W(t),W(t))‖_{L¹_ξ}
      ≤ K sqrt (t - s).

This file shows that no new nonlinear estimate is needed for that condition.
The raw finite Leray forcing is bilinear and already satisfies

    ‖N(U,V)‖_{L¹_ξ} ≤ C_force ‖U‖ ‖V‖.

Hence, on a path bounded by `M`,

    N(Ws,Ws) - N(Wt,Wt)
      = N(Ws-Wt, Ws) + N(Wt, Ws-Wt),

so a `1/2`-Hölder modulus

    ‖W(s) - W(t)‖ ≤ L sqrt (t-s)

immediately gives

    ‖N(Ws,Ws) - N(Wt,Wt)‖_{L¹_ξ}
      ≤ 2 C_force M L sqrt (t-s).

For the Banach-selected restart path, `M = 2A`, so the endpoint forcing
constant is exactly `4 C_force A L`.

After this module the nonlinear side of the second-derivative endpoint problem
is closed.  The remaining target is purely a time-regularity statement for the
selected mild path itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingSecondEndpointHalfHolder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint `1/2`-Hölder modulus for a spectral H³ path. -/
def H3SpectralEndpointHalfHolder
    (W : ℝ → H3SpectralFinVectorState)
    (t L : ℝ) : Prop :=
  ∀ s ∈ Set.Ioo (0 : ℝ) t,
    ‖W s - W t‖ ≤ L * Real.sqrt (t - s)

/-- Exact diagonal bilinear decomposition of the raw finite Leray forcing. -/
theorem h3RawFinLerayOuterProductDivergence_diagonal_sub
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergence U U i ξ -
        h3RawFinLerayOuterProductDivergence V V i ξ
      =
    h3RawFinLerayOuterProductDivergence (U - V) U i ξ +
      h3RawFinLerayOuterProductDivergence V (U - V) i ξ := by
  rw [
    h3RawFinLerayOuterProductDivergence_sub_left,
    h3RawFinLerayOuterProductDivergence_sub_right
  ]
  ring

/-- Quantitative `L¹` difference estimate for the diagonal nonlinear forcing. -/
theorem h3RawFinLerayOuterProductDivergence_diagonal_differenceL1Mass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergence U U i ξ -
          h3RawFinLerayOuterProductDivergence V V i ξ‖)
      ≤
    h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
      h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖ := by
  let A : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence (U - V) U i ξ
  let B : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence V (U - V) i ξ

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergence_integrable U U i).sub
      (h3RawFinLerayOuterProductDivergence_integrable V V i)

  have hAInt :
      Integrable A (volume : Measure H3FourierPoint3) := by
    dsimp only [A]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (U - V) U i

  have hBInt :
      Integrable B (volume : Measure H3FourierPoint3) := by
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        V (U - V) i

  have hNormBound :
      (∫ ξ : H3FourierPoint3,
          ‖h3RawFinLerayOuterProductDivergence U U i ξ -
            h3RawFinLerayOuterProductDivergence V V i ξ‖)
        ≤
      (∫ ξ : H3FourierPoint3, ‖A ξ‖) +
        ∫ ξ : H3FourierPoint3, ‖B ξ‖ := by
    rw [← integral_add hAInt.norm hBInt.norm]
    refine integral_mono_ae hTargetInt.norm (hAInt.norm.add hBInt.norm) ?_
    filter_upwards with ξ
    rw [h3RawFinLerayOuterProductDivergence_diagonal_sub]
    dsimp only [A, B]
    exact norm_add_le _ _

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergence U U i ξ -
          h3RawFinLerayOuterProductDivergence V V i ξ‖)
        ≤
      (∫ ξ : H3FourierPoint3, ‖A ξ‖) +
        ∫ ξ : H3FourierPoint3, ‖B ξ‖ :=
      hNormBound
    _ =
      h3RawFinLerayOuterProductDivergenceL1Mass (U - V) U i +
        h3RawFinLerayOuterProductDivergenceL1Mass V (U - V) i := by
      rfl
    _ ≤
      h3NonlinearForcingL1Coefficient * ‖U - V‖ * ‖U‖ +
        h3NonlinearForcingL1Coefficient * ‖V‖ * ‖U - V‖ := by
      exact add_le_add
        (h3RawFinLerayOuterProductDivergenceL1Mass_le
          (U - V) U i)
        (h3RawFinLerayOuterProductDivergenceL1Mass_le
          V (U - V) i)

/-- A bounded endpoint-half-Hölder path automatically gives the exact
nonlinear forcing endpoint condition consumed by the second-derivative
cancellation theorem. -/
theorem h3NonlinearForcingEndpointHalfHolderL1_of_path
    {W : ℝ → H3SpectralFinVectorState}
    {t M L : ℝ}
    (hM : 0 ≤ M)
    (hL : 0 ≤ L)
    (hWs : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖W s‖ ≤ M)
    (hWt : ‖W t‖ ≤ M)
    (hHolder : H3SpectralEndpointHalfHolder W t L)
    (i : Fin 3) :
    H3NonlinearForcingEndpointHalfHolderL1
      W W t
      (2 * h3NonlinearForcingL1Coefficient * M * L)
      i := by
  intro s hs

  have hDiff :
      ‖W s - W t‖ ≤ L * Real.sqrt (t - s) :=
    hHolder s hs

  have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg

  have hSqrt : 0 ≤ Real.sqrt (t - s) :=
    Real.sqrt_nonneg _

  have hLs : 0 ≤ L * Real.sqrt (t - s) :=
    mul_nonneg hL hSqrt

  unfold
    h3RawFinLerayOuterProductDivergenceEndpointDifferenceL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
          h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        ≤
      h3NonlinearForcingL1Coefficient * ‖W s - W t‖ * ‖W s‖ +
        h3NonlinearForcingL1Coefficient * ‖W t‖ * ‖W s - W t‖ :=
      h3RawFinLerayOuterProductDivergence_diagonal_differenceL1Mass_le
        (W s) (W t) i
    _ ≤
      h3NonlinearForcingL1Coefficient *
            (L * Real.sqrt (t - s)) * M +
        h3NonlinearForcingL1Coefficient * M *
            (L * Real.sqrt (t - s)) := by
      apply add_le_add
      · calc
          h3NonlinearForcingL1Coefficient * ‖W s - W t‖ * ‖W s‖
              ≤
            h3NonlinearForcingL1Coefficient *
                (L * Real.sqrt (t - s)) * ‖W s‖ := by
              exact
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hDiff hC)
                  (norm_nonneg _)
          _ ≤
            h3NonlinearForcingL1Coefficient *
                (L * Real.sqrt (t - s)) * M := by
              exact
                mul_le_mul_of_nonneg_left
                  (hWs s hs)
                  (mul_nonneg hC hLs)
      · calc
          h3NonlinearForcingL1Coefficient * ‖W t‖ * ‖W s - W t‖
              ≤
            h3NonlinearForcingL1Coefficient * M * ‖W s - W t‖ := by
              exact
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hWt hC)
                  (norm_nonneg _)
          _ ≤
            h3NonlinearForcingL1Coefficient * M *
                (L * Real.sqrt (t - s)) := by
              exact
                mul_le_mul_of_nonneg_left
                  hDiff
                  (mul_nonneg hC hM)
    _ =
      (2 * h3NonlinearForcingL1Coefficient * M * L) *
        Real.sqrt (t - s) := by
      ring

/-- Specialization to the actual Banach-selected restart path.

Once a half-Hölder time modulus `L` is established for the selected physical
extension, the nonlinear endpoint condition follows with the explicit
constant `4 * C_force * A * L`. -/
theorem h3NonlinearForcingEndpointHalfHolderL1_selectedRestart_of_path
    {ν A t L : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (_ht : 0 ≤ t)
    (_htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hL : 0 ≤ L)
    (hHolder :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      H3SpectralEndpointHalfHolder W t L)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    H3NonlinearForcingEndpointHalfHolderL1
      W W t
      (4 * h3NonlinearForcingL1Coefficient * A * L)
      i := by
  dsimp only at hHolder ⊢

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hWs :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖W s‖ ≤ 2 * A := by
    intro s _hs
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have hWt :
      ‖W t‖ ≤ 2 * A := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ t

  have h :=
    h3NonlinearForcingEndpointHalfHolderL1_of_path
      h2A hL hWs hWt hHolder i

  have hCoeff :
      2 * h3NonlinearForcingL1Coefficient * (2 * A) * L
        =
      4 * h3NonlinearForcingL1Coefficient * A * L := by
    ring

  change
    H3NonlinearForcingEndpointHalfHolderL1
      W W t
      (4 * h3NonlinearForcingL1Coefficient * A * L)
      i
  rw [← hCoeff]
  exact h

end

end Euclidean
end Bridge
end PrimeTensor
