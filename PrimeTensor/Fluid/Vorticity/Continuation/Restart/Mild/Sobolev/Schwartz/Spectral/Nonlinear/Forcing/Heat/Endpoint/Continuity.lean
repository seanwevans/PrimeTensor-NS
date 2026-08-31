import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.Generator
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.C3.Bridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Zero-lag continuity of the physical nonlinear heat forcing

The unheated finite Leray--divergence forcing already has a genuine continuous
inverse-Fourier representative.  At every positive lag, the same raw forcing
multiplied by the heat symbol has a spatially `C³` inverse-Fourier
representative.

This file joins those two endpoint objects.  For fixed spectral states `U,V`,
the positive-lag physical forcing converges pointwise to the unheated physical
forcing as the heat lag tends to zero from the right.

The proof is direct dominated convergence.  On nonnegative heat times,

    ‖exp (-ν τ q(ξ))‖ ≤ 1,

so the unheated Fourier `L¹` forcing is an integrable majorant.  Pointwise in
frequency, the heat symbol tends to one by the already-compiled time
continuity of the scalar heat multiplier.

This is the zero-lag endpoint needed for the first-order restarted Duhamel
tail: the retarded kernel may now be continuously filled at its upper time
endpoint by the instantaneous Leray nonlinear forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingHeatEndpointContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/- Keep real differentiation/continuity of complex-valued heat symbols on the
same restriction-of-scalars instance used by the generator layer. -/
attribute [local instance 1100] NormedSpace.complexToReal

/-- At zero heat lag the positive-lag raw amplitude is exactly the unheated
raw nonlinear forcing. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
    (ν : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatRepresentative ν 0 U V i
      =
    h3RawFinLerayOuterProductDivergence U V i := by
  funext ξ
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  unfold h3HeatFourierSymbol
  simp

/-- The classical heat reconstruction at zero lag is definitionally the same
physical endpoint as the unheated continuous reconstruction. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero
    (ν : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceHeatC3Representative ν 0 U V i
      =
    h3RawFinLerayOuterProductDivergenceC0Representative U V i := by
  unfold
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
    h3RawFinLerayOuterProductDivergenceC0Representative
  rw [h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero]

/-- Fixed-frequency heat multiplication tends to the unheated raw forcing as
the lag tends to zero from the right. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero_right
    {ν : ℝ}
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    Tendsto
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝 (h3RawFinLerayOuterProductDivergence U V i ξ)) := by
  have hSymbolFull :
      Tendsto
        (fun τ : ℝ => h3HeatFourierSymbol ν τ ξ)
        (𝓝 0)
        (𝓝 (h3HeatFourierSymbol ν 0 ξ)) :=
    (contDiff_one_h3HeatFourierSymbol_time ν ξ).continuous.continuousAt

  have hSymbolZero :
      h3HeatFourierSymbol ν 0 ξ = 1 := by
    unfold h3HeatFourierSymbol
    simp

  rw [hSymbolZero] at hSymbolFull

  have hSymbol :
      Tendsto
        (fun τ : ℝ => h3HeatFourierSymbol ν τ ξ)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 (1 : ℂ)) :=
    hSymbolFull.mono_left inf_le_left

  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative

  simpa only [one_mul] using
    hSymbol.mul_const
      (h3RawFinLerayOuterProductDivergence U V i ξ)

/-- Pointwise physical convergence of the positive-lag nonlinear heat forcing
to the unheated continuous forcing at zero lag. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero_right
    {ν : ℝ}
    (hν : 0 < ν)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i x)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          U V i x)) := by
  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun τ ξ =>
      phase ξ *
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ

  let f : H3FourierPoint3 → ℂ :=
    fun ξ =>
      phase ξ *
        h3RawFinLerayOuterProductDivergence U V i ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖

  have hPhaseContinuous : Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hF_meas :
      ∀ᶠ τ : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        AEStronglyMeasurable
          (F τ)
          (volume : Measure H3FourierPoint3) := by
    exact Filter.Eventually.of_forall (fun τ => by
      dsimp only [F]
      exact
        hPhaseContinuous.aestronglyMeasurable.mul
          (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
            ν τ U V i))

  have h_bound :
      ∀ᶠ τ : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F τ ξ‖ ≤ bound ξ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    filter_upwards with ξ
    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ ξ

    have hPhaseNorm : ‖phase ξ‖ = 1 := by
      dsimp only [phase]
      simp only [
        Complex.norm_exp,
        Complex.mul_re,
        Complex.ofReal_re,
        Complex.ofReal_im,
        Complex.I_re,
        Complex.I_im,
        mul_zero,
        zero_mul,
        sub_self,
        Real.exp_zero
      ]

    dsimp only [F, bound]
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    rw [norm_mul, hPhaseNorm, one_mul, norm_mul]
    exact
      mul_le_of_le_one_left
        (norm_nonneg _)
        hHeat

  have bound_integrable :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    dsimp only [bound]
    exact
      (h3RawFinLerayOuterProductDivergence_integrable U V i).norm

  have h_lim :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Tendsto
          (fun τ : ℝ => F τ ξ)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 (f ξ)) := by
    filter_upwards with ξ
    have hRaw :=
      tendsto_h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero_right
        (ν := ν) U V i ξ
    dsimp only [F, f]
    exact tendsto_const_nhds.mul hRaw

  have hMain :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure H3FourierPoint3))
      (l := (𝓝[Set.Ici (0 : ℝ)] 0))
      (F := F)
      (f := f)
      bound
      hF_meas
      h_bound
      bound_integrable
      h_lim

  have hPathEq :
      (fun τ : ℝ =>
        ∫ ξ : H3FourierPoint3, F τ ξ)
        =
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i x) := by
    funext τ
    dsimp only [F, phase]
    unfold h3RawFinLerayOuterProductDivergenceHeatC3Representative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hLimitEq :
      (∫ ξ : H3FourierPoint3, f ξ)
        =
      h3RawFinLerayOuterProductDivergenceC0Representative
        U V i x := by
    dsimp only [f, phase]
    unfold h3RawFinLerayOuterProductDivergenceC0Representative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  rw [hPathEq, hLimitEq] at hMain
  exact hMain

/-- The same zero-lag endpoint convergence after transport to the project's
`Point3` carrier. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatC3RepresentativeOnPoint3_zero_right
    {ν : ℝ}
    (hν : 0 < ν)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : Point3) :
    Tendsto
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3RepresentativeOnPoint3
          ν τ U V i x)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U V i x)) := by
  exact
    tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero_right
      hν U V i
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)

end

end Euclidean
end Bridge
end PrimeTensor
