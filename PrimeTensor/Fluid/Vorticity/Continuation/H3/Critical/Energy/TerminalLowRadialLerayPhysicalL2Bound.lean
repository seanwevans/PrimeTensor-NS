import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialLerayKineticBound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourcePhysicalDifference244
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

/-!
# Kinetic bound for the actual low-band Leray Fourier and physical L² source

The real radial frequency band Sρ = {ξ : (2π)‖ξ‖ < ρ} has finite Fourier
volume, including ρ = 0. At every actual strictly positive time after the
kinetic anchor b, each genuine Fourier Leray forcing coordinate satisfies

  ∫_{Sρ} ‖Nᵢ(ξ,t)‖² ≤ volume(Sρ) * (18 ρ E₀(b))².

This file constructs the actual Fourier L² sharp-cutoff package, proves the
exact norm-square identity, and decodes it through the project's existing
physical real inverse-Fourier contraction. The same explicit ceiling thus
holds for its squared physical L² norm. There are no artificial timewise
H³ source ceilings, Fourier L¹ assumptions, positive terminal-mass premises,
or finite full H³ dissipation inputs.

The identification of the decoded cutoff with an operator on the physical
source, and uniform time-L¹ of that physical cutoff path, are the NEXT
obligations. The Fourier sharp cutoff here is not assumed to be a smooth
multiplier or to commute with the physical real-part map without proof.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval BigOperators

noncomputable section
set_option maxHeartbeats 1000000

-- The Fourier carrier is `WithLp 2 Point3`; it inherits the volume measure
-- from the project's canonical product-measure instance on `Point3`.
noncomputable local instance axisFintypeH3LowRadialLerayPhysicalL2
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3LowRadialLerayPhysicalL2 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every fixed radial Fourier-gradient ball has finite actual volume. -/
theorem h3Critical_lowRadial_fourierBall_finiteVolume
    (ρ : ℝ) :
    (volume : Measure H3FourierPoint3)
      (h3TerminalRadialFrequencyBelow ρ) < ⊤ := by
  have hTwoPi : 0 < (2 * Real.pi) := by positivity
  have hSub : h3TerminalRadialFrequencyBelow ρ ⊆
      Metric.ball (0 : H3FourierPoint3) (ρ / (2 * Real.pi)) := by
    intro ξ hξ
    have hRadial : (2 * Real.pi) * ‖ξ‖ < ρ := by
      change h3FourierGradientMagnitude ξ < ρ at hξ
      exact hξ
    have hNorm : ‖ξ‖ < ρ / (2 * Real.pi) := by
      apply (lt_div_iff₀ hTwoPi).mpr
      simpa only [mul_comm] using hRadial
    simpa only [Metric.mem_ball, dist_zero_right] using hNorm
  exact (measure_mono hSub).trans_lt measure_ball_lt_top

/-- Finite Fourier volume and a pointwise ceiling yield a quantitative
low-band L² square-mass bound for the genuine Leray source. -/
theorem h3Critical_lowRadial_leraySquareMass_le_of_pointwise
    (U : H3SpectralVelocityState)
    (ρ C : ℝ) (i : Fin 3)
    (hBound : ∀ ξ : H3FourierPoint3,
      ξ ∈ h3TerminalRadialFrequencyBelow ρ →
        ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ ≤ C) :
    (∫ ξ in h3TerminalRadialFrequencyBelow ρ,
      ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ ^ 2 ∂volume) ≤
      (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow ρ) * C ^ 2 := by
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  have hFinite : (volume : Measure H3FourierPoint3) S < ⊤ :=
    h3Critical_lowRadial_fourierBall_finiteVolume ρ
  have hInt : IntegrableOn
      (fun ξ : H3FourierPoint3 =>
        ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ ^ 2)
      S volume :=
    ((h3RawFinLerayOuterProductDivergence_memLp2 U U i).integrable_norm_pow
      (by norm_num)).integrableOn
  have hConst : IntegrableOn (fun _ : H3FourierPoint3 => C ^ 2)
      S volume := integrableOn_const hFinite.ne
  calc
    (∫ ξ in S, ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ ^ 2 ∂volume) ≤
        ∫ _ξ in S, C ^ 2 ∂volume := by
      apply setIntegral_mono_on hInt hConst
        (measurableSet_h3TerminalRadialFrequencyBelow ρ)
      intro ξ hξ
      exact pow_le_pow_left₀ (norm_nonneg _) (hBound ξ hξ) 2
    _ = (volume : Measure H3FourierPoint3).real S * C ^ 2 := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]

/-- Kinetic energy at b quantitatively controls the actual L² mass of
one Fourier Leray source coordinate on the entire fixed low-radial ball. -/
theorem h3Critical_actual_lowRadial_lerayFourierSquareMass_le_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (i : Fin 3) :
    (∫ ξ in h3TerminalRadialFrequencyBelow ρ,
      ‖h3RawFinLerayOuterProductDivergence
        (h3AuditActualSpectralVelocityTotal hH3 t)
        (h3AuditActualSpectralVelocityTotal hH3 t) i ξ‖ ^ 2 ∂volume) ≤
      (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow ρ) *
          (18 * (ρ * velocityH3Energy0At u b)) ^ 2 := by
  exact h3Critical_lowRadial_leraySquareMass_le_of_pointwise
    (h3AuditActualSpectralVelocityTotal hH3 t)
    ρ (18 * (ρ * velocityH3Energy0At u b)) i
    (h3Critical_actual_lowRadial_lerayDivergence_le_kineticAnchor
      hH3 hClass b hb ρ hρ t ht i)

/-- The exact low-band Fourier L² state, using the already-proved genuine
nonlinear Leray source and a sharp measurable frequency indicator. -/
noncomputable def h3CriticalLowRadialLerayFourierL2
    (ρ : ℝ) (U : H3SpectralVelocityState) (i : Fin 3) :
    H3FourierComplexL2 :=
  ((h3RawFinLerayOuterProductDivergence_memLp2 U U i).indicator
    (measurableSet_h3TerminalRadialFrequencyBelow ρ)).toLp
      ((h3TerminalRadialFrequencyBelow ρ).indicator
        (h3RawFinLerayOuterProductDivergence U U i))

/-- The low-band L² package represents precisely the sharp-cutoff raw
Fourier Leray forcing, almost everywhere. -/
theorem h3Critical_lowRadialLerayFourierL2_ae
    (ρ : ℝ) (U : H3SpectralVelocityState) (i : Fin 3) :
    (h3CriticalLowRadialLerayFourierL2 ρ U i :
      H3FourierPoint3 → ℂ) =ᵐ[(volume : Measure H3FourierPoint3)]
      (h3TerminalRadialFrequencyBelow ρ).indicator
        (h3RawFinLerayOuterProductDivergence U U i) := by
  -- Name the cutoff function and its MemLp certificate before invoking
  -- coeFn_toLp. Otherwise the elaborator unfolds the full nonlinear
  -- convolution and the nested measure/coercion instances during isDefEq.
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence U U i
  have hf : MemLp (S.indicator f) 2
      (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergence_memLp2 U U i).indicator
      (measurableSet_h3TerminalRadialFrequencyBelow ρ)
  have hRepresentative :
      (hf.toLp (S.indicator f) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)] S.indicator f :=
    hf.coeFn_toLp
  -- Only unfold the small cutoff package; do not unfold the PDE forcing.
  change (hf.toLp (S.indicator f) : H3FourierPoint3 → ℂ)
    =ᵐ[(volume : Measure H3FourierPoint3)] S.indicator f
  exact hRepresentative

/-- Exact Plancherel norm-square identity for the actual low-band source. -/
theorem h3Critical_lowRadialLerayFourierL2_norm_sq
    (ρ : ℝ) (U : H3SpectralVelocityState) (i : Fin 3) :
    ‖h3CriticalLowRadialLerayFourierL2 ρ U i‖ ^ 2 =
      ∫ ξ in h3TerminalRadialFrequencyBelow ρ,
        ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ ^ 2 ∂volume := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  rw [← integral_indicator (measurableSet_h3TerminalRadialFrequencyBelow ρ)]
  apply integral_congr_ae
  filter_upwards [h3Critical_lowRadialLerayFourierL2_ae ρ U i]
    with ξ hξ
  rw [hξ]
  by_cases hS : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS]
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS]
    simp

/-- A genuine real physical L² reconstruction of the sharp-cutoff nonlinear
Fourier Leray forcing, via the existing exact inverse Fourier decoder. -/
noncomputable def h3CriticalLowRadialLerayPhysicalL2
    (ρ : ℝ) (U : H3SpectralVelocityState) (i : Fin 3) :
    H3ScalarL2 :=
  h3Path_physicalRawFourierDecoder244
    (h3CriticalLowRadialLerayFourierL2 ρ U i)

/-- Uniform physical L² square norm of the genuine low-band Leray source,
for every later actual time, bounded solely by the fixed kinetic anchor. -/
theorem h3Critical_actual_lowRadial_lerayPhysicalL2_sq_le_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (i : Fin 3) :
    ‖h3CriticalLowRadialLerayPhysicalL2 ρ
      (h3AuditActualSpectralVelocityTotal hH3 t) i‖ ^ 2 ≤
      (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow ρ) *
          (18 * (ρ * velocityH3Energy0At u b)) ^ 2 := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hDecode :
      ‖h3CriticalLowRadialLerayPhysicalL2 ρ U i‖ ≤
        ‖h3CriticalLowRadialLerayFourierL2 ρ U i‖ :=
    h3Path_physicalRawFourierDecoder_norm_le244 _
  have hSquare :
      ‖h3CriticalLowRadialLerayPhysicalL2 ρ U i‖ ^ 2 ≤
        ‖h3CriticalLowRadialLerayFourierL2 ρ U i‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hDecode 2
  calc
    ‖h3CriticalLowRadialLerayPhysicalL2 ρ U i‖ ^ 2 ≤
        ‖h3CriticalLowRadialLerayFourierL2 ρ U i‖ ^ 2 := hSquare
    _ = ∫ ξ in h3TerminalRadialFrequencyBelow ρ,
          ‖h3RawFinLerayOuterProductDivergence U U i ξ‖ ^ 2 ∂volume :=
      h3Critical_lowRadialLerayFourierL2_norm_sq ρ U i
    _ ≤ (volume : Measure H3FourierPoint3).real
          (h3TerminalRadialFrequencyBelow ρ) *
            (18 * (ρ * velocityH3Energy0At u b)) ^ 2 :=
      h3Critical_actual_lowRadial_lerayFourierSquareMass_le_kineticAnchor
        hH3 hClass b hb ρ hρ t ht i

end
end PrimeTensor.Bridge.Euclidean
