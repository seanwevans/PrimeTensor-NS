import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedRadialHighDissipation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopKineticL1EightMomentAlternative244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2
import Mathlib.Tactic

/-!
# Kinetic Bernstein bound for the actual raw quadratic Fourier convolution

On an actual strictly positive H³ Navier–Stokes tail, each raw Fourier
velocity coordinate has an L² norm controlled by the kinetic energy at
an earlier anchor. The genuine convolution is an L²-L² Hilbert pairing;
its pointwise modulus is therefore bounded by that same kinetic anchor.

Inside any fixed Fourier-gradient radius, multiplying this convolution
by one Fourier derivative symbol costs at most the radius. This is the
first concrete nonlinear low-frequency estimate toward the physical Leray
projected momentum-source L¹ bridge. The Leray matrix, finite coordinate
sums, bounded-band L² integration, and inverse Fourier reconstruction
still need to be transported; none of those is claimed here.

No assumption about terminal kinetic mass being positive, no Fourier L¹
velocity bound, and no H³ terminal energy ceiling are used.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 1000000

/-- Reflection and translation do not change the raw Fourier L² norm. -/
theorem h3Critical_rawFourierReflectedShift_norm_eq
    (G : H3SpectralScalarState) (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarRawFourierReflectedShiftL2 G ξ‖ =
      ‖h3SpectralScalarRawFourierL2 G‖ := by
  unfold h3SpectralScalarRawFourierReflectedShiftL2
  exact MeasureTheory.Lp.norm_compMeasurePreserving
    (h3SpectralScalarRawFourierL2 G)
    (h3FourierSubLeftContinuousMapFamily_measurePreserving ξ)

/-- The exact quadratic raw Fourier convolution is bounded pointwise by
its two unweighted L² inputs. No weighted Fourier L¹ input is needed. -/
theorem h3Critical_rawProductConvolution_le_rawL2Product
    (F G : H3SpectralScalarState) (ξ : H3FourierPoint3) :
    ‖h3RawProductConvolution F G ξ‖ ≤
      ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierL2 G‖ := by
  rw [h3RawProductConvolution_eq_inner_conjRaw_shift]
  calc
    ‖inner ℂ (h3SpectralScalarRawFourierConjL2 F)
        (h3SpectralScalarRawFourierReflectedShiftL2 G ξ)‖ ≤
      ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierReflectedShiftL2 G ξ‖ :=
      norm_inner_le_norm _ _
    _ = ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierL2 G‖ := by
      rw [h3Critical_rawFourierReflectedShift_norm_eq G ξ]

/-- Actual raw velocity convolution, at every output frequency and all
later physical times, is controlled by one fixed physical kinetic anchor.
The two velocity component indices are arbitrary and may be different. -/
theorem h3Critical_actual_rawConvolution_le_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ∀ (t : ℝ), t ∈ Set.Ioo b T →
      ∀ (j k : Fin 3) (ξ : H3FourierPoint3),
        ‖h3RawProductConvolution
          ((h3AuditActualSpectralVelocityTotal hH3 t) j)
          ((h3AuditActualSpectralVelocityTotal hH3 t) k) ξ‖ ≤
          velocityH3Energy0At u b := by
  intro t ht j k ξ
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 htClass.1, htClass.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hConj : ‖h3SpectralScalarRawFourierConjL2 (U j)‖ ≤
      Real.sqrt (velocityH3Energy0At u b) :=
    h3Path_rawVelocityFourierConjL2_le_sqrtKineticAnchor244
      hH3 hClass hb htClass ht.1.le j
  have hRaw : ‖h3SpectralScalarRawFourierL2 (U k)‖ ≤
      Real.sqrt (velocityH3Energy0At u b) :=
    h3Path_rawVelocityFourierL2_le_sqrtKineticAnchor244
      hH3 hClass hb htClass ht.1.le k
  have hMassNonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
  change ‖h3RawProductConvolution (U j) (U k) ξ‖ ≤ _
  calc
    ‖h3RawProductConvolution (U j) (U k) ξ‖ ≤
        ‖h3SpectralScalarRawFourierConjL2 (U j)‖ *
          ‖h3SpectralScalarRawFourierL2 (U k)‖ :=
      h3Critical_rawProductConvolution_le_rawL2Product _ _ ξ
    _ ≤ Real.sqrt (velocityH3Energy0At u b) *
          ‖h3SpectralScalarRawFourierL2 (U k)‖ :=
      mul_le_mul_of_nonneg_right hConj (norm_nonneg _)
    _ ≤ Real.sqrt (velocityH3Energy0At u b) *
          Real.sqrt (velocityH3Energy0At u b) :=
      mul_le_mul_of_nonneg_left hRaw (Real.sqrt_nonneg _)
    _ = velocityH3Energy0At u b := by
      rw [← pow_two, Real.sq_sqrt hMassNonneg]

/-- On any fixed low Fourier ball, the genuinely differentiated quadratic
raw convolution is pointwise bounded by radius times kinetic energy.
This is the frequency-localized first derivative in the nonlinear PDE source. -/
theorem h3Critical_actual_lowRadial_derivativeConvolution_le_kineticAnchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ (t : ℝ), t ∈ Set.Ioo b T →
      ∀ (i j k : Fin 3) (ξ : H3FourierPoint3),
        ξ ∈ h3TerminalRadialFrequencyBelow ρ →
        ‖h3FourierDerivativeSymbol i ξ *
          h3RawProductConvolution
            ((h3AuditActualSpectralVelocityTotal hH3 t) j)
            ((h3AuditActualSpectralVelocityTotal hH3 t) k) ξ‖ ≤
            ρ * velocityH3Energy0At u b := by
  intro t ht i j k ξ hξ
  have hRadial : h3FourierGradientMagnitude ξ < ρ := by
    simpa only [h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq] using hξ
  have hDerivative : ‖h3FourierDerivativeSymbol i ξ‖ ≤ ρ :=
    (norm_h3FourierDerivativeSymbol_le_gradientMagnitude i ξ).trans
      hRadial.le
  have hConvolution :=
    h3Critical_actual_rawConvolution_le_kineticAnchor
      hH3 hClass b hb t ht j k ξ
  rw [norm_mul]
  calc
    ‖h3FourierDerivativeSymbol i ξ‖ *
      ‖h3RawProductConvolution
          ((h3AuditActualSpectralVelocityTotal hH3 t) j)
          ((h3AuditActualSpectralVelocityTotal hH3 t) k) ξ‖ ≤
        ρ * ‖h3RawProductConvolution
          ((h3AuditActualSpectralVelocityTotal hH3 t) j)
          ((h3AuditActualSpectralVelocityTotal hH3 t) k) ξ‖ :=
      mul_le_mul_of_nonneg_right hDerivative (norm_nonneg _)
    _ ≤ ρ * velocityH3Energy0At u b :=
      mul_le_mul_of_nonneg_left hConvolution hρ

end
end PrimeTensor.Bridge.Euclidean
