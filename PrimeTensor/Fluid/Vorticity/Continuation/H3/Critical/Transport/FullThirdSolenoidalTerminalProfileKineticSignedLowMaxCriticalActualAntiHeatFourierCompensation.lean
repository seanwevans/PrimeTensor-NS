import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalPhysicalAntiHeatKineticRigidity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassFourierMassEscape
import Mathlib.Tactic

/-!
# Actual Fourier Young-gap residual and kinetic low/high compensation

The sharp Young remainder is q³|N+2qU|². The accepted physical Fourier
momentum-source identification R=-qU-N changes this, EXACTLY, into
q³|qU-R|². This is the actual projected momentum source, not an arbitrary
surrogate, and the equality persists on every sharp high-frequency region.

Separately, a real-Hilbert low/high orthogonal splitting of the actual
kinetic pairing <U,R>=-D₀ forces an adverse low-frequency pairing whenever
high-frequency momentum is near a positive multiple of high velocity.
The localization theorem makes the decomposition and orthogonality
explicit: verification that a specific Fourier cutoff supplies these data
is a distinct analytic obligation, not an implicit assumption.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeActualAntiHeatCompensation244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceActualAntiHeatCompensation244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual strict-time physical momentum Fourier source, with the
correct sign and heat multiplier. This uses its separately established
real-physical Fourier reconstruction, not a formal PDE placeholder. -/
theorem thirdFullPhysical_actualFourierSource_antiHeatRepresentative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (j : Fin 3) :
    let U : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 t
    ((h3CriticalActualProjectedFourierSource hH3 j t :
        H3FourierComplexL2) : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      -(h3FourierGradientSquare ξ : ℂ) *
        h3SpectralScalarRawFourierL2 (U j) ξ -
      h3RawFinLerayOuterProductDivergence U U j ξ) := by
  dsimp only
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let L : H3FourierComplexL2 :=
    h3SpectralScalarLaplacianRawFourierL2 (U j)
  let N : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceFourierL2 U U j
  let R : H3FourierComplexL2 :=
    h3CriticalActualProjectedFourierSource hH3 j t
  have hSource : R = L - N := by
    dsimp only [R, L, N, U]
    exact h3Critical_actualProjectedFourierSource_eq_rawRHS hH3 t ht j
  have hLap : (L : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ => -(h3FourierGradientSquare ξ : ℂ) *
        h3SpectralScalarRawFourierL2 (U j) ξ) := by
    dsimp only [L]
    exact h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw (U j)
  have hNonlin : (N : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ => h3RawFinLerayOuterProductDivergence U U j ξ) := by
    dsimp only [N]
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact MeasureTheory.MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_memLp2 U U j)
  change (R : H3FourierPoint3 → ℂ) =ᵐ[_] _
  rw [hSource]
  filter_upwards [MeasureTheory.Lp.coeFn_sub L N, hLap, hNonlin]
    with ξ hSub hLapξ hNξ
  rw [hSub]
  -- The L² subtraction has been rewritten, but the goal still contains
  -- a pointwise application of subtraction on function representatives.
  -- Expose its values at ξ before using either a.e. representative.
  simp only [Pi.sub_apply]
  rw [hLapξ, hNξ]

/-- The Fourier residual saturating the sharp Young bound is exactly the
anti-heat residual of the ACTUAL physical projected momentum source. -/
theorem thirdFullPhysical_actualYoungGap_eq_antiHeatResidual_ae244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (j : Fin 3) :
    let U : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 t
    (fun ξ : H3FourierPoint3 =>
      h3RawFinLerayOuterProductDivergence U U j ξ +
        2 * ((h3FourierGradientSquare ξ : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (h3FourierGradientSquare ξ : ℂ) *
        h3SpectralScalarRawFourierL2 (U j) ξ -
        (h3CriticalActualProjectedFourierSource hH3 j t :
          H3FourierPoint3 → ℂ) ξ) := by
  dsimp only
  have hRep := thirdFullPhysical_actualFourierSource_antiHeatRepresentative244
    hH3 t ht j
  filter_upwards [hRep] with ξ hξ
  rw [hξ]
  ring

/-- The same ACTUAL anti-heat residual identity holds on any sharp highpass
band. No endpoint uniformity or additional Fourier moment is postulated. -/
theorem thirdFullPhysical_actualYoungGap_highBand_eq_antiHeat244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) (ρ : ℝ) :
    let U : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 t
    (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence U U j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) =
    (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 3 *
        ‖(h3FourierGradientSquare ξ : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ -
          (h3CriticalActualProjectedFourierSource hH3 j t :
            H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume) := by
  dsimp only
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (s := (h3TerminalRadialFrequencyBelow ρ)ᶜ)
    (thirdFullPhysical_actualYoungGap_eq_antiHeatResidual_ae244
      hH3 t ht j)] with ξ hξ
  rw [hξ]

/-- Orthogonal low/high decompositions cannot support a positive high-band
anti-heat contribution without a compensating low-band kinetic pairing.
This is a real-Hilbert statement, preserving the signs exactly. -/
theorem thirdFullKinetic_twoChannel_antiHeatCompensation244
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ulo Uhi Rlo Rhi : H) (D rate : ℝ)
    (hPair : inner ℝ (Ulo + Uhi) (Rlo + Rhi) = -D)
    (hCrossLo : inner ℝ Ulo Rhi = 0)
    (hCrossHi : inner ℝ Uhi Rlo = 0) :
    D + rate * ‖Uhi‖ ^ 2 ≤
      ‖Ulo‖ * ‖Rlo‖ +
        ‖Uhi‖ * ‖Rhi - rate • Uhi‖ := by
  have hBase : inner ℝ Ulo Rlo + inner ℝ Uhi Rhi = -D := by
    rw [inner_add_left, inner_add_right, inner_add_right] at hPair
    linarith only [hPair, hCrossLo, hCrossHi]
  have hHigh : inner ℝ Uhi Rhi =
      inner ℝ Uhi (Rhi - rate • Uhi) + rate * ‖Uhi‖ ^ 2 := by
    calc
      inner ℝ Uhi Rhi =
          inner ℝ Uhi ((Rhi - rate • Uhi) + rate • Uhi) := by
            rw [sub_add_cancel]
      _ = inner ℝ Uhi (Rhi - rate • Uhi) + rate * ‖Uhi‖ ^ 2 := by
        rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hLoBound : -(‖Ulo‖ * ‖Rlo‖) ≤ inner ℝ Ulo Rlo :=
    (abs_le.mp (abs_real_inner_le_norm Ulo Rlo)).1
  have hHiBound : -(‖Uhi‖ * ‖Rhi - rate • Uhi‖) ≤
      inner ℝ Uhi (Rhi - rate • Uhi) :=
    (abs_le.mp (abs_real_inner_le_norm Uhi (Rhi - rate • Uhi))).1
  linarith only [hBase, hHigh, hLoBound, hHiBound]

/-- With bounded low-band source and a relative high-band anti-heat error,
the high-band kinetic carrier must obey a quantitative mass ceiling. -/
theorem thirdFullKinetic_twoChannel_highMassGate244
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ulo Uhi Rlo Rhi : H) (D rate eps M C : ℝ)
    (hPair : inner ℝ (Ulo + Uhi) (Rlo + Rhi) = -D)
    (hCrossLo : inner ℝ Ulo Rhi = 0)
    (hCrossHi : inner ℝ Uhi Rlo = 0)
    (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hUlo : ‖Ulo‖ ≤ M) (hRlo : ‖Rlo‖ ≤ C)
    (hErr : ‖Rhi - rate • Uhi‖ ≤ eps * ‖Uhi‖) :
    (rate - eps) * ‖Uhi‖ ^ 2 ≤ M * C := by
  have hComp := thirdFullKinetic_twoChannel_antiHeatCompensation244
    Ulo Uhi Rlo Rhi D rate hPair hCrossLo hCrossHi
  have hLow : ‖Ulo‖ * ‖Rlo‖ ≤ M * C := by
    calc
      ‖Ulo‖ * ‖Rlo‖ ≤ M * ‖Rlo‖ :=
        mul_le_mul_of_nonneg_right hUlo (norm_nonneg _)
      _ ≤ M * C := mul_le_mul_of_nonneg_left hRlo hM
  have hHigh : ‖Uhi‖ * ‖Rhi - rate • Uhi‖ ≤
      eps * ‖Uhi‖ ^ 2 := by
    calc
      ‖Uhi‖ * ‖Rhi - rate • Uhi‖ ≤
          ‖Uhi‖ * (eps * ‖Uhi‖) :=
        mul_le_mul_of_nonneg_left hErr (norm_nonneg _)
      _ = eps * ‖Uhi‖ ^ 2 := by ring
  nlinarith only [hComp, hD, hLow, hHigh]

/-- Actual Navier--Stokes kinetic compensation for any GIVEN orthogonal
low/high decomposition of its physical Hilbert velocity and momentum
source. For a sharp Fourier cutoff the four decomposition/orthogonality
certificates must be separately derived from Plancherel. -/
theorem thirdFullPhysical_kineticSplit_highMassGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (Ulo Uhi Rlo Rhi : H3PhysicalRealFinVectorL2Hilbert)
    (hU : h3AuditInitialOldPhysicalHilbertTotal hH3 t = Ulo + Uhi)
    (hR : h3PathActualProjectedMomentumSource244 hH3 t = Rlo + Rhi)
    (hCrossLo : inner ℝ Ulo Rhi = 0)
    (hCrossHi : inner ℝ Uhi Rlo = 0)
    (rate eps M C : ℝ) (hM : 0 ≤ M)
    (hUlo : ‖Ulo‖ ≤ M) (hRlo : ‖Rlo‖ ≤ C)
    (hErr : ‖Rhi - rate • Uhi‖ ≤ eps * ‖Uhi‖) :
    (rate - eps) * ‖Uhi‖ ^ 2 ≤ M * C := by
  have hPair : inner ℝ (Ulo + Uhi) (Rlo + Rhi) =
      -velocityH3Dissipation0At u t := by
    rw [← hU, ← hR]
    exact h3Path_physicalHilbertPairing_eq_negDissipation0_positiveTime244
      hH3 t ht
  exact thirdFullKinetic_twoChannel_highMassGate244
    Ulo Uhi Rlo Rhi (velocityH3Dissipation0At u t)
    rate eps M C hPair hCrossLo hCrossHi
    (velocityH3Dissipation0At_nonneg u t) hM hUlo hRlo hErr

end
end PrimeTensor.FirstMonomialTriad
