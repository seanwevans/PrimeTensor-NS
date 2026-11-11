import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalSharpPhysicalKineticCompensation
import Mathlib.Tactic

/-!
# Actual Navier--Stokes Young-gap localization on a finite q-annulus

Put q(ξ) = h3FourierGradientSquare ξ, V = actual raw Fourier velocity,
R = actual projected physical momentum source, and F = the genuine Fourier
Leray nonlinearity.  The accepted physical Fourier identity proves

  F + 2qV = qV - R                 almost everywhere.

On lo <= q <= hi, choose rate = (lo+hi)/2 and width=(hi-lo)/2.
The *pointwise* quantitative bridge to constant-rate anti-heat alignment is

  lo^3 |R-rate V|^2 <= 2 q^3 |F+2qV|^2 + 2 hi^3 width^2 |V|^2.

Thus Young-gap smallness alone is insufficient when the annulus is wide;
the frequency variation has its own explicit cost.  A separate integral
result keeps all three on-band integrability premises visible.  At fixed
physical H3 snapshots these are expected from raw L2 and bounded q, but
that automatic integrability is a distinct proof obligation.

There is no terminal-uniform estimate or continuation claim here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

-- Use the same concrete product Lebesgue measure as the imported Fourier
-- L² and physical sharp-cutoff modules.
noncomputable local instance axisFintypeAnnularYoungGap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularYoungGap244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Subtraction against a constant anti-heat rate differs from the true
Fourier multiplier residual by at most the multiplier's variation. -/
theorem thirdFullKinetic_annularAntiHeat_norm_le244
    (q rate width : ℝ) (hWidth : |q - rate| ≤ width)
    (z r : ℂ) :
    ‖r - (rate : ℂ) * z‖ ≤
      ‖(q : ℂ) * z - r‖ + width * ‖z‖ := by
  have hRewrite :
      r - (rate : ℂ) * z =
        -((q : ℂ) * z - r) + ((q - rate : ℝ) : ℂ) * z := by
    push_cast
    ring
  calc
    ‖r - (rate : ℂ) * z‖ =
        ‖-((q : ℂ) * z - r) + ((q - rate : ℝ) : ℂ) * z‖ := by
          rw [hRewrite]
    _ ≤ ‖-((q : ℂ) * z - r)‖ +
          ‖((q - rate : ℝ) : ℂ) * z‖ := norm_add_le _ _
    _ = ‖(q : ℂ) * z - r‖ + |q - rate| * ‖z‖ := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖(q : ℂ) * z - r‖ + width * ‖z‖ :=
          add_le_add_right
            (mul_le_mul_of_nonneg_right hWidth (norm_nonneg z)) _

/-- Bounded-frequency quantitative conversion from the q³-weighted sharp
Young remainder to unweighted constant-rate anti-heat mismatch. -/
theorem thirdFullKinetic_annularAntiHeat_weightedSquare244
    (lo hi q rate width : ℝ)
    (hLo : 0 ≤ lo) (hLower : lo ≤ q) (hUpper : q ≤ hi)
    (hWidth : |q - rate| ≤ width) (z r : ℂ) :
    lo ^ 3 * ‖r - (rate : ℂ) * z‖ ^ 2 ≤
      2 * q ^ 3 * ‖(q : ℂ) * z - r‖ ^ 2 +
        2 * hi ^ 3 * width ^ 2 * ‖z‖ ^ 2 := by
  have hWidthNonneg : 0 ≤ width :=
    le_trans (abs_nonneg _) hWidth
  have hTri := thirdFullKinetic_annularAntiHeat_norm_le244
    q rate width hWidth z r
  have hRightNonneg :
      0 ≤ ‖(q : ℂ) * z - r‖ + width * ‖z‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg hWidthNonneg (norm_nonneg _))
  have hSq :
      ‖r - (rate : ℂ) * z‖ ^ 2 ≤
        (‖(q : ℂ) * z - r‖ + width * ‖z‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hRightNonneg).mpr hTri
  have hYoung :
      ‖r - (rate : ℂ) * z‖ ^ 2 ≤
        2 * ‖(q : ℂ) * z - r‖ ^ 2 +
          2 * (width * ‖z‖) ^ 2 := by
    nlinarith only [hSq,
      sq_nonneg (‖(q : ℂ) * z - r‖ - width * ‖z‖)]
  have hQ : 0 ≤ q := le_trans hLo hLower
  have hPowLo : lo ^ 3 ≤ q ^ 3 :=
    pow_le_pow_left₀ hLo hLower 3
  have hPowHi : q ^ 3 ≤ hi ^ 3 :=
    pow_le_pow_left₀ hQ hUpper 3
  calc
    lo ^ 3 * ‖r - (rate : ℂ) * z‖ ^ 2 ≤
        q ^ 3 * ‖r - (rate : ℂ) * z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hPowLo (sq_nonneg _)
    _ ≤ q ^ 3 *
          (2 * ‖(q : ℂ) * z - r‖ ^ 2 +
            2 * (width * ‖z‖) ^ 2) :=
      mul_le_mul_of_nonneg_left hYoung (pow_nonneg hQ 3)
    _ = 2 * q ^ 3 * ‖(q : ℂ) * z - r‖ ^ 2 +
          2 * q ^ 3 * width ^ 2 * ‖z‖ ^ 2 := by ring
    _ ≤ 2 * q ^ 3 * ‖(q : ℂ) * z - r‖ ^ 2 +
          2 * hi ^ 3 * width ^ 2 * ‖z‖ ^ 2 := by
      have hMultiply := mul_le_mul_of_nonneg_right hPowHi
        (mul_nonneg (sq_nonneg width) (sq_nonneg (‖z‖)))
      nlinarith only [hMultiply]

/-- The optimal constant rate for a supplied q-band is its midpoint;
its unavoidable variation is exactly half the band's q-width. -/
theorem thirdFullKinetic_midpointAnnulus_weightedSquare244
    (lo hi q : ℝ) (hLo : 0 ≤ lo)
    (hLower : lo ≤ q) (hUpper : q ≤ hi) (z r : ℂ) :
    lo ^ 3 * ‖r - (((lo + hi) / 2 : ℝ) : ℂ) * z‖ ^ 2 ≤
      2 * q ^ 3 * ‖(q : ℂ) * z - r‖ ^ 2 +
        2 * hi ^ 3 * ((hi - lo) / 2) ^ 2 * ‖z‖ ^ 2 := by
  have hWidth : |q - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hLower, hUpper]
  exact thirdFullKinetic_annularAntiHeat_weightedSquare244
    lo hi q ((lo + hi) / 2) ((hi - lo) / 2)
    hLo hLower hUpper hWidth z r

/-- The *actual* Navier--Stokes projected momentum source obeys the
midpoint-annulus inequality almost everywhere.  In the sharp-gap term we
retain the real solenoidal Leray nonlinearity, not an abstract RHS. -/
theorem thirdFullPhysical_actualAnnularYoungGap_pointwise244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) (lo hi : ℝ) (hLo : 0 ≤ lo) :
    let U : H3SpectralVelocityState :=
      h3AuditActualSpectralVelocityTotal hH3 t
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      lo ≤ h3FourierGradientSquare ξ →
      h3FourierGradientSquare ξ ≤ hi →
        lo ^ 3 *
          ‖(h3CriticalActualProjectedFourierSource hH3 j t :
              H3FourierPoint3 → ℂ) ξ -
            (((lo + hi) / 2 : ℝ) : ℂ) *
              h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ≤
        2 * h3FourierGradientSquare ξ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U j ξ +
            2 * ((h3FourierGradientSquare ξ : ℂ) *
              h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 +
        2 * hi ^ 3 * ((hi - lo) / 2) ^ 2 *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 := by
  dsimp only
  have hRep := thirdFullPhysical_actualYoungGap_eq_antiHeatResidual_ae244
    hH3 t ht j
  filter_upwards [hRep] with ξ hξ
  intro hLower hUpper
  have hAt := thirdFullKinetic_midpointAnnulus_weightedSquare244
    lo hi (h3FourierGradientSquare ξ) hLo hLower hUpper
    (h3SpectralScalarRawFourierL2
      ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ)
    ((h3CriticalActualProjectedFourierSource hH3 j t :
      H3FourierPoint3 → ℂ) ξ)
  rw [← hξ] at hAt
  exact hAt

/-- Integrated version on any measurable fixed-time q-annulus.  The three
explicit IntegrableOn hypotheses are *local* fixed-time requirements, not
hypotheses about terminal integrability or a uniform H³ bound. -/
theorem thirdFullPhysical_actualAnnularYoungGap_integral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) (lo hi : ℝ) (hLo : 0 ≤ lo)
    (S : Set H3FourierPoint3) (hS : MeasurableSet S)
    (hBand : ∀ ξ ∈ S,
      lo ≤ h3FourierGradientSquare ξ ∧ h3FourierGradientSquare ξ ≤ hi)
    (hError : IntegrableOn (fun ξ : H3FourierPoint3 =>
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
          H3FourierPoint3 → ℂ) ξ -
        (((lo + hi) / 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourierL2
            ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2)
      S volume)
    (hGap : IntegrableOn (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 t) j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ)‖ ^ 2)
      S volume)
    (hMass : IntegrableOn (fun ξ : H3FourierPoint3 =>
      ‖h3SpectralScalarRawFourierL2
        ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2)
      S volume) :
    lo ^ 3 * (∫ ξ in S,
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
          H3FourierPoint3 → ℂ) ξ -
        (((lo + hi) / 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourierL2
            ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2 ∂volume) ≤
    2 * (∫ ξ in S,
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 t) j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ)‖ ^ 2 ∂volume) +
    (2 * hi ^ 3 * ((hi - lo) / 2) ^ 2) *
      (∫ ξ in S,
        ‖h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2 ∂volume) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let z : H3FourierPoint3 → ℂ := h3SpectralScalarRawFourierL2 (U j)
  let r : H3FourierPoint3 → ℂ :=
    (h3CriticalActualProjectedFourierSource hH3 j t :
      H3FourierPoint3 → ℂ)
  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence U U j
  let rate : ℝ := (lo + hi) / 2
  let width : ℝ := (hi - lo) / 2
  let A : H3FourierPoint3 → ℝ := fun ξ => ‖r ξ - (rate : ℂ) * z ξ‖ ^ 2
  let B : H3FourierPoint3 → ℝ := fun ξ =>
    h3FourierGradientSquare ξ ^ 3 *
      ‖f ξ + 2 * ((h3FourierGradientSquare ξ : ℂ) * z ξ)‖ ^ 2
  let C : H3FourierPoint3 → ℝ := fun ξ => ‖z ξ‖ ^ 2
  have hA : IntegrableOn A S volume := hError
  have hB : IntegrableOn B S volume := hGap
  have hC : IntegrableOn C S volume := hMass
  have hDom : ∀ᵐ ξ ∂((volume : Measure H3FourierPoint3).restrict S),
      lo ^ 3 * A ξ ≤ 2 * B ξ +
        (2 * hi ^ 3 * width ^ 2) * C ξ := by
    filter_upwards [ae_restrict_mem hS,
      ae_restrict_of_ae (s := S)
        (thirdFullPhysical_actualAnnularYoungGap_pointwise244
          hH3 t ht j lo hi hLo)] with ξ hMem hAt
    rcases hBand ξ hMem with ⟨hLower, hUpper⟩
    -- The pointwise theorem is expanded, while this target uses the local
    -- integrand aliases A, B, C and the midpoint-width abbreviations.
    -- Unfold only those aliases and normalize multiplication grouping.
    simpa only [A, B, C, U, z, r, f, rate, width, mul_assoc] using
      (hAt hLower hUpper)
  have hIntegral :
      (∫ ξ in S, lo ^ 3 * A ξ ∂volume) ≤
      ∫ ξ in S, (2 * B ξ +
        (2 * hi ^ 3 * width ^ 2) * C ξ) ∂volume := by
    exact integral_mono_ae
      (hA.const_mul (lo ^ 3))
      ((hB.const_mul 2).add (hC.const_mul (2 * hi ^ 3 * width ^ 2)))
      hDom
  rw [integral_const_mul,
    integral_add (hB.const_mul 2) (hC.const_mul (2 * hi ^ 3 * width ^ 2)),
    integral_const_mul, integral_const_mul] at hIntegral
  exact hIntegral

end
end PrimeTensor.FirstMonomialTriad
