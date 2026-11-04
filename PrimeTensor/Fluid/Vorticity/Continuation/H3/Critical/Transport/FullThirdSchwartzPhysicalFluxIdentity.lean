import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSchwartzPhysicalSevenBridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealFourierIdentification244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealImaginaryKernel244
import Mathlib.Tactic

/-!
# Exact unrestricted physical H³ commutator as sixth-power Fourier flux

The preceding physical seven-derivative bridge identifies the complete
unphased density with the *corrected* complex ordered symbol. The companion
normalization lemma commutes the five coordinate sums with the integral and
restores both the energy-pairing factor two and the Fourier phase `(2πi)^7`.

Combining that with the true six measure-preserving momentum permutations,
complex solenoidality transferred from the physical `Point3` predicate, and
the physical Fourier realization proves an exact identity for EVERY real
solenoidal Schwartz field. This is a static identity and does not supply a
new Navier--Stokes energy estimate or a global regularity conclusion.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1900000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdPhysicalFluxIdentity
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- For every real Schwartz field, the original complex physical coefficient
is the integral of the complete four-gradient/three-interpolation density,
with precisely the factor `2 * (2πi)^7`. No incompressibility is required. -/
theorem fullThirdSchwartzFourierCoefficient_eq_physicalHalfIntegral244
    (f : A3 → SchwartzMap V3 ℝ) :
    fullThirdSchwartzFourierCoefficient244 f =
      2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        (∫ z : V3 × V3,
          thirdFullSchwartzPhysicalHalfSevenKernel244
            (fun j => h3SchwartzComplexify (f j)) z
            ∂volume.prod volume) := by
  exact thirdFullSchwartzPhysicalHalfSeven_fourierCoefficient244
    (fun j => h3SchwartzComplexify (f j))

/-- The exact unrestricted COMPLEX Fourier coefficient is the sixth-power
flux integral multiplied by `(2πi)^7 / 3`. The denominator is the true
six-permutation normalization, not an assumed sign or positivity factor. -/
theorem fullThirdSchwartzFourierCoefficient_eq_sixthPowerFlux244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f) :
    fullThirdSchwartzFourierCoefficient244 f =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f j)) z
            ∂volume.prod volume) := by
  have hFlux := thirdFullRealSchwartzPhysicalHalfSeven_flux_integral244
    f hDiv
  rw [fullThirdSchwartzFourierCoefficient_eq_physicalHalfIntegral244]
  calc
    2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
      (∫ z : V3 × V3,
        thirdFullSchwartzPhysicalHalfSevenKernel244
          (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume) =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 7 / 3) *
        (6 * (∫ z : V3 × V3,
          thirdFullSchwartzPhysicalHalfSevenKernel244
            (fun j => h3SchwartzComplexify (f j)) z
            ∂volume.prod volume)) := by ring
    _ = _ := by rw [← hFlux]

/-- Seventh-order Fourier differentiation contributes the real coefficient
`(2π)^7 / 3` to the imaginary part, with the sign fixed by `I^7 = -I`. -/
theorem fullThirdSeventhPhase_divThree_real_eq_imag244 (w : ℂ) :
    ((((2 * (Real.pi : ℂ) * Complex.I) ^ 7) / 3) * w).re =
      ((2 * Real.pi) ^ 7 / 3) * w.im := by
  let c : ℂ := (2 * (Real.pi : ℂ) * Complex.I) ^ 7
  have hCast : (((1 / 3 : ℝ) : ℂ)) = (1 / 3 : ℂ) := by norm_num
  calc
    ((c / 3) * w).re =
        (((1 / 3 : ℝ) : ℂ) * (c * w)).re := by
      congr 1
      rw [hCast]
      simp only [div_eq_mul_inv]
      ring
    _ = (1 / 3 : ℝ) * (c * w).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    _ = (1 / 3 : ℝ) * ((2 * Real.pi) ^ 7 * w.im) := by
      rw [show c = (2 * (Real.pi : ℂ) * Complex.I) ^ 7 by rfl,
        thirdFullSeventhPhase_real_eq_imag244]
    _ = ((2 * Real.pi) ^ 7 / 3) * w.im := by ring

/-- **Full physical H³ sixth-power flux identity.** For EVERY real,
`Point3`-solenoidal Schwartz velocity, the original signed physical
third-order commutator equals the correctly normalized imaginary part of
three exact sixth-power radial transfer terms on `ℝ³ × ℝ³`.

No packets, cutoff windows, static absorption assumptions or PDE-time
hypotheses are added. This does not by itself bound the signed flux. -/
theorem fullSchwartzThirdCommutator_eq_sixthPowerFlux_integral244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f) :
    fullSchwartzThirdCommutator244 f =
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f j)) z
            ∂volume.prod volume).im := by
  rw [fullSchwartzThirdCommutator_eq_fullFourierRe244,
    fullThirdSchwartzFourierCoefficient_eq_sixthPowerFlux244 f hDiv]
  exact fullThirdSeventhPhase_divThree_real_eq_imag244 _

end
end PrimeTensor.FirstMonomialTriad
