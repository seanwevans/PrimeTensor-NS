import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSchwartzLongitudinalFluxDefect
import Mathlib.Tactic

/-!
# The longitudinal H³ flux error: pointwise control and the exact spectral-limit criterion

The six-orbit identity contains an explicitly longitudinal correction.  Its
three-factor majorant is pointwise and needs no solenoidality.  The second
part shows exactly which *additional* analytic statement allows the
uncorrected radial flux to converge to the physical third-order transport.

Neither weighted-H³ convergence by itself nor solenoidality of a limiting
spectral state is substituted for convergence of the longitudinal integral.
The requisite smallness of that integral is the remaining hard estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeLongitudinalControl244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The *absolute*, unsymmetrized three-channel divergence error.
Every term has exactly one Fourier divergence factor; there are no
Hermitian conjugations or inverse frequency powers. -/
noncomputable def thirdFullLongitudinalDefectMajorant244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) : ℝ :=
  let a : ℂ := (thirdTriadAxisDot244 p q : ℂ)
  let b : ℂ := (thirdTriadAxisDot244 p r : ℂ)
  let c : ℂ := (thirdTriadAxisDot244 q r : ℂ)
  ‖(thirdFullComplexPolarizationDot244 B C * mixedDot p A) * b *
      (b ^ 2 + 3 * b * c + 3 * c ^ 2)‖ +
    ‖(thirdFullComplexPolarizationDot244 A C * mixedDot q B) * c *
      (3 * b ^ 2 + 3 * b * c + c ^ 2)‖ +
    ‖(thirdFullComplexPolarizationDot244 A B * mixedDot r C) * c *
      (3 * a ^ 2 + 3 * a * c + c ^ 2)‖

/-- Exact divergence-weighted triangle estimate for arbitrary complex
polarizations. This bound does NOT claim any H³-only uniform majorization. -/
theorem thirdFullComplexLongitudinalFluxDefect_norm_le_majorant244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) :
    ‖thirdFullComplexLongitudinalFluxDefect244 p q r A B C‖ ≤
      thirdFullLongitudinalDefectMajorant244 p q r A B C := by
  let a : ℂ := (thirdTriadAxisDot244 p q : ℂ)
  let b : ℂ := (thirdTriadAxisDot244 p r : ℂ)
  let c : ℂ := (thirdTriadAxisDot244 q r : ℂ)
  let x : ℂ := (thirdFullComplexPolarizationDot244 B C * mixedDot p A) * b *
    (b ^ 2 + 3 * b * c + 3 * c ^ 2)
  let y : ℂ := (thirdFullComplexPolarizationDot244 A C * mixedDot q B) * c *
    (3 * b ^ 2 + 3 * b * c + c ^ 2)
  let z : ℂ := (thirdFullComplexPolarizationDot244 A B * mixedDot r C) * c *
    (3 * a ^ 2 + 3 * a * c + c ^ 2)
  change ‖-x - y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖
  calc
    ‖-x - y - z‖ ≤ ‖-x - y‖ + ‖z‖ := by
      simpa only [norm_neg] using (norm_sub_le (-x - y) z)
    _ ≤ (‖x‖ + ‖y‖) + ‖z‖ := by
      exact add_le_add_left
        (by simpa only [norm_neg] using (norm_sub_le (-x) y)) ‖z‖
    _ = _ := rfl

/-- Each contribution is explicitly a longitudinal amplitude multiplied by
its two transverse-looking polarization/frequency factors. -/
theorem thirdFullLongitudinalDefectMajorant_factor244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) :
    thirdFullLongitudinalDefectMajorant244 p q r A B C =
      let a : ℂ := (thirdTriadAxisDot244 p q : ℂ)
      let b : ℂ := (thirdTriadAxisDot244 p r : ℂ)
      let c : ℂ := (thirdTriadAxisDot244 q r : ℂ)
      (‖thirdFullComplexPolarizationDot244 B C‖ * ‖mixedDot p A‖) *
        ‖b‖ * ‖b ^ 2 + 3 * b * c + 3 * c ^ 2‖ +
      (‖thirdFullComplexPolarizationDot244 A C‖ * ‖mixedDot q B‖) *
        ‖c‖ * ‖3 * b ^ 2 + 3 * b * c + c ^ 2‖ +
      (‖thirdFullComplexPolarizationDot244 A B‖ * ‖mixedDot r C‖) *
        ‖c‖ * ‖3 * a ^ 2 + 3 * a * c + c ^ 2‖ := by
  unfold thirdFullLongitudinalDefectMajorant244
  simp only [norm_mul]

/-- The REAL longitudinal error of one not-necessarily-solenoidal Schwartz
velocity. The integral is defined for any function; integrability is
separately required in the error-splitting theorem below. -/
noncomputable def fullSchwartzThirdLongitudinalError244
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  ((2 * Real.pi) ^ 7 / 3) *
    (∫ z : V3 × V3,
      thirdFullSchwartzLongitudinalFluxDefect244
        (fun j => h3SchwartzComplexify (f j)) z
        ∂volume.prod volume).im

/-- If the longitudinal term is integrable, then the uncorrected flux is
integrable too, and its *exact* difference from the physical commutator is
the longitudinal integral. This does not assume the difference is small. -/
theorem fullSchwartzThirdCommutator_eq_flux_add_error244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDef : Integrable
      (thirdFullSchwartzLongitudinalFluxDefect244
        (fun j => h3SchwartzComplexify (f j)))
      (volume.prod volume)) :
    fullSchwartzThirdCommutator244 f =
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f j)) z
            ∂volume.prod volume).im +
      fullSchwartzThirdLongitudinalError244 f := by
  let v : A3 → SchwartzMap V3 ℂ :=
    fun j => h3SchwartzComplexify (f j)
  have hCorrected := thirdFullSchwartz_correctedFlux_integrable244 v
  have hFlux : Integrable (thirdFullSchwartzComplexSixthPowerFlux244 v)
      (volume.prod volume) := by
    apply (hCorrected.sub hDef).congr
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only [Pi.sub_apply]
      ring)
  have hAdd :
      (∫ z : V3 × V3,
        (thirdFullSchwartzComplexSixthPowerFlux244 v z +
          thirdFullSchwartzLongitudinalFluxDefect244 v z)
          ∂volume.prod volume) =
      (∫ z : V3 × V3,
        thirdFullSchwartzComplexSixthPowerFlux244 v z
          ∂volume.prod volume) +
      (∫ z : V3 × V3,
        thirdFullSchwartzLongitudinalFluxDefect244 v z
          ∂volume.prod volume) := integral_add hFlux hDef
  rw [fullSchwartzThirdCommutator_eq_correctedFlux244 f]
  change ((2 * Real.pi) ^ 7 / 3) *
    (∫ z : V3 × V3,
      (thirdFullSchwartzComplexSixthPowerFlux244 v z +
        thirdFullSchwartzLongitudinalFluxDefect244 v z)
        ∂volume.prod volume).im = _
  rw [hAdd]
  simp only [Complex.add_im, fullSchwartzThirdLongitudinalError244]
  ring

/-- A precise ANALYTIC TARGET for deleting the correction: strong enough
control of the signed longitudinal integral makes the uncorrected flux
converge to the already-proved canonical full H³ transport. In particular,
plain weighted-H³ convergence is NOT used as a proxy for this hypothesis. -/
theorem h3MatchedSchwartz_uncorrectedFlux_tendsto_of_error244
    (U : H3SpectralVelocityState)
    (F : H3MatchedSchwartzGradientCompletion244 U)
    (hDef : ∀ n : ℕ, Integrable
      (thirdFullSchwartzLongitudinalFluxDefect244
        (fun j => h3SchwartzComplexify (F.family.approximants n j)))
      (volume.prod volume))
    (hError : Tendsto
      (fun n : ℕ =>
        fullSchwartzThirdLongitudinalError244 (F.family.approximants n))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (F.family.approximants n j)) z
            ∂volume.prod volume).im)
      atTop (𝓝 (weightedH3CanonicalFullThirdCommutator244 U)) := by
  have hEq :
      (fun n : ℕ =>
        ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : V3 × V3,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j => h3SchwartzComplexify (F.family.approximants n j)) z
              ∂volume.prod volume).im) =
      (fun n : ℕ =>
        fullSchwartzThirdCommutator244 (F.family.approximants n) -
          fullSchwartzThirdLongitudinalError244 (F.family.approximants n)) := by
    funext n
    have h := fullSchwartzThirdCommutator_eq_flux_add_error244
      (F.family.approximants n) (hDef n)
    rw [h]
    ring
  rw [hEq]
  have hFull := h3MatchedSchwartzGradientCompletion_fullThird_tendsto244 U F
  simpa only [sub_zero] using hFull.sub hError

end
end PrimeTensor.FirstMonomialTriad
