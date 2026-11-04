import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSchwartzLongitudinalFluxDefect
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRealSolenoidalSchwartzPhysicalPDETransportLimit
import Mathlib.Tactic

/-!
# Exact solenoidal removal of the full-third longitudinal Fourier defect

The unrestricted six-orbit identity includes three longitudinal Fourier
contractions. On the ONE real solenoidal Schwartz density family already
constructed for a genuine H³ Navier--Stokes snapshot, all three contractions
vanish at EVERY triad frequency. Hence the corrected full-third Fourier flux
reduces to the genuine three-transfer sixth-power flux *at each approximation
index*, with no need to bound the correction or pass it to zero weakly.

The previously proved physical full-third transport limit then yields a pure
sixth-power Fourier flux representation of the ACTUAL physical H³ commutator.
The same sequence retains its weighted-H³ convergence and canonical physical
E₂/E₃ limits. This is a real solenoidal cancellation of the longitudinal
remainder, NOT a sign or coercivity estimate on the remaining transverse flux.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypePureSixthPowerFlux244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pointwise physical divergence of a complex Schwartz field kills every
longitudinal factor of the exact 12-term correction, not merely its integral.
This includes zero frequency and does not assume a Fourier representative
outside the genuine Schwartz transform. -/
theorem thirdFullSchwartz_longitudinalDefect_zero_of_complexDivergence244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (z : V3 × V3) :
    thirdFullSchwartzLongitudinalFluxDefect244 v z = 0 := by
  let p : A3 → ℝ := WithLp.ofLp z.1
  let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : A3 → ℝ := WithLp.ofLp z.2
  let P : (A3 → ℝ) → A3 → ℂ := h3SchwartzTriadPolarization v
  have hPolar : ∀ ξ : A3 → ℝ, mixedDot ξ (P ξ) = 0 :=
    h3SchwartzTriadPolarization_divergence_zero v hDiv
  change thirdFullComplexLongitudinalFluxDefect244
    p q r (P p) (P q) (P r) = 0
  exact thirdFullComplexLongitudinalFluxDefect_zero_of_solenoidal244
    p q r (P p) (P q) (P r) (hPolar p) (hPolar q) (hPolar r)

/-- The *uncorrected* full third Fourier transfer identity holds for any real
Schwartz velocity with the exact complexified physical divergence equation.
The correction vanishes pointwise, so no separate integrability or
zero-frequency convention is being introduced. -/
theorem thirdFullSchwartz_commutator_eq_pureFlux_of_complexDivergence244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (h3SchwartzComplexify (f j)) x
        (h3FourierAxisDirection j) = 0) :
    fullSchwartzThirdCommutator244 f =
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume).im := by
  rw [fullSchwartzThirdCommutator_eq_correctedFlux244 f]
  simp_rw [thirdFullSchwartz_longitudinalDefect_zero_of_complexDivergence244
    (fun j => h3SchwartzComplexify (f j)) hDiv]
  simp only [add_zero]

/-- Once the physical Schwartz approximants are actually solenoidal, strong
convergence of the complete signed transport implies convergence of the
*uncorrected* sixth-power Fourier transfer. No nonlinear limit hypothesis is
added; it is exactly the preexisting full-commutator limit. -/
theorem thirdFullSchwartz_pureFlux_tendsto_of_complexDivergence244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hDiv : ∀ n : ℕ, ∀ x : V3,
      ∑ j : A3, fderiv ℝ (h3SchwartzComplexify (f n j)) x
        (h3FourierAxisDirection j) = 0)
    (L : ℝ)
    (hFull : Tendsto (fun n => fullSchwartzThirdCommutator244 (f n))
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ =>
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f n j)) z
          ∂volume.prod volume).im)
      atTop (𝓝 L) := by
  have hEq :
      (fun n : ℕ => ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j => h3SchwartzComplexify (f n j)) z
          ∂volume.prod volume).im) =
      (fun n => fullSchwartzThirdCommutator244 (f n)) := by
    funext n
    exact (thirdFullSchwartz_commutator_eq_pureFlux_of_complexDivergence244
      (f n) (hDiv n)).symm
  rw [hEq]
  exact hFull

/-- At every genuine preterminal Fourier-compatible Navier--Stokes slice,
ONE real divergence-free Schwartz family simultaneously has:
 * strong H³ spectral convergence;
 * the exact weighted Fourier representative;
 * zero longitudinal Fourier defect at EACH triad and EACH index;
 * convergence of the genuine 27/81-slot physical energies;
 * pure sixth-power flux convergence to the ORIGINAL physical H³ transport.

No generic matched completion is asserted to be solenoidal. The sequence is
specifically the previously constructed solenoidality-preserving recovery. -/
theorem exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (htNS : t ∈ Set.Ioo (0 : ℝ) T)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ (V : ℕ → H3SpectralVelocityState)
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ),
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ n j,
        (V n j : V3 → ℂ) =ᵐ[volume]
          (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
            𝓕 (h3SchwartzComplexify (Ψ n j)) ξ)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ (n : ℕ) (z : V3 × V3),
        thirdFullSchwartzLongitudinalFluxDefect244
          (fun j : A3 => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))) z = 0) ∧
      Tendsto (fun n => lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalSecondJetEnergy244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier))) ∧
      Tendsto (fun n => lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalThirdJetEnergy244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier))) ∧
      Tendsto (fun n : ℕ =>
        ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : V3 × V3,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : A3 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
  obtain ⟨V, Ψ, hV, hDiv, hAE, _hE2, _hE3, hE2Limit, hE3Limit,
    _hGradient, _hSigned, hFull⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalSchwartzTransportLimits244
      hNS htNS hH3 hClass ht hFourier
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  have hDivF : ∀ n : ℕ, ∀ x : V3,
      ∑ j : A3, fderiv ℝ (h3SchwartzComplexify (f n j)) x
        (h3FourierAxisDirection j) = 0 := by
    intro n x
    exact hDiv n x
  have hDefect (n : ℕ) (z : V3 × V3) :
      thirdFullSchwartzLongitudinalFluxDefect244
        (fun j : A3 => h3SchwartzComplexify (f n j)) z = 0 :=
    thirdFullSchwartz_longitudinalDefect_zero_of_complexDivergence244
      (fun j => h3SchwartzComplexify (f n j)) (hDivF n) z
  have hFlux : Tendsto (fun n : ℕ =>
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : A3 => h3SchwartzComplexify (f n j)) z
          ∂volume.prod volume).im)
      atTop (𝓝 (velocityH3TransportDerivative3At u t)) :=
    thirdFullSchwartz_pureFlux_tendsto_of_complexDivergence244 f hDivF
      (velocityH3TransportDerivative3At u t) hFull
  have hDefectSeq : ∀ (n : ℕ) (z : V3 × V3),
      thirdFullSchwartzLongitudinalFluxDefect244
        (fun j : A3 => h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) z = 0 := by
    intro n z
    exact hDefect n z
  have hFluxSeq : Tendsto (fun n : ℕ =>
      ((2 * Real.pi) ^ 7 / 3) *
        (∫ z : V3 × V3,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : A3 => h3SchwartzComplexify
              (Ψ n (h3ClassicalizationFinOfAxis j))) z
          ∂volume.prod volume).im)
      atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
    simpa only [f] using hFlux
  exact ⟨V, Ψ, hV, hAE, hDiv, hDefectSeq,
    hE2Limit, hE3Limit, hFluxSeq⟩

end
end PrimeTensor.FirstMonomialTriad
