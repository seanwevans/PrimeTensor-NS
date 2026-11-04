import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRealSolenoidalSchwartzCanonicalEnergyLimit
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalGradientCanonicalClosure244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzDecoderRealization244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Incompressibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Encoded.Reality
import Mathlib.Tactic

/-!
# One real solenoidal Schwartz family realizes the OLD physical H³ transport

The preceding checkpoint constructed one real, physically divergence-free
Schwartz H³ density sequence whose literal second and third jets agree with
the canonical weighted reconstructions, and whose signed 243-slot monomial
converges canonically. Earlier physical work independently proved the signed
3–2–2 and gradient 3–3–1 canonical/physical identities.

The new bridge upgrades the SOLENOIDAL matched sequence to a gradient-matched
completion using its exact real L² decoder, the continuous C¹ realization
uniqueness theorem, and the existing automatic gradient-gauge theorem.
Consequently this SAME real solenoidal family has its gradient, signed and
complete G₃+3M Schwartz functionals tending to the original physical H³
Navier–Stokes transport of the Fourier-compatible preterminal snapshot.

The preterminal Navier–Stokes hypotheses themselves imply the target's
Fourier divergence-free condition. Real-valued physical data imply raw
Hermitian Fourier symmetry. No additional spectral reality or solenoidal
premises are requested of the user.

This theorem is an identification of a third-order transport functional,
not a claim that its sign is favorable or that H³ norms remain bounded
up to a singular endpoint.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean FourierTransform
open scoped ENNReal BigOperators SchwartzMap LineDeriv FourierTransform

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeSolenoidalPhysicalPDE244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact equality of the real L² decoder and a real Schwartz L² class
upgrades to equality of their *pointwise* physical C¹ realizations.
In particular solenoidal matched families have the precise zeroth-order
spectral matching needed by the full 972-term gradient channel. -/
theorem thirdFullSolenoidalSchwartz_pointwiseDecoderMatch244
    (V : H3SpectralVelocityState)
    (ψ : Fin 3 → SchwartzMap V3 ℝ)
    (hDecoder : ∀ j : Fin 3,
      h3SpectralVelocityDecodeRealL2 V j =
        (ψ j).toLp 2 (volume : Measure V3)) :
    ∀ j : A3,
      h3SchwartzPoint3Scalar (ψ (h3ClassicalizationFinOfAxis j)) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (V (h3ClassicalizationFinOfAxis j)) := by
  intro j
  have h := hDecoder (h3ClassicalizationFinOfAxis j)
  change h3SpectralScalarDecodeRealL2
    (V (h3ClassicalizationFinOfAxis j)) =
      (ψ (h3ClassicalizationFinOfAxis j)).toLp
        2 (volume : Measure V3) at h
  exact thirdFullSchwartz_zerothRealization_of_decoderEquality244
    (V (h3ClassicalizationFinOfAxis j))
    (ψ (h3ClassicalizationFinOfAxis j)) h

/-- Promote the actual solenoidal H³ density family to the complete
pointwise/second/third-matched gradient completion WITHOUT reselecting
another (possibly non-solenoidal) approximating family. -/
noncomputable def thirdFullSolenoidalSchwartzGradientCompletion244
    (target : H3SpectralVelocityState)
    (V : ℕ → H3SpectralVelocityState)
    (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ)
    (hV : Tendsto V atTop (𝓝 target))
    (hDecoder : ∀ n j,
      h3SpectralVelocityDecodeRealL2 (V n) j =
        (Ψ n j).toLp 2 (volume : Measure V3))
    (hSecond : ∀ n j a b,
      h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
              2 (volume : Measure V3)))
    (hThird : ∀ n j a b c,
      h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b}
              (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                2 (volume : Measure V3))) :
    H3MatchedSchwartzGradientCompletion244 target := by
  let f : ℕ → A3 → SchwartzMap V3 ℝ :=
    fun n j => Ψ n (h3ClassicalizationFinOfAxis j)
  have hEnergy : SchwartzH3DifferenceEnergyCauchy244 f :=
    thirdFullMatchedSchwartz_energyCauchy_of_weighted244
      target V Ψ hV hSecond hThird
  have hZero (n : ℕ) (j : A3) :
      h3SchwartzPoint3Scalar (f n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (V n (h3ClassicalizationFinOfAxis j)) :=
    thirdFullSolenoidalSchwartz_pointwiseDecoderMatch244
      (V n) (Ψ n) (hDecoder n) j
  -- A definition produces data in `Type`: an existential proof in `Prop`
  -- cannot be eliminated by `obtain`. Select the numerical limit classically.
  have hGradientExists :
      ∃ L : ℝ, Tendsto
        (fun n => fullSchwartzGradientTransport244 (f n))
        atTop (𝓝 L) :=
    exists_fullSchwartzGradientTransport_limit_of_H3Energy244
      V f target hV hZero hEnergy
  let L : ℝ := Classical.choose hGradientExists
  have hGradient : Tendsto
      (fun n => fullSchwartzGradientTransport244 (f n))
      atTop (𝓝 L) := Classical.choose_spec hGradientExists
  refine {
    spectral := V
    family := ⟨f, hEnergy⟩
    spectral_tendsto := hV
    zero_exact := hZero
    second_exact := ?_
    third_exact := ?_
    gradientLimit := L
    gradient_tendsto := hGradient
  }
  · intro n j a b
    have h := congrArg h3ToFourierRealL2
      (hSecond n (h3ClassicalizationFinOfAxis j) a b)
    simpa only [f, matchedSpectralSecondFourierJets244,
      h3ToFourierRealL2_h3FromFourierRealL2] using h.symm
  · intro n j a b c
    have h := congrArg h3ToFourierRealL2
      (hThird n (h3ClassicalizationFinOfAxis j) a b c)
    simpa only [f, matchedSpectralThirdFourierJets244,
      h3ToFourierRealL2_h3FromFourierRealL2] using h.symm

/-- For every Fourier-compatible interior Navier–Stokes H³ snapshot,
ONE sequence of actual real solenoidal Schwartz fields simultaneously:
 * converges in weighted H³;
 * has pointwise zero physical divergence;
 * retains the exact Fourier representative;
 * identifies both 27- and 81-slot physical Schwartz energies;
 * converges in the 3–3–1 gradient, 3–2–2 signed and full G₃+3M
   Schwartz functionals to the original OLD physical transport values.

No external Hermitian, solenoidal, Schwartz or nonlinear-limit witness is
assumed; the required spectral properties follow from hNS and hFourier. -/
theorem exists_thirdFullPhysicalSnapshot_solenoidalSchwartzTransportLimits244
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
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ n j,
        (V n j : V3 → ℂ) =ᵐ[volume]
          (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
            𝓕 (h3SchwartzComplexify (Ψ n j)) ξ)) ∧
      (∀ n,
        lowNormalRealSchwartzH3Energy2
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)) =
          weightedH3CanonicalSecondJetEnergy244 (V n)) ∧
      (∀ n,
        lowNormalRealSchwartzH3Energy3
          (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)) =
          weightedH3CanonicalThirdJetEnergy244 (V n)) ∧
      Tendsto (fun n => lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalSecondJetEnergy244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier))) ∧
      Tendsto (fun n => lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (weightedH3CanonicalThirdJetEnergy244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier))) ∧
      Tendsto (fun n => fullSchwartzGradientTransport244
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (thirdOrderGradientTransportSum u t)) ∧
      Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (h3PathCanonicalFirstMonomialAggregateAt u t)) ∧
      Tendsto (fun n => fullSchwartzThirdCommutator244
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have hDiv : H3SpectralFinDivergenceFree U := by
    have h :=
      velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
        hNS htNS hInt
    dsimp only at h
    exact h
  have hReal : H3SpectralVelocityRawHermitian U :=
    velocityH3SpectralStateAt_rawHermitian hFourier
  obtain ⟨V, Ψ, hV, hDivExact, hAE, hDecoder, hSecond, hThird,
      _hDecodedT, _hSecondT, _hThirdT, _hVCauchy⟩ :=
    exists_thirdFullRealSolenoidalSchwartzMatchedH3Jets244 U hDiv hReal
  let F : H3MatchedSchwartzGradientCompletion244 U :=
    thirdFullSolenoidalSchwartzGradientCompletion244
      U V Ψ hV hDecoder hSecond hThird
  -- Use the already-compiled, small, explicit signed witness for
  -- E2/E3 and the signed channel; avoid forcing the enormous gradient
  -- completion's projection reductions merely to expose its family.
  let W : WeightedH3MatchedSchwartzCompletion244 U :=
    thirdFullSolenoidalMatchedCompletion244 U V Ψ hV hSecond hThird
  have hFFamily : F.family.approximants =
      (fun n j => Ψ n (h3ClassicalizationFinOfAxis j)) := by
    rfl
  have hE2 (n : ℕ) :
      lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)) =
        weightedH3CanonicalSecondJetEnergy244 (V n) :=
    weightedH3MatchedSchwartzCompletion_secondEnergy_eq244 U W n
  have hE3 (n : ℕ) :
      lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)) =
        weightedH3CanonicalThirdJetEnergy244 (V n) :=
    weightedH3MatchedSchwartzCompletion_thirdEnergy_eq244 U W n
  have hE2Limit : Tendsto
      (fun n => lowNormalRealSchwartzH3Energy2
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (weightedH3CanonicalSecondJetEnergy244 U)) :=
    weightedH3MatchedSchwartzCompletion_secondEnergy_tendsto244 U W
  have hE3Limit : Tendsto
      (fun n => lowNormalRealSchwartzH3Energy3
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (weightedH3CanonicalThirdJetEnergy244 U)) :=
    weightedH3MatchedSchwartzCompletion_thirdEnergy_tendsto244 U W
  have hGradient : Tendsto
      (fun n => fullSchwartzGradientTransport244
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (thirdOrderGradientTransportSum u t)) := by
    have hCanon := weightedH3CanonicalGradientTransport_tendsto244 U F
    rw [hFFamily] at hCanon
    have hPhysical : thirdOrderGradientTransportSum u t =
        weightedH3CanonicalGradientTransport244 U :=
      h3PhysicalGradient_eq_weightedCanonical244 hNS htNS hFourier
    rw [← hPhysical] at hCanon
    exact hCanon
  have hSigned : Tendsto
      (fun n => lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (h3PathCanonicalFirstMonomialAggregateAt u t)) := by
    have hCanon := weightedH3CanonicalSignedFirstMonomial_tendsto244 U W
    change Tendsto
      (fun n => lowNormalRealSchwartzPoint3Monomial
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (weightedH3CanonicalSignedFirstMonomial244 U)) at hCanon
    have hPhysical : h3PathCanonicalFirstMonomialAggregateAt u t =
        weightedH3CanonicalSignedFirstMonomial244 U :=
      h3PathCanonicalFirstMonomialAggregate_eq_weightedCanonicalSigned244
        hFourier
    rw [← hPhysical] at hCanon
    exact hCanon
  have hFull : Tendsto
      (fun n => fullSchwartzThirdCommutator244
        (fun j : A3 => Ψ n (h3ClassicalizationFinOfAxis j)))
      atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
    have hCanon := h3MatchedSchwartzGradientCompletion_fullThird_tendsto244 U F
    rw [hFFamily] at hCanon
    have hPhysical : velocityH3TransportDerivative3At u t =
        weightedH3CanonicalFullThirdCommutator244 U :=
      h3PhysicalFullThird_eq_weightedCanonical244
        hNS htNS hH3 hClass ht hFourier
    rw [← hPhysical] at hCanon
    exact hCanon
  exact ⟨V, Ψ, hV, hDivExact, hAE, hE2, hE3,
    hE2Limit, hE3Limit, hGradient, hSigned, hFull⟩

end
end PrimeTensor.FirstMonomialTriad
