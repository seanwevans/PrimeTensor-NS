import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxOneSidedGapBridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticArbitraryRadialFluxTradeoff
import Mathlib.Tactic

/-!
# Adverse physical top-third transport: genuine LowMax Schwartz recovery

The previously proved arbitrary-radius signed-flux alternative discarded the
exact weighted-Fourier representatives and their strong H3 convergence after
using them in its proof. Here we retain both at the selected adverse physical
snapshot. This is the actual bridge between the PHYSICAL top-order transport
witness and the one-sided native signed LowMax flux used by the gap theorem.

The alternative is quantitative: the physical high-radial tail may pay a
quadratic cutoff-dependent amount, or a real-solenoidal Schwartz recovery
has negative signed LowMax flux, exact Fourier realization, and arbitrarily
small H3 approximation error. No common time-dependent Schwartz choice,
terminal-uniform cutoff, or terminal-uniform H3 bound is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private abbrev RA3 := PrimeTensor.Axis Depth.three
private abbrev RV3 := H3FourierPoint3
private abbrev RP3 := RV3 × RV3

noncomputable local instance axisFintypeSignedPhysicalRecovery244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual adverse physical third-derivative transport yields either the
quadratic physical high-radial H3 tail at any prescribed R, or an exactly
solenoidal Schwartz state with genuine weighted Fourier representation,
strictly negative signed LowMax flux, and arbitrary spectral recovery error.
The physical sixth-flux normalization ((2π)^7/3) is retained on both arms. -/
theorem thirdFullPhysical_adverseThird_signedLowMax_recoveredOrTail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R : ℕ) (eta gamma epsilon : ℝ)
    (hEta : 0 < eta) (hGamma : 0 < gamma) (hEpsilon : 0 < epsilon)
    (hAdverse : eta < -velocityH3TransportDerivative3At u t) :
    (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u t + 1) *
        (‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ + gamma) ^ 2)) ∨
    ∃ (p : RA3 → SchwartzMap RV3 ℂ)
      (V : H3SpectralVelocityState),
      (∀ j : RA3,
        (V (h3ClassicalizationFinOfAxis j) : RV3 → ℂ) =ᵐ[volume]
          (fun ξ : RV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (p j)) ξ)) ∧
      (∀ ξ : RV3, ∑ j : RA3,
        fderiv ℝ (p j) ξ (h3FourierAxisDirection j) = 0) ∧
      ‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ < epsilon ∧
      eta / 2 < -(((2 * Real.pi) ^ 7 / 3) *
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R p).im) := by
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS hInt
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hUeq : U = velocityH3SpectralStateAt u t hInt hMeas hFourier := by
    dsimp only [U]
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t htNS]
    rfl
  obtain ⟨V, Psi, hVraw, hAE, hDiv, _hDefect, _hE₂, _hE₃, hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
      hH3.navier_stokes htNS hH3 hClass ht hFourier
  have hV : Tendsto V atTop (𝓝 U) := by
    rw [hUeq]
    exact hVraw
  let E : ℝ := velocityH3EnergyAt u t
  let K : ℝ := E + 1
  let A : ℝ := (2 * Real.pi) ^ 7 / 3
  let B : ℝ := 1944 * h3SobolevFirstMomentDeweightingConstant * K
  let Tail : ℝ :=
    ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ + gamma
  let Charge : ℝ := A * (B * Tail ^ 2)
  have hEnergy : 1 ≤ E := one_le_velocityH3EnergyAt u t
  have hK : 0 ≤ K := by dsimp only [K]; linarith only [hEnergy]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity [h3SobolevFirstMomentDeweightingConstant_nonneg]
  have hU : ‖U‖ ≤ E := by
    rw [hUeq]
    exact norm_velocityH3SpectralStateAt_le_energyCeiling
      hFourier hEnergy le_rfl
  have hDiff : Tendsto (fun n : ℕ => ‖V n - U‖)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hV
  have hNearNorm : ∀ᶠ n : ℕ in atTop, ‖V n - U‖ < 1 :=
    hDiff.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hNearTail : ∀ᶠ n : ℕ in atTop, ‖V n - U‖ < gamma :=
    hDiff.eventually (eventually_lt_nhds hGamma)
  have hNearRecovery : ∀ᶠ n : ℕ in atTop, ‖V n - U‖ < epsilon :=
    hDiff.eventually (eventually_lt_nhds hEpsilon)
  have hThreshold : velocityH3TransportDerivative3At u t < -eta := by
    linarith only [hAdverse]
  have hFullLate : ∀ᶠ n : ℕ in atTop,
      A * (∫ z : RP3,
        thirdFullSchwartzComplexSixthPowerFlux244
          (fun j : RA3 => h3SchwartzComplexify
            (Psi n (h3ClassicalizationFinOfAxis j))) z
        ∂volume.prod volume).im < -eta := by
    have hEvent := hFlux.eventually (Iio_mem_nhds hThreshold)
    simpa only [A] using hEvent
  by_cases hLarge : eta / 2 < Charge
  · left
    simpa only [Charge, A, B, K, E, Tail, U] using hLarge
  · right
    have hSmall : Charge ≤ eta / 2 := le_of_not_gt hLarge
    obtain ⟨n, hnNorm, hnTail, hnRecovery, hnFull⟩ :=
      (hNearNorm.and (hNearTail.and
        (hNearRecovery.and hFullLate))).exists
    let p : RA3 → SchwartzMap RV3 ℂ :=
      fun j => h3SchwartzComplexify (Psi n (h3ClassicalizationFinOfAxis j))
    have hRep : ∀ j : RA3,
        (V n (h3ClassicalizationFinOfAxis j) : RV3 → ℂ) =ᵐ[volume]
          (fun ξ : RV3 => (h3SobolevFrequencyWeight ξ : ℂ) *
            (𝓕 (p j)) ξ) := by
      intro j
      exact hAE n (h3ClassicalizationFinOfAxis j)
    have hSol : ∀ ξ : RV3, ∑ j : RA3,
        fderiv ℝ (p j) ξ (h3FourierAxisDirection j) = 0 := by
      intro ξ
      exact hDiv n ξ
    have hVNorm : ‖V n‖ ≤ K := by
      have hTriangle : ‖V n‖ ≤ ‖V n - U‖ + ‖U‖ := by
        calc
          ‖V n‖ = ‖(V n - U) + U‖ := by rw [sub_add_cancel]
          _ ≤ ‖V n - U‖ + ‖U‖ := norm_add_le _ _
      dsimp only [K]
      linarith only [hTriangle, hnNorm, hU]
    have hTailBound :
        ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ≤
          ‖V n - U‖ +
            ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ := by
      calc
        ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ =
            ‖thirdFullSpectralVelocityHighRadialApply244 R ((V n - U) + U)‖ := by
              rw [sub_add_cancel]
        _ = ‖thirdFullSpectralVelocityHighRadialApply244 R (V n - U) +
            thirdFullSpectralVelocityHighRadialApply244 R U‖ := by
              rw [thirdFullSpectralVelocityHighRadialApply_add244]
        _ ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R (V n - U)‖ +
            ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ := norm_add_le _ _
        _ ≤ ‖V n - U‖ +
            ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ :=
          add_le_add
            (thirdFullSpectralVelocityHighRadialApply_norm_le244 R (V n - U))
            le_rfl
    have hTailLt :
        ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ < Tail := by
      dsimp only [Tail]
      linarith only [hTailBound, hnTail]
    have hTailSq :
        ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ^ 2 ≤
          Tail ^ 2 :=
      pow_le_pow_left₀
        (norm_nonneg (thirdFullSpectralVelocityHighRadialApply244 R (V n)))
        hTailLt.le 2
    have hGlobal := thirdFullWeightedSchwartz_highMaxIntegral_le244
      p (hSol) (V n) hRep K hK hVNorm R
    let HI : ℂ := ∫ z in thirdFullHighMaxSet244 R,
      thirdFullSchwartzComplexSixthPowerFlux244 p z ∂volume.prod volume
    let LO : ℂ := ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      thirdFullSchwartzComplexSixthPowerFlux244 p z ∂volume.prod volume
    have hHigh : ‖HI‖ ≤ B * Tail ^ 2 := by
      have hFirst : ‖HI‖ ≤ B *
          ‖thirdFullSpectralVelocityHighRadialApply244 R (V n)‖ ^ 2 :=
        hGlobal
      exact hFirst.trans (mul_le_mul_of_nonneg_left hTailSq hB)
    have hImLow : -‖HI‖ ≤ HI.im := by
      have hAbs := Complex.abs_im_le_norm HI
      have hNeg := neg_abs_le HI.im
      linarith only [hAbs, hNeg]
    have hImLowA : -(A * ‖HI‖) ≤ A * HI.im := by
      have h := mul_le_mul_of_nonneg_left hImLow hA
      linarith only [h]
    have hHighA : A * ‖HI‖ ≤ Charge := by
      dsimp only [Charge]
      exact mul_le_mul_of_nonneg_left hHigh hA
    have hSplit := thirdFullSchwartzSixthPowerFlux_setSplit244
      p hSol (thirdFullHighMaxSet244 R)
        (thirdFullHighMaxSet_measurable244 R)
    have hImEq :
        A * (∫ z : RP3,
          thirdFullSchwartzComplexSixthPowerFlux244 p z
            ∂volume.prod volume).im = A * HI.im + A * LO.im := by
      rw [hSplit, Complex.add_im]
      dsimp only [HI, LO]
      ring
    have hPhi : thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R p = LO := by
      unfold thirdFullKineticSchwartzSignedLowMaxFluxIntegral244
      apply setIntegral_congr_ae (thirdFullHighMaxSet_measurable244 R).compl
      exact Filter.Eventually.of_forall (fun z _ =>
        thirdFullKineticMixedPolarSixthFlux_schwartz244 p z)
    have hSigned : eta / 2 < -(A * LO.im) := by
      have hnFull' : A * (∫ z : RP3,
          thirdFullSchwartzComplexSixthPowerFlux244 p z
            ∂volume.prod volume).im < -eta := by
        simpa only [p] using hnFull
      linarith only [hnFull', hImEq, hImLowA, hHighA, hSmall]
    refine ⟨p, V n, hRep, hSol, ?_, ?_⟩
    · simpa only [U] using hnRecovery
    · simpa only [hPhi, A] using hSigned

/-- Convert the adverse physical signed top-third margin into the exact
unscaled native LowMax imaginary flux margin, retaining its Fourier factor. -/
noncomputable def thirdFullKineticSignedLowMaxPhysicalMargin244
    (eta : ℝ) : ℝ :=
  (eta / 2) / ((2 * Real.pi) ^ 7 / 3)

theorem thirdFullKineticSignedLowMaxPhysicalMargin_pos244
    (eta : ℝ) (hEta : 0 < eta) :
    0 < thirdFullKineticSignedLowMaxPhysicalMargin244 eta := by
  unfold thirdFullKineticSignedLowMaxPhysicalMargin244
  positivity

/-- The actual adverse physical H3 transport witness, at an ORIGINAL closed
kinetic-gap observation time t, feeds the one-sided signed flux theorem
without assuming an adverse two-snapshot Schwartz jump. The earlier reference
profile q is still explicit, so its baseline remains a genuine alternative.
The recovery state V is selected from the physical solenoidal approximation,
not postulated with a missing Fourier-realization assumption. -/
theorem thirdFullPhysical_strictGap_adverseThird_tailOrBaselineClockCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (q : RA3 → SchwartzMap RV3 ℂ) (W : H3SpectralVelocityState)
    (hq : ∀ j : RA3,
      (W (h3ClassicalizationFinOfAxis j) : RV3 → ℂ) =ᵐ[volume]
        (fun ξ : RV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (q j)) ξ))
    (eta gamma epsilon : ℝ)
    (hEta : 0 < eta) (hGamma : 0 < gamma) (hEpsilon : 0 < epsilon)
    (hAdverse : eta < -velocityH3TransportDerivative3At u t) :
    (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u t + 1) *
        (‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ + gamma) ^ 2)) ∨
    ∃ (p : RA3 → SchwartzMap RV3 ℂ) (V : H3SpectralVelocityState),
      (∀ j : RA3,
        (V (h3ClassicalizationFinOfAxis j) : RV3 → ℂ) =ᵐ[volume]
          (fun ξ : RV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (p j)) ξ)) ∧
      (∀ ξ : RV3, ∑ j : RA3,
        fderiv ℝ (p j) ξ (h3FourierAxisDirection j) = 0) ∧
      ‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ < epsilon ∧
      ((thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 2 ≤
        |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q).im|) ∨
       (thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 4 <
         thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
          (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
            thirdFullFiniteBandH3WeightCeiling244 R *
              (∫ r in x..y,
                ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
            ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖)) ∨
       (∃ z width : ℝ, (z = t ∨ z = s) ∧ 0 < width ∧
         ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
         width * (thirdFullKineticSignedLowMaxPDEViscousHeight244
           R V W (thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 2) / 4) ≤
           ∫ r in x..y, velocityH3DissipationAt u r ∂volume)) := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le (lt_trans hb.1 hx.1) ht.1,
      lt_of_le_of_lt ht.2 hy.2⟩
  obtain hTail | ⟨p, V, hp, hSol, hNear, hSigned⟩ :=
    thirdFullPhysical_adverseThird_signedLowMax_recoveredOrTail244
      hH3 hClass htClass R eta gamma epsilon
      hEta hGamma hEpsilon hAdverse
  · exact Or.inl hTail
  · right
    have hCoeff : 0 < ((2 * Real.pi) ^ 7 / 3) := by positivity
    have hMu : 0 < thirdFullKineticSignedLowMaxPhysicalMargin244 eta :=
      thirdFullKineticSignedLowMaxPhysicalMargin_pos244 eta hEta
    have hOne : thirdFullKineticSignedLowMaxPhysicalMargin244 eta ≤
        |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R p).im| := by
      have hBound := thirdFull_scalar_negativeWeightedSignedFlux_to_oneSided244
        ((2 * Real.pi) ^ 7 / 3) (eta / 2)
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R p).im
        hCoeff hSigned.le
      simpa only [thirdFullKineticSignedLowMaxPhysicalMargin244] using hBound
    have hAlt :=
      thirdFullPhysical_strictGap_signedLowMax_oneSidedBaselineOrClockOrCost244
        hH3 hClass hDInt b hb R x y hx hy hxy
        s t hs ht p q V W hp hq
        (thirdFullKineticSignedLowMaxPhysicalMargin244 eta) hMu hOne
    exact ⟨p, V, hp, hSol, hNear, hAlt⟩

end
end PrimeTensor.FirstMonomialTriad
