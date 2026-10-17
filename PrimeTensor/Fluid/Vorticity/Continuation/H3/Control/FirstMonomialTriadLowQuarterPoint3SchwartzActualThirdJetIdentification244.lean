import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSpectralThirdPhysicalJets244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Initial.Decoder

/-!
# Identify all 81 canonical physical cubic jets with the literal old H³ jets

This checkpoint removes an actual representation gap. Previous results
established that weighted spectral H³ convergence entails convergence of all
81 *canonically reconstructed* real physical cubic Fourier-multiplier jets.
For a genuine Fourier-compatible physical H³ snapshot, we now show these
reconstructed states EQUAL the original measured third spatial derivatives
in the exact physical scalar L² carrier, for every ordered (j,a,b,c) slot.

The proof uses only the original Fourier compatibility condition, the exact
weighted/deweighted Fourier encoder round trip, the existing scalar
Plancherel transform, and its inverse. No Schwartz realization of the old
velocity or additional derivative identification is postulated.

The approximants in the final sequence theorem are still weighted spectral
Schwartz representatives. To promote them to real physical Schwartz
approximants with E₂/E₃ convergence, one must independently preserve the
weighted norm under deweighting and physical inverse Fourier realization.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeSchwartzActualThirdJetIdent244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The previously constructed cubic spectral multiplier is exactly the
Fourier L² state of the concrete ordered third velocity derivative, for a
genuine compatible H³ slice. No derivative compatibility is assumed beyond
the existing `VelocityH3FourierCompatibleAt` condition. -/
theorem h3SpectralScalarRawThirdCoordinateFourierL2_actualJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) (a b c : A3) :
    h3SpectralScalarRawThirdCoordinateFourierL2 a b c
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) =
      velocityH3FourierJetAt u t hInt hMeas
        (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
          (h3ClassicalizationFinOfAxis b)
          (h3ClassicalizationFinOfAxis c)) := by
  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt u t hInt hMeas hFourier j
  have hRaw :
      h3SpectralScalarRawFourier G =ᵐ[volume]
        (velocityH3BaseFourierAt u t hInt hMeas j :
          H3FourierPoint3 → ℂ) := by
    have h := h3SpectralScalarRawFourierL2_ae G
    change
      (h3SpectralScalarRawFourierL2
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) :
          H3FourierPoint3 → ℂ) =ᵐ[volume]
        h3SpectralScalarRawFourier G at h
    rw [h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      hFourier j] at h
    exact h.symm
  have hCubic :=
    h3SpectralScalarRawThirdCoordinateFourierL2_ae a b c G
  have hActual :=
    velocityH3FourierCompatibleAt_orderThree hFourier j
      (h3ClassicalizationFinOfAxis a)
      (h3ClassicalizationFinOfAxis b)
      (h3ClassicalizationFinOfAxis c)
  change h3SpectralScalarRawThirdCoordinateFourierL2 a b c G = _
  apply MeasureTheory.Lp.ext
  filter_upwards [hCubic, hRaw, hActual] with ξ hCubicξ hRawξ hActualξ
  rw [hCubicξ, hActualξ, hRawξ]
  simp only [h3FourierDerivativeSymbol3]
  ring

/-- The reconstructed cubic real physical L² field is the *literal*
old physical third-order velocity jet, not just a Fourier-derived proxy. -/
theorem h3SpectralScalarRawThirdCoordinatePhysicalL2_actualJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) (a b c : A3) :
    h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c
        (velocityH3SpectralScalarAt u t hInt hMeas hFourier j) =
      velocityH3L2JetAt u t hInt hMeas
        (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
          (h3ClassicalizationFinOfAxis b)
          (h3ClassicalizationFinOfAxis c)) := by
  unfold h3SpectralScalarRawThirdCoordinatePhysicalL2
  rw [h3SpectralScalarRawThirdCoordinateFourierL2_actualJet244
    hFourier j a b c]
  rw [velocityH3FourierJetAt_apply]
  unfold h3ScalarFourierL2
  rw [(MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm_apply_apply]
  rw [h3RealPartFourierL2_complexify_eq]
  exact h3FromFourierRealL2_h3ToFourierRealL2 _

/-- Every one of the 81 physical real cubic Fourier-jet coordinates agrees
with its literal spatial H³ derivative at the genuine encoded snapshot. -/
theorem h3SpectralVelocityThirdPhysicalJetFamily_actualJet244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3SpectralVelocityThirdPhysicalJetFamily244
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) =
      (fun j : Fin 3 => fun a b c : A3 =>
        velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b)
            (h3ClassicalizationFinOfAxis c))) := by
  funext j a b c
  exact h3SpectralScalarRawThirdCoordinatePhysicalL2_actualJet244
    hFourier j a b c

/-- The ONE already-constructed weighted spectral Schwartz sequence
converges simultaneously to the literal old physical zero-order velocity
and to all 81 literal old physical third-order velocity L² derivatives.
No independently chosen derivative limits or matching assumptions. -/
theorem exists_h3SchwartzSpectralApprox_actualZeroAndPhysicalThird244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℂ,
      Tendsto (fun n => h3SchwartzSpectralVelocityRealization244 (Φ n))
        atTop (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeRealL2
          (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (fun j : Fin 3 =>
          h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas (h3JetSlot0 j)))) ∧
      Tendsto (fun n => h3SpectralVelocityThirdPhysicalJetFamily244
          (h3SchwartzSpectralVelocityRealization244 (Φ n)))
        atTop (𝓝 (fun j : Fin 3 => fun a b c : A3 =>
          velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b)
              (h3ClassicalizationFinOfAxis c)))) := by
  obtain ⟨Φ, hWeighted, hZero, hThird⟩ :=
    exists_h3SchwartzSpectralApprox_actualZeroAndAllThird244 hFourier
  refine ⟨Φ, hWeighted, hZero, ?_⟩
  rw [← h3SpectralVelocityThirdPhysicalJetFamily_actualJet244 hFourier]
  exact hThird

end
end PrimeTensor.FirstMonomialTriad
