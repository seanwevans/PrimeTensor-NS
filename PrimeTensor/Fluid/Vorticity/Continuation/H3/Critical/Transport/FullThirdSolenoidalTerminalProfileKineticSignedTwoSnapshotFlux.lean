import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticMixedSchwartzIntegrability
import Mathlib.Tactic

/-!
# Signed two-snapshot low-maximum sixth-flux transfer

The three-profile Schwartz theorem proves the mixed six-dimensional budget is
integrable. Here the exact trilinear telescope is applied to two Schwartz
fields. The Fourier difference is represented by the DIFFERENCE of the actual
weighted-H3 velocity states, using linearity of the Schwartz Fourier map and
a.e. subtraction of L2 representatives.

Three independently scaled Young bounds control the complex signed difference.
The reciprocal scales are deliberately retained: an unscaled arithmetic-mean
estimate for an outer difference does not yield continuity when that difference
vanishes. No uniform-in-radius or terminal-time estimate is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev TA3 := PrimeTensor.Axis Depth.three
private abbrev TV3 := H3FourierPoint3
private abbrev TPair := TV3 × TV3

noncomputable local instance axisFintypeKineticTwoSnapshot244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Literal signed complex low-maximum integral, with no premature norm or
imaginary-part projection. -/
noncomputable def thirdFullKineticSchwartzSignedLowMaxFluxIntegral244
    (R : ℕ) (v : TA3 → SchwartzMap TV3 ℂ) : ℂ :=
  ∫ z in (thirdFullHighMaxSet244 R)ᶜ,
    thirdFullKineticMixedPolarSixthFlux244
      (thirdFullKineticSchwartzPolarization244 v)
      (thirdFullKineticSchwartzPolarization244 v)
      (thirdFullKineticSchwartzPolarization244 v) z
      ∂volume.prod volume

/-- Retain all three physical weighted-H3 norms and the Young scaling.
The middle input is the one paid for by the genuine Fourier L1 mass. -/
noncomputable def thirdFullKineticTwoSnapshotMixedBound244
    (R : ℕ) (scale first middle last : ℝ) : ℝ :=
  (9 * (2 * ((R : ℝ) + 1)) ^ 7) *
    (((scale ^ 2 * (3 * first ^ 2) +
       scale⁻¹ ^ 2 * (3 * last ^ 2)) / 2) *
     (3 * h3SobolevDeweightingConstant * middle))

/-- Fourier subtraction is the map-sub law of the actual continuous linear
Schwartz Fourier transform, not a lemma `FourierTransform.fourier_sub`. -/
theorem thirdFullKineticSchwartz_fourier_sub_apply244
    (f g : SchwartzMap TV3 ℂ) (ξ : TV3) :
    (𝓕 (f - g)) ξ = (𝓕 f) ξ - (𝓕 g) ξ := by
  have h := congrArg (fun F : SchwartzMap TV3 ℂ => F ξ)
    ((SchwartzMap.fourierTransformCLM ℂ).map_sub f g)
  simpa only [SchwartzMap.fourierTransformCLM_apply,
    sub_apply] using h

/-- A Schwartz difference is represented by the actual L2-subtracted
weighted spectral state. This is an a.e. assertion, never a false pointwise
identity between arbitrary L2 representatives. -/
theorem thirdFullKineticWeightedSchwartz_difference_rep244
    (v w : TA3 → SchwartzMap TV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : TA3,
      (V (h3ClassicalizationFinOfAxis j) : TV3 → ℂ) =ᵐ[volume]
        (fun ξ : TV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : TA3,
      (W (h3ClassicalizationFinOfAxis j) : TV3 → ℂ) =ᵐ[volume]
        (fun ξ : TV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ)) :
    ∀ j : TA3,
      ((V - W) (h3ClassicalizationFinOfAxis j) : TV3 → ℂ) =ᵐ[volume]
        (fun ξ : TV3 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j - w j)) ξ) := by
  intro j
  let k := h3ClassicalizationFinOfAxis j
  have hSub := MeasureTheory.Lp.coeFn_sub (V k) (W k)
  filter_upwards [hSub, hv j, hw j] with ξ hs hvξ hwξ
  change ((V k - W k : H3SpectralScalarState) : TV3 → ℂ) ξ =
    (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j - w j)) ξ
  rw [hs, Pi.sub_apply]
  change
    ((V (h3ClassicalizationFinOfAxis j) : TV3 → ℂ) ξ -
      (W (h3ClassicalizationFinOfAxis j) : TV3 → ℂ) ξ) =
      (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j - w j)) ξ
  rw [hvξ, hwξ, thirdFullKineticSchwartz_fourier_sub_apply244]
  ring

/-- Exact identification of the telescope's raw complex difference with a
THIRD genuine Schwartz Fourier polarization. -/
theorem thirdFullKineticSchwartzPolarization_sub_apply244
    (v w : TA3 → SchwartzMap TV3 ℂ) (ξ : TV3) (j : TA3) :
    thirdFullKineticSchwartzPolarization244 (fun i => v i - w i) ξ j =
      thirdFullKineticSchwartzPolarization244 v ξ j -
      thirdFullKineticSchwartzPolarization244 w ξ j := by
  simpa only [thirdFullKineticSchwartzPolarization244,
    h3SchwartzTriadPolarization, WithLp.toLp_ofLp] using
    (thirdFullKineticSchwartz_fourier_sub_apply244 (v j) (w j) ξ)

/-- The signed low-maximum complex Fourier flux has an actual TWO-SNAPSHOT
weighted-H3 difference bound. The three mixed terms have distinct positions
for the difference, and each Young scale can be optimized independently.

The first and third terms REQUIRE reciprocal scales; choosing all three
scales equal to one would not in itself give a continuity modulus. -/
theorem thirdFullKinetic_lowMax_twoSnapshot_signedFlux_scaled244
    (R : ℕ)
    (v w : TA3 → SchwartzMap TV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : TA3,
      (V (h3ClassicalizationFinOfAxis j) : TV3 → ℂ) =ᵐ[volume]
        (fun ξ : TV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : TA3,
      (W (h3ClassicalizationFinOfAxis j) : TV3 → ℂ) =ᵐ[volume]
        (fun ξ : TV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (s₁ s₂ s₃ : ℝ)
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hs₃ : 0 < s₃) :
    ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
      thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
      (thirdFullKineticTwoSnapshotMixedBound244 R s₁
        ‖V - W‖ ‖V‖ ‖V‖ +
       thirdFullKineticTwoSnapshotMixedBound244 R s₂
        ‖W‖ ‖V - W‖ ‖V‖) +
      thirdFullKineticTwoSnapshotMixedBound244 R s₃
        ‖W‖ ‖W‖ ‖V - W‖ := by
  let d : TA3 → SchwartzMap TV3 ℂ := fun j => v j - w j
  let P := thirdFullKineticSchwartzPolarization244 v
  let Q := thirdFullKineticSchwartzPolarization244 w
  let D := thirdFullKineticSchwartzPolarization244 d
  let S : Set TPair := (thirdFullHighMaxSet244 R)ᶜ
  let μ : Measure TPair := volume.prod volume
  have hPolar : D = (fun ξ j => P ξ j - Q ξ j) := by
    funext ξ j
    exact thirdFullKineticSchwartzPolarization_sub_apply244 v w ξ j
  have hd : ∀ j : TA3,
      ((V - W) (h3ClassicalizationFinOfAxis j) : TV3 → ℂ) =ᵐ[volume]
        (fun ξ : TV3 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (d j)) ξ) :=
    thirdFullKineticWeightedSchwartz_difference_rep244 v w V W hv hw
  have hp : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244 P P P) S μ :=
    thirdFullKinetic_lowMax_mixedSchwartzFlux_integrable244 R v v v
  have hq : IntegrableOn (thirdFullKineticMixedPolarSixthFlux244 Q Q Q) S μ :=
    thirdFullKinetic_lowMax_mixedSchwartzFlux_integrable244 R w w w
  have h1 : IntegrableOn
      (thirdFullKineticMixedPolarSixthFlux244
        (fun ξ j => P ξ j - Q ξ j) P P) S μ := by
    rw [← hPolar]
    exact thirdFullKinetic_lowMax_mixedSchwartzFlux_integrable244 R d v v
  have h2 : IntegrableOn
      (thirdFullKineticMixedPolarSixthFlux244
        Q (fun ξ j => P ξ j - Q ξ j) P) S μ := by
    rw [← hPolar]
    exact thirdFullKinetic_lowMax_mixedSchwartzFlux_integrable244 R w d v
  have h3 : IntegrableOn
      (thirdFullKineticMixedPolarSixthFlux244
        Q Q (fun ξ j => P ξ j - Q ξ j)) S μ := by
    rw [← hPolar]
    exact thirdFullKinetic_lowMax_mixedSchwartzFlux_integrable244 R w w d
  let B₁ : ℝ := ∫ z in S,
    ‖thirdFullKineticMixedPolarSixthFlux244
      (fun ξ j => P ξ j - Q ξ j) P P z‖ ∂μ
  let B₂ : ℝ := ∫ z in S,
    ‖thirdFullKineticMixedPolarSixthFlux244
      Q (fun ξ j => P ξ j - Q ξ j) P z‖ ∂μ
  let B₃ : ℝ := ∫ z in S,
    ‖thirdFullKineticMixedPolarSixthFlux244
      Q Q (fun ξ j => P ξ j - Q ξ j) z‖ ∂μ
  have hb1 : B₁ ≤ thirdFullKineticTwoSnapshotMixedBound244 R s₁
        ‖V - W‖ ‖V‖ ‖V‖ := by
    dsimp only [B₁]
    rw [← hPolar]
    exact thirdFullKinetic_lowMax_mixedSchwartzFlux_autoWeightedH3_244
      R d v v (V - W) V V hd hv hv s₁ hs₁
  have hb2 : B₂ ≤ thirdFullKineticTwoSnapshotMixedBound244 R s₂
        ‖W‖ ‖V - W‖ ‖V‖ := by
    dsimp only [B₂]
    rw [← hPolar]
    exact thirdFullKinetic_lowMax_mixedSchwartzFlux_autoWeightedH3_244
      R w d v W (V - W) V hw hd hv s₂ hs₂
  have hb3 : B₃ ≤ thirdFullKineticTwoSnapshotMixedBound244 R s₃
        ‖W‖ ‖W‖ ‖V - W‖ := by
    dsimp only [B₃]
    rw [← hPolar]
    exact thirdFullKinetic_lowMax_mixedSchwartzFlux_autoWeightedH3_244
      R w w d W W (V - W) hw hw hd s₃ hs₃
  have hTelescope := thirdFullKinetic_lowMax_integralDifferenceBudget244
    R P Q hp hq h1 h2 h3
  change ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
      thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
    (B₁ + B₂) + B₃ at hTelescope
  exact hTelescope.trans (add_le_add (add_le_add hb1 hb2) hb3)

end
end PrimeTensor.FirstMonomialTriad
