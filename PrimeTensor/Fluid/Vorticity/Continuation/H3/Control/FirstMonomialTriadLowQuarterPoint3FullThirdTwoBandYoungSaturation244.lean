import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdTwoBandRadialVariance244
import Mathlib.Tactic

/-!
# Sharp H³ Young near-saturation forces two-band spectral mass collapse

The actual Fourier variance bound from TwoBandRadialVariance244 and the
first-Cauchy contribution to the exact sharp Young defect jointly imply:

  27 K⁴ E₀ ((hi-lo)/2)² m  ≤ 256 D₃ δ

whenever the optimal Young gap

  Δ = D₃ + (27/256) K⁴ E₀ - K E₃

is at most δ, D₃>0, and m is no greater than the actual Fourier mass in
B_low = {ξ | q(ξ)² ≤ lo} and B_high = {ξ | hi ≤ q(ξ)²}.

By taking m equal to the MINIMUM of these two physical masses we obtain
an effective spectral concentration restriction. When K,E₀,hi-lo>0 it
becomes an explicit upper bound on that minimum:

  min(M_low,M_high) ≤ 256 D₃ δ / (27 K⁴ E₀ ((hi-lo)/2)²).

These are *necessary* consequences of sharp-Young near-saturation, not
claims of dynamical near-saturation, spectral spreading, or continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

noncomputable local instance axisFintypeTwoBandYoungSaturation244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceTwoBandYoungSaturation244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Algebraic concentration lemma: a two-band variance floor, the exact
first-Cauchy Young budget, and an upper bound on the Young gap imply an
explicit division-free restriction on the band mass. -/
theorem h3_twoBand_nearYoung_massBudget244
    {K E0 F D x δ width m : ℝ}
    (_hK : 0 ≤ K) (hD : 0 < D)
    (hBand : E0 * width ^ 2 * m ≤ F)
    (hFirst : 27 * K ^ 4 * F * D ^ 2 ≤
      256 * D ^ 3 * (D + (27 / 256 : ℝ) * K ^ 4 * E0 - x))
    (hNear : D + (27 / 256 : ℝ) * K ^ 4 * E0 - x ≤ δ) :
    27 * K ^ 4 * E0 * width ^ 2 * m ≤ 256 * D * δ := by
  have hFactor : 0 ≤ (27 : ℝ) * K ^ 4 * D ^ 2 := by
    positivity
  have hScaled := mul_le_mul_of_nonneg_left hBand hFactor
  have hD3 : 0 ≤ (256 : ℝ) * D ^ 3 := by
    positivity
  have hNearScaled := mul_le_mul_of_nonneg_left hNear hD3
  have hWithD2 :
      (27 * K ^ 4 * E0 * width ^ 2 * m) * D ^ 2 ≤
        (256 * D * δ) * D ^ 2 := by
    calc
      _ = (27 * K ^ 4 * D ^ 2) * (E0 * width ^ 2 * m) := by ring
      _ ≤ (27 * K ^ 4 * D ^ 2) * F := hScaled
      _ = 27 * K ^ 4 * F * D ^ 2 := by ring
      _ ≤ 256 * D ^ 3 * (D + (27 / 256 : ℝ) * K ^ 4 * E0 - x) := hFirst
      _ ≤ 256 * D ^ 3 * δ := hNearScaled
      _ = (256 * D * δ) * D ^ 2 := by ring
  exact (mul_le_mul_iff_of_pos_right (pow_pos hD 2)).mp hWithD2

/-- The real Young-gap value, rather than an abstract fourth-power bound,
limits any candidate mass common to two disjoint physical Fourier bands.
No positivity assumption on the candidate mass is required. -/
theorem h3Path_topFourier_nearYoung_twoBandMassBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hK : 0 ≤ K) (hD : 0 < velocityH3Dissipation3At u t)
    (lo hi bandMass : ℝ) (hGap : lo < hi)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hLow : bandMass ≤
      ∫ ξ in {ξ : H3FourierPoint3 |
        h3FourierGradientSquare ξ ^ 2 ≤ lo},
        velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume)
    (hHigh : bandMass ≤
      ∫ ξ in {ξ : H3FourierPoint3 |
        hi ≤ h3FourierGradientSquare ξ ^ 2},
        velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
        K * velocityH3Energy3At u t ≤ δ) :
    27 * K ^ 4 * velocityH3Energy0At u t *
        ((hi - lo) / 2) ^ 2 * bandMass ≤
      256 * velocityH3Dissipation3At u t * δ := by
  have hBand := h3Path_topFourier_twoBandVariance_lower244
    hH3 hClass ht hMass lo hi bandMass hGap hInt hMeas hLow hHigh
  have hFirst := h3Path_sharpTopYoung_firstCauchy_le_gap244
    hH3 hClass ht hK
  exact h3_twoBand_nearYoung_massBudget244 hK hD hBand
    (by simpa only [mul_assoc] using hFirst)
    (by simpa only [mul_assoc] using hNear)

/-- Near Young-saturation quantitatively depletes at least one of the two
separated actual Fourier bands. The smaller band mass is bounded by the
normalized Young gap, with no hidden frequency-spread assumption. -/
theorem h3Path_topFourier_nearYoung_minBandMass_upper244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hK : 0 < K) (hD : 0 < velocityH3Dissipation3At u t)
    (lo hi : ℝ) (hGap : lo < hi)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
        K * velocityH3Energy3At u t ≤ δ) :
    min
      (∫ ξ in {ξ : H3FourierPoint3 |
        h3FourierGradientSquare ξ ^ 2 ≤ lo},
        velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume)
      (∫ ξ in {ξ : H3FourierPoint3 |
        hi ≤ h3FourierGradientSquare ξ ^ 2},
        velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume) ≤
      (256 * velocityH3Dissipation3At u t * δ) /
        (27 * K ^ 4 * velocityH3Energy0At u t * ((hi - lo) / 2) ^ 2) := by
  let lowMass : ℝ :=
    ∫ ξ in {ξ : H3FourierPoint3 |
      h3FourierGradientSquare ξ ^ 2 ≤ lo},
      velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume
  let highMass : ℝ :=
    ∫ ξ in {ξ : H3FourierPoint3 |
      hi ≤ h3FourierGradientSquare ξ ^ 2},
      velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume
  let m : ℝ := min lowMass highMass
  have hBound :
      27 * K ^ 4 * velocityH3Energy0At u t * ((hi - lo) / 2) ^ 2 * m ≤
        256 * velocityH3Dissipation3At u t * δ := by
    exact h3Path_topFourier_nearYoung_twoBandMassBudget244
      hH3 hClass ht hMass hK.le hD lo hi m hGap hInt hMeas
      (min_le_left _ _) (min_le_right _ _) hNear
  have hHalf : 0 < (hi - lo) / 2 := by
    linarith only [hGap]
  have hWeight : 0 < 27 * K ^ 4 * velocityH3Energy0At u t *
      ((hi - lo) / 2) ^ 2 := by positivity
  have hQuot : m ≤
      (256 * velocityH3Dissipation3At u t * δ) /
        (27 * K ^ 4 * velocityH3Energy0At u t * ((hi - lo) / 2) ^ 2) := by
    apply (le_div_iff₀ hWeight).2
    calc
      m * (27 * K ^ 4 * velocityH3Energy0At u t *
          ((hi - lo) / 2) ^ 2) =
        27 * K ^ 4 * velocityH3Energy0At u t *
          ((hi - lo) / 2) ^ 2 * m := by ring
      _ ≤ 256 * velocityH3Dissipation3At u t * δ := hBound
  exact hQuot

/-- Specialize the quantitative two-band concentration bound to the
actual physical Landau top-order coefficient `4398 C₁ sqrt(E)`. The
positive coefficient follows from the established strict positivity of
`C₁` and `E≥1`; no sign assumption on the physical H³ third-order
transport is inserted. -/
theorem h3Path_topLandau_nearYoung_minBandMass_upper244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t)
    (lo hi : ℝ) (hGap : lo < hi)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
        velocityH3Energy0At u t -
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) *
        velocityH3Energy3At u t ≤ δ) :
    min
      (∫ ξ in {ξ : H3FourierPoint3 |
        h3FourierGradientSquare ξ ^ 2 ≤ lo},
        velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume)
      (∫ ξ in {ξ : H3FourierPoint3 |
        hi ≤ h3FourierGradientSquare ξ ^ 2},
        velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume) ≤
      (256 * velocityH3Dissipation3At u t * δ) /
        (27 * (4398 *
          (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
          velocityH3Energy0At u t * ((hi - lo) / 2) ^ 2) := by
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hK : 0 < 4398 *
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
    exact mul_pos (by norm_num)
      (mul_pos h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
        (Real.sqrt_pos.2 hEpos))
  exact h3Path_topFourier_nearYoung_minBandMass_upper244
    hH3 hClass ht hMass hK hD lo hi hGap hInt hMeas hNear

end
end PrimeTensor.FirstMonomialTriad
