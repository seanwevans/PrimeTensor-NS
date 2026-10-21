import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRadialVarianceStrict244
import Mathlib.Tactic

/-!
# Quantitative two-band physical Fourier variance

Let S be the nonnegative actual Fourier velocity mass and
w(ξ)=q(ξ)^2, with q(ξ)=(2π)^2|ξ|². Suppose both the lower band
w≤lo and the upper band hi≤w carry at least `mass` of the Fourier
mass, where lo<hi. Then

  E₀ D₃ - E₂² ≥ E₀ · mass · ((hi-lo)/2)².

The proof uses the exact centered Fourier variance identity from
ActualRadialVariance244, rather than a bare strict Cauchy inequality.
The lower bound is CONDITIONAL on the actual band masses; it does not
assert a uniform gap along a Navier--Stokes path.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

noncomputable local instance axisFintypeTwoBandRadialVariance244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceTwoBandRadialVariance244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A spectral band on which the squared centered frequency is bounded
below contributes at least `δ²` times its Fourier mass to the variance.
This lemma does not require the ambient measure to be finite. -/
theorem h3_twoBand_centered_sector_lower244
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S z : α → ℝ) (A : Set α) (δ mass : ℝ)
    (hA : MeasurableSet A)
    (hS : ∀ ξ, 0 ≤ S ξ)
    (hSInt : Integrable S μ)
    (hZInt : Integrable (fun ξ => z ξ ^ 2 * S ξ) μ)
    (hMass : mass ≤ ∫ ξ in A, S ξ ∂μ)
    (hSq : ∀ ξ ∈ A, δ ^ 2 ≤ z ξ ^ 2) :
    δ ^ 2 * mass ≤ ∫ ξ, z ξ ^ 2 * S ξ ∂μ := by
  have hIndInt : Integrable
      (A.indicator (fun ξ => δ ^ 2 * S ξ)) μ :=
    (hSInt.const_mul _).indicator hA
  have hPoint (ξ : α) :
      A.indicator (fun η => δ ^ 2 * S η) ξ ≤
        z ξ ^ 2 * S ξ := by
    by_cases hξ : ξ ∈ A
    · simpa only [Set.indicator_of_mem hξ] using
        mul_le_mul_of_nonneg_right (hSq ξ hξ) (hS ξ)
    · have hBound : 0 ≤ z ξ ^ 2 * S ξ :=
        mul_nonneg (sq_nonneg _) (hS ξ)
      simpa [Set.indicator, hξ] using hBound
  have hIntegral := MeasureTheory.integral_mono hIndInt hZInt hPoint
  calc
    δ ^ 2 * mass ≤ δ ^ 2 * (∫ ξ in A, S ξ ∂μ) :=
      mul_le_mul_of_nonneg_left hMass (sq_nonneg δ)
    _ = ∫ ξ in A, δ ^ 2 * S ξ ∂μ := by rw [integral_const_mul]
    _ = ∫ ξ, A.indicator (fun η => δ ^ 2 * S η) ξ ∂μ :=
      (integral_indicator hA).symm
    _ ≤ ∫ ξ, z ξ ^ 2 * S ξ ∂μ := hIntegral

/-- An elementary but quantitative two-band dispersion theorem for
an arbitrary real nonnegative density, stated without division by mass.
The factor 1/4 comes from comparing the spectral mean with the midpoint
between the separated bands. -/
theorem h3_twoBand_centered_variance_lower244
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S w : α → ℝ) (m0 m2 lo hi mass : ℝ)
    (hS : ∀ ξ, 0 ≤ S ξ)
    (hSInt : Integrable S μ)
    (hWInt : Integrable (fun ξ => (m0 * w ξ - m2) ^ 2 * S ξ) μ)
    (hm0 : 0 < m0) (hGap : lo < hi)
    (hMeasLow : MeasurableSet {ξ | w ξ ≤ lo})
    (hMeasHigh : MeasurableSet {ξ | hi ≤ w ξ})
    (hLowMass : mass ≤ ∫ ξ in {ξ | w ξ ≤ lo}, S ξ ∂μ)
    (hHighMass : mass ≤ ∫ ξ in {ξ | hi ≤ w ξ}, S ξ ∂μ) :
    (m0 * ((hi - lo) / 2)) ^ 2 * mass ≤
      ∫ ξ, (m0 * w ξ - m2) ^ 2 * S ξ ∂μ := by
  let δ : ℝ := m0 * ((hi - lo) / 2)
  have hHalf : 0 < (hi - lo) / 2 := by linarith only [hGap]
  have hδ : 0 ≤ δ := (mul_pos hm0 hHalf).le
  by_cases hMid : m2 ≤ m0 * ((lo + hi) / 2)
  · apply h3_twoBand_centered_sector_lower244 μ S
      (fun ξ => m0 * w ξ - m2) {ξ | hi ≤ w ξ}
      δ mass hMeasHigh hS hSInt hWInt hHighMass
    intro ξ hξ
    have hScaled : m0 * hi ≤ m0 * w ξ :=
      mul_le_mul_of_nonneg_left hξ hm0.le
    have hDev : δ ≤ m0 * w ξ - m2 := by
      dsimp only [δ]
      nlinarith only [hScaled, hMid]
    have hSquare := mul_self_le_mul_self hδ hDev
    nlinarith only [hSquare]
  · have hReverse : m0 * ((lo + hi) / 2) < m2 := lt_of_not_ge hMid
    apply h3_twoBand_centered_sector_lower244 μ S
      (fun ξ => m0 * w ξ - m2) {ξ | w ξ ≤ lo}
      δ mass hMeasLow hS hSInt hWInt hLowMass
    intro ξ hξ
    have hScaled : m0 * w ξ ≤ m0 * lo :=
      mul_le_mul_of_nonneg_left hξ hm0.le
    have hDev : δ ≤ m2 - m0 * w ξ := by
      dsimp only [δ]
      nlinarith only [hScaled, hReverse]
    have hSquare := mul_self_le_mul_self hδ hDev
    nlinarith only [hSquare]

/-- Quantitative separation of TWO actual physical Fourier mass bands.
The masses are literal set integrals of the already-defined spectral
velocity density; they are not additional a priori PDE bounds.

At a time with kinetic mass E₀>0, mass at least `bandMass` both below
`lo` and above `hi`, where lo<hi, forces the physical first Cauchy defect
F₁ to exceed E₀ · bandMass · ((hi-lo)/2)². -/
theorem h3Path_topFourier_twoBandVariance_lower244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
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
        velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume) :
    velocityH3Energy0At u t * ((hi - lo) / 2) ^ 2 * bandMass ≤
      h3PathTopFourierFirstCauchyDefect244 u t := by
  let S : H3FourierPoint3 → ℝ :=
    velocityH3FourierMassDensityAt u t hInt hMeas
  let w : H3FourierPoint3 → ℝ :=
    fun ξ => h3FourierGradientSquare ξ ^ 2
  have hSNonneg : ∀ ξ, 0 ≤ S ξ := by
    intro ξ
    exact velocityH3FourierMassDensityAt_nonneg u t hInt hMeas ξ
  have hSInt : Integrable S volume := by
    dsimp only [S]
    exact velocityH3FourierMassDensityAt_integrable u t hInt hMeas
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt
  have h2Int : Integrable (fun ξ => w ξ * S ξ) volume := by
    dsimp only [w, S]
    exact velocityH3FourierSecondAggregateDensity_integrable
      hInt hMeas hFourier
  have h4Int : Integrable (fun ξ => w ξ ^ 2 * S ξ) volume := by
    have hEq : (fun ξ : H3FourierPoint3 => w ξ ^ 2 * S ξ) =
        (fun ξ => h3FourierGradientSquare ξ ^ 4 *
          velocityH3FourierMassDensityAt u t hInt hMeas ξ) := by
      funext ξ
      dsimp only [w, S]
      ring
    rw [hEq]
    exact h3Path_velocityH3FourierFourthAggregateDensity_integrable
      hH3 hClass ht hInt hMeas hFourier
  have hCenterInt : Integrable (fun ξ =>
      (velocityH3Energy0At u t * w ξ - velocityH3Energy2At u t) ^ 2 * S ξ)
      volume := by
    have hExpand : (fun ξ : H3FourierPoint3 =>
        (velocityH3Energy0At u t * w ξ - velocityH3Energy2At u t) ^ 2 * S ξ) =
      (fun ξ => velocityH3Energy0At u t ^ 2 * (w ξ ^ 2 * S ξ) -
        (2 * velocityH3Energy0At u t * velocityH3Energy2At u t) *
          (w ξ * S ξ) + velocityH3Energy2At u t ^ 2 * S ξ) := by
      funext ξ
      ring
    rw [hExpand]
    exact ((h4Int.const_mul _).sub (h2Int.const_mul _)).add
      (hSInt.const_mul _)
  have hwMeas : Measurable w := by
    dsimp only [w, h3FourierGradientSquare]
    fun_prop
  have hMeasLow : MeasurableSet {ξ | w ξ ≤ lo} :=
    measurableSet_le hwMeas measurable_const
  have hMeasHigh : MeasurableSet {ξ | hi ≤ w ξ} :=
    measurableSet_le measurable_const hwMeas
  have hBands :
      (velocityH3Energy0At u t * ((hi - lo) / 2)) ^ 2 * bandMass ≤
      ∫ ξ, (velocityH3Energy0At u t * w ξ - velocityH3Energy2At u t) ^ 2 * S ξ
        ∂volume := by
    exact h3_twoBand_centered_variance_lower244 volume S w
      (velocityH3Energy0At u t) (velocityH3Energy2At u t) lo hi bandMass
      hSNonneg hSInt hCenterInt hMass hGap
      hMeasLow hMeasHigh (by simpa only [w, S] using hLow)
      (by simpa only [w, S] using hHigh)
  have hVar := h3Path_topFourier_firstCauchyDefect_radialVariance244
    hH3 hClass ht
  have hVarEq :
      (∫ ξ, (velocityH3Energy0At u t * w ξ - velocityH3Energy2At u t) ^ 2 * S ξ
        ∂volume) =
      velocityH3Energy0At u t * h3PathTopFourierFirstCauchyDefect244 u t := by
    simpa only [w, S, hInt, hMeas] using hVar
  have hScaled : velocityH3Energy0At u t *
        (velocityH3Energy0At u t * ((hi - lo) / 2) ^ 2 * bandMass) ≤
      velocityH3Energy0At u t * h3PathTopFourierFirstCauchyDefect244 u t := by
    calc
      _ = (velocityH3Energy0At u t * ((hi - lo) / 2)) ^ 2 * bandMass := by ring
      _ ≤ ∫ ξ, (velocityH3Energy0At u t * w ξ - velocityH3Energy2At u t) ^ 2 * S ξ
        ∂volume := hBands
      _ = velocityH3Energy0At u t * h3PathTopFourierFirstCauchyDefect244 u t := hVarEq
  have hCancelled : velocityH3Energy0At u t *
      ((hi - lo) / 2) ^ 2 * bandMass ≤
      h3PathTopFourierFirstCauchyDefect244 u t :=
    (mul_le_mul_iff_of_pos_left hMass).mp hScaled
  exact hCancelled

/-- A genuinely quantitative improvement of physical sharp Fourier Young
absorption whenever TWO separated frequency bands retain specified mass.
The improvement is explicit, but its band-mass premise is NOT derived
uniformly in time by Navier--Stokes dynamics here. -/
theorem h3Path_topFourier_twoBandYoungGain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
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
        velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume) :
    K * velocityH3Energy3At u t +
      (27 / 256 : ℝ) *
        ((K ^ 4 * (velocityH3Energy0At u t *
          ((hi - lo) / 2) ^ 2 * bandMass)) /
          velocityH3Dissipation3At u t) ≤
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t := by
  have hVar := h3Path_topFourier_twoBandVariance_lower244
    hH3 hClass ht hMass lo hi bandMass hGap hInt hMeas hLow hHigh
  have hSharp := h3Path_topFourier_firstVarianceGain244
    hH3 hClass ht hK hD
  have hNumerator :
      K ^ 4 * (velocityH3Energy0At u t *
        ((hi - lo) / 2) ^ 2 * bandMass) ≤
      K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t :=
    mul_le_mul_of_nonneg_left hVar (pow_nonneg hK 4)
  have hCost :
      (27 / 256 : ℝ) *
        ((K ^ 4 * (velocityH3Energy0At u t *
          ((hi - lo) / 2) ^ 2 * bandMass)) /
          velocityH3Dissipation3At u t) ≤
      (27 / 256 : ℝ) *
        ((K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t) /
          velocityH3Dissipation3At u t) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (div_le_div_iff_of_pos_right hD).2 hNumerator
  linarith only [hSharp, hCost]

end
end PrimeTensor.FirstMonomialTriad
