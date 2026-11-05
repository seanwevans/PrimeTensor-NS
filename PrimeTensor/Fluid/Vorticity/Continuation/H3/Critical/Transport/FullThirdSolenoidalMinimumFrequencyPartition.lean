import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalOuterMinimumH3Budget
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Disjoint minimum-frequency partition of the genuine complex H³ flux

On the conserving Fourier momentum plane `(p,q,r)=(z.1,-(z.1+z.2),z.2)`,
assign each triple to its smallest Euclidean frequency, with deterministic
rules at ties:

* First: `|p| ≤ |q|` and `|p| ≤ |r|`.
* Middle: `|q| < |p|` and `|q| ≤ |r|`.
* Last: `|r| < |p|` and `|r| < |q|`.

The three sets are genuinely disjoint, measurable, and cover the whole plane.
The exact complex flux integral splits into three integrals. Applying the
three *previously proved* low-frequency sector inequalities yields

  ‖ ∫ F₆ ‖ ≤ 216 M₆ M₁,

where `M₆ = ∫ |ξ|⁶ |û(ξ)|²`, `M₁ = ∫ |ξ| |û(ξ)|`. For any genuine
weighted H³ Schwartz representatives with three coordinate norms ≤ K,

  ‖ ∫ F₆ ‖ ≤ 1944 C₁ K³.

The SAME physical solenoidal Schwartz recovery yields this bound uniformly
in approximation index at each fixed interior time, retaining the actual
signed physical H³ transport limit.

This bound is weaker numerically than an older global raw-mass budget; its
content is the *exact frequency-resolved partition*, with a derivative on
the smallest frequency and three on each larger one. No endpoint-time
uniformity, sign, coercivity, or global regularity follows from the split.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev PairV := V3 × V3

noncomputable local instance axisFintypeMinimumFrequencyPartition244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Tie-breaking gives the FIRST Fourier input priority at equal radii. -/
def thirdFullMinFirstSector244 : Set PairV :=
  {z | ‖z.1‖ ≤ ‖-(z.1 + z.2)‖ ∧ ‖z.1‖ ≤ ‖z.2‖}

/-- The MIDDLE input takes ties with the last input, but not with first. -/
def thirdFullMinMiddleSector244 : Set PairV :=
  {z | ‖-(z.1 + z.2)‖ < ‖z.1‖ ∧
    ‖-(z.1 + z.2)‖ ≤ ‖z.2‖}

/-- The LAST input takes precisely the remaining strict minimum. -/
def thirdFullMinLastSector244 : Set PairV :=
  {z | ‖z.2‖ < ‖z.1‖ ∧ ‖z.2‖ < ‖-(z.1 + z.2)‖}

/-- Measurability of the actual first-minimum region, including ties. -/
theorem thirdFullMinFirstSector_measurable244 :
    MeasurableSet thirdFullMinFirstSector244 := by
  have hP : Continuous (fun z : PairV => ‖z.1‖) := continuous_fst.norm
  have hQ : Continuous (fun z : PairV => ‖-(z.1 + z.2)‖) :=
    (continuous_fst.add continuous_snd).neg.norm
  have hR : Continuous (fun z : PairV => ‖z.2‖) := continuous_snd.norm
  exact (isClosed_le hP hQ).measurableSet.inter
    (isClosed_le hP hR).measurableSet

/-- Measurability of the strict/weak middle-minimum region. -/
theorem thirdFullMinMiddleSector_measurable244 :
    MeasurableSet thirdFullMinMiddleSector244 := by
  have hP : Continuous (fun z : PairV => ‖z.1‖) := continuous_fst.norm
  have hQ : Continuous (fun z : PairV => ‖-(z.1 + z.2)‖) :=
    (continuous_fst.add continuous_snd).neg.norm
  have hR : Continuous (fun z : PairV => ‖z.2‖) := continuous_snd.norm
  exact (isOpen_lt hQ hP).measurableSet.inter
    (isClosed_le hQ hR).measurableSet

/-- Measurability of the strictly smallest last-frequency region. -/
theorem thirdFullMinLastSector_measurable244 :
    MeasurableSet thirdFullMinLastSector244 := by
  have hP : Continuous (fun z : PairV => ‖z.1‖) := continuous_fst.norm
  have hQ : Continuous (fun z : PairV => ‖-(z.1 + z.2)‖) :=
    (continuous_fst.add continuous_snd).neg.norm
  have hR : Continuous (fun z : PairV => ‖z.2‖) := continuous_snd.norm
  exact (isOpen_lt hR hP).measurableSet.inter
    (isOpen_lt hR hQ).measurableSet

/-- The first and middle regions never overlap, even at equal radii. -/
theorem thirdFullMinFirstMiddle_disjoint244 :
    Disjoint thirdFullMinFirstSector244 thirdFullMinMiddleSector244 := by
  apply Set.disjoint_left.mpr
  intro z hp hq
  have hpq : ‖z.1‖ ≤ ‖-(z.1 + z.2)‖ := hp.1
  have hqp : ‖-(z.1 + z.2)‖ < ‖z.1‖ := hq.1
  exact (not_lt_of_ge hpq) hqp

/-- The first and last regions cannot both contain the same Fourier pair. -/
theorem thirdFullMinFirstLast_disjoint244 :
    Disjoint thirdFullMinFirstSector244 thirdFullMinLastSector244 := by
  apply Set.disjoint_left.mpr
  intro z hp hr
  have hpr : ‖z.1‖ ≤ ‖z.2‖ := hp.2
  have hrp : ‖z.2‖ < ‖z.1‖ := hr.1
  exact (not_lt_of_ge hpr) hrp

/-- The middle region excludes the strictly smaller last-frequency one. -/
theorem thirdFullMinMiddleLast_disjoint244 :
    Disjoint thirdFullMinMiddleSector244 thirdFullMinLastSector244 := by
  apply Set.disjoint_left.mpr
  intro z hq hr
  have hqr : ‖-(z.1 + z.2)‖ ≤ ‖z.2‖ := hq.2
  have hrq : ‖z.2‖ < ‖-(z.1 + z.2)‖ := hr.2
  exact (not_lt_of_ge hqr) hrq

/-- The union of the first and middle sectors is disjoint from the last. -/
theorem thirdFullMinFirstMiddleUnionLast_disjoint244 :
    Disjoint (thirdFullMinFirstSector244 ∪ thirdFullMinMiddleSector244)
      thirdFullMinLastSector244 := by
  apply Set.disjoint_left.mpr
  intro z hz hr
  rcases hz with hp | hq
  · exact (Set.disjoint_left.mp thirdFullMinFirstLast_disjoint244) hp hr
  · exact (Set.disjoint_left.mp thirdFullMinMiddleLast_disjoint244) hq hr

/-- There is no missing balanced sector: exactly one minimum is selected. -/
theorem thirdFullMinSectors_cover244 :
    (thirdFullMinFirstSector244 ∪ thirdFullMinMiddleSector244) ∪
      thirdFullMinLastSector244 = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  let P : ℝ := ‖z.1‖
  let Q : ℝ := ‖-(z.1 + z.2)‖
  let R : ℝ := ‖z.2‖
  change ((P ≤ Q ∧ P ≤ R) ∨ (Q < P ∧ Q ≤ R)) ∨ (R < P ∧ R < Q)
  by_cases hpq : P ≤ Q
  · by_cases hpr : P ≤ R
    · exact Or.inl (Or.inl ⟨hpq, hpr⟩)
    · have hrp : R < P := lt_of_not_ge hpr
      exact Or.inr ⟨hrp, lt_of_lt_of_le hrp hpq⟩
  · have hqp : Q < P := lt_of_not_ge hpq
    by_cases hqr : Q ≤ R
    · exact Or.inl (Or.inr ⟨hqp, hqr⟩)
    · have hrq : R < Q := lt_of_not_ge hqr
      exact Or.inr ⟨lt_trans hrq hqp, hrq⟩

/-- The first sector satisfies the precise hypothesis of the old low-first bound. -/
theorem thirdFullMinFirstSector_isLow244
    (z : PairV) (hz : z ∈ thirdFullMinFirstSector244) :
    ‖z.1‖ ≤ min ‖-(z.1 + z.2)‖ ‖z.2‖ :=
  le_min hz.1 hz.2

/-- The middle sector satisfies the old low-middle bound. -/
theorem thirdFullMinMiddleSector_isLow244
    (z : PairV) (hz : z ∈ thirdFullMinMiddleSector244) :
    ‖-(z.1 + z.2)‖ ≤ min ‖z.1‖ ‖z.2‖ :=
  le_min hz.1.le hz.2

/-- The last sector satisfies the old low-last bound. -/
theorem thirdFullMinLastSector_isLow244
    (z : PairV) (hz : z ∈ thirdFullMinLastSector244) :
    ‖z.2‖ ≤ min ‖z.1‖ ‖-(z.1 + z.2)‖ :=
  le_min hz.1.le hz.2.le

/-- The EXACT integral of the full solenoidal complex flux is the sum of the
three disjoint measurable sector integrals. No `ae` removal of ties, symmetry
assumption on amplitudes, or sign argument is needed. -/
theorem thirdFullSchwartzSixthPowerFlux_minSectorIntegralSplit244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0) :
    (∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
      ∂volume.prod volume) =
      ((∫ z in thirdFullMinFirstSector244,
          thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume) +
       (∫ z in thirdFullMinMiddleSector244,
          thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume)) +
       (∫ z in thirdFullMinLastSector244,
          thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume) := by
  let F : PairV → ℂ := thirdFullSchwartzComplexSixthPowerFlux244 v
  have hF : Integrable F (volume.prod volume) :=
    thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244 v hDiv
  have hTwo : (∫ z in (thirdFullMinFirstSector244 ∪ thirdFullMinMiddleSector244),
        F z ∂volume.prod volume) =
      (∫ z in thirdFullMinFirstSector244, F z ∂volume.prod volume) +
        ∫ z in thirdFullMinMiddleSector244, F z ∂volume.prod volume :=
    setIntegral_union thirdFullMinFirstMiddle_disjoint244
      thirdFullMinMiddleSector_measurable244 hF.integrableOn hF.integrableOn
  calc
    (∫ z : PairV, F z ∂volume.prod volume) =
        ∫ z in (Set.univ : Set PairV), F z ∂volume.prod volume := by simp
    _ = ∫ z in ((thirdFullMinFirstSector244 ∪ thirdFullMinMiddleSector244) ∪
          thirdFullMinLastSector244), F z ∂volume.prod volume := by
          rw [thirdFullMinSectors_cover244]
    _ = (∫ z in (thirdFullMinFirstSector244 ∪ thirdFullMinMiddleSector244),
          F z ∂volume.prod volume) +
        (∫ z in thirdFullMinLastSector244, F z ∂volume.prod volume) :=
      setIntegral_union thirdFullMinFirstMiddleUnionLast_disjoint244
        thirdFullMinLastSector_measurable244 hF.integrableOn hF.integrableOn
    _ = _ := by rw [hTwo]

/-- Frequency-resolved global complex Fourier flux budget. Each of the THREE
disjoint sectors puts one derivative on its minimum frequency; the two
larger frequencies each carry cubic Fourier weight. -/
theorem thirdFullSchwartzSixthPowerFlux_globalMinSectorMomentBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0) :
    ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      216 * thirdFullBudgetSixthMoment244 v * thirdFullBudgetFirstMoment244 v := by
  have hP := thirdFullSchwartzSixthPowerFlux_lowFirstIntegral_le_H3Moments244
    v hDiv thirdFullMinFirstSector244 thirdFullMinFirstSector_measurable244
      (fun z hz => thirdFullMinFirstSector_isLow244 z hz)
  have hQ := thirdFullSchwartzSixthPowerFlux_lowMiddleIntegral_le_H3Moments244
    v hDiv thirdFullMinMiddleSector244 thirdFullMinMiddleSector_measurable244
      (fun z hz => thirdFullMinMiddleSector_isLow244 z hz)
  have hR := thirdFullSchwartzSixthPowerFlux_lowLastIntegral_le_H3Moments244
    v hDiv thirdFullMinLastSector244 thirdFullMinLastSector_measurable244
      (fun z hz => thirdFullMinLastSector_isLow244 z hz)
  let P : ℂ := ∫ z in thirdFullMinFirstSector244,
    thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume
  let Q : ℂ := ∫ z in thirdFullMinMiddleSector244,
    thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume
  let R : ℂ := ∫ z in thirdFullMinLastSector244,
    thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume
  have hSplit : (∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume) = (P + Q) + R :=
    thirdFullSchwartzSixthPowerFlux_minSectorIntegralSplit244 v hDiv
  calc
    ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ = ‖(P + Q) + R‖ := by rw [hSplit]
    _ ≤ ‖P + Q‖ + ‖R‖ := norm_add_le _ _
    _ ≤ (‖P‖ + ‖Q‖) + ‖R‖ :=
      add_le_add (norm_add_le P Q) le_rfl
    _ ≤ (72 * thirdFullBudgetSixthMoment244 v * thirdFullBudgetFirstMoment244 v +
          72 * thirdFullBudgetSixthMoment244 v * thirdFullBudgetFirstMoment244 v) +
          72 * thirdFullBudgetSixthMoment244 v * thirdFullBudgetFirstMoment244 v :=
      add_le_add (add_le_add hP hQ) hR
    _ = _ := by ring

/-- Native weighted H³ coordinates imply a global frequency-resolved bound,
using exactly the real/complex weighted representatives from the old bridge. -/
theorem thirdFullWeightedSchwartz_globalMinSectorIntegral_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ∀ j, ‖G j‖ ≤ K) :
    ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      1944 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by
  have hSix := thirdFullWeightedSchwartz_sixthMoment_le_coordinateBound244
    v G hG K hK hBound
  have hFirst := (thirdFullWeightedSchwartz_moments_le_coordinateBound244
    v G hG K hK hBound).2
  have hFirst0 := (thirdFullBudgetMoments_nonneg244 v).2
  calc
    ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      216 * thirdFullBudgetSixthMoment244 v * thirdFullBudgetFirstMoment244 v :=
        thirdFullSchwartzSixthPowerFlux_globalMinSectorMomentBound244 v hDiv
    _ ≤ 216 * (3 * K ^ 2) * thirdFullBudgetFirstMoment244 v := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSix (by norm_num)) hFirst0
    _ ≤ 216 * (3 * K ^ 2) *
        (3 * h3SobolevFirstMomentDeweightingConstant * K) := by
      exact mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = 1944 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by ring

/-- At an actual physical interior NS snapshot, the SAME real solenoidal
Schwartz recovery has a uniform global complex flux bound and converges to
the exact physical signed H³ transport. The K here is snapshot-dependent. -/
theorem exists_thirdFullPhysicalSnapshot_globalMinSectorH3Bound244
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
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ) (K : ℝ),
      0 ≤ K ∧
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ n : ℕ,
        let v : A3 → SchwartzMap V3 ℂ :=
          fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
        ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume‖ ≤
          1944 * h3SobolevFirstMomentDeweightingConstant * K ^ 3) ∧
      Tendsto (fun n : ℕ =>
        ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : PairV,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : A3 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
  obtain ⟨V, Ψ, hV, hAE, hDiv, _hDefect, _hE2, _hE3, hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
      hNS htNS hH3 hClass ht hFourier
  obtain ⟨K, hK, hBound⟩ :=
    thirdFullWeightedRecovery_normBound_of_tendsto244
      V (velocityH3SpectralStateAt u t hInt hMeas hFourier) hV
  refine ⟨V, Ψ, K, hK, hV, hDiv, ?_, hFlux⟩
  intro n
  let v : A3 → SchwartzMap V3 ℂ :=
    fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
  let G : A3 → H3SpectralScalarState :=
    fun j => V n (h3ClassicalizationFinOfAxis j)
  have hRep : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ) := by
    intro j
    exact hAE n (h3ClassicalizationFinOfAxis j)
  have hCoord : ∀ j : A3, ‖G j‖ ≤ K := by
    intro j
    exact (h3SpectralFinVector_coordinate_norm_le
      (V n) (h3ClassicalizationFinOfAxis j)).trans (hBound n)
  exact thirdFullWeightedSchwartz_globalMinSectorIntegral_le244
    v (hDiv n) G hRep K hK hCoord

end
end PrimeTensor.FirstMonomialTriad
