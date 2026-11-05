import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalOuterHighMaxTail
import Mathlib.Tactic

/-!
# Complete high-maximum trilinear H3 Fourier tail

The tie-broken first, middle and last minimal-frequency sectors partition
the common high-maximum region exactly, including threshold and radius ties.
The original full complex sixth-power flux therefore has an exact three-part
integral decomposition on that region. Each part has a high-sixth-moment
bound; summation yields 216 M6_high M1 and the original physical recovery
has a uniformly vanishing *entire* high-maximum trilinear integral at every
fixed interior time.

This is a cutoff-removal theorem for the signed physical transport recovery,
not a terminal-time uniform a priori H3 bound or global regularity claim.
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

noncomputable local instance axisFintypeGlobalHighMaxTail244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The previous middle-minimum region is the same common high-max
restriction as the two newly proved outer regions. -/
theorem thirdFullMinMiddleHighMaxSector_eq_inter244 (R : ℕ) :
    thirdFullMinMiddleHighMaxSector244 R =
      thirdFullMinMiddleSector244 ∩ thirdFullHighMaxSet244 R := by
  rfl

/-- The three tie-broken high-max regions partition the exact high-max set. -/
theorem thirdFullHighMaxSectors_cover244 (R : ℕ) :
    (thirdFullMinFirstHighMaxSector244 R ∪
      thirdFullMinMiddleHighMaxSector244 R) ∪
      thirdFullMinLastHighMaxSector244 R = thirdFullHighMaxSet244 R := by
  ext z
  change (((z ∈ thirdFullMinFirstSector244 ∧ z ∈ thirdFullHighMaxSet244 R) ∨
    (z ∈ thirdFullMinMiddleSector244 ∧ z ∈ thirdFullHighMaxSet244 R)) ∨
    (z ∈ thirdFullMinLastSector244 ∧ z ∈ thirdFullHighMaxSet244 R)) ↔
      z ∈ thirdFullHighMaxSet244 R
  constructor
  · intro hz
    rcases hz with (hp | hq) | hr
    · exact hp.2
    · exact hq.2
    · exact hr.2
  · intro hHigh
    have hAll : z ∈ ((thirdFullMinFirstSector244 ∪
        thirdFullMinMiddleSector244) ∪ thirdFullMinLastSector244) := by
      rw [thirdFullMinSectors_cover244]
      exact Set.mem_univ z
    rcases hAll with (hp | hq) | hr
    · exact Or.inl (Or.inl ⟨hp, hHigh⟩)
    · exact Or.inl (Or.inr ⟨hq, hHigh⟩)
    · exact Or.inr ⟨hr, hHigh⟩

/-- No two distinct high-max tie-broken sectors overlap. -/
theorem thirdFullHighMaxFirstMiddle_disjoint244 (R : ℕ) :
    Disjoint (thirdFullMinFirstHighMaxSector244 R)
      (thirdFullMinMiddleHighMaxSector244 R) := by
  apply Set.disjoint_left.mpr
  intro z hp hq
  exact (Set.disjoint_left.mp thirdFullMinFirstMiddle_disjoint244) hp.1 hq.1

theorem thirdFullHighMaxFirstMiddleLast_disjoint244 (R : ℕ) :
    Disjoint (thirdFullMinFirstHighMaxSector244 R ∪
      thirdFullMinMiddleHighMaxSector244 R)
        (thirdFullMinLastHighMaxSector244 R) := by
  apply Set.disjoint_left.mpr
  intro z hpq hr
  have hOld : z ∈ thirdFullMinFirstSector244 ∪
      thirdFullMinMiddleSector244 := by
    rcases hpq with hp | hq
    · exact Or.inl hp.1
    · exact Or.inr hq.1
  exact (Set.disjoint_left.mp thirdFullMinFirstMiddleUnionLast_disjoint244)
    hOld hr.1

/-- Exact split of the genuine high-max complex flux on the three
minimal-frequency regions, with no discarded null tie set. -/
theorem thirdFullSchwartzSixthPowerFlux_highMaxIntegralSplit244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (R : ℕ) :
    (∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume) =
      ((∫ z in thirdFullMinFirstHighMaxSector244 R,
          thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume) +
       (∫ z in thirdFullMinMiddleHighMaxSector244 R,
          thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume)) +
       (∫ z in thirdFullMinLastHighMaxSector244 R,
          thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume) := by
  let F : PairV → ℂ := thirdFullSchwartzComplexSixthPowerFlux244 v
  have hF : Integrable F (volume.prod volume) :=
    thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244 v hDiv
  have hTwo : (∫ z in (thirdFullMinFirstHighMaxSector244 R ∪
        thirdFullMinMiddleHighMaxSector244 R), F z ∂volume.prod volume) =
      (∫ z in thirdFullMinFirstHighMaxSector244 R, F z ∂volume.prod volume) +
        ∫ z in thirdFullMinMiddleHighMaxSector244 R, F z ∂volume.prod volume :=
    setIntegral_union (thirdFullHighMaxFirstMiddle_disjoint244 R)
      (thirdFullMinMiddleHighMaxSector_measurable244 R)
      hF.integrableOn hF.integrableOn
  calc
    (∫ z in thirdFullHighMaxSet244 R, F z ∂volume.prod volume) =
      ∫ z in ((thirdFullMinFirstHighMaxSector244 R ∪
        thirdFullMinMiddleHighMaxSector244 R) ∪
        thirdFullMinLastHighMaxSector244 R), F z ∂volume.prod volume := by
          rw [thirdFullHighMaxSectors_cover244]
    _ = (∫ z in (thirdFullMinFirstHighMaxSector244 R ∪
          thirdFullMinMiddleHighMaxSector244 R), F z ∂volume.prod volume) +
        (∫ z in thirdFullMinLastHighMaxSector244 R, F z ∂volume.prod volume) :=
      setIntegral_union (thirdFullHighMaxFirstMiddleLast_disjoint244 R)
        (thirdFullMinLastHighMaxSector_measurable244 R)
        hF.integrableOn hF.integrableOn
    _ = _ := by rw [hTwo]

/-- Complete high-max trilinear bound: all three real frequency minimum
orientations contribute one localized homogeneous sixth moment. -/
theorem thirdFullSchwartzSixthPowerFlux_highMaxIntegral_le_H3Tail244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (R : ℕ) :
    ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      216 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
      thirdFullBudgetFirstMoment244 v := by
  have hP := thirdFullSchwartzSixthPowerFlux_firstHighMaxIntegral_le_H3Tail244
    v hDiv R
  have hQ := thirdFullSchwartzSixthPowerFlux_middleHighMaxIntegral_le_H3Tail244
    v hDiv R
  have hS := thirdFullSchwartzSixthPowerFlux_lastHighMaxIntegral_le_H3Tail244
    v hDiv R
  let P : ℂ := ∫ z in thirdFullMinFirstHighMaxSector244 R,
    thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume
  let Q : ℂ := ∫ z in thirdFullMinMiddleHighMaxSector244 R,
    thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume
  let S : ℂ := ∫ z in thirdFullMinLastHighMaxSector244 R,
    thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume
  have hSplit : (∫ z in thirdFullHighMaxSet244 R,
      thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume) =
        (P + Q) + S :=
    thirdFullSchwartzSixthPowerFlux_highMaxIntegralSplit244 v hDiv R
  calc
    ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ =
      ‖(P + Q) + S‖ := by rw [hSplit]
    _ ≤ ‖P + Q‖ + ‖S‖ := norm_add_le _ _
    _ ≤ (‖P‖ + ‖Q‖) + ‖S‖ := add_le_add (norm_add_le P Q) le_rfl
    _ ≤ (72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
          ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
          thirdFullBudgetFirstMoment244 v +
          72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
          ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
          thirdFullBudgetFirstMoment244 v) +
          72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
          ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
          thirdFullBudgetFirstMoment244 v :=
            add_le_add (add_le_add hP hQ) hS
    _ = _ := by ring

/-- The global high-max trilinear integral is quadratically small in
its exact weighted Fourier tail, not merely uniformly bounded. -/
theorem thirdFullWeightedSchwartz_highMaxIntegral_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (V : H3SpectralVelocityState)
    (hRep : ∀ j : A3,
      (V (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ‖V‖ ≤ K)
    (R : ℕ) :
    ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      1944 * h3SobolevFirstMomentDeweightingConstant * K *
        ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 := by
  have hMoment := thirdFullWeightedSchwartz_highRadialSixthMoment_le_velocityTail244
    v V hRep R
  have hCoord : ∀ j : A3,
      ‖V (h3ClassicalizationFinOfAxis j)‖ ≤ K := by
    intro j
    exact (h3SpectralFinVector_coordinate_norm_le
      V (h3ClassicalizationFinOfAxis j)).trans hBound
  have hFirst := (thirdFullWeightedSchwartz_moments_le_coordinateBound244
    v (fun j : A3 => V (h3ClassicalizationFinOfAxis j))
    hRep K hK hCoord).2
  have hFirst0 := (thirdFullBudgetMoments_nonneg244 v).2
  calc
    ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      216 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
        thirdFullBudgetFirstMoment244 v :=
          thirdFullSchwartzSixthPowerFlux_highMaxIntegral_le_H3Tail244 v hDiv R
    _ ≤ 216 * (3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2) *
        thirdFullBudgetFirstMoment244 v :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMoment (by norm_num)) hFirst0
    _ ≤ 216 * (3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2) *
        (3 * h3SobolevFirstMomentDeweightingConstant * K) :=
          mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = _ := by ring

/-- Complete high-max trilinear flux cutoff removal for the original
real-solenoidal physical snapshot recovery. The full signed physical
transport limit is retained on the same recovery, with no extra premise. -/
theorem exists_thirdFullPhysicalSnapshot_highMaxTailVanishing244
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
      (∀ ε : ℝ, 0 < ε → ∃ R N : ℕ, ∀ m : ℕ, N ≤ m →
        ‖∫ z in thirdFullHighMaxSet244 R,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : A3 => h3SchwartzComplexify
              (Ψ m (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume‖ < ε) ∧
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
  let v : ℕ → A3 → SchwartzMap V3 ℂ := fun n j =>
    h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
  have hRep : ∀ (n : ℕ) (j : A3),
      (V n (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v n j)) ξ) := by
    intro n j
    exact hAE n (h3ClassicalizationFinOfAxis j)
  have hSix := thirdFullWeightedRecovery_eventuallyUniformHighSixthMoment244
    V (velocityH3SpectralStateAt u t hInt hMeas hFourier) hV v hRep
  let B : ℝ := 648 * h3SobolevFirstMomentDeweightingConstant * K
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity [h3SobolevFirstMomentDeweightingConstant_nonneg]
  refine ⟨V, Ψ, hV, hDiv, ?_, hFlux⟩
  intro ε hε
  let δ : ℝ := ε / (1 + B)
  have hOneB : 0 < 1 + B := by linarith
  have hδ : 0 < δ := div_pos hε hOneB
  have hδeq : (1 + B) * δ = ε := by
    calc
      (1 + B) * δ = (ε / (1 + B)) * (1 + B) := by
        dsimp only [δ]
        ring
      _ = ε := div_mul_cancel₀ ε hOneB.ne'
  obtain ⟨R, N, hSmall⟩ := hSix δ hδ
  refine ⟨R, N, ?_⟩
  intro m hm
  let G : A3 → H3SpectralScalarState :=
    fun j => V m (h3ClassicalizationFinOfAxis j)
  have hCoord : ∀ j : A3, ‖G j‖ ≤ K := by
    intro j
    exact (h3SpectralFinVector_coordinate_norm_le
      (V m) (h3ClassicalizationFinOfAxis j)).trans (hBound m)
  have hFirst := (thirdFullWeightedSchwartz_moments_le_coordinateBound244
    (v m) G (hRep m) K hK hCoord).2
  have hSmallM := hSmall m hm
  have hNonneg : 0 ≤ (∫ ξ in h3TopTailNaturalHighRadialSet R,
      ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) :=
    integral_nonneg (fun ξ => mul_nonneg
      (pow_nonneg (norm_nonneg ξ) 6) (sq_nonneg _))
  have hStrict : B * δ < ε := by
    calc
      B * δ < (1 + B) * δ :=
        mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := hδeq
  calc
    ‖∫ z in thirdFullHighMaxSet244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 (v m) z
        ∂volume.prod volume‖ ≤
      216 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) *
        thirdFullBudgetFirstMoment244 (v m) :=
          thirdFullSchwartzSixthPowerFlux_highMaxIntegral_le_H3Tail244
            (v m) (hDiv m) R
    _ ≤ 216 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) *
        (3 * h3SobolevFirstMomentDeweightingConstant * K) :=
          mul_le_mul_of_nonneg_left hFirst
            (mul_nonneg (by norm_num) hNonneg)
    _ = B * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) := by
          dsimp only [B]
          ring
    _ ≤ B * δ := mul_le_mul_of_nonneg_left hSmallM.le hB
    _ < ε := hStrict

end
end PrimeTensor.FirstMonomialTriad
