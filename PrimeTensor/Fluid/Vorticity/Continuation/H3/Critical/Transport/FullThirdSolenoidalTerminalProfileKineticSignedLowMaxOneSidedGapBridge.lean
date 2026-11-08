import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCofinalGapCompression
import Mathlib.Tactic

/-!
# Single-snapshot signed LowMax flux: anchored baseline or physical gap cost

The existing cofinal signed-flux compression theorem requires a *difference*
of signed imaginary LowMax fluxes of two Schwartz representatives. The older
physical adverse-transport Fourier theorem only supplies a signed flux at
ONE Schwartz snapshot and one physical time. These are logically distinct.

Here a one-sided signed flux magnitude eta is split against a second,
independently realized Schwartz profile at an earlier physical observation:
its signed LowMax baseline is already large, OR the two snapshots differ by
more than eta/2. The latter feeds the certified closed kinetic-gap charge,
including the same observation times and both forward and backward annular
windows. On the original cofinal kinetic gaps, the actual finite-H3 viscous
integral tends to zero and thus compresses the exact charge.

The second reference profile and its weighted Fourier recovery are explicit:
this theorem does NOT assert that the physical one-snapshot adverse theorem
constructs such a reference with small baseline or small recovery error.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev OA3 := PrimeTensor.Axis Depth.three
private abbrev OV3 := H3FourierPoint3

noncomputable local instance axisFintypeSignedOneSidedBridge244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact one-sided signed-flux dichotomy. A large single sample and an
arbitrary reference sample imply either a large reference value or an
actually adverse signed difference; no time-continuity assumption enters. -/
theorem thirdFull_scalar_signedOneSided_baselineOrDifference244
    (a b eta : ℝ) (hLarge : eta ≤ |a|) :
    eta / 2 ≤ |b| ∨ eta / 2 < |a - b| := by
  by_cases hBaseline : eta / 2 ≤ |b|
  · exact Or.inl hBaseline
  · right
    have hSmall : |b| < eta / 2 := lt_of_not_ge hBaseline
    have hTriangle : |a| ≤ |a - b| + |b| := by
      calc
        |a| = |(a - b) + b| := by simp only [sub_add_cancel]
        _ ≤ |a - b| + |b| := abs_add_le _ _
    linarith only [hLarge, hSmall, hTriangle]

/-- Keep the genuine positive Fourier normalization when extracting
an unsigned one-snapshot magnitude from the negative signed physical arm.
For the actual sixth-flux normalization, take the positive coefficient
`((2 * Real.pi) ^ 7 / 3)`; it must not be discarded. -/
theorem thirdFull_scalar_negativeWeightedSignedFlux_to_oneSided244
    (C eta f : ℝ) (hC : 0 < C)
    (hSigned : eta ≤ -(C * f)) :
    eta / C ≤ |f| := by
  have hAbs : -f ≤ |f| := neg_le_abs f
  have hScaled : eta ≤ C * (-f) := by
    have hEq : C * (-f) = -(C * f) := by ring
    rw [hEq]
    exact hSigned
  have hUpper : C * (-f) ≤ C * |f| :=
    mul_le_mul_of_nonneg_left hAbs hC.le
  have hOrdered : eta ≤ |f| * C := by
    calc
      eta ≤ C * (-f) := hScaled
      _ ≤ C * |f| := hUpper
      _ = |f| * C := mul_comm _ _
  exact (div_le_iff₀ hC).2 hOrdered

/-- A one-sided signed imaginary LowMax flux excursion at an original
physical kinetic-gap observation forces THREE exact physical possibilities:
the independent reference profile already carries half of the signed flux,
or recovery plus the genuine physical PDE source clock pays a quarter,
or a certified positive-width annular interval is paid by the full H3
viscous integral INSIDE the same closed gap. No adverse two-snapshot
assumption is needed; the second Fourier representative remains explicit. -/
theorem thirdFullPhysical_strictGap_signedLowMax_oneSidedBaselineOrClockOrCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (p q : OA3 → SchwartzMap OV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hp : ∀ j : OA3,
      (V (h3ClassicalizationFinOfAxis j) : OV3 → ℂ) =ᵐ[volume]
        (fun ξ : OV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (p j)) ξ))
    (hq : ∀ j : OA3,
      (W (h3ClassicalizationFinOfAxis j) : OV3 → ℂ) =ᵐ[volume]
        (fun ξ : OV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (q j)) ξ))
    (eta : ℝ) (hEta : 0 < eta)
    (hOneSided : eta ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R p).im|) :
    (eta / 2 ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q).im|) ∨
    (eta / 4 < thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
        thirdFullFiniteBandH3WeightCeiling244 R *
          (∫ r in x..y,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖)) ∨
    (∃ z width : ℝ, (z = t ∨ z = s) ∧ 0 < width ∧
      ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
      width * (thirdFullKineticSignedLowMaxPDEViscousHeight244
        R V W (eta / 2) / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume) := by
  have hSplit := thirdFull_scalar_signedOneSided_baselineOrDifference244
    (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R p).im
    (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R q).im
    eta hOneSided
  rcases hSplit with hBaseline | hDifference
  · exact Or.inl hBaseline
  · have hHalf : 0 < eta / 2 := by positivity
    have hAlt := thirdFullPhysical_strictGap_signedLowMax_clockOrFullGapCharge244
      hH3 hClass hDInt b hb R x y hx hy hxy s t hs ht
      p q V W hp hq (eta / 2) hHalf hDifference.le
    rcases hAlt with hClock | hCost
    · right; left
      have hQuarter : (eta / 2) / 2 = eta / 4 := by ring
      rw [hQuarter] at hClock
      exact hClock
    · exact Or.inr (Or.inr hCost)

/-- One-sided cofinal signed LowMax samples, weaker than the previously
required adverse difference of TWO profiles. The reference and both true
weighted-H3 Fourier realizations are still part of the data. -/
def ThirdFullKineticSignedLowMaxCofinalOneSidedSamples244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ) (δ : ℕ → ℝ) (v R : ℕ → ℕ)
    (eta : ℝ) (s t : ℕ → ℝ)
    (p q : ℕ → OA3 → SchwartzMap OV3 ℂ)
    (V W : ℕ → H3SpectralVelocityState) : Prop :=
  ∀ k : ℕ,
    s k ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
    t k ∈ Set.Icc (τ (v k) + δ (v k)) (τ (v (k + 1))) ∧
    (∀ j : OA3,
      (V k (h3ClassicalizationFinOfAxis j) : OV3 → ℂ) =ᵐ[volume]
        (fun ξ : OV3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          (𝓕 (p k j)) ξ)) ∧
    (∀ j : OA3,
      (W k (h3ClassicalizationFinOfAxis j) : OV3 → ℂ) =ᵐ[volume]
        (fun ξ : OV3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          (𝓕 (q k j)) ξ)) ∧
    eta ≤ |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244
      (R k) (p k)).im|

/-- One-sided signed-flux replenishment on the ORIGINAL cofinal kinetic gaps:
all sufficiently late indices satisfy baseline, weighted clock, or a small
real viscous annular charge. The amplitude, moving cutoff and same-gap
physical source action remain visible, rather than being absorbed into an
unjustified cutoff-uniform constant. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_oneSidedBaselineOrCompressedCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (τ : ℕ → ℝ) (N : ℕ → ℕ)
    (δ : ℕ → ℝ) (v R : ℕ → ℕ)
    (hLimit : Tendsto (fun k => τ (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      τ (v k) + δ (v k) < τ (v l))
    (hWindows : ∀ k : ℕ,
      τ (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (τ (v k)) (v k) (N (v k))
        (M (v k)) (δ (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (s t : ℕ → ℝ)
    (p q : ℕ → OA3 → SchwartzMap OV3 ℂ)
    (V W : ℕ → H3SpectralVelocityState)
    (hSamples : ThirdFullKineticSignedLowMaxCofinalOneSidedSamples244
      hH3 τ δ v R eta s t p q V W)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      (eta / 2 ≤ |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244
        (R k) (q k)).im|) ∨
      (eta / 4 < thirdFullKineticSignedLowMaxFluxClockWeight244
        (R k) (V k) (W k) *
        (‖V k - h3AuditActualSpectralVelocityTotal hH3 (t k)‖ +
          thirdFullFiniteBandH3WeightCeiling244 (R k) *
            (∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
          ‖h3AuditActualSpectralVelocityTotal hH3 (s k) - W k‖)) ∨
      (∃ z width : ℝ, (z = t k ∨ z = s k) ∧ 0 < width ∧
        ((z + width < τ (v (k + 1))) ∨
          (z = τ (v (k + 1)) ∧ τ (v k) + δ (v k) < z - width)) ∧
        width * (thirdFullKineticSignedLowMaxPDEViscousHeight244
          (R k) (V k) (W k) (eta / 2) / 4) < epsilon) := by
  have hDZero := thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
    hH3 hClass hDInt b hb M τ N δ v hLimit hSeparated hWindows
  have hSmall : ∀ᶠ k : ℕ in atTop,
      (∫ r in (τ (v k) + δ (v k))..τ (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) < epsilon :=
    hDZero.eventually (eventually_lt_nhds hEpsilon)
  filter_upwards [hSmall] with k hk
  obtain ⟨hs, ht, hp, hq, hOneSided⟩ := hSamples k
  have hStart : τ (v k) + δ (v k) ∈ Set.Ioo b T := by
    have hWin := (hWindows k).2
    rcases hWin with ⟨_, hδ, _, hEnd, _, _⟩
    exact ⟨by linarith only [(hWindows k).1.1, hδ], hEnd⟩
  have hFinish : τ (v (k + 1)) ∈ Set.Ioo b T :=
    (hWindows (k + 1)).1
  have hGap : τ (v k) + δ (v k) < τ (v (k + 1)) :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hAlt := thirdFullPhysical_strictGap_signedLowMax_oneSidedBaselineOrClockOrCost244
    hH3 hClass hDInt b hb (R k)
    (τ (v k) + δ (v k)) (τ (v (k + 1)))
    hStart hFinish hGap (s k) (t k) hs ht
    (p k) (q k) (V k) (W k) hp hq eta hEta hOneSided
  rcases hAlt with hBaseline | hClock | ⟨z, width, hz, hWidth, hInside, hCost⟩
  · exact Or.inl hBaseline
  · exact Or.inr (Or.inl hClock)
  · have hInside' :
        (z + width < τ (v (k + 1))) ∨
          (z = τ (v (k + 1)) ∧
            τ (v k) + δ (v k) < z - width) := by
      rcases hInside with hForward | ⟨hRight, hBackward⟩
      · exact Or.inl hForward
      · exact Or.inr ⟨hRight, by simpa only [hRight] using hBackward⟩
    exact Or.inr (Or.inr ⟨z, width, hz, hWidth, hInside',
      lt_of_le_of_lt hCost hk⟩)

end
end PrimeTensor.FirstMonomialTriad
