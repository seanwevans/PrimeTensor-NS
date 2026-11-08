import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxViscousPDEWindow
import Mathlib.Tactic

/-!
# Signed sixth-flux viscous windows: exact localization inside kinetic gaps

A positive forward annular persistence window at an actual physical time z
need not end before the right-hand kinetic gap endpoint y. Here we use the
EXISTING certified PDE width δ and truncate it to

  ε = min δ ((y-z)/2).

When z<y this produces an explicit strictly positive interval inside the
original gap, with its own real integrated annular dissipation cost.
When z=y, that truncation necessarily has zero width; the actual signed flux
alternative therefore retains a distinct right-endpoint branch. We do not
silently discard it or claim that a pointwise spike implies an integrated
cost inside the preceding gap. No terminal-uniform persistence width is used.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev GA3 := PrimeTensor.Axis Depth.three
private abbrev GV3 := H3FourierPoint3

noncomputable local instance axisFintypeSignedInGapAnnulus244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The SAME anchored PDE window, restricted before the gap right endpoint.
It retains the original finite outer radius, state/source ceilings, exact
original PDE width, and exact truncated width. The last inequality is a real
integrated annular charge on a subinterval of the original gap. -/
def ThirdFullKineticSignedLowMaxInGapAnnularCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R : ℕ) (H z y : ℝ) : Prop :=
  ∃ (N : ℕ) (K C δ ε : ℝ),
    R ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧
    δ = thirdFullProfileAnchoredPDEWidth244 hH3 z R N K C H ∧
    ε = min δ ((y - z) / 2) ∧ 0 < ε ∧ z + ε < y ∧
    (∀ r : ℝ, r ∈ Set.Icc z (z + ε) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) ∧
    (∀ r : ℝ, r ∈ Set.Icc z (z + ε) →
      H / 4 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
    ε * (H / 4) ≤
      ∫ r in z..(z + ε),
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 r)

/-- HARD LOCALIZATION: the original certified physical PDE width remains
valid after truncation to a strictly earlier right endpoint. The integrated
annular cost is re-proved on the shortened interval, not inferred from the
integral over the larger window (which would reverse the inequality). -/
theorem thirdFullPhysical_signedLowMax_certifiedWindow_truncateInGap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (H z y : ℝ)
    (hz : z ∈ Set.Ioo a T) (hzy : z < y) (hyT : y ≤ T)
    (hWindow : ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244
      hH3 R H z) :
    ThirdFullKineticSignedLowMaxInGapAnnularCharge244 hH3 R H z y := by
  obtain ⟨N, K, C, δ, hRN, hK, hC, hδ, _hδOne, _hδEnd,
    _hState, hSource, _hAt, hWidth, hFloor, _hOriginalCost⟩ := hWindow
  let ε : ℝ := min δ ((y - z) / 2)
  have hHalf : 0 < (y - z) / 2 := by linarith only [hzy]
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min hδ hHalf
  have hεδ : ε ≤ δ := by
    dsimp only [ε]
    exact min_le_left _ _
  have hεGap : ε ≤ (y - z) / 2 := by
    dsimp only [ε]
    exact min_le_right _ _
  have hEndGap : z + ε < y := by
    linarith only [hεGap, hzy]
  have hEndT : z + ε < T := lt_of_lt_of_le hEndGap hyT
  let Ann : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r) -
    h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r)
  have hInsideOld (r : ℝ) (hr : r ∈ Set.Icc z (z + ε)) :
      r ∈ Set.Icc z (z + δ) :=
    ⟨hr.1, by linarith only [hr.2, hεδ]⟩
  have hSourceNew (r : ℝ) (hr : r ∈ Set.Icc z (z + ε)) :
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C :=
    hSource r (hInsideOld r hr)
  have hFloorNew (r : ℝ) (hr : r ∈ Set.Icc z (z + ε)) :
      H / 4 < Ann r := by
    exact hFloor r (hInsideOld r hr)
  have hSub : Set.Icc z (z + ε) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hz.1 hr.1, lt_of_le_of_lt hr.2 hEndT⟩
  have hAnnCont : ContinuousOn Ann (Set.Ioo a T) :=
    h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((R : ℝ) + 1) ((N : ℝ) + 1)
      (by positivity) (by positivity)
  have hAnnInt : IntervalIntegrable Ann volume z (z + ε) :=
    (hAnnCont.mono hSub).intervalIntegrable_of_Icc
      (by linarith only [hε])
  have hCost : ε * (H / 4) ≤ ∫ r in z..(z + ε), Ann r := by
    have h := h3Path_localPositiveHeight_forces_integratedCost244
      Ann z (z + ε) (H / 4)
      (by linarith only [hε]) hAnnInt
      (fun r hr => (hFloorNew r hr).le)
    calc
      ε * (H / 4) = ((z + ε) - z) * (H / 4) := by ring
      _ ≤ ∫ r in z..(z + ε), Ann r := h
  exact ⟨N, K, C, δ, ε, hRN, hK, hC, hWidth,
    rfl, hε, hEndGap, hSourceNew, hFloorNew, hCost⟩

/-- For arbitrary observation times in the CLOSED physical kinetic gap,
there are three genuinely different outcomes. An adverse signed sixth-flux
increment either charges the weighted PDE/recovery clock, places its PDE
annular window at the RIGHT endpoint y, or yields a positive-width annular
charge actually INSIDE the preceding gap. No false gap containment. -/
theorem thirdFullPhysical_strictGap_signedLowMax_clockOrEndpointOrInGap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Icc x y) (ht : t ∈ Set.Icc x y)
    (v w : GA3 → SchwartzMap GV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : GA3,
      (V (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
        (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : GA3,
      (W (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
        (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (η : ℝ) (hη : 0 < η)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|) :
    (η / 2 < thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
        thirdFullFiniteBandH3WeightCeiling244 R *
          (∫ r in x..y,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖)) ∨
    (∃ z : ℝ, (z = t ∨ z = s) ∧ z = y ∧
      ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244 hH3 R
        (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η) z) ∨
    (∃ z : ℝ, (z = t ∨ z = s) ∧ z < y ∧
      ThirdFullKineticSignedLowMaxInGapAnnularCharge244 hH3 R
        (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η) z y) := by
  obtain hClock | ⟨z, hzTime, hWindow⟩ :=
    thirdFullPhysical_strictGap_signedLowMax_clockOrPDEAnnularWindow244
      hH3 hClass R x y hx hy hxy s t hs ht v w V W hv hw η hη hAdverse
  · exact Or.inl hClock
  · have hzGap : z ∈ Set.Icc x y := by
      rcases hzTime with rfl | rfl
      · exact ht
      · exact hs
    have hzClass : z ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hx.1 hzGap.1, lt_of_le_of_lt hzGap.2 hy.2⟩
    rcases lt_or_eq_of_le hzGap.2 with hzy | hzy
    · exact Or.inr (Or.inr ⟨z, hzTime, hzy,
        thirdFullPhysical_signedLowMax_certifiedWindow_truncateInGap244
          hH3 hClass R
          (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η)
          z y hzClass hzy hy.2.le hWindow⟩)
    · exact Or.inr (Or.inl ⟨z, hzTime, hzy, hWindow⟩)

/-- If the SAME selected signed-flux observation times both lie STRICTLY
inside the kinetic gap, the endpoint branch is impossible and the charged
annular window is contained before y. This is a precise conditional result:
interior sampling is not silently inferred for arbitrary adverse snapshots. -/
theorem thirdFullPhysical_strictGap_signedLowMax_interiorClockOrInGapCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Ioo x y) (ht : t ∈ Set.Ioo x y)
    (v w : GA3 → SchwartzMap GV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : GA3,
      (V (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
        (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : GA3,
      (W (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
        (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (η : ℝ) (hη : 0 < η)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|) :
    (η / 2 < thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
        thirdFullFiniteBandH3WeightCeiling244 R *
          (∫ r in x..y,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖)) ∨
    (∃ z : ℝ, (z = t ∨ z = s) ∧ z < y ∧
      ThirdFullKineticSignedLowMaxInGapAnnularCharge244 hH3 R
        (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η) z y) := by
  have hsClosed : s ∈ Set.Icc x y := ⟨hs.1.le, hs.2.le⟩
  have htClosed : t ∈ Set.Icc x y := ⟨ht.1.le, ht.2.le⟩
  have h := thirdFullPhysical_strictGap_signedLowMax_clockOrEndpointOrInGap244
    hH3 hClass R x y hx hy hxy s t hsClosed htClosed
    v w V W hv hw η hη hAdverse
  rcases h with hClock | hAtRight | hInside
  · exact Or.inl hClock
  · obtain ⟨z, hzTime, hzy, _hWindow⟩ := hAtRight
    have hlt : z < y := by
      rcases hzTime with rfl | rfl
      · exact ht.2
      · exact hs.2
    exact False.elim (ne_of_lt hlt hzy)
  · exact Or.inr hInside

/-- The restricted annular cost is paid by the ACTUAL physical full H³
viscous dissipation over the ORIGINAL kinetic gap. Here finite dissipation is
an explicit interval-integrability hypothesis, not an inferred consequence
of a pointwise spike. -/
theorem thirdFullPhysical_signedLowMax_inGapCharge_le_fullGapDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (R : ℕ) (H x z y : ℝ)
    (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T)
    (hxy : x ≤ y) (hz : z ∈ Set.Icc x y)
    (hCharge : ThirdFullKineticSignedLowMaxInGapAnnularCharge244
      hH3 R H z y) :
    ∃ ε : ℝ, 0 < ε ∧ z + ε < y ∧
      ε * (H / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume := by
  obtain ⟨N, K, C, δ, ε, _hRN, _hK, _hC, _hWidth,
    _hεEq, hε, hEndGap, _hSource, _hFloor, hCost⟩ := hCharge
  let U : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let Ann : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1) (U r) -
    h3PathActualLowRadialDissipation244 ((R : ℝ) + 1) (U r)
  let D : ℝ → ℝ := velocityH3DissipationAt u
  have hzClass : z ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  have hEndT : z + ε < T := lt_trans hEndGap hy.2
  have hSub : Set.Icc z (z + ε) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hzClass.1 hr.1, lt_of_le_of_lt hr.2 hEndT⟩
  have hAnnCont : ContinuousOn Ann (Set.Ioo a T) :=
    h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((R : ℝ) + 1) ((N : ℝ) + 1)
      (by positivity) (by positivity)
  have hAnnInt : IntervalIntegrable Ann volume z (z + ε) :=
    (hAnnCont.mono hSub).intervalIntegrable_of_Icc
      (by linarith only [hε])
  have hDGap : IntervalIntegrable D volume x y := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc x y := by
      simpa only [Set.uIcc_of_le hxy] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hx.1.le.trans hrIcc.1, hrIcc.2.trans hy.2.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hDWin : IntervalIntegrable D volume z (z + ε) := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc z (z + ε) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hε.le)] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hzClass.1.le.trans hrIcc.1, hrIcc.2.trans hEndT.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hAnnLeFull : (∫ r in z..(z + ε), Ann r ∂volume) ≤
      ∫ r in z..(z + ε), D r ∂volume := by
    apply intervalIntegral.integral_mono_on
      (le_add_of_nonneg_right hε.le) hAnnInt hDWin
    intro r hr
    have hrClass : r ∈ Set.Ioo a T := hSub hr
    exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass r hrClass ((R : ℝ) + 1) ((N : ℝ) + 1)
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc x y)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  have hInsideGap : (∫ r in z..(z + ε), D r ∂volume) ≤
      ∫ r in x..y, D r ∂volume :=
    intervalIntegral.integral_mono_interval
      hz.1 (le_add_of_nonneg_right hε.le) hEndGap.le
      hNonneg hDGap
  refine ⟨ε, hε, hEndGap, ?_⟩
  exact (hCost.trans hAnnLeFull).trans hInsideGap

/-- Interior physical signed-flux samples: either the exact weighted
recovery/PDE clock pays, or a positive explicitly truncated annulus forces
a lower bound for the FULL physical dissipation integral on the same
original gap. No new gap interval is chosen, and no terminal-uniform cutoff
or positive lower bound on the shrinking widths is asserted. -/
theorem thirdFullPhysical_strictGap_signedLowMax_interiorClockOrFullGapCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (R : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo a T) (hy : y ∈ Set.Ioo a T) (hxy : x < y)
    (s t : ℝ) (hs : s ∈ Set.Ioo x y) (ht : t ∈ Set.Ioo x y)
    (v w : GA3 → SchwartzMap GV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : GA3,
      (V (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
        (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : GA3,
      (W (h3ClassicalizationFinOfAxis j) : GV3 → ℂ) =ᵐ[volume]
        (fun ξ : GV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (η : ℝ) (hη : 0 < η)
    (hAdverse : η ≤
      |(thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v).im -
        (thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w).im|) :
    (η / 2 < thirdFullKineticSignedLowMaxFluxClockWeight244 R V W *
      (‖V - h3AuditActualSpectralVelocityTotal hH3 t‖ +
        thirdFullFiniteBandH3WeightCeiling244 R *
          (∫ r in x..y,
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ∂volume) +
        ‖h3AuditActualSpectralVelocityTotal hH3 s - W‖)) ∨
    (∃ z ε : ℝ, (z = t ∨ z = s) ∧ 0 < ε ∧ z + ε < y ∧
      ε * (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume) := by
  have h := thirdFullPhysical_strictGap_signedLowMax_interiorClockOrInGapCharge244
    hH3 hClass R x y hx hy hxy s t hs ht v w V W hv hw η hη hAdverse
  rcases h with hClock | ⟨z, hzTime, _hzy, hInGap⟩
  · exact Or.inl hClock
  · right
    have hzGap : z ∈ Set.Icc x y := by
      rcases hzTime with rfl | rfl
      · exact ⟨ht.1.le, ht.2.le⟩
      · exact ⟨hs.1.le, hs.2.le⟩
    obtain ⟨ε, hε, hEnd, hCost⟩ :=
      thirdFullPhysical_signedLowMax_inGapCharge_le_fullGapDissipation244
        hH3 hClass hDInt R
        (thirdFullKineticSignedLowMaxPDEViscousHeight244 R V W η)
        x z y hx hy hxy.le hzGap hInGap
    exact ⟨z, ε, hzTime, hε, hEnd, hCost⟩

end
end PrimeTensor.FirstMonomialTriad
