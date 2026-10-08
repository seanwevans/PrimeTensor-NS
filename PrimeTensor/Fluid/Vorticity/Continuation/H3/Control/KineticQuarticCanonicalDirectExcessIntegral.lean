import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalDirectDefect
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Near.Alternative

/-!
# Exact direct regime carries the nonintegrable full-dissipation transport excess

The canonical selected direct coefficient equals the full canonical gradient
coefficient at every sufficiently late time of a hypothetical nonextendible
H3 path, for any fixed positive-mass kinetic anchor. Independently, the exact
positive logarithmic growth (full-dissipation transport excess) is not L1 on
any H3 energy-class terminal tail under nonextension.

Localizing the latter to the *actual direct selection set* gives a sharper
necessary obstruction: its restricted normalized transport excess cannot be
integrable on any strict terminal interval. A single integrable selected-direct
excess tail is therefore a sufficient continuation criterion. No bound on the
actual PDE excess is proved here, and no existence of nonextension is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- The minimal positive normalized full-dissipation transport excess,
restricted to times when the exact adaptive kinetic coefficient selects the
whole canonical direct coefficient. -/
noncomputable def h3PathCanonicalSelectedDirectFullExcessRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b : ℝ) : ℝ → ℝ :=
  {t : ℝ | h3ExactAdaptiveSelectedDirectCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b t =
        h3PathCanonicalKineticTransportCoefficient u t}.indicator
    (h3PathFullDissipationTransportExcessRate u)

/-- On exactly direct-selected times, the restricted excess is the full PDE
excess rate, with no coefficient loss. -/
theorem h3PathCanonicalSelectedDirectFullExcessRate_eq_of_direct
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ)
    (hDirect : h3ExactAdaptiveSelectedDirectCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b t =
        h3PathCanonicalKineticTransportCoefficient u t) :
    h3PathCanonicalSelectedDirectFullExcessRate u b t =
      h3PathFullDissipationTransportExcessRate u t := by
  simp [h3PathCanonicalSelectedDirectFullExcessRate, Set.indicator, hDirect]

/-- Outside the exactly selected direct regime the localized rate vanishes. -/
theorem h3PathCanonicalSelectedDirectFullExcessRate_eq_zero_of_not_direct
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b t : ℝ)
    (hNotDirect : ¬ h3ExactAdaptiveSelectedDirectCoefficient u
      (h3PathCanonicalKineticTransportCoefficient u) b t =
        h3PathCanonicalKineticTransportCoefficient u t) :
    h3PathCanonicalSelectedDirectFullExcessRate u b t = 0 := by
  simp [h3PathCanonicalSelectedDirectFullExcessRate, Set.indicator, hNotDirect]

/-- Under nonextension, at every positive-mass kinetic anchor the localized
excess equals the full exact transport excess throughout one final interval. -/
theorem h3PathCanonicalSelectedDirectFullExcessRate_eventually_eq_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        h3PathCanonicalSelectedDirectFullExcessRate u b t =
          h3PathFullDissipationTransportExcessRate u t := by
  obtain ⟨c, hc, hDirect⟩ :=
    h3PathCanonical_eventually_direct_of_noExtension_positive_mass
      hH3 hNoExtension hClass hMass
  refine ⟨c, hc, ?_⟩
  intro t ht
  exact h3PathCanonicalSelectedDirectFullExcessRate_eq_of_direct
    u b t (hDirect t ht).1

/-- Nonextension forces failure of temporal integrability for the normalized
full-dissipation excess *on direct-selected times alone*, on every strict tail
at a positive-mass anchor. -/
theorem h3PathCanonicalSelectedDirectFullExcessRate_nonintegrable_on_later_tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ¬ IntegrableOn (h3PathCanonicalSelectedDirectFullExcessRate u b)
      (Set.Ioo d T) := by
  intro hSelectedInt
  obtain ⟨c, hc, hEq⟩ :=
    h3PathCanonicalSelectedDirectFullExcessRate_eventually_eq_of_noExtension
      hH3 hNoExtension hClass hMass
  let r : ℝ := max d c
  have hr : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hd.1 (le_max_left d c), max_lt hd.2 hc.2⟩
  have hSelectedR : IntegrableOn
      (h3PathCanonicalSelectedDirectFullExcessRate u b) (Set.Ioo r T) := by
    apply hSelectedInt.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left d c) ht.1, ht.2⟩
  have hFullR : IntegrableOn
      (h3PathFullDissipationTransportExcessRate u) (Set.Ioo r T) := by
    exact IntegrableOn.congr_fun hSelectedR
      (fun t ht => hEq t ⟨lt_of_le_of_lt (le_max_right d c) ht.1, ht.2⟩)
      measurableSet_Ioo
  have hClassR : PreterminalH3EnergyClass u r T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hr.1) hr.2
  exact (not_integrableFullDissipationTransportExcessRateOnEveryTail_of_noH3PathExtension
    hH3 hNoExtension r hClassR) hFullR

/-- One integrable terminal tail of the exact-direct-selected normalized
full-dissipation excess suffices for smooth continuation at a positive anchor. -/
theorem h3PathCanonical_extension_of_integrable_selectedDirectFullExcessRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hSelectedInt : IntegrableOn (h3PathCanonicalSelectedDirectFullExcessRate u b)
      (Set.Ioo d T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  exact (h3PathCanonicalSelectedDirectFullExcessRate_nonintegrable_on_later_tail
    hH3 hNoExtension hClass hd hMass) hSelectedInt

/-- Neutral alternative: either the H3 path continues, or every positive-mass
anchor carries nonintegrable normalized full-dissipation transport excess on
its exactly direct-selected times on every strict terminal tail. -/
theorem h3PathCanonical_extension_or_nonintegrable_selectedDirectFullExcessRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∀ d : ℝ, d ∈ Set.Ioo a T →
        ¬ IntegrableOn (h3PathCanonicalSelectedDirectFullExcessRate u b)
          (Set.Ioo d T) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass d hd
    exact h3PathCanonicalSelectedDirectFullExcessRate_nonintegrable_on_later_tail
      hH3 hExt hClass hd hMass

end Euclidean
end Bridge
end PrimeTensor
