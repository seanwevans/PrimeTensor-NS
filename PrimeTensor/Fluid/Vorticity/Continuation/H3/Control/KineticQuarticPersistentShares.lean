import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticSelectedRegimes

/-!
# Persistent selected-share obstruction across strict terminal subtails

The selected exact adaptive coefficient decomposes into direct and absorbed
shares without requiring a persistent threshold regime.  Since integrability
on a terminal interval persists after moving its left endpoint forward, two
shares integrable on possibly different subtails are both integrable on their
common later subtail.  Under nonextension, this rules out the possibility
that both shares have an integrable later tail.

Consequently, for every fixed kinetic anchor, one selected share is
nonintegrable on *every* later strict subtail.  The identity of the failing
share may depend on the kinetic anchor.  No claim is made that one pointwise
threshold regime eventually persists, or that continuation/blowup holds
unconditionally.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Two integrable terminal tails for different functions have a common later
terminal tail where both functions are integrable. -/
theorem h3_selected_share_integrableOn_common_later_subtail
    {f g : ℝ → ℝ} {b c d T : ℝ}
    (hc : c ∈ Set.Ioo b T) (hd : d ∈ Set.Ioo b T)
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo c T))
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo d T)) :
    ∃ e : ℝ, e ∈ Set.Ioo b T ∧
      MeasureTheory.IntegrableOn f (Set.Ioo e T) ∧
      MeasureTheory.IntegrableOn g (Set.Ioo e T) := by
  refine ⟨max c d, ?_, ?_, ?_⟩
  · exact ⟨lt_of_lt_of_le hc.1 (le_max_left c d), max_lt hc.2 hd.2⟩
  · apply hf.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left c d) ht.1, ht.2⟩
  · apply hg.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_right c d) ht.1, ht.2⟩

/-- A binary nonintegrability alternative on each terminal subtail upgrades
to one fixed, nonintegrable share on all such subtails.  This uses only the
restriction property of integrability, not the PDE or eventual regime
selection. -/
theorem h3_selected_share_persistent_nonintegrability_of_each_tail
    {f g : ℝ → ℝ} {b T : ℝ}
    (hFailure : ∀ c : ℝ, c ∈ Set.Ioo b T →
      (¬ MeasureTheory.IntegrableOn f (Set.Ioo c T) ∨
       ¬ MeasureTheory.IntegrableOn g (Set.Ioo c T))) :
    (∀ c : ℝ, c ∈ Set.Ioo b T →
      ¬ MeasureTheory.IntegrableOn f (Set.Ioo c T)) ∨
    (∀ c : ℝ, c ∈ Set.Ioo b T →
      ¬ MeasureTheory.IntegrableOn g (Set.Ioo c T)) := by
  classical
  by_cases hSomeF : ∃ c : ℝ, c ∈ Set.Ioo b T ∧
      MeasureTheory.IntegrableOn f (Set.Ioo c T)
  · right
    intro d hd hG
    obtain ⟨c, hc, hF⟩ := hSomeF
    obtain ⟨e, he, hFe, hGe⟩ :=
      h3_selected_share_integrableOn_common_later_subtail hc hd hF hG
    exact (hFailure e he).elim (fun h => h hFe) (fun h => h hGe)
  · left
    intro c hc hF
    exact hSomeF ⟨c, hc, hF⟩

/-- Exact selected-share dichotomy with one persistent failing share for
*each* kinetic anchor.  The failing share may differ between anchors. -/
theorem h3PathSelectedExactAdaptivePersistentShareContinuationOrObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ((∀ c : ℝ, c ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u B b) (Set.Ioo c T)) ∨
       (∀ c : ℝ, c ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedAbsorbedCoefficient u B b) (Set.Ioo c T))) := by
  rcases h3PathSelectedExactAdaptiveContinuationOrObstruction_on_every_two_anchor_subtail
      hH3 hClass hB hTransport with hExtension | hFailure
  · exact Or.inl hExtension
  · right
    intro b hb
    apply h3_selected_share_persistent_nonintegrability_of_each_tail
    intro c hc
    exact hFailure b hb c hc

/-- Gradient-envelope version of the persistent selected-share dichotomy.
No eventual direct/absorbed regime selection is assumed. -/
theorem h3PathSelectedExactAdaptiveGradientPersistentShareContinuationOrObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo a T → VelocityGradientEnvelope u h t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ((∀ c : ℝ, c ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedDirectCoefficient u
            (fun t : ℝ => 4422 * (1 + |h t|)) b) (Set.Ioo c T)) ∨
       (∀ c : ℝ, c ∈ Set.Ioo b T →
        ¬ MeasureTheory.IntegrableOn
          (h3ExactAdaptiveSelectedAbsorbedCoefficient u
            (fun t : ℝ => 4422 * (1 + |h t|)) b) (Set.Ioo c T))) := by
  rcases h3PathSelectedExactAdaptiveGradientContinuationOrObstruction_on_every_two_anchor_subtail
      hH3 hClass hGradient with hExtension | hFailure
  · exact Or.inl hExtension
  · right
    intro b hb
    apply h3_selected_share_persistent_nonintegrability_of_each_tail
    intro c hc
    exact hFailure b hb c hc

end Euclidean
end Bridge
end PrimeTensor
