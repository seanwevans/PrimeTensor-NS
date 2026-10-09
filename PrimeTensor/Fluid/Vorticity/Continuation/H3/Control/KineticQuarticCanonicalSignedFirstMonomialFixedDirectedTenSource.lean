import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialFixedSevenSource

/-!
# Fixed directed velocity-component obstruction among ten H³ sources

The seven-source obstruction isolates one gradient excess and six signed
velocity-component channels, three of which are symmetric off-diagonal pairs.
A negative pair has a negative *ordered* member.  Scaling an off-diagonal
member by 18, instead of 9, places each of the nine ordered entries of Q on
exactly the same quantitative threshold as the gradient channel.

Under hypothetical nonextension, a single index among these ten sources is
cofinal on every strict terminal subtail at every nonnegative threshold.
This does not prove any sign or PDE estimate for a component.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- The one gradient excess and nine signed *ordered* velocity channels.
The off-diagonal weights 18 account for splitting a symmetric pair;
the diagonal weights 9 are unchanged. -/
noncomputable def h3PathCanonicalJointDirectedTenSourceAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (i : Fin 10) : ℝ :=
  let Q := h3PathCanonicalFirstMonomialComponentAt u t
  match i.val with
  | 0 =>
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
        velocityH3DissipationAt u t
  | 1 => -(9 * Q xAxis xAxis)
  | 2 => -(9 * Q yAxis yAxis)
  | 3 => -(9 * Q zAxis zAxis)
  | 4 => -(18 * Q xAxis yAxis)
  | 5 => -(18 * Q yAxis xAxis)
  | 6 => -(18 * Q xAxis zAxis)
  | 7 => -(18 * Q zAxis xAxis)
  | 8 => -(18 * Q yAxis zAxis)
  | _ => -(18 * Q zAxis yAxis)

/-- An adverse symmetric off-diagonal pair forces an adverse ordered entry,
with the exact factor of two in the scalar normalization. -/
private theorem h3PathCanonical_negativePair_forces_directed
    {a b E R : ℝ} (hPair : a + b < -R * E) :
    9 * R * E < -(18 * a) ∨ 9 * R * E < -(18 * b) := by
  by_cases ha : 9 * R * E < -(18 * a)
  · exact Or.inl ha
  · right
    have hNot : -(18 * a) ≤ 9 * R * E := le_of_not_gt ha
    nlinarith only [hPair, hNot]

/-- Generic finite cofinal pigeonhole principle. The index is fixed for all
terminal subintervals and all thresholds, not merely along one sequence. -/
private theorem h3PathCanonical_directed_fixedIndex_cofinal_pigeonhole
    {ι : Type} [Fintype ι]
    {b T : ℝ} (hbT : b < T)
    (P : ι → ℝ → ℝ → Prop)
    (hMono : ∀ i t R S, R ≤ S → P i t S → P i t R)
    (hCover : ∀ d : ℝ, d ∈ Set.Ioo b T →
      ∀ R : ℝ, 0 ≤ R →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ ∃ i : ι, P i t R) :
    ∃ i : ι, ∀ d : ℝ, d ∈ Set.Ioo b T →
      ∀ R : ℝ, 0 ≤ R →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ P i t R := by
  classical
  by_contra hNone
  have hBad (i : ι) :
      ∃ d : ℝ, d ∈ Set.Ioo b T ∧
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ t : ℝ, t ∈ Set.Ioo d T → ¬ P i t R := by
    by_contra hEmpty
    apply hNone
    refine ⟨i, ?_⟩
    intro d hd R hR
    by_contra hNoWitness
    apply hEmpty
    refine ⟨d, hd, R, hR, ?_⟩
    intro t ht hp
    apply hNoWitness
    exact ⟨t, ht, hp⟩
  have hAll (s : Finset ι) :
      ∃ d : ℝ, d ∈ Set.Ioo b T ∧
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ i : ι, i ∈ s →
            ∀ t : ℝ, t ∈ Set.Ioo d T → ¬ P i t R := by
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨(b + T) / 2, ?_, 0, by norm_num, ?_⟩
        · constructor <;> linarith only [hbT]
        · intro i hi
          simp at hi
    | @insert i s _ ih =>
        obtain ⟨di, hdi, Ri, hRi, hNoi⟩ := hBad i
        obtain ⟨d, hd, R, hR, hNo⟩ := ih
        refine ⟨max d di, ?_, max R Ri, ?_, ?_⟩
        · exact ⟨lt_of_lt_of_le hd.1 (le_max_left d di),
            (max_lt_iff).mpr ⟨hd.2, hdi.2⟩⟩
        · exact le_trans hR (le_max_left R Ri)
        · intro j hj t ht hp
          rcases Finset.mem_insert.mp hj with hji | hjs
          · subst j
            have htDi : t ∈ Set.Ioo di T :=
              ⟨lt_of_le_of_lt (le_max_right d di) ht.1, ht.2⟩
            exact hNoi t htDi
              (hMono i t Ri (max R Ri) (le_max_right R Ri) hp)
          · have htD : t ∈ Set.Ioo d T :=
              ⟨lt_of_le_of_lt (le_max_left d di) ht.1, ht.2⟩
            exact hNo j hjs t htD
              (hMono j t R (max R Ri) (le_max_left R Ri) hp)
  obtain ⟨d, hd, R, hR, hForbid⟩ := hAll Finset.univ
  obtain ⟨t, ht, i, hp⟩ := hCover d hd R hR
  exact hForbid i (Finset.mem_univ i) t ht hp

/-- Every subtail/threshold has an actual ordered velocity-component witness
or the original gradient-excess witness, with a common coefficient 9. -/
theorem h3PathCanonical_jointDirectedTenSource_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d R : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hR : 0 ≤ R) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ i : Fin 10,
        9 * R * velocityH3EnergyAt u t <
          h3PathCanonicalJointDirectedTenSourceAt u t i := by
  obtain ⟨t, ht, hAlt⟩ :=
    h3PathCanonical_gradientExcess_or_sixChannel_on_every_subtail
      hH3 hNoExtension hClass hb hd hR
  rcases hAlt with hGradient | hSix
  · refine ⟨t, ht, ⟨0, by decide⟩, ?_⟩
    change 9 * R * velocityH3EnergyAt u t <
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
        velocityH3DissipationAt u t
    exact hGradient
  · dsimp [h3PathCanonicalFirstMonomialSixChannelAdverseAt] at hSix
    rcases hSix with hxx | hyy | hzz | hxy | hxz | hyz
    · refine ⟨t, ht, ⟨1, by decide⟩, ?_⟩
      change 9 * R * velocityH3EnergyAt u t <
        -(9 * h3PathCanonicalFirstMonomialComponentAt u t xAxis xAxis)
      nlinarith only [hxx]
    · refine ⟨t, ht, ⟨2, by decide⟩, ?_⟩
      change 9 * R * velocityH3EnergyAt u t <
        -(9 * h3PathCanonicalFirstMonomialComponentAt u t yAxis yAxis)
      nlinarith only [hyy]
    · refine ⟨t, ht, ⟨3, by decide⟩, ?_⟩
      change 9 * R * velocityH3EnergyAt u t <
        -(9 * h3PathCanonicalFirstMonomialComponentAt u t zAxis zAxis)
      nlinarith only [hzz]
    · rcases h3PathCanonical_negativePair_forces_directed hxy with hxy' | hyx'
      · refine ⟨t, ht, ⟨4, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(18 * h3PathCanonicalFirstMonomialComponentAt u t xAxis yAxis)
        exact hxy'
      · refine ⟨t, ht, ⟨5, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(18 * h3PathCanonicalFirstMonomialComponentAt u t yAxis xAxis)
        exact hyx'
    · rcases h3PathCanonical_negativePair_forces_directed hxz with hxz' | hzx'
      · refine ⟨t, ht, ⟨6, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(18 * h3PathCanonicalFirstMonomialComponentAt u t xAxis zAxis)
        exact hxz'
      · refine ⟨t, ht, ⟨7, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(18 * h3PathCanonicalFirstMonomialComponentAt u t zAxis xAxis)
        exact hzx'
    · rcases h3PathCanonical_negativePair_forces_directed hyz with hyz' | hzy'
      · refine ⟨t, ht, ⟨8, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(18 * h3PathCanonicalFirstMonomialComponentAt u t yAxis zAxis)
        exact hyz'
      · refine ⟨t, ht, ⟨9, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(18 * h3PathCanonicalFirstMonomialComponentAt u t zAxis yAxis)
        exact hzy'

/-- The obstruction index is now a fixed *ordered* velocity-component
channel, or the gradient excess. It persists at all normalized thresholds
on every terminal subtail. No exchange symmetry is required for each entry. -/
theorem h3PathCanonical_fixedJointDirectedTenSource_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ i : Fin 10, ∀ d : ℝ, d ∈ Set.Ioo b T →
      ∀ R : ℝ, 0 ≤ R →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧
          9 * R * velocityH3EnergyAt u t <
            h3PathCanonicalJointDirectedTenSourceAt u t i := by
  have hMono : ∀ i t R S, R ≤ S →
      (9 * S * velocityH3EnergyAt u t <
        h3PathCanonicalJointDirectedTenSourceAt u t i) →
      9 * R * velocityH3EnergyAt u t <
        h3PathCanonicalJointDirectedTenSourceAt u t i := by
    intro i t R S hRS hp
    have hEnergy : 0 ≤ velocityH3EnergyAt u t :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1)
        (one_le_velocityH3EnergyAt u t)
    have hScaled : R * velocityH3EnergyAt u t ≤
        S * velocityH3EnergyAt u t :=
      mul_le_mul_of_nonneg_right hRS hEnergy
    nlinarith only [hp, hScaled]
  have hCover : ∀ d : ℝ, d ∈ Set.Ioo b T →
      ∀ R : ℝ, 0 ≤ R →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ ∃ i : Fin 10,
          9 * R * velocityH3EnergyAt u t <
            h3PathCanonicalJointDirectedTenSourceAt u t i := by
    intro d hd R hR
    exact h3PathCanonical_jointDirectedTenSource_on_every_subtail
      hH3 hNoExtension hClass hb hd hR
  exact h3PathCanonical_directed_fixedIndex_cofinal_pigeonhole hb.2
    (fun i t R =>
      9 * R * velocityH3EnergyAt u t <
        h3PathCanonicalJointDirectedTenSourceAt u t i)
    hMono hCover

/-- Separate eventual normalized ceilings on all ten *ordered* sources
suffice for continuation. Each source may have its own tail and bound. -/
theorem h3PathCanonical_extension_of_separateDirectedTenSourceCeilings
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeilings : ∀ i : Fin 10,
      ∃ d : ℝ, d ∈ Set.Ioo b T ∧
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ t : ℝ, t ∈ Set.Ioo d T →
            h3PathCanonicalJointDirectedTenSourceAt u t i ≤
              9 * R * velocityH3EnergyAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, hPersistent⟩ :=
    h3PathCanonical_fixedJointDirectedTenSource_on_every_subtail
      hH3 hNoExtension hClass hb
  obtain ⟨d, hd, R, hR, hBound⟩ := hCeilings i
  obtain ⟨t, ht, hBad⟩ := hPersistent d hd R hR
  exact (not_lt_of_ge (hBound t ht)) hBad

end Euclidean
end Bridge
end PrimeTensor
