import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialJointObstruction

/-!
# A fixed H³ obstruction source on every terminal subtail

The preceding signed theorem gave seven *possible* adverse sources at each
terminal time: the H³ gradient excess and six symmetric first-monomial
velocity-component channels.  This file proves a finite-pigeonhole upgrade:
under nonextension, **one fixed index among those seven** works at arbitrarily
large normalized thresholds on *every* strict terminal subtail.

The resulting channel may be the gradient excess or one of the six signed
channels.  The proof does not decide which channel occurs and does not show
any favorable PDE sign.  The same result yields continuation when each of
the seven sources has its *own* eventual normalized ceiling, possibly on
seven different terminal tails with seven different constants.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- A seven-index scalar representation of the joint obstruction.
Index zero is the gradient excess `G-D`.  Indices 1,2,3 are the negatives
of nine times the `xx`, `yy`, `zz` component channels; indices 4,5,6 are
the negatives of nine times the `xy+yx`, `xz+zx`, `yz+zy` channel pairs.
The common adversity comparison is `9 * R * E < source`. -/
noncomputable def h3PathCanonicalJointSevenSourceAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (i : Fin 7) : ℝ :=
  let Q := h3PathCanonicalFirstMonomialComponentAt u t
  match i.val with
  | 0 =>
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
        velocityH3DissipationAt u t
  | 1 => -(9 * Q xAxis xAxis)
  | 2 => -(9 * Q yAxis yAxis)
  | 3 => -(9 * Q zAxis zAxis)
  | 4 => -(9 * (Q xAxis yAxis + Q yAxis xAxis))
  | 5 => -(9 * (Q xAxis zAxis + Q zAxis xAxis))
  | _ => -(9 * (Q yAxis zAxis + Q zAxis yAxis))

/-- Finite pigeonhole with *both* a terminal-tail parameter and a threshold.
If every tail/threshold has one witness from a finite index set, and increasing
the threshold only strengthens each predicate, there is one fixed index with
witnesses on every tail at every nonnegative threshold. -/
private theorem h3PathCanonical_fixedIndex_cofinal_pigeonhole
    {b T : ℝ} (hbT : b < T)
    (P : Fin 7 → ℝ → ℝ → Prop)
    (hMono : ∀ i t R S, R ≤ S → P i t S → P i t R)
    (hCover : ∀ d : ℝ, d ∈ Set.Ioo b T →
      ∀ R : ℝ, 0 ≤ R →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ ∃ i : Fin 7, P i t R) :
    ∃ i : Fin 7, ∀ d : ℝ, d ∈ Set.Ioo b T →
      ∀ R : ℝ, 0 ≤ R →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ P i t R := by
  classical
  by_contra hNone
  have hBad (i : Fin 7) :
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
  have hAll (s : Finset (Fin 7)) :
      ∃ d : ℝ, d ∈ Set.Ioo b T ∧
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ i : Fin 7, i ∈ s →
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

/-- Hypothetical H³ nonextension selects one *fixed* obstruction index from
seven possibilities.  At every prescribed normalized threshold `R >= 0` and
on every strict terminal subtail, that same index has a physical witness.
This does **not** prove an unbounded physical norm or settle continuation. -/
theorem h3PathCanonical_fixedJointSevenSource_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ i : Fin 7, ∀ d : ℝ, d ∈ Set.Ioo b T →
      ∀ R : ℝ, 0 ≤ R →
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧
          9 * R * velocityH3EnergyAt u t <
            h3PathCanonicalJointSevenSourceAt u t i := by
  have hMono : ∀ i t R S, R ≤ S →
      (9 * S * velocityH3EnergyAt u t <
        h3PathCanonicalJointSevenSourceAt u t i) →
      9 * R * velocityH3EnergyAt u t <
        h3PathCanonicalJointSevenSourceAt u t i := by
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
        ∃ t : ℝ, t ∈ Set.Ioo d T ∧ ∃ i : Fin 7,
          9 * R * velocityH3EnergyAt u t <
            h3PathCanonicalJointSevenSourceAt u t i := by
    intro d hd R hR
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
      · refine ⟨t, ht, ⟨4, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(9 * (h3PathCanonicalFirstMonomialComponentAt u t xAxis yAxis +
            h3PathCanonicalFirstMonomialComponentAt u t yAxis xAxis))
        nlinarith only [hxy]
      · refine ⟨t, ht, ⟨5, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(9 * (h3PathCanonicalFirstMonomialComponentAt u t xAxis zAxis +
            h3PathCanonicalFirstMonomialComponentAt u t zAxis xAxis))
        nlinarith only [hxz]
      · refine ⟨t, ht, ⟨6, by decide⟩, ?_⟩
        change 9 * R * velocityH3EnergyAt u t <
          -(9 * (h3PathCanonicalFirstMonomialComponentAt u t yAxis zAxis +
            h3PathCanonicalFirstMonomialComponentAt u t zAxis yAxis))
        nlinarith only [hyz]
  exact h3PathCanonical_fixedIndex_cofinal_pigeonhole hb.2
    (fun i t R =>
      9 * R * velocityH3EnergyAt u t <
        h3PathCanonicalJointSevenSourceAt u t i)
    hMono hCover

/-- Individual terminal ceilings for the seven sources suffice for
continuation, even if the ceilings use different constants and begin on
different strict terminal subtails.  No one *common* tail or `R` is assumed. -/
theorem h3PathCanonical_extension_of_separateSevenSourceEventualCeilings
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeilings : ∀ i : Fin 7,
      ∃ d : ℝ, d ∈ Set.Ioo b T ∧
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ t : ℝ, t ∈ Set.Ioo d T →
            h3PathCanonicalJointSevenSourceAt u t i ≤
              9 * R * velocityH3EnergyAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨i, hPersistent⟩ :=
    h3PathCanonical_fixedJointSevenSource_on_every_subtail
      hH3 hNoExtension hClass hb
  obtain ⟨d, hd, R, hR, hBound⟩ := hCeilings i
  obtain ⟨t, ht, hBad⟩ := hPersistent d hd R hR
  exact (not_lt_of_ge (hBound t ht)) hBad

end Euclidean
end Bridge
end PrimeTensor
