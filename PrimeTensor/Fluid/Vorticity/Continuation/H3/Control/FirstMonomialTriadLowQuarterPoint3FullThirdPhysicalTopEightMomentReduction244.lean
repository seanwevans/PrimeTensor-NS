import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopVelocityMomentFactor244
import Mathlib.Tactic

/-!
# Isolate the eighth-moment velocity obstruction from the six-factor corridor

The existing physical fourth-radial top-mass escape theorem forces one of six
velocity input quantities arbitrarily high on every terminal subtail. Four
of those inputs are low Fourier L¹ / L² masses, whereas the other two are
true eighth-order raw moments of the velocity components. Under an explicit
uniform low-input ceiling, the escape must therefore occur in the eighth
moments. No time-uniform L¹ estimate is asserted without proof, and the
strict-time order-eight integrability premise is retained.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual eighth-order raw Fourier moment of one physical velocity
coordinate, zero-extended off the strict physical interval. -/
noncomputable def h3PathVelocityRawEightMomentComponent244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    h3SpectralScalarRawFourierMomentMass (8 : ℝ)
      (h3TerminalVelocitySpectralStateAt hH3 t htAbs j)
  else 0

/-- The second of the six Young factors is the eighth moment of the first
velocity input (index `2` in the six-factor enumeration). -/
theorem h3Path_orderEightPrimitive_two_eq_velocityMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (k j : Fin 3) :
    h3PathOrderEightVelocityPairPrimitive244 hH3 hClass k j (2 : Fin 6) t =
      h3PathVelocityRawEightMomentComponent244 hH3 hClass k t := by
  unfold h3PathOrderEightVelocityPairPrimitive244
    h3PathVelocityRawEightMomentComponent244
  simp only [dite_eq_left ht]
  simp [h3RawOrderEightVelocityPairPrimitive244]

/-- The sixth of the six Young factors is the eighth moment of the second
velocity input (index `5` in the six-factor enumeration). -/
theorem h3Path_orderEightPrimitive_five_eq_velocityMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (k j : Fin 3) :
    h3PathOrderEightVelocityPairPrimitive244 hH3 hClass k j (5 : Fin 6) t =
      h3PathVelocityRawEightMomentComponent244 hH3 hClass j t := by
  unfold h3PathOrderEightVelocityPairPrimitive244
    h3PathVelocityRawEightMomentComponent244
  simp only [dite_eq_left ht]
  simp [h3RawOrderEightVelocityPairPrimitive244]

/-- The four non-eighth-moment factors are just the genuine raw Fourier
L² and L¹ masses of the two input velocity components. -/
theorem h3_orderEightVelocityPairPrimitive_lowBound244
    (U : H3SpectralFinVectorState) (k j : Fin 3) (B : ℝ)
    (hConj : ‖h3SpectralScalarRawFourierConjL2 (U k)‖ ≤ B)
    (hL2 : ‖h3SpectralScalarRawFourierL2 (U j)‖ ≤ B)
    (hL1j : h3SpectralScalarRawFourierL1Mass (U j) ≤ B)
    (hL1k : h3SpectralScalarRawFourierL1Mass (U k) ≤ B)
    (q : Fin 6) (hq2 : q ≠ 2) (hq5 : q ≠ 5) :
    h3RawOrderEightVelocityPairPrimitive244 U k j q ≤ B := by
  fin_cases q
  · simpa [h3RawOrderEightVelocityPairPrimitive244] using hConj
  · simpa [h3RawOrderEightVelocityPairPrimitive244] using hL2
  · exact False.elim (hq2 rfl)
  · simpa [h3RawOrderEightVelocityPairPrimitive244] using hL1j
  · simpa [h3RawOrderEightVelocityPairPrimitive244] using hL1k
  · exact False.elim (hq5 rfl)

/-- A ceiling on exactly the four low primitive channels forces the
cofinally escaping six-factor obstruction into channels `2` or `5`, i.e.
into actual eighth-order velocity moments. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMoment_of_lowPrimitiveCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hLow : ∀ t (ht : t ∈ Set.Ioo a T), s < t →
      ∀ (k j : Fin 3) (q : Fin 6), q ≠ 2 → q ≠ 5 →
      h3PathOrderEightVelocityPairPrimitive244 hH3 hClass k j q t ≤ B) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r := by
  intro σ hσ K
  let H : ℝ := max B K + 1
  have hBH : B < H := by
    dsimp [H]
    have hMax := le_max_left B K
    linarith only [hMax]
  have hKH : K < H := by
    dsimp [H]
    have hMax := le_max_right B K
    linarith only [hMax]
  obtain ⟨r, hr, k, j, q, hHigh⟩ :=
    h3Path_unboundedPhysicalTop_forces_eightMomentPrimitiveEscape244
      hH3 hClass hs hEscape hMom σ hσ H
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 (lt_trans hσ.1 hr.1), hr.2⟩
  by_cases hq2 : q = 2
  · subst q
    refine ⟨r, hr, k, ?_⟩
    rw [← h3Path_orderEightPrimitive_two_eq_velocityMoment244
      hH3 hClass hrClass k j]
    exact lt_trans hKH hHigh
  by_cases hq5 : q = 5
  · subst q
    refine ⟨r, hr, j, ?_⟩
    rw [← h3Path_orderEightPrimitive_five_eq_velocityMoment244
      hH3 hClass hrClass k j]
    exact lt_trans hKH hHigh
  have hBound := hLow r hrClass (lt_trans hσ.1 hr.1) k j q hq2 hq5
  exact False.elim ((not_lt_of_ge hBound) (lt_trans hBH hHigh))

/-- The same eighth-moment escape criterion, with the low Fourier premise
stated directly as uniform estimates for actual physical velocity components.
No uniform kinetic/Fourier-L¹ bound is manufactured by this theorem. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMoment_of_lowFourierCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hLow : ∀ t (ht : t ∈ Set.Ioo a T), s < t →
      ∀ k : Fin 3,
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let U : H3SpectralFinVectorState :=
        h3TerminalVelocitySpectralStateAt hH3 t htAbs
      ‖h3SpectralScalarRawFourierConjL2 (U k)‖ ≤ B ∧
      ‖h3SpectralScalarRawFourierL2 (U k)‖ ≤ B ∧
      h3SpectralScalarRawFourierL1Mass (U k) ≤ B) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r := by
  apply h3Path_unboundedPhysicalTop_forces_eightMoment_of_lowPrimitiveCeiling244
    (B := B) hH3 hClass hs hEscape hMom
  intro t ht hst k j q hq2 hq5
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hk := hLow t ht hst k
  have hj := hLow t ht hst j
  unfold h3PathOrderEightVelocityPairPrimitive244
  rw [dite_eq_left ht]
  exact h3_orderEightVelocityPairPrimitive_lowBound244 U k j B
    hk.1 hj.2.1 hj.2.2 hk.2.2 q hq2 hq5

end
end PrimeTensor.FirstMonomialTriad
