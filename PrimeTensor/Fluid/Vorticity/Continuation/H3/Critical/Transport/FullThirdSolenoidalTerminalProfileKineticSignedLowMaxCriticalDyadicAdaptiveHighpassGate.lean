import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicKineticHighpassForcing
import Mathlib.Tactic

/-!
# One physical source peak works at every Fourier cutoff

The preceding cubic-rate source-peak result chooses an actual physical time
on a last-half window. The kinetic low/high decomposition, however, was
presented with a prescribed cutoff BEFORE that time was selected.

Here the real forcing peak is chosen FIRST, using only the exact PDE clock.
At that same strict time, every nonnegative Fourier radius satisfies the
kinetic low-band plus exact nonlinear highpass inequality. In particular
any radius selected a posteriori from the *observed* top H3 dissipation
must either spend the kinetic low-band budget or exhibit a quantitative
highpass Leray forcing charge. In the second branch one actual Fourier
forcing coordinate witnesses the charge (it may depend on the radius).

No raw order-eight Fourier moments, highpass smallness, or new PDE ceiling
are assumed. This strengthens the quantifier order of the necessary source
obstruction. It does NOT rule out a singular Navier--Stokes trajectory:
the new mathematical estimate required next is a natural H3/viscous upper
control on the nonlinear highpass forcing at the selected physical time.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A SINGLE true interior peak selected by the physical cubic clock
satisfies the kinetic/highpass forcing budget at EVERY real cutoff. The
cutoff is quantified after the physical witness, not before it. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_allRadiusHighpassBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      ∀ ρ : ℝ, 0 ≤ ρ →
        K * h3TerminalPhysicalTopDissipation3Path hClass r <
          2 * (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
                ρ (velocityH3Energy0At u b) +
              ∑ j : Fin 3,
                (‖thirdFullPhysicalCriticalThirdForcingHighpass244
                    hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  obtain ⟨r, hr, hPeak⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_thirdRadialLerayPeak244
      hH3 hClass hsClass htClass hst hD hDouble B hB hRate K hNear
  have hrTail : r ∈ Set.Ioo b T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  refine ⟨r, hr, ?_⟩
  intro ρ hρ
  exact lt_of_lt_of_le hPeak
    (thirdFullPhysical_criticalThirdForcingMass_kineticLowHigh244
      hH3 hClass b hb ρ hρ r hrTail)

/-- At the SAME physical witness, every radius has the low-versus-high
alternative. The cutoff can be a function of the observed physical state. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_allRadiusLowOrHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      ∀ ρ : ℝ, 0 ≤ ρ →
        (K * h3TerminalPhysicalTopDissipation3Path hClass r <
          12 * (2 * Real.pi) ^ 6 *
            thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b) ∨
         K * h3TerminalPhysicalTopDissipation3Path hClass r <
          4 * (2 * Real.pi) ^ 6 *
            ∑ j : Fin 3,
              (‖thirdFullPhysicalCriticalThirdForcingHighpass244
                  hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  obtain ⟨r, hr, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_allRadiusHighpassBudget244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, ?_⟩
  intro ρ hρ
  let X : ℝ := K * h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6
  let L : ℝ := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  let H : ℝ := ∑ j : Fin 3,
    (‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j r‖ : ℝ) ^ 2
  have hLarge : X < 2 * C * (3 * L + H) := by
    simpa only [X, C, L, H] using hAll ρ hρ
  have hSplit : X < 12 * C * L ∨ X < 4 * C * H := by
    by_cases hSmallLow : X < 12 * C * L
    · exact Or.inl hSmallLow
    · right
      have hLowLarge : 12 * C * L ≤ X := le_of_not_gt hSmallLow
      nlinarith only [hLarge, hLowLarge]
  simpa only [X, C, L, H] using hSplit

/-- Every radius whose kinetically controlled portion is less than half
of the peak necessarily carries a quantitatively large true nonlinear
highpass source at that same physical time. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_adaptiveHighpassCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      ∀ ρ : ℝ, 0 ≤ ρ →
        (12 * (2 * Real.pi) ^ 6 *
            thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b) ≤
            K * h3TerminalPhysicalTopDissipation3Path hClass r →
         K * h3TerminalPhysicalTopDissipation3Path hClass r <
           4 * (2 * Real.pi) ^ 6 *
             ∑ j : Fin 3,
               (‖thirdFullPhysicalCriticalThirdForcingHighpass244
                   hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  obtain ⟨r, hr, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_allRadiusHighpassBudget244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, ?_⟩
  intro ρ hρ hLow
  let X : ℝ := K * h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6
  let L : ℝ := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  let H : ℝ := ∑ j : Fin 3,
    (‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j r‖ : ℝ) ^ 2
  have hLarge : X < 2 * C * (3 * L + H) := by
    simpa only [X, C, L, H] using hAll ρ hρ
  have hLowLarge : 12 * C * L ≤ X := by
    simpa only [X, C, L] using hLow
  have hHigh : X < 4 * C * H := by
    nlinarith only [hLarge, hLowLarge]
  simpa only [X, C, H] using hHigh

/-- A single actual third-radial Leray coordinate pays the highpass charge.
The time is fixed before the cutoff; the coordinate may depend on it. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_oneHighpassCoordinate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      ∀ ρ : ℝ, 0 ≤ ρ →
        (12 * (2 * Real.pi) ^ 6 *
            thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b) ≤
            K * h3TerminalPhysicalTopDissipation3Path hClass r →
         ∃ j : Fin 3,
           K * h3TerminalPhysicalTopDissipation3Path hClass r <
             12 * (2 * Real.pi) ^ 6 *
               (‖thirdFullPhysicalCriticalThirdForcingHighpass244
                   hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  classical
  obtain ⟨r, hr, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_adaptiveHighpassCharge244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, ?_⟩
  intro ρ hρ hLow
  let X : ℝ := K * h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6
  let f (j : Fin 3) : ℝ :=
    (‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j r‖ : ℝ) ^ 2
  have hHigh : X < 4 * C * (∑ j : Fin 3, f j) := by
    simpa only [X, C, f] using hAll ρ hρ hLow
  by_contra hNone
  have hEach (j : Fin 3) : 12 * C * f j ≤ X := by
    apply le_of_not_gt
    intro hLarge
    apply hNone
    refine ⟨j, ?_⟩
    simpa only [X, C, f] using hLarge
  have hSum : 4 * C * (∑ j : Fin 3, f j) ≤ X := by
    calc
      4 * C * (∑ j : Fin 3, f j) =
          ∑ j : Fin 3, (4 * C) * f j := by rw [Finset.mul_sum]
      _ ≤ ∑ _j : Fin 3, X / 3 := by
        apply Finset.sum_le_sum
        intro j _
        have hj := hEach j
        nlinarith only [hj]
      _ = X := by simp <;> ring
  exact (not_lt_of_ge hSum) hHigh

end
end PrimeTensor.FirstMonomialTriad
