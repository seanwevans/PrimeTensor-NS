import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopCubicTerminalCriterion244
import Mathlib.Tactic

/-!
# Physical unnormalized fourth-radial dissipation: cubic forcing clock

The exact Fourier Navier--Stokes PDE identity yields

  D3'(t) + M5(t) + P(t) = M3(t),    M5, P >= 0,

so D3'(t) <= M3(t). Unlike the normalized logarithmic result this
requires no positivity of D3. The actual third-radial Leray forcing mass
M3 is continuous on compact strict intervals; a one-sided derivative
argument makes D3' interval integrable without assuming its continuity.
The raw physical clock is

  D3(t) - D3(s) <= integral_s^t M3(r) dr.

Thus escape of the actual fourth-radial mass requires unbounded cumulative
*unnormalized* cubic forcing mass, and arbitrarily large instantaneous
unnormalized forcing mass on every terminal subtail. The time-integrated
source is not asserted to be finite uniformly up to terminal time.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- The genuine unnormalized third-radial Leray forcing square mass is
continuous, hence time-integrable, on every compact strict H3 interval.
This fact does not require D3 to be positive. -/
theorem h3Path_topRawCubicMass_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    IntervalIntegrable
      (h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile hH3 hClass)
      volume s t := by
  have hInside : Set.Icc s t ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  exact ((h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
    hH3 hClass).mono hInside).intervalIntegrable_of_Icc hst

/-- Physical fourth-radial top-mass derivative is automatically integrable
on compact strict intervals. No positive lower bound for D3 is needed.
A continuous upper forcing ceiling and the one-sided derivative theorem
suffice, even if D3' itself is not continuous. -/
theorem h3Path_topRawDerivative_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    IntervalIntegrable
      (deriv (h3TerminalPhysicalTopDissipation3Path hClass)) volume s t := by
  let F : ℝ → ℝ := h3TerminalPhysicalTopDissipation3Path hClass
  let M : ℝ → ℝ :=
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile hH3 hClass
  have hInside : Set.Icc s t ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hMassCont : ContinuousOn M (Set.Icc s t) :=
    (h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
      hH3 hClass).mono hInside
  obtain ⟨r₀, _hr₀, hMaximum⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hst) hMassCont
  have hPathDeriv (r : ℝ) (hr : r ∈ Set.Icc s t) :
      HasDerivAt F (deriv F r) r := by
    have h := h3TerminalPhysicalTopDissipation3Path_hasDerivAt
      hH3 hClass (hInside hr)
    rw [h.deriv]
    exact h
  have hPathCont : ContinuousOn F (Set.Icc s t) := by
    intro r hr
    exact (hPathDeriv r hr).continuousAt.continuousWithinAt
  have hOpenDeriv : ∀ r, r ∈ Set.Ioo s t → HasDerivAt F (deriv F r) r := by
    intro r hr
    exact hPathDeriv r ⟨hr.1.le, hr.2.le⟩
  have hBound : ∀ r, r ∈ Set.Ioo s t → deriv F r ≤ M r₀ := by
    intro r hr
    have hrClosed : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2.le⟩
    calc
      deriv F r ≤ h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass (hInside hrClosed) :=
        h3Path_topDerivative_le_cubic244 hH3 hClass (hInside hrClosed)
      _ = M r := (h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
          hH3 hClass (hInside hrClosed)).symm
      _ ≤ M r₀ := hMaximum hrClosed
  exact h3_scalar_signedRate_intervalIntegrable_of_upperDerivative244
    F (deriv F) s t (M r₀) hst hPathCont hOpenDeriv hBound

/-- The raw physical fourth-radial moment is controlled additively by
actual third-radial Leray forcing action. The proof does NOT divide by D3. -/
theorem h3Path_topRawDissipation_le_integratedCubicMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    velocityH3Dissipation3At u t ≤ velocityH3Dissipation3At u s +
      ∫ r in s..t,
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile hH3 hClass r := by
  let F : ℝ → ℝ := h3TerminalPhysicalTopDissipation3Path hClass
  let M : ℝ → ℝ :=
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile hH3 hClass
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDiff : ∀ r : ℝ, r ∈ Set.uIcc s t → DifferentiableAt ℝ F r := by
    intro r hr
    rw [Set.uIcc_of_le hst] at hr
    exact (h3TerminalPhysicalTopDissipation3Path_hasDerivAt
      hH3 hClass (hInside r hr)).differentiableAt
  have hIntDeriv : IntervalIntegrable (deriv F) volume s t :=
    h3Path_topRawDerivative_intervalIntegrable244 hH3 hClass hs ht hst
  have hIntMass : IntervalIntegrable M volume s t :=
    h3Path_topRawCubicMass_intervalIntegrable244 hH3 hClass hs ht hst
  have hFTC := intervalIntegral.integral_deriv_eq_sub hDiff hIntDeriv
  have hIntegralBound : (∫ r in s..t, deriv F r) ≤ ∫ r in s..t, M r := by
    apply intervalIntegral.integral_mono_on hst hIntDeriv hIntMass
    intro r hr
    calc
      deriv F r ≤
          h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
            hH3 hClass (hInside r hr) :=
        h3Path_topDerivative_le_cubic244 hH3 hClass (hInside r hr)
      _ = M r := (h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
          hH3 hClass (hInside r hr)).symm
  have hRaw : F t - F s ≤ ∫ r in s..t, M r := by
    rw [← hFTC]
    exact hIntegralBound
  have hGrowth : F t ≤ F s + ∫ r in s..t, M r := by
    linarith only [hRaw]
  change
    h3TerminalPhysicalTopDissipation3Path hClass t ≤
      h3TerminalPhysicalTopDissipation3Path hClass s +
        ∫ r in s..t,
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass r at hGrowth
  rw [h3TerminalPhysicalTopDissipation3Path_eq hClass ht,
      h3TerminalPhysicalTopDissipation3Path_eq hClass hs] at hGrowth
  exact hGrowth

/-- An a priori bound on the unnormalized cubic Leray action bounds D3,
with no hypothesis that D3 be strictly positive on the interval. -/
theorem h3Path_boundedRawCubicAction_bounds_topPhysicalDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hAction : ∀ t, t ∈ Set.Ioo s T →
      (∫ r in s..t,
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass r) ≤ B) :
    ∀ t, t ∈ Set.Ioo s T →
      velocityH3Dissipation3At u t ≤ velocityH3Dissipation3At u s + B := by
  intro t ht
  have htClass : t ∈ Set.Ioo a T := ⟨lt_trans hs.1 ht.1, ht.2⟩
  have hIntegralBound :
      velocityH3Dissipation3At u s +
        (∫ r in s..t,
          h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
            hH3 hClass r) ≤
        velocityH3Dissipation3At u s + B := by
    calc
      velocityH3Dissipation3At u s +
          (∫ r in s..t,
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass r) =
          (∫ r in s..t,
            h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
              hH3 hClass r) + velocityH3Dissipation3At u s := by ring
      _ ≤ B + velocityH3Dissipation3At u s :=
        add_le_add_left (hAction t ht) _
      _ = velocityH3Dissipation3At u s + B := by ring
  exact (h3Path_topRawDissipation_le_integratedCubicMass244
    hH3 hClass hs htClass ht.1.le).trans hIntegralBound

/-- Terminal escape of the actual fourth-radial physical mass implies
unbounded cumulative UNNORMALIZED third-radial Leray forcing action.
Unlike the previous logarithmic criterion, no D3 positivity is used. -/
theorem h3Path_unboundedPhysicalTop_forces_unboundedRawCubicAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    ∀ B : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      B < ∫ r in s..t,
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass r := by
  intro B
  by_contra hNo
  have hAction : ∀ t, t ∈ Set.Ioo s T →
      (∫ r in s..t,
        h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass r) ≤ B := by
    intro t ht
    exact le_of_not_gt (by
      intro hGreater
      exact hNo ⟨t, ht, hGreater⟩)
  have hTop := h3Path_boundedRawCubicAction_bounds_topPhysicalDissipation244
    hH3 hClass hs hAction
  obtain ⟨t, ht, hLarge⟩ := hEscape (velocityH3Dissipation3At u s + B)
  exact (not_lt_of_ge (hTop t ht)) hLarge

/-- Bound the actual D3 growth by a pointwise ceiling on the *raw* cubic
forcing mass. This is mean-value calculus, requiring no D3 positivity. -/
theorem h3Path_topRawDissipationGrowth_le_cubicMassCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hCeiling : ∀ r, r ∈ Set.Ioo s t →
      h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClass r ≤ K) :
    velocityH3Dissipation3At u t - velocityH3Dissipation3At u s ≤
      K * (t - s) := by
  let F : ℝ → ℝ := h3TerminalPhysicalTopDissipation3Path hClass
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hPathDeriv (r : ℝ) (hr : r ∈ Set.Icc s t) :=
    h3TerminalPhysicalTopDissipation3Path_hasDerivAt hH3 hClass (hInside r hr)
  have hCont : ContinuousOn F (Set.Icc s t) := by
    intro r hr
    exact (hPathDeriv r hr).continuousAt.continuousWithinAt
  have hDifferentiable : DifferentiableOn ℝ F (interior (Set.Icc s t)) := by
    intro r hr
    exact (hPathDeriv r (interior_subset hr)).differentiableAt.differentiableWithinAt
  have hBound : ∀ r ∈ interior (Set.Icc s t), deriv F r ≤ K := by
    intro r hr
    have hrClosed : r ∈ Set.Icc s t := interior_subset hr
    have hrOpen : r ∈ Set.Ioo s t := by
      simpa only [interior_Icc] using hr
    calc
      deriv F r ≤ h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass (hInside r hrClosed) :=
        h3Path_topDerivative_le_cubic244 hH3 hClass (hInside r hrClosed)
      _ = h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
          hH3 hClass r := (h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
          hH3 hClass (hInside r hrClosed)).symm
      _ ≤ K := hCeiling r hrOpen
  have hGrowth := h3_scalar_oneSidedDerivativeCeiling244
    F s t K hst hCont hDifferentiable hBound
  change
    h3TerminalPhysicalTopDissipation3Path hClass t -
      h3TerminalPhysicalTopDissipation3Path hClass s ≤
        K * (t - s) at hGrowth
  rw [h3TerminalPhysicalTopDissipation3Path_eq hClass ht,
      h3TerminalPhysicalTopDissipation3Path_eq hClass hs] at hGrowth
  exact hGrowth

/-- Top mass escape forces unbounded INSTANTANEOUS raw cubic forcing mass,
not only unbounded cubic/D3 ratio. This is a genuine higher Fourier source
necessity, uniform across a fixed finite terminal time horizon. -/
theorem h3Path_unboundedPhysicalTop_forces_highRawCubicMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    ∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClass r := by
  intro K
  by_contra hNo
  let L : ℝ := max K 0
  have hL : 0 ≤ L := le_max_right K 0
  have hCeiling : ∀ r, r ∈ Set.Ioo s T →
      h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClass r ≤ L := by
    intro r hr
    have hNot : ¬ K < h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClass r := by
      intro hHigh
      exact hNo ⟨r, hr, hHigh⟩
    exact (le_of_not_gt hNot).trans (le_max_left K 0)
  have hBound : ∀ t, t ∈ Set.Ioo s T →
      velocityH3Dissipation3At u t ≤
        velocityH3Dissipation3At u s + L * (T - s) := by
    intro t ht
    have htClass : t ∈ Set.Ioo a T := ⟨lt_trans hs.1 ht.1, ht.2⟩
    have hGrowth := h3Path_topRawDissipationGrowth_le_cubicMassCeiling244
      hH3 hClass hs htClass ht.1.le
      (fun r hr => hCeiling r ⟨hr.1, lt_trans hr.2 ht.2⟩)
    have hDuration : L * (t - s) ≤ L * (T - s) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le s) hL
    linarith only [hGrowth, hDuration]
  obtain ⟨t, ht, hLarge⟩ := hEscape
    (velocityH3Dissipation3At u s + L * (T - s))
  exact (not_lt_of_ge (hBound t ht)) hLarge

/-- The necessary unnormalized cubic blowup is witnessed by the actual
three-component third-radial Fourier Leray L2 square norms. This is the
physical spectral forcing decoder, not a new scalar proxy. -/
theorem h3Path_unboundedPhysicalTop_forces_highThirdRadialFourierNormSum244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    ∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < (2 * Real.pi) ^ 6 *
        ∑ j : Fin 3,
          (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
             hH3 hClass j r‖ : ℝ) ^ 2 := by
  intro K
  obtain ⟨r, hr, hHigh⟩ :=
    h3Path_unboundedPhysicalTop_forces_highRawCubicMass244
      hH3 hClass hs hEscape K
  have hrClass : r ∈ Set.Ioo a T := ⟨lt_trans hs.1 hr.1, hr.2⟩
  rw [h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq_sum_norm_sq_thirdRadialPath
    hH3 hClass hrClass] at hHigh
  exact ⟨r, hr, hHigh⟩

end
end PrimeTensor.FirstMonomialTriad
