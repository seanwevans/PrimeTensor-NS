import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryPDEClock
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousPolynomialCutoffBarrier
import Mathlib.Tactic

/-!
# Constructive reciprocal-square-root tail threshold for late viscous PDE peaks

Let A>0 be the normalized prescribed-gauge late spike, B>0 the actual
terminal H³ viscous action, R>0 the physical quintic rate multiplier, and
E>=0 the fixed kinetic anchor. The two-slice rate branch reads

  A² <= R B (E+3 D(sState)) (E+3 D(sSource)).

Whenever 4 R B E² < A², no arbitrary height threshold is required: choose

  h = A / (12 sqrt(R B)) > 0.

Then R B (E+3h)² < A², so one of the ACTUAL selected times has D(s)>h.
The existing finite-band Navier--Stokes clock gives a second physical window
with a tail charge and a new capturing frequency J2. Kinetic anchoring
therefore forces h/2 < 4 E0(b) (J2+1)^8. This is a quantitative source/
viscous/frequency escape criterion, not a uniform bound or continuation.
It does not assume the secondary window is disjoint from the original one.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The natural reciprocal-square-root terminal-tail height automatically
exceeds the kinetic-only payment if that payment is less than a quarter
of the squared normalized spike. -/
theorem thirdFull_scalar_twoSlice_constructiveSqrtTailThreshold244
    (A B R E : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) (hE : 0 ≤ E)
    (hGap : 4 * R * B * E ^ 2 < A ^ 2) :
    0 < A / (12 * Real.sqrt (R * B)) ∧
      R * (E + 3 * (A / (12 * Real.sqrt (R * B)))) ^ 2 * B < A ^ 2 := by
  let q : ℝ := Real.sqrt (R * B)
  have hRB : 0 < R * B := mul_pos hR hB
  have hq : 0 < q := Real.sqrt_pos.2 hRB
  have hqSq : q ^ 2 = R * B := Real.sq_sqrt hRB.le
  have hPos : 0 < A / (12 * q) := by positivity
  have hSquared : (2 * q * E) ^ 2 < A ^ 2 := by
    calc
      (2 * q * E) ^ 2 = 4 * q ^ 2 * E ^ 2 := by ring
      _ = 4 * R * B * E ^ 2 := by rw [hqSq]; ring
      _ < A ^ 2 := hGap
  have hKinetic : 2 * q * E < A :=
    (sq_lt_sq₀ (by positivity : 0 ≤ 2 * q * E) hA.le).1 hSquared
  have hCancel :
      q * (E + 3 * (A / (12 * q))) = q * E + A / 4 := by
    field_simp [ne_of_gt hq]
    <;> ring
  have hUpper : q * (E + 3 * (A / (12 * q))) < A := by
    rw [hCancel]
    linarith only [hKinetic, hA]
  have hLeft : 0 ≤ q * (E + 3 * (A / (12 * q))) := by
    positivity
  have hSmallSq :
      (q * (E + 3 * (A / (12 * q)))) ^ 2 < A ^ 2 :=
    (sq_lt_sq₀ hLeft hA.le).2 hUpper
  have hEquality :
      R * (E + 3 * (A / (12 * q))) ^ 2 * B =
        (q * (E + 3 * (A / (12 * q)))) ^ 2 := by
    rw [mul_pow, hqSq]
    ring
  constructor
  · simpa only [q] using hPos
  · have hFinal : R * (E + 3 * (A / (12 * q))) ^ 2 * B < A ^ 2 := by
      rw [hEquality]
      exact hSmallSq
    simpa only [q] using hFinal

/-- At the selected actual late source/state maxima, a kinetic-only gap
constructively forces one physical viscous observation above A/(12 sqrt(RB))
and thus a NEW finite-band Navier--Stokes persistence interval. -/
theorem thirdFullPhysical_twoSlice_constructiveSqrtTailPDEClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m sState sSource A B R E : ℝ)
    (hm : m ∈ Set.Ioo a T)
    (hsState : sState ∈ Set.Ioo m T)
    (hsSource : sSource ∈ Set.Ioo m T)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) (hE : 0 ≤ E)
    (hRate : A ^ 2 ≤
      R * (E + 3 * velocityH3DissipationAt u sState) *
        (E + 3 * velocityH3DissipationAt u sSource) * B)
    (hGap : 4 * R * B * E ^ 2 < A ^ 2) :
    let h := A / (12 * Real.sqrt (R * B))
    0 < h ∧
      (h < velocityH3DissipationAt u sState ∨
        h < velocityH3DissipationAt u sSource) ∧
      ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h := by
  obtain ⟨hh, hBeyond⟩ :=
    thirdFull_scalar_twoSlice_constructiveSqrtTailThreshold244
      A B R E hA hB hR hE hGap
  let h : ℝ := A / (12 * Real.sqrt (R * B))
  have hSpike := thirdFull_scalar_twoSliceRate_forces_actualViscousObservation244
    A B R E (velocityH3DissipationAt u sState)
      (velocityH3DissipationAt u sSource) h
      hB.le hR.le hE
      (velocityH3DissipationAt_nonneg u sState)
      (velocityH3DissipationAt_nonneg u sSource)
      hRate (by simpa only [h] using hBeyond)
  have hClock := thirdFullPhysical_twoSelectedTimes_secondaryPDEClock244
    hH3 hClass hDInt m sState sSource h hm hsState hsSource
      (by simpa only [h] using hh) hSpike
  exact ⟨by simpa only [h] using hh, hSpike, hClock⟩

/-- A second clock above height h/2 must escape the eighth-power kinetic
low-frequency ceiling. This applies even if the two late windows overlap. -/
theorem thirdFullPhysical_secondaryClock_forces_eighthCutoffPayment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m sState sSource h : ℝ)
    (hsState : sState ∈ Set.Ioo b T)
    (hsSource : sSource ∈ Set.Ioo b T)
    (hClock : ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h) :
    ∃ J2 : ℕ, h / 2 <
      4 * velocityH3Energy0At u b * (((J2 : ℝ) + 1) ^ 8) := by
  rcases hClock with ⟨s, hWhich, J2, zSource, zState, eta,
      _hzSource, _hzState, _hEtaEq, hEta, _hEnd, hFloor, _hCost⟩
  have hs : s ∈ Set.Ioo b T := by
    rcases hWhich with rfl | rfl
    · exact hsState
    · exact hsSource
  have hStart : s ∈ Set.Icc s (s + eta) :=
    ⟨le_rfl, le_add_of_nonneg_right hEta.le⟩
  have hLower : h / 2 <
      h3PathActualLowRadialDissipation244 ((J2 : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) :=
    (hFloor s hStart).1
  have hKinetic := h3Path_actualLowRadialDissipation_le_kineticAnchor244
    hH3 hClass b hb ((J2 : ℝ) + 1) (by positivity) s hs
  have hLowCeiling := h3Critical_scalar_lowRadialKineticCeiling_le_eighthPower
    ((J2 : ℝ) + 1) (velocityH3Energy0At u b)
    (h3PathActualLowRadialDissipation244 ((J2 : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s))
    (by
      have hJ : (0 : ℝ) ≤ (J2 : ℝ) := Nat.cast_nonneg _
      linarith only [hJ])
    (velocityH3Energy0At_nonneg u b) hKinetic
  exact ⟨J2, hLower.trans_le hLowCeiling⟩


/-- The same prescribed-gauge cofinal witnesses now carry a CONSTRUCTIVE
secondary late spike when the kinetic-only payment is insufficient. The
second capturing cutoff must pay the original physical kinetic eighth-power
budget. No claim of disjointness between late windows is made. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_lateConstructiveSqrtTailGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (H : ℕ → ℝ) (hH : ∀ n : ℕ, 1 ≤ H n) :
    ∃ (U : H3PhysicalRealFinVectorL2Hilbert)
      (tau : ℕ → ℝ) (N : ℕ → ℕ) (K C delta : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => tau (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (fun n : ℕ => (H n) ^ 8) tau N K C delta (v k)) ∧
      (∀ j : ℕ,
        (∑ k ∈ Finset.range j,
          delta (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ s in a..T, velocityH3DissipationAt u s) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        let t := tau (v k)
        let m := (t + T) / 2
        let Q := (N (v k) : ℝ) + 2
        let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
        let C0 := 3 + h3AuditInitialLerayEnergyCoefficient
        let E0 := 1 + 6 * velocityH3Energy0At u b
        let P := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
        let V := (H (v k)) ^ 4
        let B := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
        V < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          V < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        V < 56 * Q ^ 4 * (‖F‖ * C0 * ((T - m) * E0)) ∨
        (∃ (r : ℝ) (J : ℕ) (sSource sState : ℝ),
          r ∈ Set.Ioo m T ∧ 0 < P ∧
          sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
          sState ∈ Set.Icc r (r + (T - r) / 2) ∧
          ((T - r) * (V / (2 * P)) ≤ 4 * B ∨
          (V / (2 * P)) ^ 2 ≤ 4 * B ∨
          ((V / (2 * P)) ^ 2 ≤
            96 * (E0 + 3 * velocityH3DissipationAt u sState) *
              (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
              (((J : ℝ) + 2) ^ 5) * B ∧
            (∀ h : ℝ, 0 < h →
              96 * C0 * (((J : ℝ) + 2) ^ 5) * (E0 + 3 * h) ^ 2 * B <
                (V / (2 * P)) ^ 2 →
              ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h) ∧
            (4 * (96 * C0 * (((J : ℝ) + 2) ^ 5)) * B * E0 ^ 2 <
                (V / (2 * P)) ^ 2 →
              ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource
                ((V / (2 * P)) /
                  (12 * Real.sqrt ((96 * C0 * (((J : ℝ) + 2) ^ 5)) * B))) ∧
              (∃ J2 : ℕ,
                ((V / (2 * P)) /
                    (12 * Real.sqrt ((96 * C0 * (((J : ℝ) + 2) ^ 5)) * B))) / 2 <
                  4 * velocityH3Energy0At u b * (((J2 : ℝ) + 1) ^ 8))))))) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_lateSecondaryPDEClock244
      hH3 hClass b hb hNoTrace hDInt H hH
  have hAfter : ∀ᶠ k : ℕ in atTop, b < tau (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  refine ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, ?_, hViscousTail⟩
  filter_upwards [hOld, hAfter] with k hkOld hkAfter
  dsimp only at hkOld ⊢
  let t : ℝ := tau (v k)
  let m : ℝ := (t + T) / 2
  let Q : ℝ := (N (v k) : ℝ) + 2
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let P : ℝ := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
  let V : ℝ := (H (v k)) ^ 4
  let B : ℝ := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
  rcases hkOld with hCarrier | hSource | hClock |
      ⟨r, J, sSource, sState, hr, hP, hsSource, hsState, hGate⟩
  · exact Or.inl hCarrier
  · exact Or.inr (Or.inl hSource)
  · exact Or.inr (Or.inr (Or.inl hClock))
  · right; right; right
    rcases hGate with hTime | hTail | ⟨hRate, hAll⟩
    · exact ⟨r, J, sSource, sState, hr, hP, hsSource, hsState,
        Or.inl hTime⟩
    · exact ⟨r, J, sSource, sState, hr, hP, hsSource, hsState,
        Or.inr (Or.inl hTail)⟩
    · refine ⟨r, J, sSource, sState, hr, hP, hsSource, hsState,
        Or.inr (Or.inr ⟨hRate, hAll, ?_⟩)⟩
      let A : ℝ := V / (2 * P)
      let S : ℝ := (((J : ℝ) + 2) ^ 5)
      let R : ℝ := 96 * C0 * S
      have hA : 0 < A := by
        dsimp only [A, V]
        have hHpos : 0 < H (v k) :=
          lt_of_lt_of_le zero_lt_one (hH (v k))
        positivity
      have hC0 : 0 < C0 := by
        dsimp only [C0]
        have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
        linarith only [hCoeff]
      have hS : 0 < S := by
        dsimp only [S]
        positivity
      have hR : 0 < R := by
        dsimp only [R]
        positivity
      have hE0 : 0 ≤ E0 := by
        dsimp only [E0]
        have hE := velocityH3Energy0At_nonneg u b
        linarith only [hE]
      have hmT : m < T := lt_trans hr.1 hr.2
      have hB0 : 0 ≤ B := by
        dsimp only [B]
        exact intervalIntegral.integral_nonneg hmT.le
          (fun s _ => velocityH3DissipationAt_nonneg u s)
      have hB : 0 < B := by
        by_contra hNot
        have hBzero : B = 0 :=
          le_antisymm (le_of_not_gt hNot) hB0
        have hRateZero : A ^ 2 ≤ 0 := by
          have hRateB : A ^ 2 ≤
              96 * (E0 + 3 * velocityH3DissipationAt u sState) *
                (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
                S * B := by
            exact hRate
          simpa only [hBzero, mul_zero] using hRateB
        have hAPosSq : 0 < A ^ 2 := by positivity
        exact (not_le_of_gt hAPosSq) hRateZero
      have htT : t < T := by
        dsimp only [m] at hmT
        linarith only [hmT]
      have hbm : b < m := by
        dsimp only [m]
        linarith only [hkAfter, htT]
      have hHalfEnd : r + (T - r) / 2 < T := by
        linarith only [hr.2]
      have hsStateB : sState ∈ Set.Ioo b T :=
        ⟨lt_trans hbm (lt_of_lt_of_le hr.1 hsState.1),
          lt_of_le_of_lt hsState.2 hHalfEnd⟩
      have hsSourceB : sSource ∈ Set.Ioo b T :=
        ⟨lt_trans hbm (lt_of_lt_of_le hr.1 hsSource.1),
          lt_of_le_of_lt hsSource.2 hHalfEnd⟩
      intro hGap
      have hGap' : 4 * R * B * E0 ^ 2 < A ^ 2 := by
        simpa only [R, S, A] using hGap
      obtain ⟨hh, hBeyond⟩ :=
        thirdFull_scalar_twoSlice_constructiveSqrtTailThreshold244
          A B R E0 hA hB hR hE0 hGap'
      let h : ℝ := A / (12 * Real.sqrt (R * B))
      have hCanonicalClock :
          ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h := by
        apply hAll h
        · simpa only [h] using hh
        · simpa only [h, R, S, A] using hBeyond
      have hCut :=
        thirdFullPhysical_secondaryClock_forces_eighthCutoffPayment244
          hH3 hClass b hb m sState sSource h
          hsStateB hsSourceB hCanonicalClock
      constructor
      · simpa only [h, A, R, S] using hCanonicalClock
      · simpa only [h, A, R, S] using hCut

end
end PrimeTensor.FirstMonomialTriad
