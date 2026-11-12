import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularTruncatedClockCharge
import Mathlib.Tactic

/-!
# Actual annular kinetic mass continuity and one-snapshot viscous clocks

The genuine physical sharp highpass is 1-Lipschitz on the physical
three-component real L2 Hilbert space. Since the actual physical velocity
is continuous at all strict times, its highpass kinetic square mass is
continuous, with no moving-frequency or endpoint compactness premise.

For fixed annular radii, the exact nonlinear Young-gap/width cost is the
remaining temporal-continuity input. The deficit is a polynomial of this
cost and the highpass mass; its continuity follows algebraically. A single
strict kinetic-excess observation with a doubled positive deficit floor
therefore produces a positive right physical window paying the canonical
cap-free viscous height against the actual finite H3 dissipation integral.

This does NOT prove continuity of the nonlinear Young-gap/width integral,
or a uniform lower bound for the lengths of cofinal windows. Both remain
explicit analytic obligations. The proof does not introduce any new axiom.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularPersistence244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularPersistence244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The genuine three-coordinate sharp real physical Fourier lowpass
respects subtraction, by the already proved scalar physical identity. -/
theorem thirdFullPhysical_sharpVectorLowCutoff_sub244
    (rho : ℝ) (V W : H3PhysicalRealFinVectorL2Hilbert) :
    thirdFullPhysicalSharpLowCutoffHilbert244 rho (V - W) =
      thirdFullPhysicalSharpLowCutoffHilbert244 rho V -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho W := by
  apply PiLp.ext
  intro j
  change h3CriticalPhysicalSharpLowCutoffApply rho ((V - W).ofLp j) =
    h3CriticalPhysicalSharpLowCutoffApply rho (V.ofLp j) -
      h3CriticalPhysicalSharpLowCutoffApply rho (W.ofLp j)
  simpa only [PiLp.sub_apply] using
    (h3Critical_physicalSharpLowCutoff_sub rho (V.ofLp j) (W.ofLp j))

/-- The physical three-coordinate HIGHpass, not just the lowpass, is a
nonexpansive operator. -/
theorem thirdFullPhysical_sharpVectorHighpass_norm_sub_le244
    (rho : ℝ) (V W : H3PhysicalRealFinVectorL2Hilbert) :
    ‖(V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V) -
      (W - thirdFullPhysicalSharpLowCutoffHilbert244 rho W)‖ ≤
      ‖V - W‖ := by
  have hSub := thirdFullPhysical_sharpVectorLowCutoff_sub244 rho V W
  have hEq :
      (V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V) -
        (W - thirdFullPhysicalSharpLowCutoffHilbert244 rho W) =
      (V - W) - thirdFullPhysicalSharpLowCutoffHilbert244 rho (V - W) := by
    rw [hSub]
    abel
  rw [hEq]
  exact thirdFullPhysical_sharpVectorHighpass_norm_le244 rho (V - W)

/-- The true sharp physical highpass depends continuously on its physical
L2 input, with operator Lipschitz constant one. -/
theorem thirdFullPhysical_sharpVectorHighpass_continuous244 (rho : ℝ) :
    Continuous (fun V : H3PhysicalRealFinVectorL2Hilbert =>
      V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V) := by
  have hLip : LipschitzWith 1
      (fun V : H3PhysicalRealFinVectorL2Hilbert =>
        V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V) :=
    LipschitzWith.of_dist_le_mul (fun V W => by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
        thirdFullPhysical_sharpVectorHighpass_norm_sub_le244 rho V W)
  exact hLip.continuous

/-- The ACTUAL highpass kinetic mass is continuous at every strict
positive physical time for each fixed real radius, without a kinetic cap. -/
theorem thirdFullPhysical_actualSharpHighMass_continuousAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (rho t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousAt
      (fun s : ℝ => thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)
      t := by
  have hOld := h3Audit_initialOldPhysicalHilbert_continuousAt hH3 ht
  have hHigh : ContinuousAt (fun s : ℝ =>
      h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        thirdFullPhysicalSharpLowCutoffHilbert244 rho
          (h3AuditInitialOldPhysicalHilbertTotal hH3 s)) t :=
    (thirdFullPhysical_sharpVectorHighpass_continuous244 rho).continuousAt.comp hOld
  change ContinuousAt (fun s : ℝ =>
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
      thirdFullPhysicalSharpLowCutoffHilbert244 rho
        (h3AuditInitialOldPhysicalHilbertTotal hH3 s)‖ ^ 2) t
  exact hHigh.norm.pow 2

/-- Continuity of the EXACT physical annular kinetic deficit follows from
actual highpass kinetic continuity and continuity of the remaining
nonlinear Young-gap/width cost. No continuity of viscosity is used. -/
theorem thirdFullPhysical_actualAnnularKineticDeficit_continuousAt_of_young244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b rho sigma t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hYoung : ContinuousAt
      (fun s : ℝ => thirdFullPhysicalActualAnnularYoungWidthCost244
        hH3 s rho sigma) t) :
    ContinuousAt
      (fun s : ℝ => thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b s rho sigma) t := by
  let M : ℝ → ℝ := fun s =>
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Y : ℝ → ℝ := fun s =>
    thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  let R : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let W : ℝ := (rho ^ 2) ^ 3
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b R
  have hM : ContinuousAt M t :=
    thirdFullPhysical_actualSharpHighMass_continuousAt244 hH3 rho t ht
  have hY : ContinuousAt Y t := hYoung
  have hF : ContinuousAt (fun s => R * M s - B) t :=
    (continuousAt_const.mul hM).sub continuousAt_const
  have hX : ContinuousAt (fun s => W * (R * M s - B) ^ 2) t :=
    continuousAt_const.mul (hF.pow 2)
  have hC : ContinuousAt (fun s => Y s + W * P) t :=
    hY.add continuousAt_const
  have hProd : ContinuousAt (fun s => M s * (Y s + W * P)) t :=
    hM.mul hC
  change ContinuousAt
    (fun s => W * (R * M s - B) ^ 2 -
      M s * (Y s + W * P)) t
  exact hX.sub hProd

/-- The same-time annular deficit has an explicit cap-free viscous floor:
choose the cap H=epsilon in the accepted truncated-clock theorem, so the
spike and cap-bounded branches both pay epsilon/C(b,rho,epsilon). -/
theorem thirdFullPhysical_annularDeficit_forces_selfCalibratedClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (epsilon : ℝ) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hFloor : epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma) :
    epsilon / thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon ≤
      velocityH3DissipationAt u t := by
  let C := thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon
  have hCpos : 0 < C :=
    thirdFullPhysical_annularCapClockFactor_pos244 u b rho epsilon
  have hCge : 1 ≤ C := by
    dsimp only [C, thirdFullPhysicalAnnularCapClockFactor244]
    exact le_max_left _ _
  have hDiv : epsilon / C ≤ epsilon := by
    apply (div_le_iff₀ hCpos).2
    have hMul := mul_le_mul_of_nonneg_left hCge hEps.le
    simpa only [mul_one] using hMul
  have hTrunc :=
    thirdFullPhysical_annularDeficit_forces_truncatedClockHeight244
      hH3 hClass b hb rho sigma hRho hOrder t ht
      epsilon epsilon hEps.le hExcess hFloor
  change min epsilon (epsilon / C) ≤ velocityH3DissipationAt u t at hTrunc
  rw [min_eq_right hDiv] at hTrunc
  exact hTrunc

/-- A single actual physical observation with strict kinetic excess and a
DOUBLED annular deficit floor selects a nonzero right time window. The
highpass part is continuous unconditionally; the only temporal hypothesis
is continuity at the observation time of the exact nonlinear Young/width
functional. The resulting interval pays actual physical H3 dissipation. -/
theorem thirdFullPhysical_annularDeficit_snapshotRightWindowCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (epsilon : ℝ) (hEps : 0 < epsilon)
    (hYoung : ContinuousAt
      (fun s : ℝ => thirdFullPhysicalActualAnnularYoungWidthCost244
        hH3 s rho sigma) x)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) <
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      (∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
        epsilon ≤
          thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b s rho sigma) ∧
      delta * (epsilon /
        thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon) ≤
        ∫ r in a..T, velocityH3DissipationAt u r := by
  let M : ℝ → ℝ := fun s =>
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let R : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let F : ℝ → ℝ := fun s => R * M s - B
  let G : ℝ → ℝ := fun s =>
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma
  let D : ℝ → ℝ := velocityH3DissipationAt u
  let A : ℝ := epsilon /
    thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon
  have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hx.1), hx.2⟩
  have hM : ContinuousAt M x :=
    thirdFullPhysical_actualSharpHighMass_continuousAt244 hH3 rho x hxAbs
  have hF : ContinuousAt F x :=
    (continuousAt_const.mul hM).sub continuousAt_const
  have hG : ContinuousAt G x :=
    thirdFullPhysical_actualAnnularKineticDeficit_continuousAt_of_young244
      hH3 b rho sigma x hxAbs hYoung
  have hFx : 0 < F x := by
    dsimp only [F, M, R, B]
    exact sub_pos.mpr hExcess
  have hGx : 0 < G x - epsilon := by
    dsimp only [G]
    linarith only [hPeak, hEps]
  obtain ⟨rF, hrF, hNearF⟩ :=
    (Metric.continuousAt_iff.mp hF) (F x) hFx
  obtain ⟨rG, hrG, hNearG⟩ :=
    (Metric.continuousAt_iff.mp hG) (G x - epsilon) hGx
  let delta : ℝ := min (rF / 2) (min (rG / 2) ((T - x) / 2))
  have hd : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by linarith only [hrF])
      (lt_min (by linarith only [hrG]) (by linarith only [hx.2]))
  have hdF : delta < rF := by
    have h := min_le_left (rF / 2) (min (rG / 2) ((T - x) / 2))
    dsimp only [delta]
    linarith only [h, hrF]
  have hdG : delta < rG := by
    have h := (min_le_right (rF / 2) (min (rG / 2) ((T - x) / 2))).trans
      (min_le_left (rG / 2) ((T - x) / 2))
    dsimp only [delta]
    linarith only [h, hrG]
  have hdT : delta ≤ (T - x) / 2 := by
    have h := (min_le_right (rF / 2) (min (rG / 2) ((T - x) / 2))).trans
      (min_le_right (rG / 2) ((T - x) / 2))
    exact h
  have hdEnd : x + delta < T := by
    linarith only [hdT, hx.2]
  have hWindow (s : ℝ) (hs : s ∈ Set.Icc x (x + delta)) :
      B ≤ R * M s ∧ epsilon ≤ G s := by
    have hDist : dist s x ≤ delta := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith only [hs.2]
    have hFs := hNearF (lt_of_le_of_lt hDist hdF)
    have hGs := hNearG (lt_of_le_of_lt hDist hdG)
    rw [Real.dist_eq] at hFs hGs
    have hFineq := (abs_lt.mp hFs).1
    have hGineq := (abs_lt.mp hGs).1
    constructor
    · dsimp only [F] at hFineq
      linarith only [hFineq]
    · linarith only [hGineq]
  have hPoint (s : ℝ) (hs : s ∈ Set.Icc x (x + delta)) :
      A ≤ D s := by
    have hsTail : s ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hdEnd⟩
    obtain ⟨hEx, hFloor⟩ := hWindow s hs
    exact thirdFullPhysical_annularDeficit_forces_selfCalibratedClock244
      hH3 hClass b hb rho sigma hRho hOrder s hsTail
      epsilon hEps hEx hFloor
  have hxClass : a < x := lt_trans hb.1 hx.1
  have hDwin : IntervalIntegrable D volume x (x + delta) := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc x (x + delta) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hd.le)] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hxClass.le.trans hrIcc.1, hrIcc.2.trans hdEnd.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hLocal : delta * A ≤ ∫ r in x..(x + delta), D r := by
    have hCost := h3Path_localPositiveHeight_forces_integratedCost244
      D x (x + delta) A (by linarith only [hd]) hDwin hPoint
    calc
      delta * A = ((x + delta) - x) * A := by ring
      _ ≤ ∫ r in x..(x + delta), D r := hCost
  have hDnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a T)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  have hFull : (∫ r in x..(x + delta), D r) ≤
      ∫ r in a..T, D r :=
    intervalIntegral.integral_mono_interval
      hxClass.le (le_add_of_nonneg_right hd.le) hdEnd.le hDnonneg hDInt
  refine ⟨delta, hd, hdEnd, ?_, ?_⟩
  · intro s hs
    exact hWindow s hs
  · exact hLocal.trans hFull


/-- A cap-free disjoint-clock statement, with canonical cap H_k=epsilon_k.
Once exact annular deficit and excess persist on selected disjoint physical
windows, the actual finite H3 dissipation pays the entire self-calibrated
series. Unlike the preceding result, H is no longer an independent input. -/
theorem thirdFullPhysical_disjointAnnularDeficit_selfCalibratedSummable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (p delta rho sigma epsilon : ℕ → ℝ)
    (hRho : ∀ k, 0 ≤ rho k)
    (hOrder : ∀ k, rho k ≤ sigma k)
    (hEps : ∀ k, 0 < epsilon k)
    (hStart : ∀ k, a ≤ p k)
    (hWidth : ∀ k, 0 ≤ delta k)
    (hEnd : ∀ k, p k + delta k ≤ T)
    (hSeparate : ∀ k, p k + delta k ≤ p (k + 1))
    (hTimes : ∀ k s, s ∈ Set.Icc (p k) (p k + delta k) →
      s ∈ Set.Ioo b T)
    (hExcess : ∀ k s, s ∈ Set.Icc (p k) (p k + delta k) →
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) ≤
      ((rho k ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k))
    (hFloor : ∀ k s, s ∈ Set.Icc (p k) (p k + delta k) →
      epsilon k ≤
        thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b s (rho k) (sigma k)) :
    (Summable (fun k : ℕ =>
      delta k * (epsilon k /
        thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (epsilon k))) ∧
     Tendsto (fun k : ℕ =>
      delta k * (epsilon k /
        thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (epsilon k)))
       atTop (𝓝 (0 : ℝ)) ∧
     ∀ m : ℕ,
       (∑ k ∈ Finset.range m,
         delta k * (epsilon k /
           thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (epsilon k))) ≤
         ∫ r in a..T, velocityH3DissipationAt u r) := by
  have hTrunc := thirdFullPhysical_disjointAnnularDeficit_truncatedClockSummable244
    hH3 hClass b hb hDInt p delta rho sigma epsilon epsilon
    hRho hOrder hEps hEps hStart hWidth hEnd hSeparate
    hTimes hExcess hFloor
  have hEq (k : ℕ) :
      thirdFullPhysicalAnnularTruncatedClockHeight244
          u b (rho k) (epsilon k) (epsilon k) =
        epsilon k /
          thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (epsilon k) := by
    let C := thirdFullPhysicalAnnularCapClockFactor244 u b (rho k) (epsilon k)
    have hPos : 0 < C :=
      thirdFullPhysical_annularCapClockFactor_pos244 u b (rho k) (epsilon k)
    have hOne : 1 ≤ C := by
      dsimp only [C, thirdFullPhysicalAnnularCapClockFactor244]
      exact le_max_left _ _
    have hDiv : epsilon k / C ≤ epsilon k := by
      apply (div_le_iff₀ hPos).2
      have hMul := mul_le_mul_of_nonneg_left hOne (hEps k).le
      simpa only [mul_one] using hMul
    change min (epsilon k) (epsilon k / C) = epsilon k / C
    exact min_eq_right hDiv
  simpa only [hEq] using hTrunc

end
end PrimeTensor.FirstMonomialTriad
