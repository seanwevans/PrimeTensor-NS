import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierViscousSpike
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungWidthTemporalContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeDelayedViscousTail
import Mathlib.Tactic

/-!
# Selected outer carrier: automatic viscous windows and sixth-power compression

The genuine outer-carrier Fourier proof gives the instantaneous physical PDE
bound 119 * margin * sigma^6 <= 80 * D_H3(t). We do NOT infer a time
integral from a single instant. Here the already-verified exact Young-width
continuity and physical L2 highpass continuity preserve HALF the strict
kinetic excess margin and a positive annular deficit on a small right
interval. We then integrate the SAME actual physical viscous spike.

For cofinal selected strict snapshots, the intervals can be made disjoint.
Finite H3 dissipation implies the *terminal-tail* estimate

    delta_k * (119 * margin_k * sigma_k^6 / 160)
       <= integral_(x_k)^T D_H3(t) dt -> 0.

Thus the selected width is forced to compress as the outer sixth-power
radius cost grows. There is NO automatic lower bound on delta_k, and no
claim of a contradiction with finite dissipation or a Navier--Stokes solution.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The positive selected kinetic margin, rather than merely its sign,
remains at least half its snapshot value. The actual Young deficit also
remains positive on the SAME right physical-time interval. -/
theorem thirdFullPhysical_selectedOuterMargin_rightWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      ∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + margin / 2 ≤
          ((rho ^ 2 + sigma ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
        epsilon ≤ thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b s rho sigma := by
  let M : ℝ → ℝ := fun s =>
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let R : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let F : ℝ → ℝ := fun s => R * M s - B
  let G : ℝ → ℝ := fun s =>
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma
  have hxAbs : x ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hx.1), hx.2⟩
  have hOrder : rho ≤ sigma := by linarith only [hRho, hAspect]
  have hM : ContinuousAt M x :=
    thirdFullPhysical_actualSharpHighMass_continuousAt244 hH3 rho x hxAbs
  have hF : ContinuousAt F x :=
    (continuousAt_const.mul hM).sub continuousAt_const
  have hG : ContinuousAt G x :=
    thirdFullPhysical_actualAnnularKineticDeficit_continuousAt244
      hH3 b rho sigma x hRho.le hOrder hxAbs
  have hFx : margin ≤ F x := by
    dsimp only [F, M, R, B]
    linarith only [hExcess]
  obtain ⟨rF, hrF, hNearF⟩ :=
    (Metric.continuousAt_iff.mp hF) (margin / 2) (by positivity)
  obtain ⟨rG, hrG, hNearG⟩ :=
    (Metric.continuousAt_iff.mp hG) epsilon hEps
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
    exact (min_le_right (rF / 2) (min (rG / 2) ((T - x) / 2))).trans
      (min_le_right (rG / 2) ((T - x) / 2))
  have hdEnd : x + delta < T := by
    linarith only [hdT, hx.2]
  refine ⟨delta, hd, hdEnd, ?_⟩
  intro s hs
  have hDist : dist s x ≤ delta := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    linarith only [hs.2]
  have hFs := hNearF (lt_of_le_of_lt hDist hdF)
  have hGs := hNearG (lt_of_le_of_lt hDist hdG)
  rw [Real.dist_eq] at hFs hGs
  have hFineq := (abs_lt.mp hFs).1
  have hGineq := (abs_lt.mp hGs).1
  constructor
  · dsimp only [F, M, R, B] at hFineq hFx
    linarith only [hFineq, hFx]
  · have hGx : 2 * epsilon ≤ G x := hPeak
    dsimp only [G] at hGineq hGx ⊢
    linarith only [hGineq, hGx]

/-- A genuinely positive excess margin on an entire physical time window
charges that interval by sigma^6 times its width. No temporal width lower
bound is inserted into the statement. -/
theorem thirdFullPhysical_selectedOuterMargin_integratedWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin delta : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hd : 0 < delta) (hdEnd : x + delta < T)
    (hWindow : ∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
      0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b s rho sigma) :
    delta * (119 * margin * sigma ^ 6 / 80) ≤
      ∫ r in x..T, velocityH3DissipationAt u r := by
  let D : ℝ → ℝ := velocityH3DissipationAt u
  let A : ℝ := 119 * margin * sigma ^ 6 / 80
  have hDtail : IntervalIntegrable D volume x T := by
    apply hDInt.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc x T := by
      simpa only [Set.uIcc_of_le hx.2.le] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨(le_of_lt (lt_trans hb.1 hx.1)).trans hr'.1, hr'.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hDwin : IntervalIntegrable D volume x (x + delta) := by
    apply hDtail.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc x (x + delta) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hd.le)] using hr
    have hrAll : r ∈ Set.Icc x T := ⟨hr'.1, hr'.2.trans hdEnd.le⟩
    simpa only [Set.uIcc_of_le hx.2.le] using hrAll
  have hPoint (s : ℝ) (hs : s ∈ Set.Icc x (x + delta)) : A ≤ D s := by
    have hsTail : s ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hdEnd⟩
    obtain ⟨hEx, hDef⟩ := hWindow s hs
    have hCharge := thirdFullPhysical_selectedWideOuterMargin_forces_viscousSpike244
      hH3 hClass b hb s hsTail rho sigma margin hRho hAspect
      hMargin hEx hDef
    dsimp only [A]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 80)).2
    calc
      119 * margin * sigma ^ 6 ≤ 80 * D s := hCharge
      _ = D s * 80 := by ring
  have hLocal : delta * A ≤ ∫ r in x..(x + delta), D r := by
    have hCost := h3Path_localPositiveHeight_forces_integratedCost244
      D x (x + delta) A (by linarith only [hd]) hDwin hPoint
    calc
      delta * A = ((x + delta) - x) * A := by ring
      _ ≤ ∫ r in x..(x + delta), D r := hCost
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc x T)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  have hTail : (∫ r in x..(x + delta), D r) ≤
      ∫ r in x..T, D r :=
    intervalIntegral.integral_mono_interval
      (le_refl x) (le_add_of_nonneg_right hd.le) hdEnd.le
      hNonneg hDtail
  exact hLocal.trans hTail

/-- The positive-margin physical snapshot AUTOMATICALLY produces a
right viscous window with a quantitative terminal-tail integral charge.
The cost is half the original margin because the snapshot margin is
preserved by continuity. -/
theorem thirdFullPhysical_selectedOuterMargin_snapshotIntegratedSpike244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) + margin ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : 2 * epsilon ≤
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      delta * (119 * margin * sigma ^ 6 / 160) ≤
        ∫ r in x..T, velocityH3DissipationAt u r := by
  obtain ⟨delta, hd, hdEnd, hWindow⟩ :=
    thirdFullPhysical_selectedOuterMargin_rightWindow244
      hH3 hClass b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak
  have hCharge := thirdFullPhysical_selectedOuterMargin_integratedWindow244
    hH3 hClass hDInt b hb x hx rho sigma (margin / 2) delta
    hRho hAspect (by positivity) hd hdEnd (by
      intro s hs
      obtain ⟨hEx, hFloor⟩ := hWindow s hs
      exact ⟨hEx, (hEps.le.trans hFloor)⟩)
  refine ⟨delta, hd, hdEnd, ?_⟩
  convert hCharge using 1 <;> ring

/-- At one cofinal strict snapshot per index, keep half the true kinetic
margin and a positive deficit on disjoint right windows. Their original
sigma^6 viscous prices must collapse along the terminal tails; no uniform
lower bound on their widths is assumed or obtained. -/
theorem thirdFullPhysical_cofinalSelectedOuterMargins_integratedCompression244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hStep : ∀ k : ℕ, x k < x (k + 1))
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hRho : ∀ k : ℕ, 0 < rho k)
    (hAspect : ∀ k : ℕ, 2 * rho k ≤ sigma k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hEps : ∀ k : ℕ, 0 < epsilon k)
    (hExcess : ∀ k : ℕ,
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k ≤
      ((rho k ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k))
    (hPeak : ∀ k : ℕ, 2 * epsilon k ≤
      thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b (x k) (rho k) (sigma k)) :
    ∃ delta : ℕ → ℝ,
      (∀ k : ℕ, 0 < delta k ∧ x k + delta k < x (k + 1) ∧
          x k + delta k < T) ∧
      (∀ k : ℕ, delta k * (119 * margin k * sigma k ^ 6 / 160) ≤
        ∫ r in x k..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        delta k * (119 * margin k * sigma k ^ 6 / 160))
        atTop (𝓝 (0 : ℝ)) := by
  classical
  have hWin (k : ℕ) :
      ∃ d : ℝ, 0 < d ∧ x k + d < T ∧
        ∀ s : ℝ, s ∈ Set.Icc (x k) (x k + d) →
          Real.sqrt (velocityH3Energy0At u b) *
            (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
              (rho k) (velocityH3Energy0At u b)) + margin k / 2 ≤
          ((rho k ^ 2 + sigma k ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) ∧
          epsilon k ≤ thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b s (rho k) (sigma k) := by
    exact thirdFullPhysical_selectedOuterMargin_rightWindow244
      hH3 hClass b hb (x k) (hx k)
      (rho k) (sigma k) (margin k) (epsilon k)
      (hRho k) (hAspect k) (hMargin k) (hEps k)
      (hExcess k) (hPeak k)
  choose d₀ hd₀ hEnd₀ hWindow₀ using hWin
  let delta : ℕ → ℝ := fun k =>
    min (d₀ k) ((x (k + 1) - x k) / 2)
  have hd (k : ℕ) : 0 < delta k := by
    dsimp only [delta]
    exact lt_min (hd₀ k) (by linarith only [hStep k])
  have hSmall (k : ℕ) : delta k ≤ d₀ k := by
    dsimp only [delta]
    exact min_le_left _ _
  have hNext (k : ℕ) : x k + delta k < x (k + 1) := by
    have hs : delta k ≤ (x (k + 1) - x k) / 2 := by
      dsimp only [delta]
      exact min_le_right _ _
    linarith only [hs, hStep k]
  have hEnd (k : ℕ) : x k + delta k < T :=
    lt_of_le_of_lt (add_le_add_right (hSmall k) (x k)) (hEnd₀ k)
  have hWindow (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (x k) (x k + delta k)) :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          (rho k) (velocityH3Energy0At u b)) + margin k / 2 ≤
      ((rho k ^ 2 + sigma k ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) ∧
      epsilon k ≤ thirdFullPhysicalActualAnnularKineticDeficit244
        hH3 b s (rho k) (sigma k) :=
    hWindow₀ k s ⟨hs.1, hs.2.trans (add_le_add_right (hSmall k) (x k))⟩
  have hIntegrated (k : ℕ) :
      delta k * (119 * margin k * sigma k ^ 6 / 160) ≤
        ∫ r in x k..T, velocityH3DissipationAt u r := by
    have hCharge := thirdFullPhysical_selectedOuterMargin_integratedWindow244
      hH3 hClass hDInt b hb (x k) (hx k)
      (rho k) (sigma k) (margin k / 2) (delta k)
      (hRho k) (hAspect k)
      (div_pos (hMargin k) (by norm_num : (0 : ℝ) < 2))
      (hd k) (hEnd k)
      (by
        intro s hs
        obtain ⟨hEx, hFloor⟩ := hWindow k s hs
        exact ⟨hEx, (hEps k).le.trans hFloor⟩)
    convert hCharge using 1 <;> ring
  have hTail : Tendsto (fun k : ℕ =>
      ∫ r in x k..T, velocityH3DissipationAt u r)
      atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt x hCofinal
      (Filter.Eventually.of_forall (fun k =>
        ⟨le_of_lt (lt_trans hb.1 (hx k).1), (hx k).2.le⟩))
  have hLimit : Tendsto (fun k : ℕ =>
      delta k * (119 * margin k * sigma k ^ 6 / 160))
      atTop (𝓝 (0 : ℝ)) := by
    have hNonneg (k : ℕ) :
        0 ≤ delta k * (119 * margin k * sigma k ^ 6 / 160) := by
      have hDeltaNonneg : 0 ≤ delta k := (hd k).le
      have hMarginNonneg : 0 ≤ margin k := (hMargin k).le
      have hSigma : 0 ≤ sigma k := by linarith only [hRho k, hAspect k]
      positivity
    exact squeeze_zero'
      (Filter.Eventually.of_forall hNonneg)
      (Filter.Eventually.of_forall hIntegrated) hTail
  exact ⟨delta, (fun k => ⟨hd k, hNext k, hEnd k⟩), hIntegrated, hLimit⟩

end
end PrimeTensor.FirstMonomialTriad
