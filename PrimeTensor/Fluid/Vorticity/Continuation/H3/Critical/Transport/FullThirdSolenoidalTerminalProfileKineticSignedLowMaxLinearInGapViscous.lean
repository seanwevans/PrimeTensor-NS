import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxGammaFreeViscousEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxBackwardGapCharge
import Mathlib.Tactic

/-!
# Native signed LowMax sixth-flux: linear-margin viscous persistence on original gaps

The previous gamma-free theorem yields a strict-time high-radial carrier,
but records only full H3 dissipation at that instant. Here the ORIGINAL
high-radial spectral inequality, prior to the last coercivity step, gives an
explicit strictly positive high-radial viscous height. Its margin dependence
is linear (eta rather than eta squared); its denominator uses the true
physical one-snapshot energy factor, not the Schwartz sixth-flux Lipschitz
amplitude.

The established anchored finite-annulus PDE clock then constructs a genuine
positive-width time interval. It is truncated forward inside [x,y] when t<y
and transported backward from y when t=y, so both endpoints of the original
closed kinetic gap are handled. On cofinal gaps, both this new linear-height
charge and the old quadratic-height annular alternative are genuine
integrated costs, and hence become epsilon-compressed. They are unified with
the minimum of the two explicit, strictly positive physical heights.

NO lower bound uniform across moving cutoff, energy or gap is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Genuine Fourier normalization of the adverse one-time sixth flux. -/
noncomputable def thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
    (E : ℝ) : ℝ :=
  ((2 * Real.pi) ^ 7 / 3) *
    (1944 * h3SobolevFirstMomentDeweightingConstant * (E + 1))

/-- Positive radial high-tail height, linear in eta and inverse in the
actual physical H3 energy coefficient. The extra one prevents a zero
recovery coefficient from creating a spurious division. -/
noncomputable def thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    (R : ℕ) (eta E : ℝ) : ℝ :=
  (((R : ℝ) + 1) ^ 2 * (eta / 2)) /
    (2 * (thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 E + 1))

/-- The genuine gamma-free high-tail inequality yields a STRICT high-radial
H3 viscous floor at the same physical time, with a LINEAR signed margin.
The Fourier radius and instantaneous physical energy remain explicit. -/
theorem thirdFullPhysical_signedLowMax_gammaFreeTail_linearHighRadialFloor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (eta : ℝ) (hEta : 0 < eta)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) :
    0 < thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
      R eta (velocityH3EnergyAt u t) ∧
    thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
      R eta (velocityH3EnergyAt u t) <
      h3PathActualHighRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let P := thirdFullSpectralVelocityHighRadialApply244 R U
  let A : ℝ := thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
    (velocityH3EnergyAt u t)
  let Q : ℝ := ((R : ℝ) + 1) ^ 2 * (eta / 2)
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  have hFactor : 0 < A := by
    by_contra hn
    have hAle : A ≤ 0 := le_of_not_gt hn
    have hProd : A * ‖P‖ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hAle (sq_nonneg _)
    change eta / 2 ≤ A * ‖P‖ ^ 2 at hTail
    linarith only [hProd, hTail, hEta]
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  have hDen : 0 < 2 * (A + 1) := by linarith only [hFactor]
  have hH : 0 < H := by
    change 0 < Q / (2 * (A + 1))
    exact div_pos hQ hDen
  have hRatio : A / (2 * (A + 1)) < 1 := by
    apply (div_lt_iff₀ hDen).mpr
    linarith only [hFactor]
  have hBudget : A * H < Q := by
    change A * (Q / (2 * (A + 1))) < Q
    calc
      A * (Q / (2 * (A + 1))) =
          (A / (2 * (A + 1))) * Q := by ring
      _ < 1 * Q := mul_lt_mul_of_pos_right hRatio hQ
      _ = Q := one_mul Q
  have hCoercive := thirdFullPhysical_highRadialViscousCoercivity244
    hH3 hClass t ht R
  change ((R : ℝ) + 1) ^ 2 * ‖P‖ ^ 2 ≤
    h3PathActualHighRadialDissipation244 ((R : ℝ) + 1) U at hCoercive
  have hQCharge : Q ≤ A *
      h3PathActualHighRadialDissipation244 ((R : ℝ) + 1) U := by
    calc
      Q = ((R : ℝ) + 1) ^ 2 * (eta / 2) := rfl
      _ ≤ ((R : ℝ) + 1) ^ 2 * (A * ‖P‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hTail (sq_nonneg _)
      _ = A * (((R : ℝ) + 1) ^ 2 * ‖P‖ ^ 2) := by ring
      _ ≤ A * h3PathActualHighRadialDissipation244
          ((R : ℝ) + 1) U :=
        mul_le_mul_of_nonneg_left hCoercive hFactor.le
  have hScaled : A * H < A *
      h3PathActualHighRadialDissipation244 ((R : ℝ) + 1) U :=
    lt_of_lt_of_le hBudget hQCharge
  exact ⟨hH, lt_of_mul_lt_mul_left hScaled hFactor.le⟩

/-- The positive high-radial viscous floor persists in a certified finite
annulus, either FORWARD inside the same original gap or BACKWARD from its
right endpoint. Both cases yield true full-H3 integrated dissipation. -/
theorem thirdFullPhysical_signedLowMax_gammaFreeTail_linearInGapCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (x y t : ℝ)
    (hx : x ∈ Set.Ioo b T) (hy : y ∈ Set.Ioo b T)
    (hxy : x < y) (ht : t ∈ Set.Icc x y)
    (eta : ℝ) (hEta : 0 < eta)
    (hTail : eta / 2 ≤
      thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ ^ 2) :
    ∃ width : ℝ, 0 < width ∧
      ((t + width < y) ∨ (t = y ∧ x < t - width)) ∧
      width * (thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
        R eta (velocityH3EnergyAt u t) / 4) ≤
        ∫ r in x..y, velocityH3DissipationAt u r ∂volume := by
  let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hx.1, hx.2⟩
  have hyClass : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hy.1, hy.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hxClass.1 ht.1, lt_of_le_of_lt ht.2 hyClass.2⟩
  obtain ⟨hH, hHigh⟩ :=
    thirdFullPhysical_signedLowMax_gammaFreeTail_linearHighRadialFloor244
      hH3 hClass R t htClass eta hEta hTail
  have hWindow : ThirdFullKineticSignedLowMaxCertifiedAnnularWindow244
      hH3 R H t :=
    thirdFullPhysical_highRadialHeight_to_signedCertifiedWindow244
      hH3 hClass t htClass R H hH hHigh
  by_cases hRight : t = y
  · subst t
    obtain ⟨N, width, _hRN, _hWidthEq, hWidth, hInside,
      _hFloor, hCharge⟩ :=
      thirdFullPhysical_signedLowMax_rightEndpoint_backwardGapCharge244
        hH3 hClass hDInt b hb R H x y hH hx hy hxy hWindow
    exact ⟨width, hWidth, Or.inr ⟨rfl, hInside⟩, hCharge⟩
  · have hty : t < y := lt_of_le_of_ne ht.2 hRight
    have hInGap : ThirdFullKineticSignedLowMaxInGapAnnularCharge244
        hH3 R H t y :=
      thirdFullPhysical_signedLowMax_certifiedWindow_truncateInGap244
        hH3 hClass R H t y htClass hty hy.2.le hWindow
    obtain ⟨width, hWidth, hInside, hCharge⟩ :=
      thirdFullPhysical_signedLowMax_inGapCharge_le_fullGapDissipation244
        hH3 hClass hDInt R H x t y hxClass hyClass
        hxy.le ht hInGap
    exact ⟨width, hWidth, Or.inl hInside, hCharge⟩

/-- The minimum of the newly constructed LINEAR-margin high-tail height and
the old calibrated quadratic signed-flux height is strictly positive at
every actual adverse physical snapshot. No uniform lower bound is implied. -/
noncomputable def thirdFullKineticSignedLowMaxUnifiedPhysicalViscousHeight244
    (R : ℕ) (eta : ℝ) (X Y : H3SpectralVelocityState) (E : ℝ) : ℝ :=
  min (thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244 R eta E)
    (thirdFullKineticSignedLowMaxPhysicalViscousHeight244 R X Y
      (thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 2))

/-- The unified annular height is genuinely positive at each strict
physical energy, although it need not remain bounded away from zero along
a moving terminal gauge. -/
theorem thirdFullKinetic_signedLowMax_unifiedPhysicalHeight_pos244
    (R : ℕ) (eta E : ℝ) (X Y : H3SpectralVelocityState)
    (hEta : 0 < eta) (hE : 1 ≤ E) :
    0 < thirdFullKineticSignedLowMaxUnifiedPhysicalViscousHeight244
      R eta X Y E := by
  have hFactor : 0 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 E := by
    unfold thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
    have hMoment : 0 ≤ h3SobolevFirstMomentDeweightingConstant :=
      h3SobolevFirstMomentDeweightingConstant_nonneg
    have hEnergy : 0 ≤ E + 1 := by linarith only [hE]
    positivity
  have hLinear : 0 < thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
      R eta E := by
    unfold thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    have hDen : 0 < 2 *
        (thirdFullKineticSignedLowMaxPhysicalHighTailFactor244 E + 1) := by
      linarith only [hFactor]
    exact div_pos (by positivity) hDen
  have hMu : 0 < thirdFullKineticSignedLowMaxPhysicalMargin244 eta :=
    thirdFullKineticSignedLowMaxPhysicalMargin_pos244 eta hEta
  have hQuad : 0 < thirdFullKineticSignedLowMaxPhysicalViscousHeight244
      R X Y (thirdFullKineticSignedLowMaxPhysicalMargin244 eta / 2) := by
    unfold thirdFullKineticSignedLowMaxPhysicalViscousHeight244
    positivity
  unfold thirdFullKineticSignedLowMaxUnifiedPhysicalViscousHeight244
  exact lt_min hLinear hQuad

/-- All late cofinal signed-sixth-flux costs, now WITHOUT an isolated
instantaneous viscous spike: an earlier physical cubic baseline, an actual
radius/energy escape, or a positive-width, full-gap physically charged
annulus with a calibrated positive height. -/
def ThirdFullKineticSignedLowMaxIntegratedGapEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R J : ℕ) (E eta epsilon x y t : ℝ) : Prop :=
  (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
   let X := h3AuditActualSpectralVelocityTotal hH3 t
   let Y := h3AuditActualSpectralVelocityTotal hH3 x
   (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
   (J < R ∨ E < velocityH3EnergyAt u t ∨ E < velocityH3EnergyAt u x) ∨
   (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
      ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
      width * (thirdFullKineticSignedLowMaxUnifiedPhysicalViscousHeight244
        R eta X Y (velocityH3EnergyAt u t) / 4) < epsilon))

/-- Every sufficiently late original kinetic gap has a THREE-way necessary
physical cost for each genuine adverse third-order observation, uniformly
in the selected natural radius. No pointwise-only dissipation arm remains.
The positive persistence width is allowed to shrink with the gap. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_integratedViscousEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => tau (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ R : ℕ, ∀ t : ℝ,
        t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        eta < -velocityH3TransportDerivative3At u t →
        ThirdFullKineticSignedLowMaxIntegratedGapEscape244
          hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  have hOld := thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated
    hWindows eta hEta J E epsilon hE hEpsilon
  have hDiss := thirdFullPhysical_kineticGaps_fullDissipation_tendsto_zero244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated hWindows
  have hDissSmall : ∀ᶠ k : ℕ in atTop,
      (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) < epsilon :=
    hDiss.eventually (eventually_lt_nhds hEpsilon)
  filter_upwards [hOld, hDissSmall] with k hk hkDiss
  intro R t ht hAdverse
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  let X : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 t
  let Y : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 x
  let mu : ℝ := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
  let Hlinear : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    R eta (velocityH3EnergyAt u t)
  let Hquadratic : ℝ := thirdFullKineticSignedLowMaxPhysicalViscousHeight244
    R X Y (mu / 2)
  let Hmin : ℝ := thirdFullKineticSignedLowMaxUnifiedPhysicalViscousHeight244
    R eta X Y (velocityH3EnergyAt u t)
  have hx : x ∈ Set.Ioo b T := by
    obtain ⟨htWin, hw⟩ := hWindows k
    rcases hw with ⟨_, hd, _, he, _, _⟩
    exact ⟨by linarith only [htWin.1, hd], he⟩
  have hy : y ∈ Set.Ioo b T := (hWindows (k + 1)).1
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hMinLinear : Hmin ≤ Hlinear := min_le_left _ _
  have hMinQuadratic : Hmin ≤ Hquadratic := min_le_right _ _
  have hHminScale (width : ℝ) (hw : 0 ≤ width)
      (HH : ℝ) (hHH : Hmin ≤ HH) :
      width * (Hmin / 4) ≤ width * (HH / 4) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hHH (by norm_num)) hw
  have hAlt :
      eta / 2 ≤ thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
        (velocityH3EnergyAt u t) *
        ‖thirdFullSpectralVelocityHighRadialApply244 R X‖ ^ 2 ∨
      (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
       let X := h3AuditActualSpectralVelocityTotal hH3 t
       let Y := h3AuditActualSpectralVelocityTotal hH3 x
       (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
       (J < R ∨ E < velocityH3EnergyAt u t ∨ E < velocityH3EnergyAt u x) ∨
       (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
          ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
          width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
            R X Y (mu / 2) / 4) < epsilon)) := by
    let A : ℝ := thirdFullKineticSignedLowMaxPhysicalHighTailFactor244
      (velocityH3EnergyAt u t)
    let H : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 R X‖
    let Q : Prop :=
      let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
      let X := h3AuditActualSpectralVelocityTotal hH3 t
      let Y := h3AuditActualSpectralVelocityTotal hH3 x
      (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
      (J < R ∨ E < velocityH3EnergyAt u t ∨ E < velocityH3EnergyAt u x) ∨
      (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
        ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
        width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
          R X Y (mu / 2) / 4) < epsilon)
    have hEach (gamma : ℝ) (hGamma : 0 < gamma) :
        eta / 2 < A * (H + gamma) ^ 2 ∨ Q := by
      have hPrev := hk R gamma hGamma t ht hAdverse
      change (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
        (1944 * h3SobolevFirstMomentDeweightingConstant *
          (velocityH3EnergyAt u t + 1) * (H + gamma) ^ 2)) ∨ Q at hPrev
      rcases hPrev with hTail | hOther
      · left
        simpa only [A, H, thirdFullKineticSignedLowMaxPhysicalHighTailFactor244,
          mul_assoc] using hTail
      · exact Or.inr hOther
    have hZero := thirdFull_scalar_signedLowMax_removePositiveTailTolerance244
      (eta / 2) A H Q hEach
    simpa only [A, H, Q, thirdFullKineticSignedLowMaxPhysicalHighTailFactor244]
      using hZero
  change ThirdFullKineticSignedLowMaxIntegratedGapEscape244
    hH3 R J E eta epsilon x y t
  rcases hAlt with hTail | hRest
  · obtain ⟨width, hWidth, hInside, hCost⟩ :=
      thirdFullPhysical_signedLowMax_gammaFreeTail_linearInGapCharge244
        hH3 hClass hDInt b hb R x y t hx hy hxy ht
        eta hEta (by simpa only [X] using hTail)
    right; right
    have hInsideGap :
        t + width < y ∨ (t = y ∧ x < y - width) := by
      rcases hInside with hForward | ⟨hty, hBackward⟩
      · exact Or.inl hForward
      · exact Or.inr ⟨hty, by simpa only [hty] using hBackward⟩
    refine ⟨t, width, Or.inl rfl, hWidth, hInsideGap, ?_⟩
    exact lt_of_le_of_lt
      ((hHminScale width hWidth.le Hlinear hMinLinear).trans hCost)
      hkDiss
  · rcases hRest with hBaseline | hRest
    · exact Or.inl hBaseline
    · rcases hRest with hEscape | ⟨z, width, hz, hWidth, hInside, hCost⟩
      · exact Or.inr (Or.inl hEscape)
      · right; right
        refine ⟨z, width, hz, hWidth, hInside, ?_⟩
        exact lt_of_le_of_lt
          (hHminScale width hWidth.le Hquadratic hMinQuadratic) hCost

/-- The actual signed integrated surplus on a late original kinetic gap
selects the adverse third-transport time automatically. Every branch then
uses only the original physical endpoints and a positive-width in-gap
viscous charge. The surplus premise is conditional on each selected gap. -/
theorem thirdFullPhysical_kineticGaps_signedSurplus_integratedViscousEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => tau (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      ∀ R : ℕ,
        thirdFullKineticGapLowOrderMargin244 u eta
            (tau (v k) + delta (v k)) (tau (v (k + 1))) <
          thirdFullKineticGapSignedSurplus244 u
            (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        ∃ t : ℝ,
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
          eta < -velocityH3TransportDerivative3At u t ∧
          ThirdFullKineticSignedLowMaxIntegratedGapEscape244
            hH3 R J E eta epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  have hEventually :=
    thirdFullPhysical_kineticGaps_signedLowMax_integratedViscousEscape244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  filter_upwards [hEventually] with k hk
  intro R hExcess
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  have hx : x ∈ Set.Ioo a T := by
    obtain ⟨htWin, hw⟩ := hWindows k
    rcases hw with ⟨_, hd, _, he, _, _⟩
    exact ⟨by linarith only [hb.1, htWin.1, hd], he⟩
  have hy : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  have hxy : x < y := hSeparated k (k + 1) (Nat.lt_succ_self k)
  obtain ⟨t, ht, hAdverse⟩ :=
    thirdFullPhysical_gapLowOrderExcess_forces_adverseThird244
      hH3 hClass x y eta hx hy hxy hEta hExcess
  exact ⟨t, ht, hAdverse, hk R t ht hAdverse⟩

end
end PrimeTensor.FirstMonomialTriad
