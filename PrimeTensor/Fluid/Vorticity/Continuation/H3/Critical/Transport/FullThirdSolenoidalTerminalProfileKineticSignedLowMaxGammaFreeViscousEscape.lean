import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxRadialTenthPowerEscape
import Mathlib.Tactic

/-!
# Eliminate positive high-tail recovery tolerance by a physical viscous limit

The previously established cofinal signed LowMax radius-or-energy alternative
holds for ALL positive Fourier recovery tolerances `gamma`, with its other
three branches independent of `gamma`. Taking `gamma -> 0` by the genuine
native Schwartz/physical recovery theorem yields the TRUE high-radial norm,
not an arbitrary `norm + gamma` surrogate. Physical high-radial coercivity
then charges this highpass witness directly to the *actual instantaneous*
full fourth-derivative H3 dissipation at the adverse physical time.

This is an independent, pointwise H3 viscous gate: it is NOT a lower bound on
the full time-integrated dissipation over a positive-width interval. The
remaining baseline, radial/energy escape, and in-gap annular alternatives
are unchanged. The order of quantifiers allows gamma to be removed after
choosing any cofinal original kinetic gap, radius and adverse observation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A uniform strict quadratic estimate at every positive offset has a
non-strict zero-offset limit, even if an unrelated, offset-INDEPENDENT
alternative can hold. The same alternative must appear for each offset. -/
theorem thirdFull_scalar_signedLowMax_removePositiveTailTolerance244
    (eta A H : ℝ) (Q : Prop)
    (hAlt : ∀ gamma : ℝ, 0 < gamma →
      eta < A * (H + gamma) ^ 2 ∨ Q) :
    eta ≤ A * H ^ 2 ∨ Q := by
  classical
  by_cases hQ : Q
  · exact Or.inr hQ
  left
  let gamma : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hGamma : Tendsto gamma atTop (𝓝 (0 : ℝ)) := by
    simpa only [gamma] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          atTop (𝓝 (0 : ℝ)))
  have hPos (n : ℕ) : 0 < gamma n := by
    dsimp only [gamma]
    positivity
  have hEvent : ∀ᶠ n : ℕ in atTop,
      eta ≤ A * (H + gamma n) ^ 2 := by
    exact Filter.Eventually.of_forall (fun n => by
      rcases hAlt (gamma n) (hPos n) with hTail | hOther
      · exact hTail.le
      · exact False.elim (hQ hOther))
  have hOffset : Tendsto (fun n : ℕ => H + gamma n)
      atTop (𝓝 H) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hGamma :
        Tendsto (fun n : ℕ => H + gamma n) atTop (𝓝 (H + 0)))
  have hLimit : Tendsto (fun n : ℕ => A * (H + gamma n) ^ 2)
      atTop (𝓝 (A * H ^ 2)) :=
    tendsto_const_nhds.mul (hOffset.pow 2)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hLimit hEvent

/-- The four physical cofinal costs, with NO Schwartz error or positive
high-frequency recovery tolerance. The first cost is a genuine instantaneous
fourth-order physical H3 viscous spike at the adverse time. Its coefficient
is exactly the original physical sixth-flux normalization and energy factor. -/
def ThirdFullKineticSignedLowMaxGammaFreeViscousEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R J : ℕ) (E eta epsilon x y t : ℝ) : Prop :=
  (((R : ℝ) + 1) ^ 2 * (eta / 2) ≤
    (((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u t + 1))) *
          velocityH3DissipationAt u t) ∨
  (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
   let X := h3AuditActualSpectralVelocityTotal hH3 t
   let Y := h3AuditActualSpectralVelocityTotal hH3 x
   (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
   (J < R ∨ E < velocityH3EnergyAt u t ∨ E < velocityH3EnergyAt u x) ∨
   (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
      ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
      width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
        R X Y (mu / 2) / 4) < epsilon))

/-- The universal positive-recovery-error physical theorem implies a
strictly more informative error-FREE theorem. The true radial H3 tail is
converted to instantaneous full physical H3 dissipation at the SAME time. -/
theorem thirdFullPhysical_signedLowMax_gammaFreeViscous_of_allErrors244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (R J : ℕ) (E eta epsilon x y : ℝ)
    (hAll : ∀ gamma : ℝ, 0 < gamma →
      ThirdFullKineticSignedLowMaxRadiusEnergyEscape244
        hH3 R J E gamma eta epsilon x y t) :
    ThirdFullKineticSignedLowMaxGammaFreeViscousEscape244
      hH3 R J E eta epsilon x y t := by
  classical
  let X : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let H : ℝ := ‖thirdFullSpectralVelocityHighRadialApply244 R X‖
  let A : ℝ := ((2 * Real.pi) ^ 7 / 3) *
    (1944 * h3SobolevFirstMomentDeweightingConstant *
      (velocityH3EnergyAt u t + 1))
  let Q : Prop :=
    let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
    let Y := h3AuditActualSpectralVelocityTotal hH3 x
    (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
    (J < R ∨ E < velocityH3EnergyAt u t ∨ E < velocityH3EnergyAt u x) ∨
    (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
      ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
      width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
        R X Y (mu / 2) / 4) < epsilon)
  have hAlt (gamma : ℝ) (hGamma : 0 < gamma) :
      eta / 2 < A * (H + gamma) ^ 2 ∨ Q := by
    have hOld := hAll gamma hGamma
    change (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
      (1944 * h3SobolevFirstMomentDeweightingConstant *
        (velocityH3EnergyAt u t + 1) *
        (‖thirdFullSpectralVelocityHighRadialApply244 R X‖ + gamma) ^ 2)) ∨ Q
      at hOld
    rcases hOld with hTail | hOther
    · left
      simpa only [A, H, mul_assoc] using hTail
    · exact Or.inr hOther
  have hA : 0 ≤ A := by
    have hEnergy : 1 ≤ velocityH3EnergyAt u t :=
      one_le_velocityH3EnergyAt u t
    have hEnergyPlus : 0 ≤ velocityH3EnergyAt u t + 1 := by
      linarith only [hEnergy]
    have hC : 0 ≤ h3SobolevFirstMomentDeweightingConstant :=
      h3SobolevFirstMomentDeweightingConstant_nonneg
    dsimp only [A]
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) hC) hEnergyPlus)
  have hAbstract := thirdFull_scalar_signedLowMax_removePositiveTailTolerance244
    (eta / 2) A H Q hAlt
  change ThirdFullKineticSignedLowMaxGammaFreeViscousEscape244
    hH3 R J E eta epsilon x y t
  rcases hAbstract with hTail | hOther
  · left
    have hRadial : 0 ≤ ((R : ℝ) + 1) ^ 2 := sq_nonneg _
    have hCoercive := thirdFullPhysical_fullViscousCoercivity244
      hH3 hClass t ht R
    change ((R : ℝ) + 1) ^ 2 * H ^ 2 ≤
      velocityH3DissipationAt u t at hCoercive
    calc
      ((R : ℝ) + 1) ^ 2 * (eta / 2) ≤
          ((R : ℝ) + 1) ^ 2 * (A * H ^ 2) :=
        mul_le_mul_of_nonneg_left hTail hRadial
      _ = A * (((R : ℝ) + 1) ^ 2 * H ^ 2) := by ring
      _ ≤ A * velocityH3DissipationAt u t :=
        mul_le_mul_of_nonneg_left hCoercive hA
  · exact Or.inr hOther

/-- Uniform-in-cutoff cofinal obstruction with the TRUE instantaneous
physical viscous cost. The terminal threshold does not depend on the
cutoff R, observation t, or an approximation tolerance. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_gammaFreeViscousEscape244
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
        ThirdFullKineticSignedLowMaxGammaFreeViscousEscape244
          hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  have hOld := thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
    hH3 hClass hDInt b hb M tau N delta v hLimit hSeparated
    hWindows eta hEta J E epsilon hE hEpsilon
  filter_upwards [hOld] with k hk
  intro R t ht hAdverse
  let x : ℝ := tau (v k) + delta (v k)
  let y : ℝ := tau (v (k + 1))
  have hx : x ∈ Set.Ioo a T := by
    obtain ⟨htWin, hw⟩ := hWindows k
    rcases hw with ⟨_, hd, _, he, _, _⟩
    exact ⟨by linarith only [hb.1, htWin.1, hd], he⟩
  have hy : y ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (hWindows (k + 1)).1.1,
      (hWindows (k + 1)).1.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  apply thirdFullPhysical_signedLowMax_gammaFreeViscous_of_allErrors244
    hH3 hClass htClass R J E eta epsilon x y
  intro gamma hGamma
  exact hk R gamma hGamma t ht hAdverse

/-- The original *integrated signed surplus* selects one adverse physical
observation before the auxiliary gamma limit. The final physical statement
contains no Schwartz profile and no positive Fourier recovery tolerance. -/
theorem thirdFullPhysical_kineticGaps_signedSurplus_gammaFreeViscousEscape244
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
          ThirdFullKineticSignedLowMaxGammaFreeViscousEscape244
            hH3 R J E eta epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  have hEventually :=
    thirdFullPhysical_kineticGaps_signedLowMax_gammaFreeViscousEscape244
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
