import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCofinalPhysicalEscape
import Mathlib.Tactic

/-!
# A tenth-power radial / physical-energy escape gate for signed LowMax flux

The preceding cofinal theorem shows that a surviving projected-source clock
has an unbounded multiplicative coefficient. Here the EXACT finite-band H3
weight is bounded above by twice the third power of its radius. Combined with
the genuine seventh-power signed flux estimate, this yields the explicit
TENTH radial power and a cubic physical-H3 amplitude, not an unspecified
frequency constant.

On the original cofinal kinetic gaps, at every fixed radial cap J and physical
energy cap E, a genuine adverse third-order observation must therefore pay
its high tail, its earlier cubic baseline, a radius/energy threshold escape,
or a compressed in-gap physical viscous charge. The source multiplier cannot
be a fifth, hidden branch when both physical caps hold.

No assumption that adverse observations occur on every gap is made. No
fixed-radius or uniform-in-time H3 bound is introduced into the hypotheses
of the original Navier--Stokes theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators Interval ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The literal finite-band H3 multiplier has a cubic radial upper bound.
The sharp cutoff is at R+1, not at the LowMax threshold 2(R+1). -/
theorem thirdFullFiniteBandH3WeightCeiling_le_radialCubic244
    (R : ℕ) :
    thirdFullFiniteBandH3WeightCeiling244 R ≤
      2 * ((R : ℝ) + 1) ^ 3 := by
  let r : ℝ := (R : ℝ) + 1
  have hr : 1 ≤ r := by
    dsimp only [r]
    have hNat : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    linarith only [hNat]
  have hr2 : 1 ≤ r ^ 2 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hr 2)
  have hr4 : 1 ≤ r ^ 4 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hr 4)
  have hr6 : 1 ≤ r ^ 6 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hr 6)
  have hr26 : r ^ 2 ≤ r ^ 6 := by
    calc
      r ^ 2 = r ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * r ^ 4 :=
        mul_le_mul_of_nonneg_left hr4 (sq_nonneg r)
      _ = r ^ 6 := by ring
  have hr46 : r ^ 4 ≤ r ^ 6 := by
    calc
      r ^ 4 = r ^ 4 * 1 := by ring
      _ ≤ r ^ 4 * r ^ 2 :=
        mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = r ^ 6 := by ring
  have hPoly : 1 + r ^ 2 + r ^ 4 + r ^ 6 ≤ (2 * r ^ 3) ^ 2 := by
    nlinarith only [hr6, hr26, hr46]
  have hSqrt := Real.sqrt_le_sqrt hPoly
  have hr0 : 0 ≤ r := by linarith only [hr]
  have hRight : 0 ≤ 2 * r ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg hr0 3)
  change Real.sqrt (1 + r ^ 2 + r ^ 4 + r ^ 6) ≤ 2 * r ^ 3
  calc
    Real.sqrt (1 + r ^ 2 + r ^ 4 + r ^ 6) ≤
        Real.sqrt ((2 * r ^ 3) ^ 2) := hSqrt
    _ = 2 * r ^ 3 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRight]

/-- The physical PDE signed-flux clock grows at most as radius to the TENTH
power times the cube of the two actual H3 state norms. -/
theorem thirdFullKinetic_signedLowMax_physicalClock_le_radialTenth244
    (R : ℕ) (X Y : H3SpectralVelocityState) :
    thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y *
        thirdFullFiniteBandH3WeightCeiling244 R ≤
      (62208 * h3SobolevDeweightingConstant) *
        ((R : ℝ) + 1) ^ 10 * (3 + ‖X‖ + ‖Y‖) ^ 3 := by
  have hB : 0 ≤ thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y := by
    unfold thirdFullKineticSignedLowMaxPhysicalClockCeiling244
    positivity [h3SobolevDeweightingConstant_nonneg]
  calc
    _ ≤ thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y *
        (2 * ((R : ℝ) + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (thirdFullFiniteBandH3WeightCeiling_le_radialCubic244 R) hB
    _ = (62208 * h3SobolevDeweightingConstant) *
          ((R : ℝ) + 1) ^ 10 * (3 + ‖X‖ + ‖Y‖) ^ 3 := by
      unfold thirdFullKineticSignedLowMaxPhysicalClockCeiling244
      ring

/-- A uniform physical cap on both H3 spectral norms and on the natural
Fourier radius gives a NUMERICAL upper bound for the original PDE clock. -/
noncomputable def thirdFullKineticSignedLowMaxRadiusEnergyCeiling244
    (J : ℕ) (E : ℝ) : ℝ :=
  (62208 * h3SobolevDeweightingConstant) *
    ((J : ℝ) + 1) ^ 10 * (3 + 2 * E) ^ 3

theorem thirdFullKinetic_signedLowMax_radiusEnergyCeiling_nonneg244
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E) :
    0 ≤ thirdFullKineticSignedLowMaxRadiusEnergyCeiling244 J E := by
  unfold thirdFullKineticSignedLowMaxRadiusEnergyCeiling244
  positivity [h3SobolevDeweightingConstant_nonneg]

/-- The clock at a bounded cutoff and two bounded physical spectral states
cannot exceed the polynomial tenth-power bound. -/
theorem thirdFullKinetic_signedLowMax_clock_le_radiusEnergyCeiling244
    (R J : ℕ) (E : ℝ) (X Y : H3SpectralVelocityState)
    (hRJ : R ≤ J) (hX : ‖X‖ ≤ E) (hY : ‖Y‖ ≤ E) :
    thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y *
        thirdFullFiniteBandH3WeightCeiling244 R ≤
      thirdFullKineticSignedLowMaxRadiusEnergyCeiling244 J E := by
  have hRadius : (R : ℝ) + 1 ≤ (J : ℝ) + 1 := by
    have hCast : (R : ℝ) ≤ (J : ℝ) := by exact_mod_cast hRJ
    linarith only [hCast]
  have hRadiusPow : ((R : ℝ) + 1) ^ 10 ≤ ((J : ℝ) + 1) ^ 10 :=
    pow_le_pow_left₀ (by positivity) hRadius 10
  have hSum : 3 + ‖X‖ + ‖Y‖ ≤ 3 + 2 * E := by
    linarith only [hX, hY]
  have hAmplitudePow : (3 + ‖X‖ + ‖Y‖) ^ 3 ≤ (3 + 2 * E) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hSum 3
  have hC : 0 ≤ 62208 * h3SobolevDeweightingConstant := by
    positivity [h3SobolevDeweightingConstant_nonneg]
  calc
    _ ≤ (62208 * h3SobolevDeweightingConstant) *
          ((R : ℝ) + 1) ^ 10 * (3 + ‖X‖ + ‖Y‖) ^ 3 :=
      thirdFullKinetic_signedLowMax_physicalClock_le_radialTenth244 R X Y
    _ ≤ (62208 * h3SobolevDeweightingConstant) *
          ((J : ℝ) + 1) ^ 10 * (3 + ‖X‖ + ‖Y‖) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hRadiusPow hC
    _ ≤ thirdFullKineticSignedLowMaxRadiusEnergyCeiling244 J E := by
      unfold thirdFullKineticSignedLowMaxRadiusEnergyCeiling244
      exact mul_le_mul_of_nonneg_left hAmplitudePow (by positivity)

/-- An arbitrarily high physical source multiplier must exceed either a
chosen radial cutoff J or a chosen H3 STATE-NORM ceiling E. -/
theorem thirdFullKinetic_signedLowMax_clockEscape_radiusOrState244
    (R J : ℕ) (E : ℝ) (X Y : H3SpectralVelocityState)
    (hEscape : thirdFullKineticSignedLowMaxRadiusEnergyCeiling244 J E <
      thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R X Y *
        thirdFullFiniteBandH3WeightCeiling244 R) :
    J < R ∨ E < ‖X‖ ∨ E < ‖Y‖ := by
  by_cases hJ : J < R
  · exact Or.inl hJ
  right
  have hRJ : R ≤ J := Nat.le_of_not_gt hJ
  by_cases hX : E < ‖X‖
  · exact Or.inl hX
  right
  by_cases hY : E < ‖Y‖
  · exact hY
  have hXBound : ‖X‖ ≤ E := le_of_not_gt hX
  have hYBound : ‖Y‖ ≤ E := le_of_not_gt hY
  have hBound := thirdFullKinetic_signedLowMax_clock_le_radiusEnergyCeiling244
    R J E X Y hRJ hXBound hYBound
  exact False.elim ((not_lt_of_ge hBound) hEscape)

/-- The actual strict-time weighted spectral state is bounded by the
project's physical H3 energy at that same time; no terminal ceiling used. -/
theorem thirdFullPhysical_signedLowMax_stateNorm_le_energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
      velocityH3EnergyAt u s := by
  have hsNS : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  let hInt : VelocityH3IntegrableAt u s :=
    hH3.velocity_h3_integrable s hsNS
  let hMeas : VelocityH3MeasurableAt u s :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes hsNS
  let hFourier : VelocityH3FourierCompatibleAt u s hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes hsNS hInt
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 s hsNS]
  exact norm_velocityH3SpectralStateAt_le_energyCeiling
    hFourier (one_le_velocityH3EnergyAt u s) le_rfl

/-- The strengthened physical cofinal outcome: after the true source-L1
terminal limit, the former source multiplier is replaced by a concrete
radius escape or by growth of one of the TWO ACTUAL physical H3 energies. -/
def ThirdFullKineticSignedLowMaxRadiusEnergyEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R J : ℕ) (E gamma eta epsilon x y t : ℝ) : Prop :=
  (eta / 2 < ((2 * Real.pi) ^ 7 / 3) *
    (1944 * h3SobolevFirstMomentDeweightingConstant *
      (velocityH3EnergyAt u t + 1) *
      (‖thirdFullSpectralVelocityHighRadialApply244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)‖ + gamma) ^ 2)) ∨
  (let mu := thirdFullKineticSignedLowMaxPhysicalMargin244 eta
   let X := h3AuditActualSpectralVelocityTotal hH3 t
   let Y := h3AuditActualSpectralVelocityTotal hH3 x
   (mu / 2 ≤ thirdFullKineticSignedLowMaxPhysicalBaselineCeiling244 R Y) ∨
   (J < R ∨ E < velocityH3EnergyAt u t ∨ E < velocityH3EnergyAt u x) ∨
   (∃ z width : ℝ, (z = t ∨ z = x) ∧ 0 < width ∧
      ((z + width < y) ∨ (z = y ∧ x < y - width)) ∧
      width * (thirdFullKineticSignedLowMaxPhysicalViscousHeight244
        R X Y (mu / 2) / 4) < epsilon))

/-- On EVERY sufficiently late original gap, all positive signed adverse
physical observations satisfy a four-way alternative with a tenth-power
RADIAL / PHYSICAL H3 ENERGY escape. The chosen caps J and E are arbitrary;
the original Navier--Stokes solution is not assumed to obey them. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
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
      ∀ (R : ℕ) (gamma : ℝ), 0 < gamma →
        ∀ t : ℝ,
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
          eta < -velocityH3TransportDerivative3At u t →
          ThirdFullKineticSignedLowMaxRadiusEnergyEscape244
            hH3 R J E gamma eta epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  let K := thirdFullKineticSignedLowMaxRadiusEnergyCeiling244 J E
  have hK : 0 ≤ K :=
    thirdFullKinetic_signedLowMax_radiusEnergyCeiling_nonneg244 J E hE
  have hOld := thirdFullPhysical_kineticGaps_signedLowMax_physicalCofinalEscape244
    hH3 hClass hDInt b hb M tau N delta v
    hLimit hSeparated hWindows eta hEta K epsilon hK hEpsilon
  filter_upwards [hOld] with k hk
  intro R gamma hGamma t ht hAdverse
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
  have hXNorm := thirdFullPhysical_signedLowMax_stateNorm_le_energy244
    hH3 hClass htClass
  have hYNorm := thirdFullPhysical_signedLowMax_stateNorm_le_energy244
    hH3 hClass hx
  have hPrev := hk R gamma hGamma t ht hAdverse
  change ThirdFullKineticSignedLowMaxPhysicalCofinalEscape244
    hH3 R gamma eta K epsilon x y t at hPrev
  change ThirdFullKineticSignedLowMaxRadiusEnergyEscape244
    hH3 R J E gamma eta epsilon x y t
  rcases hPrev with hTail | hRest
  · exact Or.inl hTail
  right
  rcases hRest with hBaseline | hRest
  · exact Or.inl hBaseline
  right
  rcases hRest with hClock | hCharge
  · left
    have hClock' :
        thirdFullKineticSignedLowMaxRadiusEnergyCeiling244 J E <
          thirdFullKineticSignedLowMaxPhysicalClockCeiling244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)
            (h3AuditActualSpectralVelocityTotal hH3 x) *
              thirdFullFiniteBandH3WeightCeiling244 R := by
      simpa only [K] using hClock
    rcases thirdFullKinetic_signedLowMax_clockEscape_radiusOrState244
      R J E
      (h3AuditActualSpectralVelocityTotal hH3 t)
      (h3AuditActualSpectralVelocityTotal hH3 x) hClock'
      with hRadius | hTime | hStart
    · exact Or.inl hRadius
    · exact Or.inr (Or.inl (lt_of_lt_of_le hTime hXNorm))
    · exact Or.inr (Or.inr (lt_of_lt_of_le hStart hYNorm))
  · exact Or.inr hCharge

/-- No adverse physical snapshot is postulated in this variant. The actual
integrated signed surplus supplies it on any qualifying original gap. -/
theorem thirdFullPhysical_kineticGaps_signedSurplus_radiusEnergyEscape244
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
      ∀ (R : ℕ) (gamma : ℝ), 0 < gamma →
        thirdFullKineticGapLowOrderMargin244 u eta
            (tau (v k) + delta (v k)) (tau (v (k + 1))) <
          thirdFullKineticGapSignedSurplus244 u
            (tau (v k) + delta (v k)) (tau (v (k + 1))) →
        ∃ t : ℝ,
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) ∧
          eta < -velocityH3TransportDerivative3At u t ∧
          ThirdFullKineticSignedLowMaxRadiusEnergyEscape244
            hH3 R J E gamma eta epsilon
            (tau (v k) + delta (v k)) (tau (v (k + 1))) t := by
  have hEventually :=
    thirdFullPhysical_kineticGaps_signedLowMax_radiusEnergyEscape244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  filter_upwards [hEventually] with k hk
  intro R gamma hGamma hExcess
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
  exact ⟨t, ht, hAdverse, hk R gamma hGamma t ht hAdverse⟩

end
end PrimeTensor.FirstMonomialTriad
