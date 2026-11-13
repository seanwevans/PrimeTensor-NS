import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierSignedYoungPDEGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularDeficitUniformSlope
import Mathlib.Tactic

/-!
# Exact early-time anchored Young slope and physical source-budget coercivity

The earlier signed Young gate uses the later Young cost inside the coefficient
multiplying the highpass-mass difference. Its size is therefore not controlled
by the finite-radius *snapshot* slope theorem.

An exact, nontrivial refactor of the physical deficit polynomial uses instead

the early Young cost and the LATER sharp kinetic mass as the multiplier of
signed Young growth:

  deficit(x)-deficit(s) = [M(x)-M(s)] * anchoredSlope(x,s)
                          + M(s) * [Y(s)-Y(x)].

The anchored slope is bounded by the genuine one-snapshot Fourier residual,
kinetic low-ball source ceiling and viscous base. No bound on Y(s), no novel
source derivative and no uniform-in-frequency Lipschitz assumption is needed.

The resulting scalar majorant is *dynamically calibrated*: the cap on M(s)
comes from the actual projected physical Navier--Stokes source action, instead
of requiring the mass error to be at most one. This removes the unknown exact
slope from the cofinal alternative, at the price of a transparent finite-R
snapshot envelope. Its growth as the selected frequency escapes is the next
hard analytic obstacle; finite H3 dissipation does not bound it uniformly.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The actual physical projected source budget, multiplied by the quadratic
Hilbert mass-variation coefficient at the selected snapshot. -/
noncomputable def thirdFullPhysicalOuterSourceMassBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x : ℝ) : ℝ :=
  let H := thirdFullPhysicalOuterTerminalSourceBudget244 u b x T
  let V := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  H * (2 * ‖V‖ + H)

/-- The EXACT annular deficit slope anchored at the EARLIER (snapshot)
Young-width cost. This is not the later-time coefficient from the preceding
signed Young theorem. -/
noncomputable def thirdFullPhysicalOuterEarlyYoungSlope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma : ℝ) : ℝ :=
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  w * a * (a * (Mx + Ms) - 2 * B) - (Yx + w * P)

/-- The finite-radius snapshot slope ceiling with an arbitrary nonnegative
physical kinetic-mass error A, rather than the artificial error cap 1. -/
noncomputable def thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b R A : ℝ) (U : H3SpectralVelocityState)
    (V : H3PhysicalRealFinVectorL2Hilbert) : ℝ :=
  let E : ℝ := velocityH3Energy0At u b
  let H : ℝ := ‖V‖ ^ 2 + A
  let Bcap : ℝ := Real.sqrt E *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244 R E)
  let Pcap : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b (R ^ 2)
  let Ycap : ℝ := thirdFullPhysicalAnnularSnapshotYoungEnvelope244 R U
  let Wcap : ℝ := (R ^ 2) ^ 3
  (Wcap * R ^ 2) * (R ^ 2 * (2 * H) + 2 * Bcap) +
    (Ycap + Wcap * Pcap)

/-- Pure algebra: changing the Young time anchor replaces M(x) by M(s)
as the multiplier of signed nonlinear growth. No estimate has been used. -/
theorem thirdFullKinetic_deficitPolynomial_earlyYoungIdentity244
    (a B w P mx ms yx ys : ℝ) :
    (w * (a * mx - B) ^ 2 - mx * (yx + w * P)) -
      (w * (a * ms - B) ^ 2 - ms * (ys + w * P)) =
      (mx - ms) * (w * a * (a * (mx + ms) - 2 * B) - (yx + w * P)) +
        ms * (ys - yx) := by
  ring

/-- The ORIGINAL physical deficit has the anchored identity: its true
signed Young-width increment is paid by the *later* kinetic highpass mass. -/
theorem thirdFullPhysical_outerDeficit_earlyYoungIdentity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma : ℝ) :
    let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
    let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma =
      (Mx - Ms) * thirdFullPhysicalOuterEarlyYoungSlope244 hH3 b x s rho sigma +
        Ms * (Ys - Yx) := by
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  have hExact := thirdFullPhysical_actualAnnularDeficit_twoTimeIdentity244
    hH3 b x s rho sigma
  change
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma =
      (Mx - Ms) * (w * a * (a * (Mx + Ms) - 2 * B) - (Ys + w * P)) -
        Mx * (Yx - Ys) at hExact
  change
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma =
      (Mx - Ms) * (w * a * (a * (Mx + Ms) - 2 * B) - (Yx + w * P)) +
        Ms * (Ys - Yx)
  calc
    _ = (Mx - Ms) * (w * a * (a * (Mx + Ms) - 2 * B) - (Ys + w * P)) -
        Mx * (Yx - Ys) := hExact
    _ = (Mx - Ms) * (w * a * (a * (Mx + Ms) - 2 * B) - (Yx + w * P)) +
        Ms * (Ys - Yx) := by ring

/-- Signed polynomial splitting with the later kinetic mass; unlike a
pure absolute-value estimate this forces a positive Young increment. -/
theorem thirdFullKinetic_earlyYoungDrop_forcesSlopeOrGain244
    (epsilon mx ms Q A yx ys : ℝ)
    (hMass : |mx - ms| ≤ A)
    (hDrop : epsilon < (mx - ms) * Q + ms * (ys - yx)) :
    epsilon / 2 < A * |Q| ∨
      epsilon / 2 < ms * (ys - yx) := by
  have hSlope : (mx - ms) * Q ≤ A * |Q| := by
    calc
      (mx - ms) * Q ≤ |(mx - ms) * Q| := le_abs_self _
      _ = |mx - ms| * |Q| := abs_mul _ _
      _ ≤ A * |Q| := mul_le_mul_of_nonneg_right hMass (abs_nonneg Q)
  by_cases hBig : epsilon / 2 < A * |Q|
  · exact Or.inl hBig
  · right
    have hSmall : A * |Q| ≤ epsilon / 2 := le_of_not_gt hBig
    linarith only [hDrop, hSlope, hSmall]

/-- The actual projected physical momentum equation bounds sharp Fourier
kinetic mass variation, uniformly in the sharp cutoff, by a source budget
quadratic in the terminal projected source L1 payment. -/
theorem thirdFullPhysical_outerHighpassMassDrift_le_sourceBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho : ℝ) :
    |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤
      thirdFullPhysicalOuterSourceMassBudget244 hH3 b x := by
  let S : ℝ := ∫ r in x..T,
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖
  let H : ℝ := thirdFullPhysicalOuterTerminalSourceBudget244 u b x T
  let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Vs := h3AuditInitialOldPhysicalHilbertTotal hH3 s
  have hIncrement : ‖Vs - Vx‖ ≤ S :=
    thirdFullPhysical_outerSourceTail_controlsVelocityIncrement244
      hH3 hClass hDInt b hb x hx s hxs hsT
  have hSH : S ≤ H := by
    dsimp only [S, H, thirdFullPhysicalOuterTerminalSourceBudget244]
    exact thirdFullPhysical_outerSourceTail_le_kineticViscousBudget244
      hH3 hClass hDInt b hb x hx
  have hS : 0 ≤ S :=
    (norm_nonneg (Vs - Vx)).trans hIncrement
  have hTriangle : ‖Vs‖ ≤ ‖Vs - Vx‖ + ‖Vx‖ := by
    calc
      ‖Vs‖ = ‖(Vs - Vx) + Vx‖ := by rw [sub_add_cancel]
      _ ≤ ‖Vs - Vx‖ + ‖Vx‖ := norm_add_le _ _
  have hSum : ‖Vs‖ + ‖Vx‖ ≤ 2 * ‖Vx‖ + S := by
    linarith only [hTriangle, hIncrement]
  have hQuadratic :
      ‖Vs - Vx‖ * (‖Vs‖ + ‖Vx‖) ≤
        S * (2 * ‖Vx‖ + S) := by
    calc
      _ ≤ S * (‖Vs‖ + ‖Vx‖) :=
        mul_le_mul_of_nonneg_right hIncrement (by positivity)
      _ ≤ S * (2 * ‖Vx‖ + S) :=
        mul_le_mul_of_nonneg_left hSum
          (le_trans (norm_nonneg (Vs - Vx)) hIncrement)
  have hHQuadratic : S * (2 * ‖Vx‖ + S) ≤
      H * (2 * ‖Vx‖ + H) := by
    have hWidth : 2 * ‖Vx‖ + S ≤ 2 * ‖Vx‖ + H := by
      linarith only [hSH]
    calc
      _ ≤ H * (2 * ‖Vx‖ + S) :=
        mul_le_mul_of_nonneg_right hSH (by positivity)
      _ ≤ H * (2 * ‖Vx‖ + H) :=
        mul_le_mul_of_nonneg_left hWidth (hS.trans hSH)
  have hHighpass := thirdFullPhysical_actualSharpHighMass_uniformTwoTime244
    hH3 rho s x
  change
    |thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho -
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho| ≤
      H * (2 * ‖Vx‖ + H)
  exact (hHighpass.trans hQuadratic).trans hHQuadratic

/-- With a physical source-budget mass error A, the EARLY-YOUNG slope is
bounded by the already-proved true finite-radius snapshot envelope. Unlike
an error-cap-1 estimate, this bound requires no restriction on the amount
of physical highpass drift before T. -/
theorem thirdFullPhysical_outerEarlyYoungSlope_le_dynamicSnapshotCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a₀ : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a₀ T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a₀ T)
    (b : ℝ) (hb : b ∈ Set.Ioo a₀ T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma R : ℝ)
    (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) (hUpper : sigma ≤ R) :
    |thirdFullPhysicalOuterEarlyYoungSlope244 hH3 b x s rho sigma| ≤
      thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b R
        (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
        (h3AuditActualSpectralVelocityTotal hH3 x)
        (h3AuditInitialOldPhysicalHilbertTotal hH3 x) := by
  let E : ℝ := velocityH3Energy0At u b
  let U : H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3 x
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let A : ℝ := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
  let H : ℝ := ‖V‖ ^ 2 + A
  let Bcap : ℝ := Real.sqrt E *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244 R E)
  let Pcap : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b (R ^ 2)
  let Ycap : ℝ := thirdFullPhysicalAnnularSnapshotYoungEnvelope244 R U
  let Wcap : ℝ := (R ^ 2) ^ 3
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt E *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244 rho E)
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  have hMass : |Ms - Mx| ≤ A :=
    thirdFullPhysical_outerHighpassMassDrift_le_sourceBudget244
      hH3 hClass hDInt b hb x hx s hxs hsT rho
  have hA : 0 ≤ A := (abs_nonneg (Ms - Mx)).trans hMass
  have hR : 0 ≤ R := hRho.trans (hOrder.trans hUpper)
  have ha : 0 ≤ a ∧ a ≤ R ^ 2 :=
    thirdFullKinetic_annularMeanSquare_bound244 rho sigma R hRho hOrder hUpper
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hwCap : w ≤ Wcap := by
    dsimp only [w, Wcap]
    have hSq : rho ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ hRho (hOrder.trans hUpper) 2
    exact pow_le_pow_left₀ (sq_nonneg rho) hSq 3
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (Real.sqrt_nonneg E)
      (mul_nonneg (by norm_num)
        (thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 rho E))
  have hBcap : B ≤ Bcap := by
    dsimp only [B, Bcap]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (thirdFullPhysical_kineticSourceCeiling_mono_real244
          rho R E hRho (hOrder.trans hUpper) hE) (by norm_num))
      (Real.sqrt_nonneg E)
  have hPcap : 0 ≤ P ∧ P ≤ Pcap := by
    simpa only [P, Pcap] using
      thirdFullPhysical_outerViscousCapBase_boundedReal244 u b a R ha.1 ha.2
  have hY : 0 ≤ Yx :=
    thirdFullPhysical_actualYoungWidth_nonneg244 hH3 x rho sigma hRho hOrder
  have hYcap : Yx ≤ Ycap :=
    thirdFullPhysical_actualYoungWidth_le_snapshotEnvelope244
      hH3 x rho sigma R hRho hOrder hUpper
  have hMs : 0 ≤ Ms := sq_nonneg _
  have hMx : 0 ≤ Mx := sq_nonneg _
  have hMx0 : Mx ≤ ‖V‖ ^ 2 := by
    change ‖V - thirdFullPhysicalSharpLowCutoffHilbert244 rho V‖ ^ 2 ≤ ‖V‖ ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _)
      (thirdFullPhysical_sharpVectorHighpass_norm_le244 rho V) 2
  have hMxH : Mx ≤ H := by
    dsimp only [H]
    linarith only [hMx0, hA]
  have hMsH : Ms ≤ H := by
    have hAbove : Ms - Mx ≤ |Ms - Mx| := le_abs_self _
    dsimp only [H]
    linarith only [hAbove, hMass, hMx0]
  change
    |w * a * (a * (Mx + Ms) - 2 * B) - (Yx + w * P)| ≤
      (Wcap * R ^ 2) * (R ^ 2 * (2 * H) + 2 * Bcap) +
        (Ycap + Wcap * Pcap)
  exact thirdFullKinetic_deficitSlope_bound_of_caps244
    a w B P Yx Mx Ms (R ^ 2) Wcap Bcap Pcap Ycap H
    ha.1 ha.2 hw hwCap hB hBcap
    hPcap.1 hPcap.2 hY hYcap hMx hMxH hMs hMsH

/-- The exact physical deficit drop pays either a KNOWN earlier-snapshot
finite-radius Fourier envelope times the projected source cost, or a
strictly positive signed growth of the ORIGINAL Young-width integral. No
unknown later-time polynomial slope remains. -/
theorem thirdFullPhysical_outerDeficitDrop_dynamicSlopeOrSignedYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma R epsilon : ℝ)
    (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) (hUpper : sigma ≤ R)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma) :
    let A := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
    let C := thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b R A
      (h3AuditActualSpectralVelocityTotal hH3 x)
      (h3AuditInitialOldPhysicalHilbertTotal hH3 x)
    let Ms := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Yx := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    let Ys := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    epsilon / 2 < A * C ∨ epsilon / 2 < Ms * (Ys - Yx) := by
  let A : ℝ := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
  let C : ℝ := thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b R A
    (h3AuditActualSpectralVelocityTotal hH3 x)
    (h3AuditInitialOldPhysicalHilbertTotal hH3 x)
  let Q : ℝ := thirdFullPhysicalOuterEarlyYoungSlope244 hH3 b x s rho sigma
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  have hMass' : |Ms - Mx| ≤ A :=
    thirdFullPhysical_outerHighpassMassDrift_le_sourceBudget244
      hH3 hClass hDInt b hb x hx s hxs hsT rho
  have hMass : |Mx - Ms| ≤ A := by
    calc
      |Mx - Ms| = |Ms - Mx| := abs_sub_comm _ _
      _ ≤ A := hMass'
  have hA : 0 ≤ A := (abs_nonneg _).trans hMass
  have hQ : |Q| ≤ C :=
    thirdFullPhysical_outerEarlyYoungSlope_le_dynamicSnapshotCeiling244
      hH3 hClass hDInt b hb x hx s hxs hsT
      rho sigma R hRho hOrder hUpper
  have hIdentity := thirdFullPhysical_outerDeficit_earlyYoungIdentity244
    hH3 b x s rho sigma
  change
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma =
      (Mx - Ms) * Q + Ms * (Ys - Yx) at hIdentity
  have hDrop' : epsilon < (Mx - Ms) * Q + Ms * (Ys - Yx) := by
    rw [hIdentity] at hDrop
    exact hDrop
  change epsilon / 2 < A * C ∨ epsilon / 2 < Ms * (Ys - Yx)
  rcases thirdFullKinetic_earlyYoungDrop_forcesSlopeOrGain244
      epsilon Mx Ms Q A Yx Ys hMass hDrop' with hSlope | hYoung
  · exact Or.inl (lt_of_lt_of_le hSlope (mul_le_mul_of_nonneg_left hQ hA))
  · exact Or.inr hYoung

/-- The half-tail physical selection now pays one of THREE EXPLICIT costs:
(1) the kinetic margin by source transport, (2) the deficit by source
transport times its bounded EARLY-time snapshot slope, or (3) a positive
signed increase of the actual nonlinear Young-width cost, multiplied by
later highpass mass. The frequency-bound R is chosen to be sigma itself. -/
theorem thirdFullPhysical_selectedOuter_lowHalfTail_dynamicSlopeOrSignedYoung244
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
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hSmall :
      (∫ r in x..T, velocityH3DissipationAt u r) <
        119 * margin * sigma ^ 6 * (T - x) / 320) :
    let H := thirdFullPhysicalOuterTerminalSourceBudget244 u b x T
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let A := thirdFullPhysicalOuterSourceMassBudget244 hH3 b x
    let C := thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b sigma A
      (h3AuditActualSpectralVelocityTotal hH3 x) Vx
    margin < (rho ^ 2 + sigma ^ 2) * A ∨
      (∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
        (epsilon / 2 < A * C ∨
         epsilon / 2 <
           thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho *
           (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
             thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma))) := by
  have hB := thirdFullPhysical_selectedOuter_lowHalfTail_forcesViscousSourceOrYoung244
    hH3 hClass hDInt b hb x hx rho sigma margin epsilon
    hRho hAspect hMargin hEps hExcess hPeak hSmall
  dsimp only at hB ⊢
  rcases hB with hSource | ⟨s, hs, hDrop⟩
  · exact Or.inl hSource
  · right
    have hsT : s < T := by linarith only [hs.2, hx.2]
    have hOrder : rho ≤ sigma := by linarith only [hRho, hAspect]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_dynamicSlopeOrSignedYoung244
        hH3 hClass hDInt b hb x hx s hs.1.le hsT
        rho sigma sigma epsilon hRho.le hOrder le_rfl hDrop⟩

/-- The later sharp highpass mass is nonnegative. Thus the signed branch
forces genuinely positive growth of the original Young-width cost itself,
not just a positive product or an absolute-value oscillation. -/
theorem thirdFullKinetic_laterMass_signedYoung_forcesStrictGrowth244
    (epsilon ms yx ys : ℝ)
    (hEps : 0 < epsilon) (hMs : 0 ≤ ms)
    (hGain : epsilon / 2 < ms * (ys - yx)) :
    yx < ys := by
  by_contra hNot
  have hDiff : ys - yx ≤ 0 := sub_nonpos.mpr (le_of_not_gt hNot)
  have hProd : ms * (ys - yx) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMs hDiff
  have hPos : 0 < epsilon / 2 := by positivity
  linarith only [hGain, hProd, hPos]


/-- A concrete sufficient criterion for ACTUAL signed nonlinear Young growth.
The two physical source payments are bounded using only the finite-radius
snapshot envelope. No later-time Young-cost bound or slope hypothesis is
assumed: the only extra hypotheses are explicit verifiable inequalities
on the snapshot, remaining physical time and H3 viscous terminal action. -/
theorem thirdFullPhysical_selectedOuter_dynamicSlopeSmall_forcesYoungGrowth244
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
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma)
    (hSmall :
      (∫ r in x..T, velocityH3DissipationAt u r) <
        119 * margin * sigma ^ 6 * (T - x) / 320)
    (hSourceSmall :
      (rho ^ 2 + sigma ^ 2) *
        thirdFullPhysicalOuterSourceMassBudget244 hH3 b x ≤ margin)
    (hSlopeSmall :
      thirdFullPhysicalOuterSourceMassBudget244 hH3 b x *
        thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244 u b sigma
          (thirdFullPhysicalOuterSourceMassBudget244 hH3 b x)
          (h3AuditActualSpectralVelocityTotal hH3 x)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 x) ≤ epsilon / 2) :
    ∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma <
        thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma := by
  have hChoice :=
    thirdFullPhysical_selectedOuter_lowHalfTail_dynamicSlopeOrSignedYoung244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak hSmall
  dsimp only at hChoice
  rcases hChoice with hSource | ⟨s, hs, hAlt⟩
  · exact False.elim ((not_lt_of_ge hSourceSmall) hSource)
  · rcases hAlt with hSlope | hYoung
    · exact False.elim ((not_lt_of_ge hSlopeSmall) hSlope)
    · exact ⟨s, hs,
        thirdFullKinetic_laterMass_signedYoung_forcesStrictGrowth244
          epsilon
          (thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho)
          (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)
          (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma)
          hEps (sq_nonneg _) hYoung⟩

/-- Along every cofinal physical time sequence with finite full H3
viscosity, the explicit physical source-tail budget tends to zero. This
vanishing is unweighted: no assertion is made about a moving-frequency
snapshot slope multiplying it. -/
theorem thirdFullPhysical_outerTerminalSourceBudget_cofinal_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℕ → ℝ) (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hCofinal : Tendsto x atTop (𝓝 T)) :
    Tendsto (fun k : ℕ =>
      thirdFullPhysicalOuterTerminalSourceBudget244 u b (x k) T)
      atTop (𝓝 (0 : ℝ)) := by
  have hTail : Tendsto (fun k : ℕ =>
      ∫ r in x k..T, velocityH3DissipationAt u r)
      atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt x hCofinal
      (Filter.Eventually.of_forall (fun k =>
        ⟨le_of_lt (lt_trans hb.1 (hx k).1), (hx k).2.le⟩))
  have hTime : Tendsto (fun k : ℕ => T - x k)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (T : ℝ))
        atTop (𝓝 T)).sub hCofinal
  have hKinetic : Tendsto (fun k : ℕ =>
      (1 + 6 * velocityH3Energy0At u b) * (T - x k))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (1 + 6 * velocityH3Energy0At u b))
        atTop (𝓝 (1 + 6 * velocityH3Energy0At u b))).mul hTime
  have hViscous : Tendsto (fun k : ℕ =>
      3 * (∫ r in x k..T, velocityH3DissipationAt u r))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ))
        atTop (𝓝 (3 : ℝ))).mul hTail
  have hSum := hKinetic.add hViscous
  have hBudget :=
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (3 + h3AuditInitialLerayEnergyCoefficient))
      atTop (𝓝 (3 + h3AuditInitialLerayEnergyCoefficient))).mul hSum
  simpa only [thirdFullPhysicalOuterTerminalSourceBudget244,
    zero_add, mul_zero] using hBudget

/-- Cofinal terminal version with no unknown two-time slope: every late
selected annulus must pay a directly calibrated physical source excursion,
the SAME source excursion multiplied by the finite-radius snapshot Fourier
slope envelope, or a strictly positive later-mass-weighted signed growth
of the true nonlinear Young-width cost. The source action itself vanishes.
The radius-dependent envelope is not proved uniformly bounded. -/
theorem thirdFullPhysical_cofinalSelectedOuterMargins_dynamicSlopeOrSignedYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x rho sigma margin epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
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
        hH3 b (x k) (rho k) (sigma k))
    (c : ℝ) (hc : 0 < c)
    (hTerminalScale : ∀ᶠ k : ℕ in atTop,
      c ≤ margin k * sigma k ^ 6 * (T - x k)) :
    (∀ᶠ k : ℕ in atTop,
      let H := thirdFullPhysicalOuterTerminalSourceBudget244 u b (x k) T
      let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)
      let A := thirdFullPhysicalOuterSourceMassBudget244 hH3 b (x k)
      let C := thirdFullPhysicalOuterDynamicSnapshotSlopeCeiling244
        u b (sigma k) A (h3AuditActualSpectralVelocityTotal hH3 (x k)) Vx
      margin k < (rho k ^ 2 + sigma k ^ 2) * A ∨
      (∃ s : ℝ, s ∈ Set.Ioc (x k) ((x k + T) / 2) ∧
        (epsilon k / 2 < A * C ∨
         epsilon k / 2 <
           thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (rho k) *
           (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s
              (rho k) (sigma k) -
            thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 (x k)
              (rho k) (sigma k))))) ∧
    Tendsto (fun k : ℕ =>
      thirdFullPhysicalOuterTerminalSourceBudget244 u b (x k) T)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨hChoice, _hSourceTail⟩ :=
    thirdFullPhysical_cofinalSelectedOuterMargins_forceSourceOrYoung244
      hH3 hClass hDInt b hb x rho sigma margin epsilon
      hx hCofinal hRho hAspect hMargin hEps hExcess hPeak
      c hc hTerminalScale
  refine ⟨?_, thirdFullPhysical_outerTerminalSourceBudget_cofinal_zero244
    hH3 hClass hDInt b hb x hx hCofinal⟩
  filter_upwards [hChoice] with k hk
  dsimp only at hk ⊢
  rcases hk with hSource | ⟨s, hs, hDrop⟩
  · exact Or.inl hSource
  · right
    have hsT : s < T := by linarith only [hs.2, (hx k).2]
    have hOrder : rho k ≤ sigma k := by
      linarith only [hRho k, hAspect k]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_dynamicSlopeOrSignedYoung244
        hH3 hClass hDInt b hb (x k) (hx k) s hs.1.le hsT
        (rho k) (sigma k) (sigma k) (epsilon k)
        (hRho k).le hOrder le_rfl hDrop⟩

end
end PrimeTensor.FirstMonomialTriad
