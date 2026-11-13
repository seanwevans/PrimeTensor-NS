import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierSourceTailYoungObstruction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularDeficitTwoTimeLedger
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularUniformYoungWidthWindow
import Mathlib.Tactic

/-!
# The signed nonlinear Young-width gain forced by physical source-tail rigidity

The original selected outer carrier can lose its positive annular deficit
before the terminal midpoint. The exact two-time identity resolves this loss
into the true sharp highpass mass drift times its physical polynomial slope,
PLUS the *signed increase* of the ORIGINAL cubic Young-width cost. The
unconditional physical momentum FTC pays the first term using only the
kinetic anchor, remaining time and actual H3 dissipation.

No time derivative of the Young functional, no new upper source derivative,
and no uniform radial modulus is assumed. The remaining alternatives are
(1) a frequency-weighted physical source payment; (2) a source payment
amplified by the exact annular polynomial slope; (3) a strictly positive
signed increase of the genuine nonlinear Young-width cost.

The unweighted projected-source tail vanishes cofinally, but its frequency
and polynomial multipliers need not vanish. No Navier--Stokes continuation
or contradiction with finite H3 dissipation follows from this theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The actual projected-source tail's kinetic-plus-viscous upper bound. -/
noncomputable def thirdFullPhysicalOuterTerminalSourceBudget244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b x T : ℝ) : ℝ :=
  (3 + h3AuditInitialLerayEnergyCoefficient) *
    ((1 + 6 * velocityH3Energy0At u b) * (T - x) +
      3 * (∫ r in x..T, velocityH3DissipationAt u r))

/-- Exact selected two-snapshot coefficient multiplying the physical sharp
highpass kinetic-mass difference in the original annular deficit identity.
It includes the original nonlinear Young-width cost at the LATER time. -/
noncomputable def thirdFullPhysicalOuterDeficitTimeSlope244
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
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  w * a * (a * (Mx + Ms) - 2 * B) - (Ys + w * P)

/-- Pure algebra: a positive deficit loss and a bounded mass excursion force
an exact slope payment or SIGNED Young-width increase, not merely an
absolute-value oscillation of the nonlinear functional. -/
theorem thirdFullKinetic_deficitDrop_forces_signedYoungGain244
    (epsilon m n L A yx ys : ℝ)
    (hMass : |m - n| ≤ A)
    (hDrop : epsilon < (m - n) * L + m * (ys - yx)) :
    epsilon / 2 < A * |L| ∨
      epsilon / 2 < m * (ys - yx) := by
  have hSlope : (m - n) * L ≤ A * |L| := by
    calc
      (m - n) * L ≤ |(m - n) * L| := le_abs_self _
      _ = |m - n| * |L| := abs_mul _ _
      _ ≤ A * |L| := mul_le_mul_of_nonneg_right hMass (abs_nonneg L)
  by_cases hRate : epsilon / 2 < A * |L|
  · exact Or.inl hRate
  · right
    have hRateLe : A * |L| ≤ epsilon / 2 := le_of_not_gt hRate
    linarith only [hDrop, hSlope, hRateLe]

/-- The actual physical two-time annular deficit drop pays either the
source-tail transport cost times the EXACT polynomial slope, or the
POSITIVE signed growth of the original nonlinear Young-width functional.
The source budget is obtained from the Navier--Stokes momentum FTC. -/
theorem thirdFullPhysical_outerDeficitDrop_sourceSlopeOrSignedYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (s : ℝ) (hxs : x ≤ s) (hsT : s < T)
    (rho sigma epsilon : ℝ)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma) :
    let H : ℝ := thirdFullPhysicalOuterTerminalSourceBudget244 u b x T
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
    let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    epsilon / 2 < H * (2 * ‖Vx‖ + H) *
        |thirdFullPhysicalOuterDeficitTimeSlope244 hH3 b x s rho sigma| ∨
      epsilon / 2 < Mx * (Ys - Yx) := by
  let S : ℝ := ∫ r in x..T,
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖
  let H : ℝ := thirdFullPhysicalOuterTerminalSourceBudget244 u b x T
  let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  let Vs := h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  let Q : ℝ := thirdFullPhysicalOuterDeficitTimeSlope244 hH3 b x s rho sigma
  have hIncrement : ‖Vs - Vx‖ ≤ S :=
    thirdFullPhysical_outerSourceTail_controlsVelocityIncrement244
      hH3 hClass hDInt b hb x hx s hxs hsT
  have hSH : S ≤ H := by
    dsimp only [S, H, thirdFullPhysicalOuterTerminalSourceBudget244]
    exact thirdFullPhysical_outerSourceTail_le_kineticViscousBudget244
      hH3 hClass hDInt b hb x hx
  have hS : 0 ≤ S := by
    have hZero := thirdFullPhysical_outerSourceTail_controlsVelocityIncrement244
      hH3 hClass hDInt b hb x hx x (le_refl x) hx.2
    simpa only [sub_self, norm_zero] using hZero
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
  have hHighpass : |Mx - Ms| ≤
      ‖Vs - Vx‖ * (‖Vs‖ + ‖Vx‖) := by
    have hTwoTime := thirdFullPhysical_actualSharpHighMass_uniformTwoTime244
      hH3 rho s x
    calc
      |Mx - Ms| = |Ms - Mx| := abs_sub_comm _ _
      _ ≤ ‖Vs - Vx‖ * (‖Vs‖ + ‖Vx‖) := hTwoTime
  have hMass : |Mx - Ms| ≤ H * (2 * ‖Vx‖ + H) :=
    (hHighpass.trans hQuadratic).trans hHQuadratic
  have hIdentity :
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma =
          (Mx - Ms) * Q + Mx * (Ys - Yx) := by
    have hExact := thirdFullPhysical_actualAnnularDeficit_twoTimeIdentity244
      hH3 b x s rho sigma
    change
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma =
          (Mx - Ms) * Q - Mx * (Yx - Ys) at hExact
    calc
      _ = (Mx - Ms) * Q - Mx * (Yx - Ys) := hExact
      _ = (Mx - Ms) * Q + Mx * (Ys - Yx) := by ring
  have hSigned : epsilon < (Mx - Ms) * Q + Mx * (Ys - Yx) := by
    rw [hIdentity] at hDrop
    exact hDrop
  change epsilon / 2 < H * (2 * ‖Vx‖ + H) * |Q| ∨
    epsilon / 2 < Mx * (Ys - Yx)
  exact thirdFullKinetic_deficitDrop_forces_signedYoungGain244
    epsilon Mx Ms Q (H * (2 * ‖Vx‖ + H)) Yx Ys hMass hSigned

/-- The physical half-tail selected carrier has THREE precisely separated
alternatives: direct PDE source transport; source transport multiplied by
its exact annular deficit slope; or POSITIVE original Young-width growth.
No abstract temporal Lipschitz bound is used. -/
theorem thirdFullPhysical_selectedOuter_lowHalfTail_sourceSlopeOrSignedYoung244
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
    let H : ℝ := thirdFullPhysicalOuterTerminalSourceBudget244 u b x T
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
    let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    (margin < (rho ^ 2 + sigma ^ 2) *
      (H * (2 * ‖Vx‖ + H))) ∨
    (∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      (epsilon / 2 < H * (2 * ‖Vx‖ + H) *
          |thirdFullPhysicalOuterDeficitTimeSlope244 hH3 b x s rho sigma| ∨
       epsilon / 2 < Mx *
          (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
            Yx))) := by
  have hBase := thirdFullPhysical_selectedOuter_lowHalfTail_forcesViscousSourceOrYoung244
    hH3 hClass hDInt b hb x hx rho sigma margin epsilon
    hRho hAspect hMargin hEps hExcess hPeak hSmall
  change
    (margin < (rho ^ 2 + sigma ^ 2) *
      (thirdFullPhysicalOuterTerminalSourceBudget244 u b x T *
        (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ +
          thirdFullPhysicalOuterTerminalSourceBudget244 u b x T))) ∨
    (∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      (epsilon / 2 < thirdFullPhysicalOuterTerminalSourceBudget244 u b x T *
          (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ +
            thirdFullPhysicalOuterTerminalSourceBudget244 u b x T) *
          |thirdFullPhysicalOuterDeficitTimeSlope244 hH3 b x s rho sigma| ∨
       epsilon / 2 <
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho *
          (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
            thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma)))
  dsimp only at hBase
  rcases hBase with hSource | ⟨s, hs, hDeficit⟩
  · exact Or.inl hSource
  · right
    have hsT : s < T := by
      linarith only [hs.2, hx.2]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_sourceSlopeOrSignedYoung244
        hH3 hClass hDInt b hb x hx s hs.1.le hsT
        rho sigma epsilon hDeficit⟩

/-- If the actual projected-source payment is too small to explain the
kinetic excess AND its mass drift times the exact annular slope is too small
to explain the observed deficit loss, a later half-tail time necessarily
exhibits a strictly positive signed increase in the original nonlinear
Young-width cost. These are quantitative physical-PDE tests, not assumed
derivative estimates or a claim that they hold automatically. -/
theorem thirdFullPhysical_selectedOuter_sourceSlopeSmall_forcesSignedYoungGrowth244
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
        (thirdFullPhysicalOuterTerminalSourceBudget244 u b x T *
          (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ +
            thirdFullPhysicalOuterTerminalSourceBudget244 u b x T)) ≤ margin)
    (hSlopeSmall : ∀ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) →
      thirdFullPhysicalOuterTerminalSourceBudget244 u b x T *
        (2 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ +
          thirdFullPhysicalOuterTerminalSourceBudget244 u b x T) *
        |thirdFullPhysicalOuterDeficitTimeSlope244 hH3 b x s rho sigma| ≤
          epsilon / 2) :
    ∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      epsilon / 2 <
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho *
          (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
            thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma) := by
  have hGate := thirdFullPhysical_selectedOuter_lowHalfTail_sourceSlopeOrSignedYoung244
    hH3 hClass hDInt b hb x hx rho sigma margin epsilon
    hRho hAspect hMargin hEps hExcess hPeak hSmall
  dsimp only at hGate
  rcases hGate with hSource | ⟨s, hs, hAlt⟩
  · exact False.elim ((not_lt_of_ge hSourceSmall) hSource)
  · rcases hAlt with hSlope | hYoung
    · exact False.elim ((not_lt_of_ge (hSlopeSmall s hs)) hSlope)
    · exact ⟨s, hs, hYoung⟩

/-- Cofinal version: under a noncollapsing sixth-power terminal-scale floor,
finite H3 dissipation eventually forces direct source transport, amplified
polynomial-slope transport, or signed original Young-width growth. The
UNWEIGHTED projected source action still tends to zero, without any claim
that its moving-frequency multipliers do. -/
theorem thirdFullPhysical_cofinalSelectedOuterMargins_sourceSlopeOrSignedYoung244
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
      let H : ℝ := thirdFullPhysicalOuterTerminalSourceBudget244 u b (x k) T
      let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)
      let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) (rho k)
      let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 (x k) (rho k) (sigma k)
      (margin k < (rho k ^ 2 + sigma k ^ 2) *
        (H * (2 * ‖Vx‖ + H))) ∨
      (∃ s : ℝ, s ∈ Set.Ioc (x k) ((x k + T) / 2) ∧
        (epsilon k / 2 < H * (2 * ‖Vx‖ + H) *
            |thirdFullPhysicalOuterDeficitTimeSlope244 hH3 b (x k) s (rho k) (sigma k)| ∨
         epsilon k / 2 < Mx *
           (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s (rho k) (sigma k) -
             Yx)))) ∧
    Tendsto (fun k : ℕ =>
      ∫ r in x k..T, ‖h3PathActualProjectedMomentumSource244 hH3 r‖)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨hChoice, hSourceTail⟩ :=
    thirdFullPhysical_cofinalSelectedOuterMargins_forceSourceOrYoung244
      hH3 hClass hDInt b hb x rho sigma margin epsilon
      hx hCofinal hRho hAspect hMargin hEps hExcess hPeak
      c hc hTerminalScale
  refine ⟨?_, hSourceTail⟩
  filter_upwards [hChoice] with k hk
  dsimp only at hk ⊢
  rcases hk with hSource | ⟨s, hs, hDeficit⟩
  · exact Or.inl hSource
  · right
    have hsT : s < T := by
      linarith only [hs.2, (hx k).2]
    exact ⟨s, hs,
      thirdFullPhysical_outerDeficitDrop_sourceSlopeOrSignedYoung244
        hH3 hClass hDInt b hb (x k) (hx k) s hs.1.le hsT
        (rho k) (sigma k) (epsilon k) hDeficit⟩

end
end PrimeTensor.FirstMonomialTriad
