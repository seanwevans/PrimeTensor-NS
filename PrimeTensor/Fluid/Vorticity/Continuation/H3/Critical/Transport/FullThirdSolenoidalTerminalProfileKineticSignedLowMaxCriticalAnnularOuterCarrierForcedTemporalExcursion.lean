import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierRateAmplification
import Mathlib.Tactic

/-!
# An unconditional two-snapshot terminal-rate obstruction for selected outer carriers

The physical selected-outer-carrier theorem already proves that an interval
on which a positive kinetic excess and nonnegative genuine Young-width deficit
persist pays a fixed physical H3 viscous price at every time.

Instead of assuming either observable has a temporal Lipschitz rate, we use
finite dissipation directly. If the remaining dissipation is too small to pay
the price over a specified right interval, a concrete later time MUST exhibit
one of two sizeable changes of the original observables. This produces
physical-time excursions without introducing a time derivative or uniform
modulus. A highpass drop forces a true physical L2 velocity-state increment.

At cofinal snapshots with m_k*sigma_k^6*(T-x_k) >= c > 0, the terminal
viscous tail tends to zero, so one of these changes necessarily occurs by
halfway to T, eventually in k. The result is an obstruction, not H3 closure:
we still have no scale-independent upper modulus controlling either change.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Without a *temporal-rate hypothesis*, insufficient actual terminal
viscosity forces the selected weighted kinetic mass or the exact nonlinear
annular deficit to lose a quantitative part of its snapshot margin. -/
theorem thirdFullPhysical_selectedOuterMargin_lowTail_forcesRightExcursion244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x : ℝ) (hx : x ∈ Set.Ioo b T)
    (rho sigma margin epsilon delta : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hd : 0 < delta) (hEnd : x + delta < T)
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
        delta * (119 * margin * sigma ^ 6 / 160)) :
    ∃ s : ℝ, s ∈ Set.Ioc x (x + delta) ∧
      (((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho >
            margin / 2 ∨
       thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma >
            epsilon) := by
  have hExists : ∃ s : ℝ, s ∈ Set.Icc x (x + delta) ∧
      (((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho >
            margin / 2 ∨
       thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma >
            epsilon) := by
    by_contra hNo
    have hWindow (s : ℝ) (hs : s ∈ Set.Icc x (x + delta)) :
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + margin / 2 ≤
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
        0 ≤ thirdFullPhysicalActualAnnularKineticDeficit244
          hH3 b s rho sigma := by
      have hMass :
          ((rho ^ 2 + sigma ^ 2) / 2) *
              thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
            ((rho ^ 2 + sigma ^ 2) / 2) *
              thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ≤
            margin / 2 := by
        apply le_of_not_gt
        intro hDrop
        exact hNo ⟨s, hs, Or.inl hDrop⟩
      have hDef :
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
            thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma ≤
          epsilon := by
        apply le_of_not_gt
        intro hDrop
        exact hNo ⟨s, hs, Or.inr hDrop⟩
      constructor
      · linarith only [hExcess, hMass]
      · linarith only [hPeak, hDef, hEps]
    have hCharge := thirdFullPhysical_selectedOuterMargin_integratedWindow244
      hH3 hClass hDInt b hb x hx rho sigma (margin / 2) delta
      hRho hAspect (div_pos hMargin (by norm_num : (0 : ℝ) < 2))
      hd hEnd hWindow
    have hSame :
        delta * (119 * (margin / 2) * sigma ^ 6 / 80) =
          delta * (119 * margin * sigma ^ 6 / 160) := by ring
    rw [hSame] at hCharge
    exact (not_lt_of_ge hCharge) hSmall
  obtain ⟨s, hs, hDrop⟩ := hExists
  have hsStrict : x < s := by
    rcases (lt_or_eq_of_le hs.1) with hlt | heq
    · exact hlt
    · subst s
      rcases hDrop with hMass | hDef
      · have hm : 0 < margin / 2 := by positivity
        simp only [sub_self] at hMass
        linarith only [hm, hMass]
      · simp only [sub_self] at hDef
        linarith only [hEps, hDef]
  exact ⟨s, ⟨hsStrict, hs.2⟩, hDrop⟩

/-- The canonical half-tail window makes the rate-free excursion cost
119/320 times the selected sixth-power margin-times-terminal-gap. -/
theorem thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesExcursion244
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
    ∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      (((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho >
            margin / 2 ∨
       thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma >
            epsilon) := by
  have hd : 0 < (T - x) / 2 := by linarith only [hx.2]
  have hEnd : x + (T - x) / 2 < T := by linarith only [hx.2]
  have hEquivalent :
      (T - x) / 2 * (119 * margin * sigma ^ 6 / 160) =
        119 * margin * sigma ^ 6 * (T - x) / 320 := by ring
  have hSmall' :
      (∫ r in x..T, velocityH3DissipationAt u r) <
        (T - x) / 2 * (119 * margin * sigma ^ 6 / 160) := by
    rw [hEquivalent]
    exact hSmall
  obtain ⟨s, hs, hDrop⟩ :=
    thirdFullPhysical_selectedOuterMargin_lowTail_forcesRightExcursion244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      ((T - x) / 2) hRho hAspect hMargin hEps hd hEnd
      hExcess hPeak hSmall'
  refine ⟨s, ?_, hDrop⟩
  have hMid : x + (T - x) / 2 = (x + T) / 2 := by ring
  simpa only [hMid] using hs

/-- The mass branch is a real quantitative increment of the original
physical three-component L2 velocity, not merely an abstract Fourier jump. -/
theorem thirdFullPhysical_selectedOuterMassDrop_forcesPhysicalL2Increment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (rho sigma margin x s : ℝ)
    (hDrop :
      ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho -
        ((rho ^ 2 + sigma ^ 2) / 2) *
          thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho >
        margin / 2) :
    margin < (rho ^ 2 + sigma ^ 2) *
      (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
          h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ *
       (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ +
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖)) := by
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let N : ℝ :=
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
      h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ *
    (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ +
     ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖)
  have hVariation : |Ms - Mx| ≤ N :=
    thirdFullPhysical_actualSharpHighMass_uniformTwoTime244 hH3 rho s x
  have hDifference : Mx - Ms ≤ N := by
    calc
      Mx - Ms ≤ |Mx - Ms| := le_abs_self _
      _ = |Ms - Mx| := abs_sub_comm _ _
      _ ≤ N := hVariation
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hScaled : a * (Mx - Ms) ≤ a * N :=
    mul_le_mul_of_nonneg_left hDifference ha
  have hDrop' : margin / 2 < a * (Mx - Ms) := by
    calc
      margin / 2 < a * Mx - a * Ms := hDrop
      _ = a * (Mx - Ms) := by ring
  have hHalf : margin / 2 < a * N := lt_of_lt_of_le hDrop' hScaled
  calc
    margin = 2 * (margin / 2) := by ring
    _ < 2 * (a * N) :=
      mul_lt_mul_of_pos_left hHalf (by norm_num : (0 : ℝ) < 2)
    _ = (rho ^ 2 + sigma ^ 2) *
      (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
          h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ *
       (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ +
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖)) := by
          dsimp only [a, N]
          ring

/-- Direct, rate-free actual-physical-time alternative: either a quantitative
L2 velocity increment or a loss of the *original* nonlinear Young-width
annular deficit, on a specified interval inside the terminal half-tail. -/
theorem thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesVelocityOrDeficit244
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
    ∃ s : ℝ, s ∈ Set.Ioc x ((x + T) / 2) ∧
      (margin < (rho ^ 2 + sigma ^ 2) *
        (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
            h3AuditInitialOldPhysicalHilbertTotal hH3 x‖ *
         (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ +
          ‖h3AuditInitialOldPhysicalHilbertTotal hH3 x‖)) ∨
       thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma >
            epsilon) := by
  obtain ⟨s, hs, hChange⟩ :=
    thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesExcursion244
      hH3 hClass hDInt b hb x hx rho sigma margin epsilon
      hRho hAspect hMargin hEps hExcess hPeak hSmall
  refine ⟨s, hs, ?_⟩
  rcases hChange with hMass | hDef
  · exact Or.inl
      (thirdFullPhysical_selectedOuterMassDrop_forcesPhysicalL2Increment244
        hH3 rho sigma margin x s hMass)
  · exact Or.inr hDef

/-- A strict drop of the exact ORIGINAL physical Young-width deficit forces
one of two concrete variations in its exact two-time Fourier polynomial:
kinetic mass times its slope, or genuine nonlinear Young-width action.
Neither channel is replaced by an abstract time derivative. -/
theorem thirdFullPhysical_selectedOuterDeficitDrop_massOrYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma epsilon : ℝ)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma) :
    let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    let w : ℝ := (rho ^ 2) ^ 3
    let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
      (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        rho (velocityH3Energy0At u b))
    let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
    let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
    let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
    epsilon / 2 < |Ms - Mx| *
      |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| ∨
    epsilon / 2 < Ms * |Ys - Yx| := by
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  have hAbs : epsilon <
      |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma| := by
    calc
      epsilon <
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
            thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma := hDrop
      _ ≤ |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma| :=
          le_abs_self _
      _ = |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma| :=
          abs_sub_comm _ _
  have hBound :
      |thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma| ≤
      |Ms - Mx| *
        |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| +
      Ms * |Ys - Yx| :=
    thirdFullPhysical_actualAnnularDeficit_twoTimeAbsBound244
      hH3 b s x rho sigma
  have hSum : epsilon <
      |Ms - Mx| *
        |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| +
      Ms * |Ys - Yx| := lt_of_lt_of_le hAbs hBound
  dsimp only
  by_cases hMass : epsilon / 2 <
      |Ms - Mx| *
        |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)|
  · exact Or.inl hMass
  · right
    have hMassLe :
        |Ms - Mx| *
            |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| ≤
          epsilon / 2 := le_of_not_gt hMass
    linarith only [hSum, hMassLe]

/-- The second (deficit) arm is itself a concrete physical-state
alternative: either old physical L2 highpass variation pays the *exact*
polynomial slope, or the original nonlinear Young-width term forces a
quantitative increment of the actual H3 spectral velocity state. -/
theorem thirdFullPhysical_selectedOuterDeficitDrop_forcesStateMovement244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b x s rho sigma epsilon : ℝ)
    (hRho : 0 < rho) (hAspect : 2 * rho ≤ sigma)
    (hDrop : epsilon <
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma -
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b s rho sigma) :
    let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
    let w : ℝ := (rho ^ 2) ^ 3
    let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
      (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
        rho (velocityH3Energy0At u b))
    let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
    let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
    let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
    let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
    let U := h3AuditActualSpectralVelocityTotal hH3 s
    let W := h3AuditActualSpectralVelocityTotal hH3 x
    let Vs := h3AuditInitialOldPhysicalHilbertTotal hH3 s
    let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
    epsilon / 2 <
      (‖Vs - Vx‖ * (‖Vs‖ + ‖Vx‖)) *
        |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| ∨
    epsilon / 2 <
      Ms * (thirdFullPhysicalAnnularFullYoungWidthModulus244 sigma U W *
        ‖U - W‖) := by
  let a : ℝ := (rho ^ 2 + sigma ^ 2) / 2
  let w : ℝ := (rho ^ 2) ^ 3
  let B : ℝ := Real.sqrt (velocityH3Energy0At u b) *
    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
      rho (velocityH3Energy0At u b))
  let P : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b a
  let Ms : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho
  let Mx : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho
  let Yx : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 x rho sigma
  let Ys : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma
  let U := h3AuditActualSpectralVelocityTotal hH3 s
  let W := h3AuditActualSpectralVelocityTotal hH3 x
  let Vs := h3AuditInitialOldPhysicalHilbertTotal hH3 s
  let Vx := h3AuditInitialOldPhysicalHilbertTotal hH3 x
  have hSplit := thirdFullPhysical_selectedOuterDeficitDrop_massOrYoung244
    hH3 b x s rho sigma epsilon hDrop
  have hMass : |Ms - Mx| ≤ ‖Vs - Vx‖ * (‖Vs‖ + ‖Vx‖) :=
    thirdFullPhysical_actualSharpHighMass_uniformTwoTime244 hH3 rho s x
  have hOrder : rho ≤ sigma := by linarith only [hRho, hAspect]
  have hYoung : |Ys - Yx| ≤
      thirdFullPhysicalAnnularFullYoungWidthModulus244 sigma U W *
        ‖U - W‖ :=
    thirdFullPhysical_actualAnnularYoungWidth_uniformTwoTime244
      hH3 rho sigma sigma s x hRho.le hOrder (le_refl sigma)
  change
    epsilon / 2 <
      (‖Vs - Vx‖ * (‖Vs‖ + ‖Vx‖)) *
        |w * a * (a * (Ms + Mx) - 2 * B) - (Yx + w * P)| ∨
    epsilon / 2 <
      Ms * (thirdFullPhysicalAnnularFullYoungWidthModulus244 sigma U W *
        ‖U - W‖)
  rcases hSplit with hMassPrice | hYoungPrice
  · left
    exact lt_of_lt_of_le hMassPrice
      (mul_le_mul_of_nonneg_right hMass (abs_nonneg _))
  · right
    exact lt_of_lt_of_le hYoungPrice
      (mul_le_mul_of_nonneg_left hYoung (sq_nonneg _))

/-- Cofinal selected snapshots with a noncollapsing sixth-power terminal
scale automatically generate real physical L2 motion or nonlinear
Young-width deficit loss on the right terminal half interval.
No Lipschitz-rate premise from the previous module is used here. -/
theorem thirdFullPhysical_cofinalSelectedOuterMargins_forceVelocityOrDeficit244
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
    ∀ᶠ k : ℕ in atTop,
      ∃ s : ℝ, s ∈ Set.Ioc (x k) ((x k + T) / 2) ∧
        (margin k < ((rho k ^ 2 + sigma k ^ 2)) *
          (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
              h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)‖ *
           (‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ +
            ‖h3AuditInitialOldPhysicalHilbertTotal hH3 (x k)‖)) ∨
         thirdFullPhysicalActualAnnularKineticDeficit244
             hH3 b (x k) (rho k) (sigma k) -
           thirdFullPhysicalActualAnnularKineticDeficit244
             hH3 b s (rho k) (sigma k) > epsilon k) := by
  let V : ℕ → ℝ := fun k =>
    ∫ r in x k..T, velocityH3DissipationAt u r
  have hTail : Tendsto V atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt x hCofinal
      (Filter.Eventually.of_forall (fun k =>
        ⟨le_of_lt (lt_trans hb.1 (hx k).1), (hx k).2.le⟩))
  have hSmallTime : ∀ᶠ k : ℕ in atTop, V k < 119 * c / 320 :=
    hTail.eventually
      (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < 119 * c / 320))
  filter_upwards [hTerminalScale, hSmallTime] with k hFloor hSmall
  have hScaled : (119 / 320 : ℝ) * c ≤
      (119 / 320 : ℝ) * (margin k * sigma k ^ 6 * (T - x k)) :=
    mul_le_mul_of_nonneg_left hFloor (by norm_num)
  have hShort : V k <
      119 * margin k * sigma k ^ 6 * (T - x k) / 320 := by
    calc
      V k < (119 / 320 : ℝ) * c := by
        convert hSmall using 1 <;> ring
      _ ≤ (119 / 320 : ℝ) * (margin k * sigma k ^ 6 * (T - x k)) := hScaled
      _ = 119 * margin k * sigma k ^ 6 * (T - x k) / 320 := by ring
  exact thirdFullPhysical_selectedOuterMargin_lowHalfTail_forcesVelocityOrDeficit244
    hH3 hClass hDInt b hb (x k) (hx k)
    (rho k) (sigma k) (margin k) (epsilon k)
    (hRho k) (hAspect k) (hMargin k) (hEps k)
    (hExcess k) (hPeak k) hShort

end
end PrimeTensor.FirstMonomialTriad
