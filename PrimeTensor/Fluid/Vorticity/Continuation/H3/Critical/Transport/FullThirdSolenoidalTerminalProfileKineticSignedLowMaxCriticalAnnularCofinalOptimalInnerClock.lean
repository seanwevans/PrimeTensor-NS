import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalUniformClockExtraction
import Mathlib.Tactic

/-!
# Cofinal annular viscous clocks: optimal inner radius and terminal-tail compression

The self-calibrated clock normalization is `max 1 (E rho^6 slope(epsilon))`.
It is monotone in the nonnegative INNER annular radius, independently of
outer radius sigma and of the varying family ceiling R. Thus a common
finite-radius deficit window pays its strongest available viscous floor at
the family's smallest allowed inner radius.

Applying this to the accepted cofinal disjoint-window extraction removes
an arbitrary selected annulus and yields both summability of the optimized
inner clock and an index-by-index upper bound by the *actual terminal tail*
physical H3 dissipation integral. No noncompression or snapshot-margin
premise is derived from the PDE here. In particular no global H3 regularity
claim follows from a vanishing product of width and clock height.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The original cap-linearized viscous coefficient is nonnegative whenever
its cap is nonnegative. Both factors arise from actual kinetic energy. -/
theorem thirdFullPhysical_outerViscousCapSlope_nonneg244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b H : ℝ) (hH : 0 ≤ H) :
    0 ≤ thirdFullPhysicalOuterViscousCapSlope244 u b H := by
  unfold thirdFullPhysicalOuterViscousCapSlope244
  have hEnergy : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hCoefficient : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    linarith only [h3AuditInitialLerayEnergyCoefficient_nonneg]
  positivity

/-- At a fixed positive cap, the EXACT physical clock normalizer is
monotone in its nonnegative inner radius. Its outer radius does not enter. -/
theorem thirdFullPhysical_annularCapClockFactor_mono_inner244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b H rho sigma : ℝ) (hH : 0 ≤ H)
    (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) :
    thirdFullPhysicalAnnularCapClockFactor244 u b rho H ≤
      thirdFullPhysicalAnnularCapClockFactor244 u b sigma H := by
  have hEnergy : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hSlope : 0 ≤ thirdFullPhysicalOuterViscousCapSlope244 u b H :=
    thirdFullPhysical_outerViscousCapSlope_nonneg244 u b H hH
  have hRadialSquare : rho ^ 2 ≤ sigma ^ 2 :=
    pow_le_pow_left₀ hRho hOrder 2
  have hRadialSix : (rho ^ 2) ^ 3 ≤ (sigma ^ 2) ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg rho) hRadialSquare 3
  have hProduct :
      velocityH3Energy0At u b * (rho ^ 2) ^ 3 *
          thirdFullPhysicalOuterViscousCapSlope244 u b H ≤
        velocityH3Energy0At u b * (sigma ^ 2) ^ 3 *
          thirdFullPhysicalOuterViscousCapSlope244 u b H := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRadialSix hEnergy) hSlope
  unfold thirdFullPhysicalAnnularCapClockFactor244
  exact max_le_max_left 1 hProduct

/-- Radius monotonicity reverses for the positive self-calibrated viscous
height: the smallest admissible inner annulus supplies the strongest floor. -/
theorem thirdFullPhysical_annularClockHeight_antitone_inner244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b epsilon rho sigma : ℝ) (hEps : 0 < epsilon)
    (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma) :
    epsilon / thirdFullPhysicalAnnularCapClockFactor244 u b sigma epsilon ≤
      epsilon / thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon := by
  have hPos : 0 < thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon :=
    thirdFullPhysical_annularCapClockFactor_pos244 u b rho epsilon
  exact div_le_div_of_nonneg_left hEps.le hPos
    (thirdFullPhysical_annularCapClockFactor_mono_inner244
      u b epsilon rho sigma hEps.le hRho hOrder)

/-- Generic terminal-tail charge: a physical height maintained on one right
window must be paid by the *remaining* integrable nonnegative dissipation,
not merely by the global terminal budget. -/
theorem thirdFull_scalar_rightWindowHeight_le_terminalTail244
    (D : ℝ → ℝ) (a T x delta height : ℝ)
    (haT : a < T) (ha : a ≤ x) (hx : x < T)
    (hDelta : 0 < delta) (hEnd : x + delta ≤ T)
    (hDInt : IntervalIntegrable D volume a T)
    (hDNonneg : ∀ r : ℝ, 0 ≤ D r)
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc x (x + delta) → height ≤ D s) :
    delta * height ≤ ∫ r in x..T, D r := by
  have hDWin : IntervalIntegrable D volume x (x + delta) := by
    apply hDInt.mono_set
    intro r hr
    have hrWin : r ∈ Set.Icc x (x + delta) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hDelta.le)] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨ha.trans hrWin.1, hrWin.2.trans hEnd⟩
    simpa only [Set.uIcc_of_le haT.le] using hrAll
  have hDTail : IntervalIntegrable D volume x T := by
    apply hDInt.mono_set
    intro r hr
    have hrTail : r ∈ Set.Icc x T := by
      simpa only [Set.uIcc_of_le hx.le] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨ha.trans hrTail.1, hrTail.2⟩
    simpa only [Set.uIcc_of_le haT.le] using hrAll
  have hNonnegAE : 0 ≤ᵐ[volume.restrict (Set.Ioc x T)] D :=
    Filter.Eventually.of_forall hDNonneg
  have hLocal := h3Path_localPositiveHeight_forces_integratedCost244
    D x (x + delta) height (by linarith only [hDelta]) hDWin hFloor
  have hMono : (∫ r in x..(x + delta), D r) ≤ ∫ r in x..T, D r :=
    intervalIntegral.integral_mono_interval
      le_rfl (le_add_of_nonneg_right hDelta.le) hEnd hNonnegAE hDTail
  calc
    delta * height = ((x + delta) - x) * height := by ring
    _ ≤ ∫ r in x..(x + delta), D r := hLocal
    _ ≤ ∫ r in x..T, D r := hMono

/-- An exact positive self-calibrated height converts the genuine
terminal-tail budget into a quantitative upper bound for the window width.
No positive lower bound on this width is inferred. -/
theorem thirdFull_scalar_tailCost_forces_widthCompression244
    (delta epsilon C tail : ℝ) (hEps : 0 < epsilon) (hC : 0 < C)
    (hCost : delta * (epsilon / C) ≤ tail) :
    delta ≤ tail / (epsilon / C) := by
  exact (le_div_iff₀ (div_pos hEps hC)).mpr hCost

/-- The common finite-radius physical interval supplies a stronger floor
at the family's minimal radius than at any other annulus. The same floor
holds for every time in one interval selected by the ORIGINAL PDE theorem. -/
theorem thirdFullPhysical_actualAnnularDeficit_optimalInnerClockRightWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (radiusMin R x margin epsilon : ℝ)
    (hRadiusMin : 0 < radiusMin) (hRadiusMax : radiusMin ≤ R)
    (hx : x ∈ Set.Ioo b T)
    (hMargin : 0 < margin) (hEps : 0 < epsilon)
    (hExcess : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + 2 * margin ≤
          ((rho ^ 2 + sigma ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 x rho)
    (hPeak : ∀ rho sigma : ℝ,
      radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        2 * epsilon ≤
          thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b x rho sigma) :
    ∃ delta : ℝ, 0 < delta ∧ x + delta < T ∧
      (∀ s : ℝ, s ∈ Set.Icc x (x + delta) →
        epsilon / thirdFullPhysicalAnnularCapClockFactor244
          u b radiusMin epsilon ≤ velocityH3DissipationAt u s) ∧
      (∀ rho sigma : ℝ,
        radiusMin ≤ rho → rho ≤ sigma → sigma ≤ R →
        epsilon / thirdFullPhysicalAnnularCapClockFactor244 u b rho epsilon ≤
          epsilon / thirdFullPhysicalAnnularCapClockFactor244
            u b radiusMin epsilon) := by
  obtain ⟨delta, hd, hEnd, hWindow⟩ :=
    thirdFullPhysical_actualAnnularDeficit_uniformViscousRightWindow244
      hH3 hClass b hb radiusMin R x margin epsilon
      hRadiusMin hRadiusMax hx hMargin hEps hExcess hPeak
  refine ⟨delta, hd, hEnd, ?_, ?_⟩
  · intro s hs
    exact hWindow s hs radiusMin radiusMin le_rfl le_rfl hRadiusMax
  · intro rho sigma hRad hOrder hUpper
    exact thirdFullPhysical_annularClockHeight_antitone_inner244
      u b epsilon radiusMin rho hEps hRadiusMin.le hRad

/-- The accepted cofinal extraction can always choose the MINIMAL inner
radius at each index. This yields summability of the strongest normalized
clock in the whole bounded annular family, and an individual terminal-tail
bound for each such clock. Neither requires a cutoff-independent modulus. -/
theorem thirdFullPhysical_cofinalAnnularUniformSnapshots_optimalInnerClocks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x radiusMin R margin epsilon : ℕ → ℝ)
    (hx : ∀ k : ℕ, x k ∈ Set.Ioo b T)
    (hStep : ∀ k : ℕ, x k < x (k + 1))
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hRadiusMin : ∀ k : ℕ, 0 < radiusMin k)
    (hRadiusMax : ∀ k : ℕ, radiusMin k ≤ R k)
    (hMargin : ∀ k : ℕ, 0 < margin k)
    (hEps : ∀ k : ℕ, 0 < epsilon k)
    (hExcess : ∀ k : ℕ, ∀ rho sigma : ℝ,
      radiusMin k ≤ rho → rho ≤ sigma → sigma ≤ R k →
        Real.sqrt (velocityH3Energy0At u b) *
          (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
            rho (velocityH3Energy0At u b)) + 2 * margin k ≤
          ((rho ^ 2 + sigma ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 (x k) rho)
    (hPeak : ∀ k : ℕ, ∀ rho sigma : ℝ,
      radiusMin k ≤ rho → rho ≤ sigma → sigma ≤ R k →
        2 * epsilon k ≤
          thirdFullPhysicalActualAnnularKineticDeficit244
            hH3 b (x k) rho sigma) :
    ∃ delta : ℕ → ℝ,
      (∀ k : ℕ,
        0 < delta k ∧ x k + delta k < x (k + 1) ∧
          x k + delta k < T ∧
          ∀ s : ℝ, s ∈ Set.Icc (x k) (x k + delta k) →
            ∀ rho sigma : ℝ,
              radiusMin k ≤ rho → rho ≤ sigma → sigma ≤ R k →
                Real.sqrt (velocityH3Energy0At u b) *
                    (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
                      rho (velocityH3Energy0At u b)) + margin k ≤
                  ((rho ^ 2 + sigma ^ 2) / 2) *
                    thirdFullPhysicalActualSharpKineticHighMass244 hH3 s rho ∧
                epsilon k ≤
                  thirdFullPhysicalActualAnnularKineticDeficit244
                    hH3 b s rho sigma) ∧
      (∀ k : ℕ, delta k *
        (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (radiusMin k) (epsilon k)) ≤
        ∫ r in x k..T, velocityH3DissipationAt u r) ∧
      (∀ k : ℕ, delta k ≤
        (∫ r in x k..T, velocityH3DissipationAt u r) /
          (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
            u b (radiusMin k) (epsilon k))) ∧
      Summable (fun k : ℕ => delta k *
        (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (radiusMin k) (epsilon k))) ∧
      Tendsto (fun k : ℕ => delta k *
        (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (radiusMin k) (epsilon k))) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m, delta k *
          (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
            u b (radiusMin k) (epsilon k))) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in x k..(x k + delta k),
          velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) ∧
      (∀ k : ℕ, ∀ rho : ℝ, radiusMin k ≤ rho →
        epsilon k / thirdFullPhysicalAnnularCapClockFactor244 u b rho (epsilon k) ≤
          epsilon k / thirdFullPhysicalAnnularCapClockFactor244
            u b (radiusMin k) (epsilon k)) := by
  have hSelected (k : ℕ) :
      radiusMin k ≤ radiusMin k ∧
      radiusMin k ≤ radiusMin k ∧ radiusMin k ≤ R k :=
    ⟨le_rfl, le_rfl, hRadiusMax k⟩
  obtain ⟨delta, hWin, hSum, hZero, hFinite, hActualTail⟩ :=
    thirdFullPhysical_cofinalAnnularUniformSnapshots_disjointSummable244
      hH3 hClass hDInt b hb x radiusMin R margin epsilon
      radiusMin radiusMin hx hStep hCofinal
      hRadiusMin hRadiusMax hMargin hEps hSelected hExcess hPeak
  have hTailBound (k : ℕ) :
      delta k * (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (radiusMin k) (epsilon k)) ≤
      ∫ r in x k..T, velocityH3DissipationAt u r := by
    have hFloor (s : ℝ) (hs : s ∈ Set.Icc (x k) (x k + delta k)) :
        epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (radiusMin k) (epsilon k) ≤
        velocityH3DissipationAt u s := by
      have hBoth := (hWin k).2.2.2 s hs
        (radiusMin k) (radiusMin k) le_rfl le_rfl (hRadiusMax k)
      have hExcessS :
          Real.sqrt (velocityH3Energy0At u b) *
            (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
              (radiusMin k) (velocityH3Energy0At u b)) ≤
          ((radiusMin k ^ 2 + radiusMin k ^ 2) / 2) *
            thirdFullPhysicalActualSharpKineticHighMass244 hH3 s (radiusMin k) := by
        linarith only [hBoth.1, hMargin k]
      have hsTime : s ∈ Set.Ioo b T :=
        ⟨lt_of_lt_of_le (hx k).1 hs.1,
          lt_of_le_of_lt hs.2 (hWin k).2.2.1⟩
      exact thirdFullPhysical_annularDeficit_forces_selfCalibratedClock244
        hH3 hClass b hb (radiusMin k) (radiusMin k)
        (hRadiusMin k).le le_rfl s hsTime (epsilon k) (hEps k)
        hExcessS hBoth.2
    have hStart : a ≤ x k :=
      (lt_trans hb.1 (hx k).1).le
    exact thirdFull_scalar_rightWindowHeight_le_terminalTail244
      (velocityH3DissipationAt u) a T (x k) (delta k)
      (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (radiusMin k) (epsilon k))
      hClass.terminal_start.2 hStart (hx k).2 (hWin k).1
      (hWin k).2.2.1.le hDInt (velocityH3DissipationAt_nonneg u) hFloor
  have hWidthBound (k : ℕ) :
      delta k ≤
        (∫ r in x k..T, velocityH3DissipationAt u r) /
          (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
            u b (radiusMin k) (epsilon k)) := by
    exact thirdFull_scalar_tailCost_forces_widthCompression244
      (delta k) (epsilon k)
      (thirdFullPhysicalAnnularCapClockFactor244 u b (radiusMin k) (epsilon k))
      (∫ r in x k..T, velocityH3DissipationAt u r)
      (hEps k)
      (thirdFullPhysical_annularCapClockFactor_pos244
        u b (radiusMin k) (epsilon k)) (hTailBound k)
  refine ⟨delta, hWin, hTailBound, hWidthBound,
    hSum, hZero, hFinite, hActualTail, ?_⟩
  intro k rho hRad
  exact thirdFullPhysical_annularClockHeight_antitone_inner244
    u b (epsilon k) (radiusMin k) rho (hEps k)
    (hRadiusMin k).le hRad

end
end PrimeTensor.FirstMonomialTriad
