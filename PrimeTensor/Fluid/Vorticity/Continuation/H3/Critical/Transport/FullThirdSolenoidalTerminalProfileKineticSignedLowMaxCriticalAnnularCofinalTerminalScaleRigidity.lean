import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalOptimalInnerClock
import Mathlib.Tactic

/-!
# Terminal-scale rigidity of genuine cofinal physical annular viscous clocks

The preceding kernel theorem constructs disjoint actual H3-viscous windows
and charges their optimal inner-radius heights to the remaining physical
viscous dissipation integral. Its width-times-height conclusion alone does
not identify which factor collapses near the terminal time.

Here we normalize BOTH factors against the physical terminal horizon
  tau(k) = T - x(k) > 0.
The exact product (delta/tau) * (tau*height) is delta*height, so it is
bounded above by the actual vanishing L1 terminal tail. This yields an
unconditional square-root bottleneck, and two sharp conditional consequences:
  (i)  a critical or supercritical inverse-terminal-time viscous height
       forces delta/(T-x) -> 0;
  (ii) a noncompressing relative window forces (T-x)*height -> 0.

No persistence width, noncompression, or snapshot margin is derived from
Navier--Stokes; the actual charged windows are supplied by the preceding
finite-radius/cofinal snapshot theorem. Neither arm alone proves H3 continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The terminal-normalized clock product is exactly its physical
width-times-height charge. -/
theorem thirdFull_scalar_terminalNormalizedClock_product244
    (T x delta height : ℝ) (hx : x < T) :
    (delta / (T - x)) * ((T - x) * height) = delta * height := by
  have hGap : 0 < T - x := sub_pos.mpr hx
  calc
    (delta / (T - x)) * ((T - x) * height) =
        ((delta / (T - x)) * (T - x)) * height := by ring
    _ = delta * height := by rw [div_mul_cancel₀ _ hGap.ne']

/-- The smaller of the two terminal-scaled clocks is always at most the
square root of the actual remaining dissipative payment. This does not
require either factor to have an independent positive lower bound. -/
theorem thirdFull_scalar_terminalNormalizedClock_min_le_sqrt244
    (T x delta height tail : ℝ) (hx : x < T)
    (hDelta : 0 ≤ delta) (hHeight : 0 ≤ height)
    (hCost : delta * height ≤ tail) :
    min (delta / (T - x)) ((T - x) * height) ≤ Real.sqrt tail := by
  let q : ℝ := delta / (T - x)
  let z : ℝ := (T - x) * height
  have hGap : 0 ≤ T - x := (sub_pos.mpr hx).le
  have hq : 0 ≤ q := div_nonneg hDelta hGap
  have hz : 0 ≤ z := mul_nonneg hGap hHeight
  have hmin : 0 ≤ min q z := le_min hq hz
  have hProduct : q * z ≤ tail := by
    change (delta / (T - x)) * ((T - x) * height) ≤ tail
    rw [thirdFull_scalar_terminalNormalizedClock_product244 T x delta height hx]
    exact hCost
  have hSquare : (min q z) ^ 2 ≤ tail := by
    calc
      (min q z) ^ 2 = min q z * min q z := by ring
      _ ≤ q * min q z := mul_le_mul_of_nonneg_right (min_le_left _ _) hmin
      _ ≤ q * z := mul_le_mul_of_nonneg_left (min_le_right _ _) hq
      _ ≤ tail := hProduct
  exact Real.le_sqrt_of_sq_le hSquare

/-- At a critical inverse-time height, finite actual tail payment forces
relative width compression. This is stronger than delta -> 0. -/
theorem thirdFull_scalar_terminalCriticalHeight_relativeWidth_tendsto_zero244
    (T c : ℝ) (x delta height tail : ℕ → ℝ)
    (hc : 0 < c) (hx : ∀ k, x k < T)
    (hDelta : ∀ k, 0 ≤ delta k)
    (hTail : Tendsto tail atTop (𝓝 (0 : ℝ)))
    (hCharge : ∀ k, delta k * height k ≤ tail k)
    (hCritical : ∀ k, c ≤ (T - x k) * height k) :
    Tendsto (fun k => delta k / (T - x k)) atTop (𝓝 (0 : ℝ)) := by
  have hLower (k : ℕ) : 0 ≤ delta k / (T - x k) :=
    div_nonneg (hDelta k) (sub_pos.mpr (hx k)).le
  have hUpper (k : ℕ) : delta k / (T - x k) ≤ tail k / c := by
    have hProduct := thirdFull_scalar_terminalNormalizedClock_product244
      T (x k) (delta k) (height k) (hx k)
    have hScaled :
        (delta k / (T - x k)) * c ≤ delta k * height k := by
      calc
        (delta k / (T - x k)) * c ≤
          (delta k / (T - x k)) * ((T - x k) * height k) :=
          mul_le_mul_of_nonneg_left (hCritical k) (hLower k)
        _ = delta k * height k := hProduct
    exact (le_div_iff₀ hc).2 (hScaled.trans (hCharge k))
  have hTailRatio :
      Tendsto (fun k => tail k / c) atTop (𝓝 (0 : ℝ)) := by
    simpa using hTail.div_const c
  exact squeeze_zero'
    (Filter.Eventually.of_forall hLower)
    (Filter.Eventually.of_forall hUpper) hTailRatio

/-- Conversely, a fixed positive fraction of the remaining terminal
horizon forces the terminal-scaled viscous floor to disappear. -/
theorem thirdFull_scalar_terminalNoncompression_scaledHeight_tendsto_zero244
    (T c : ℝ) (x delta height tail : ℕ → ℝ)
    (hc : 0 < c) (hx : ∀ k, x k < T)
    (hHeight : ∀ k, 0 ≤ height k)
    (hTail : Tendsto tail atTop (𝓝 (0 : ℝ)))
    (hCharge : ∀ k, delta k * height k ≤ tail k)
    (hNoncompression : ∀ k, c ≤ delta k / (T - x k)) :
    Tendsto (fun k => (T - x k) * height k) atTop (𝓝 (0 : ℝ)) := by
  have hLower (k : ℕ) : 0 ≤ (T - x k) * height k :=
    mul_nonneg (sub_pos.mpr (hx k)).le (hHeight k)
  have hUpper (k : ℕ) : (T - x k) * height k ≤ tail k / c := by
    have hProduct := thirdFull_scalar_terminalNormalizedClock_product244
      T (x k) (delta k) (height k) (hx k)
    have hScaled :
        c * ((T - x k) * height k) ≤ delta k * height k := by
      calc
        c * ((T - x k) * height k) ≤
          (delta k / (T - x k)) * ((T - x k) * height k) :=
          mul_le_mul_of_nonneg_right (hNoncompression k) (hLower k)
        _ = delta k * height k := hProduct
    apply (le_div_iff₀ hc).2
    calc
      ((T - x k) * height k) * c =
          c * ((T - x k) * height k) := by ring
      _ ≤ delta k * height k := hScaled
      _ ≤ tail k := hCharge k
  have hTailRatio :
      Tendsto (fun k => tail k / c) atTop (𝓝 (0 : ℝ)) := by
    simpa using hTail.div_const c
  exact squeeze_zero'
    (Filter.Eventually.of_forall hLower)
    (Filter.Eventually.of_forall hUpper) hTailRatio

/-- With NO noncompression/height premise, finite H3 dissipation forces
at least one of the two terminal-scaled factors to collapse: quantitatively,
the smaller one is no larger than sqrt of the remaining physical tail. -/
theorem thirdFullPhysical_cofinalOptimalInnerClock_minTerminalScale_tendsto_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (x delta radiusMin epsilon : ℕ → ℝ)
    (hx : ∀ k, a ≤ x k ∧ x k < T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hDelta : ∀ k, 0 ≤ delta k)
    (hEps : ∀ k, 0 < epsilon k)
    (hCharge : ∀ k,
      delta k * (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (radiusMin k) (epsilon k)) ≤
      ∫ r in x k..T, velocityH3DissipationAt u r) :
    Tendsto (fun k =>
      min (delta k / (T - x k))
        ((T - x k) * (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
          u b (radiusMin k) (epsilon k))))
      atTop (𝓝 (0 : ℝ)) := by
  let h : ℕ → ℝ := fun k => epsilon k /
    thirdFullPhysicalAnnularCapClockFactor244 u b (radiusMin k) (epsilon k)
  let tail : ℕ → ℝ := fun k =>
    ∫ r in x k..T, velocityH3DissipationAt u r
  have hTail : Tendsto tail atTop (𝓝 (0 : ℝ)) :=
    thirdFull_scalarTerminalTail_integral_tendsto_zero244
      (velocityH3DissipationAt u) a T hClass.terminal_start.2
      hDInt x hCofinal (Filter.Eventually.of_forall (fun k =>
        ⟨(hx k).1, (hx k).2.le⟩))
  have hHeight (k : ℕ) : 0 ≤ h k := by
    dsimp only [h]
    exact (div_pos (hEps k)
      (thirdFullPhysical_annularCapClockFactor_pos244
        u b (radiusMin k) (epsilon k))).le
  have hMinLower (k : ℕ) :
      0 ≤ min (delta k / (T - x k)) ((T - x k) * h k) :=
    le_min (div_nonneg (hDelta k) (sub_pos.mpr (hx k).2).le)
      (mul_nonneg (sub_pos.mpr (hx k).2).le (hHeight k))
  have hMinUpper (k : ℕ) :
      min (delta k / (T - x k)) ((T - x k) * h k) ≤ Real.sqrt (tail k) :=
    thirdFull_scalar_terminalNormalizedClock_min_le_sqrt244
      T (x k) (delta k) (h k) (tail k)
      (hx k).2 (hDelta k) (hHeight k) (hCharge k)
  have hTailSqrt :
      Tendsto (fun k => Real.sqrt (tail k)) atTop (𝓝 (0 : ℝ)) := by
    simpa using hTail.sqrt
  exact squeeze_zero'
    (Filter.Eventually.of_forall hMinLower)
    (Filter.Eventually.of_forall hMinUpper) hTailSqrt

/-- The PDE-facing critical inverse-terminal-time obstruction, for the
actual optimized annular clock. The cap factor is the ORIGINAL physical
linearized-viscosity normalization at the fixed kinetic anchor b. -/
theorem thirdFullPhysical_cofinalOptimalInnerClock_criticalHeight_forcesWidthCollapse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b c : ℝ) (hc : 0 < c)
    (x delta radiusMin epsilon : ℕ → ℝ)
    (hx : ∀ k, a ≤ x k ∧ x k < T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hDelta : ∀ k, 0 ≤ delta k)
    (hCharge : ∀ k,
      delta k * (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (radiusMin k) (epsilon k)) ≤
      ∫ r in x k..T, velocityH3DissipationAt u r)
    (hCritical : ∀ k,
      c ≤ (T - x k) * (epsilon k /
        thirdFullPhysicalAnnularCapClockFactor244 u b (radiusMin k) (epsilon k))) :
    Tendsto (fun k => delta k / (T - x k)) atTop (𝓝 (0 : ℝ)) := by
  have hTail := thirdFull_scalarTerminalTail_integral_tendsto_zero244
    (velocityH3DissipationAt u) a T hClass.terminal_start.2
    hDInt x hCofinal (Filter.Eventually.of_forall (fun k =>
      ⟨(hx k).1, (hx k).2.le⟩))
  exact thirdFull_scalar_terminalCriticalHeight_relativeWidth_tendsto_zero244
    T c x delta
    (fun k => epsilon k / thirdFullPhysicalAnnularCapClockFactor244
      u b (radiusMin k) (epsilon k))
    (fun k => ∫ r in x k..T, velocityH3DissipationAt u r)
    hc (fun k => (hx k).2) hDelta hTail hCharge hCritical

/-- Conversely, if the actual cofinal clock persists over a fixed fraction
of the remaining horizon, its normalized height must be subcritical:
(T-x(k)) * epsilon(k)/C(b,rho_min(k),epsilon(k)) -> 0. -/
theorem thirdFullPhysical_cofinalOptimalInnerClock_noncompression_forcesHeightCollapse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b c : ℝ) (hc : 0 < c)
    (x delta radiusMin epsilon : ℕ → ℝ)
    (hx : ∀ k, a ≤ x k ∧ x k < T)
    (hCofinal : Tendsto x atTop (𝓝 T))
    (hEps : ∀ k, 0 < epsilon k)
    (hCharge : ∀ k,
      delta k * (epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (radiusMin k) (epsilon k)) ≤
      ∫ r in x k..T, velocityH3DissipationAt u r)
    (hNoncompression : ∀ k, c ≤ delta k / (T - x k)) :
    Tendsto (fun k => (T - x k) * (epsilon k /
      thirdFullPhysicalAnnularCapClockFactor244 u b (radiusMin k) (epsilon k)))
      atTop (𝓝 (0 : ℝ)) := by
  have hTail := thirdFull_scalarTerminalTail_integral_tendsto_zero244
    (velocityH3DissipationAt u) a T hClass.terminal_start.2
    hDInt x hCofinal (Filter.Eventually.of_forall (fun k =>
      ⟨(hx k).1, (hx k).2.le⟩))
  have hHeight (k : ℕ) :
      0 ≤ epsilon k / thirdFullPhysicalAnnularCapClockFactor244
        u b (radiusMin k) (epsilon k) :=
    (div_pos (hEps k)
      (thirdFullPhysical_annularCapClockFactor_pos244
        u b (radiusMin k) (epsilon k))).le
  exact thirdFull_scalar_terminalNoncompression_scaledHeight_tendsto_zero244
    T c x delta
    (fun k => epsilon k / thirdFullPhysicalAnnularCapClockFactor244
      u b (radiusMin k) (epsilon k))
    (fun k => ∫ r in x k..T, velocityH3DissipationAt u r)
    hc (fun k => (hx k).2) hHeight hTail hCharge hNoncompression

/-- This is the complete PDE-facing extraction theorem: the genuine
finite-radius snapshot margins from the previous module already construct
physical windows for which the terminal-normalized width/height bottleneck
vanishes. No independent terminal-tail-charge hypothesis is needed here. -/
theorem thirdFullPhysical_cofinalAnnularSnapshotMargins_terminalScaleCollapse244
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
      (∀ k : ℕ, 0 < delta k ∧ x k + delta k < x (k + 1)) ∧
      Tendsto (fun k =>
        min (delta k / (T - x k))
          ((T - x k) * (epsilon k /
            thirdFullPhysicalAnnularCapClockFactor244
              u b (radiusMin k) (epsilon k))))
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨delta, hWin, hTailBound, hWidthBound, hSum,
      hZero, hFinite, hActualTail, hAntitone⟩ :=
    thirdFullPhysical_cofinalAnnularUniformSnapshots_optimalInnerClocks244
      hH3 hClass hDInt b hb x radiusMin R margin epsilon
      hx hStep hCofinal hRadiusMin hRadiusMax hMargin hEps hExcess hPeak
  refine ⟨delta, (fun k => ⟨(hWin k).1, (hWin k).2.1⟩), ?_⟩
  exact thirdFullPhysical_cofinalOptimalInnerClock_minTerminalScale_tendsto_zero244
    hClass hDInt b x delta radiusMin epsilon
    (fun k => ⟨(lt_trans hb.1 (hx k).1).le, (hx k).2⟩)
    hCofinal (fun k => (hWin k).1.le) hEps hTailBound

end
end PrimeTensor.FirstMonomialTriad
