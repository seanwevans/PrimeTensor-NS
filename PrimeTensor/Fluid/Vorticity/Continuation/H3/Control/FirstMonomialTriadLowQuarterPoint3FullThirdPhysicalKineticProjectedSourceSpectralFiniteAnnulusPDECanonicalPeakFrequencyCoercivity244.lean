import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakDisjointPersistence244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostCollapse244
import Mathlib.Tactic

/-!
# Frequency-resolved coercivity at actual canonical H³ spectral peaks

The exact Fourier decomposition and the genuine physical kinetic ceiling give,
at every positive strict-time slice after a fixed kinetic anchor b,

  ‖U₃(t)‖² ≤ K(ρ) E₀(b) + HighMass_ρ(U₃(t)),
  ρ² ‖U₃(t)‖² ≤ D₃(t) + ρ² K(ρ) E₀(b).

When the spectral peak is above twice the explicitly quantified low-frequency
kinetic ceiling, at least half its squared norm is outside the radial carrier,
and full physical dissipation is >= ρ² ‖U₃(t)‖² / 2.

The radius can be chosen independently of the physical time; at ρ >= 1, the
polynomial Fourier ceiling obeys K(ρ) <= 4ρ⁶. In particular the checkable
condition 8ρ⁶ E₀(b) <= ‖U₃(t)‖² yields the same half-mass coercivity.

On any cofinal spectral-peak sequence with divergent SUP norms this lower
bound holds eventually at each fixed positive radius, at the SAME peak times.
No uniform time modulus or lower bound on peak persistence widths is inferred.

Finally, the preexisting disjoint-window partial-sum budget gives SUMMABILITY
of the actual nonnegative height-width charges, hence convergence of each
charge to zero. This is sharper than mere width collapse but compatible with
finite terminal dissipation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeCanonicalPeakFrequencyCoercivity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCanonicalPeakFrequencyCoercivity244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- SUP spectral norm is bounded by the EXACT low/high Hilbert-square split;
it is never identified with the sum-of-three-squares as an equality. -/
theorem h3Path_spectralSupSquare_le_lowPlusHigh244
    (ρ : ℝ) (G : H3SpectralVelocityState) :
    ‖G‖ ^ 2 ≤
      h3PathActualSpectralLowRadialSquareMass244 ρ G +
        h3PathActualSpectralHighRadialRemainder244 ρ G := by
  have hEnergy := h3Path_spectralSupNorm_sq_le_squareEnergy244 G
  dsimp only [h3PathActualSpectralHighRadialRemainder244]
  linarith only [hEnergy]

/-- Exact physical L² kinetic monotonicity gives a fixed low-radial ceiling,
leaving only the genuine integrated high-radial Fourier H³ mass. -/
theorem h3Path_physicalSpectralSupSquare_le_kineticPlusHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
      h3TerminalRadialSobolevWeightSquareCeiling ρ *
        velocityH3Energy0At u b +
      h3PathActualSpectralHighRadialRemainder244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hSplit := h3Path_spectralSupSquare_le_lowPlusHigh244 ρ G
  have hLow :=
    h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
      hH3 hClass b hb ρ hρ t ht
  dsimp only [G] at hSplit hLow ⊢
  linarith only [hSplit, hLow]

/-- Radius-resolved H³ coercivity: the spectral SUP square is paid for by
actual full physical H⁴-type dissipation and the bounded low kinetic carrier.
No time derivatives of the weighted H³ state enter the proof. -/
theorem h3Path_physicalSpectralSupSquare_radiusDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ ^ 2 * ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
      velocityH3DissipationAt u t +
        ρ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b) := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let L : ℝ := h3TerminalRadialSobolevWeightSquareCeiling ρ *
    velocityH3Energy0At u b
  have hMass : ‖G‖ ^ 2 ≤ L +
      h3PathActualSpectralHighRadialRemainder244 ρ G := by
    exact h3Path_physicalSpectralSupSquare_le_kineticPlusHigh244
      hH3 hClass b hb t ht ρ hρ
  have hScaled := mul_le_mul_of_nonneg_left hMass (sq_nonneg ρ)
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hHigh := h3Path_highRadialMass_le_fullDissipationAt244
    hH3 hClass t htClass ρ hρ
  dsimp only [G, L] at hMass hScaled hHigh ⊢
  nlinarith only [hScaled, hHigh]

/-- If squared H³ amplitude exceeds twice the exact low-radial kinetic
ceiling, at least half that amplitude lies in the complementary Fourier set. -/
theorem h3Path_physicalSpectralPeak_halfMassHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hLarge : 2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
        velocityH3Energy0At u b) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2) :
    ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 / 2 ≤
      h3PathActualSpectralHighRadialRemainder244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have hSplit := h3Path_physicalSpectralSupSquare_le_kineticPlusHigh244
    hH3 hClass b hb t ht ρ hρ
  linarith only [hSplit, hLarge]

/-- The half-high-mass inequality translates to a physical dissipation
height >= ρ²/2 times the squared weighted H³ peak amplitude. -/
theorem h3Path_physicalSpectralPeak_halfDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hLarge : 2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
        velocityH3Energy0At u b) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2) :
    (ρ ^ 2 / 2) *
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
        velocityH3DissipationAt u t := by
  have hHigh := h3Path_physicalSpectralPeak_halfMassHigh244
    hH3 hClass b hb t ht ρ hρ hLarge
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hFull := h3Path_highRadialMass_le_fullDissipationAt244
    hH3 hClass t htClass ρ hρ
  have hScaled := mul_le_mul_of_nonneg_left hHigh (sq_nonneg ρ)
  nlinarith only [hScaled, hFull]

/-- The exact ordered-derivative H³ weight-square has a four-term polynomial
ceiling, and for any radius >= 1 all four terms are below ρ⁶. -/
theorem h3Path_radialSobolevCeiling_le_four_sixth244
    (ρ : ℝ) (hρ : 1 ≤ ρ) :
    h3TerminalRadialSobolevWeightSquareCeiling ρ ≤ 4 * ρ ^ 6 := by
  have h01 : (1 : ℝ) ≤ ρ ^ 2 := by
    nlinarith only [hρ, sq_nonneg (ρ - 1)]
  have h12 : ρ ^ 2 ≤ (ρ ^ 2) ^ 2 := by
    calc
      ρ ^ 2 = ρ ^ 2 * 1 := by ring
      _ ≤ ρ ^ 2 * ρ ^ 2 :=
        mul_le_mul_of_nonneg_left h01 (sq_nonneg ρ)
      _ = (ρ ^ 2) ^ 2 := by ring
  have h23 : (ρ ^ 2) ^ 2 ≤ (ρ ^ 2) ^ 3 := by
    calc
      (ρ ^ 2) ^ 2 = (ρ ^ 2) ^ 2 * 1 := by ring
      _ ≤ (ρ ^ 2) ^ 2 * ρ ^ 2 :=
        mul_le_mul_of_nonneg_left h01 (sq_nonneg (ρ ^ 2))
      _ = (ρ ^ 2) ^ 3 := by ring
  unfold h3TerminalRadialSobolevWeightSquareCeiling
  nlinarith only [h01, h12, h23]

/-- Explicit polynomial frequency detector: a peak above eight times the
sixth-power radial kinetic scale pays half its squared amplitude at the
frequency-squared physical dissipation rate. -/
theorem h3Path_physicalPeak_sixthThreshold_forces_dissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hKinetic : 0 ≤ velocityH3Energy0At u b)
    (hLarge : 8 * ρ ^ 6 * velocityH3Energy0At u b ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2) :
    (ρ ^ 2 / 2) *
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
        velocityH3DissipationAt u t := by
  have hCeiling := h3Path_radialSobolevCeiling_le_four_sixth244 ρ hρ
  have hThreshold :
      2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
        velocityH3Energy0At u b) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 := by
    have hMult := mul_le_mul_of_nonneg_right hCeiling hKinetic
    nlinarith only [hMult, hLarge]
  exact h3Path_physicalSpectralPeak_halfDissipation244
    hH3 hClass b hb t ht ρ (by linarith only [hρ]) hThreshold

/-- Spectral SUP norm divergence forces the quantitative half-mass
coercivity eventually at every FIXED positive radial cutoff on those same
genuine physical observation times. No new times are reselected. -/
theorem h3Path_cofinalSpectralPeaks_eventualRadiusDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℕ → ℝ)
    (hs : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T)
    (hEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ᶠ k : ℕ in atTop,
      (ρ ^ 2 / 2) *
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 ≤
          velocityH3DissipationAt u (s k) := by
  let L : ℝ := h3TerminalRadialSobolevWeightSquareCeiling ρ *
    velocityH3Energy0At u b
  have hLarge : ∀ᶠ k : ℕ in atTop,
      max (2 * L) 1 ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    hEscape.eventually (eventually_ge_atTop (max (2 * L) 1))
  filter_upwards [hs, hLarge] with k ht hk
  have h1 : 1 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    (le_max_right _ _).trans hk
  have hL : 2 * L ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ :=
    (le_max_left _ _).trans hk
  have hSq : 2 * L ≤ ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 := by
    have hPow : ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 := by
      nlinarith only [h1, sq_nonneg
        (‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ - 1)]
    linarith only [hL, hPow]
  exact h3Path_physicalSpectralPeak_halfDissipation244
    hH3 hClass b hb (s k) ht ρ hρ (by simpa only [L] using hSq)

/-- Nonnegative disjoint peak persistence charges have summable actual
physical H³ dissipation costs, not merely bounded individual heights. -/
theorem h3Path_disjointPeakHeightWidthCost_summable244
    (d H : ℕ → ℝ) (ρ B : ℝ)
    (_hρ : 0 < ρ)
    (hd : ∀ k, 0 ≤ d k)
    (hH : ∀ k, 0 ≤ H k)
    (hBudget : ∀ m, (∑ k ∈ Finset.range m,
      d k * (ρ ^ 2 * H k)) ≤ B) :
    Summable (fun k => d k * (ρ ^ 2 * H k)) := by
  apply h3Path_nonnegativeBoundedRangeSums_summable244
    (fun k => d k * (ρ ^ 2 * H k)) B
  · intro k
    exact mul_nonneg (hd k) (mul_nonneg (sq_nonneg ρ) (hH k))
  · exact hBudget

/-- In particular, the entire frequency-weighted persistence charge of
each selected disjoint high-frequency peak must tend to zero. This is
stronger than dₖ -> 0 when the spectral height Hₖ diverges. -/
theorem h3Path_disjointPeakHeightWidthCost_tendsto_zero244
    (d H : ℕ → ℝ) (ρ B : ℝ)
    (hρ : 0 < ρ)
    (hd : ∀ k, 0 ≤ d k)
    (hH : ∀ k, 0 ≤ H k)
    (hBudget : ∀ m, (∑ k ∈ Finset.range m,
      d k * (ρ ^ 2 * H k)) ≤ B) :
    Tendsto (fun k => d k * (ρ ^ 2 * H k)) atTop (𝓝 (0 : ℝ)) := by
  exact (h3Path_disjointPeakHeightWidthCost_summable244
    d H ρ B hρ hd hH hBudget).tendsto_atTop_zero

end
end PrimeTensor.FirstMonomialTriad
