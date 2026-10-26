import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDESourceCeilingEscape244
import Mathlib.Tactic

/-!
# Quadratically sharp exact physical PDE persistence clocks

The anchored physical annulus variation has a genuinely quadratic term
`Λ*δ + Ξ*δ^2`. The earlier exact selector replaced `δ^2` by `δ` and
collapsed both rates into `Λ+Ξ+1`, losing the square-root persistence
scale. Here the exact width separately caps the linear and quadratic
variation, keeping the latter as a square-root condition.

A selected annulus retains strictly more than a quarter cubic surplus.
The same physical source ceiling and initial spectral bound are used for
both the exact width and the verified integrated dissipation persistence.
No terminal regularity, source bound, or automatically finite full H³
dissipation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact selector respecting both linear and *quadratic* PDE temporal
variation without converting the quadratic correction to a linear rate. -/
noncomputable def h3PathCubicAnnulusQuadraticSharpPDEWidth244
    (b gap Λ Ξ : ℝ) : ℝ :=
  min (b / 2) (min (1 : ℝ)
    (min (gap / (4 * (Λ + 1)))
      (Real.sqrt (gap / (4 * (Ξ + 1))))))

/-- Literal new width is positive, within the physical terminal time,
and strictly meets the *unlinearized* quadratic PDE budget. -/
theorem h3Path_cubicAnnulusQuadraticSharpPDEWidth_valid244
    (b gap Λ Ξ : ℝ)
    (hb : 0 < b) (hgap : 0 < gap)
    (hΛ : 0 ≤ Λ) (hΞ : 0 ≤ Ξ) :
    ∃ δ : ℝ,
      δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 b gap Λ Ξ ∧
      0 < δ ∧ δ < b ∧ δ ≤ 1 ∧
      Λ * δ + Ξ * δ ^ 2 < gap := by
  have hL : 0 < Λ + 1 := by linarith only [hΛ]
  have hQ : 0 < Ξ + 1 := by linarith only [hΞ]
  have hLinearPos : 0 < gap / (4 * (Λ + 1)) := by positivity
  have hArg : 0 < gap / (4 * (Ξ + 1)) := by positivity
  have hRootPos : 0 < Real.sqrt (gap / (4 * (Ξ + 1))) :=
    Real.sqrt_pos.2 hArg
  let δ : ℝ := h3PathCubicAnnulusQuadraticSharpPDEWidth244 b gap Λ Ξ
  have hδ : 0 < δ := by
    dsimp only [δ, h3PathCubicAnnulusQuadraticSharpPDEWidth244]
    apply lt_min
    · linarith only [hb]
    · apply lt_min
      · norm_num
      · exact lt_min hLinearPos hRootPos
  have hBcap : δ ≤ b / 2 := by
    dsimp only [δ, h3PathCubicAnnulusQuadraticSharpPDEWidth244]
    exact min_le_left _ _
  have hOne : δ ≤ 1 := by
    dsimp only [δ, h3PathCubicAnnulusQuadraticSharpPDEWidth244]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hLinear : δ ≤ gap / (4 * (Λ + 1)) := by
    dsimp only [δ, h3PathCubicAnnulusQuadraticSharpPDEWidth244]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hRoot : δ ≤ Real.sqrt (gap / (4 * (Ξ + 1))) := by
    dsimp only [δ, h3PathCubicAnnulusQuadraticSharpPDEWidth244]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hRootNonneg : 0 ≤ Real.sqrt (gap / (4 * (Ξ + 1))) :=
    Real.sqrt_nonneg _
  have hSquareLe : δ ^ 2 ≤ (Real.sqrt (gap / (4 * (Ξ + 1)))) ^ 2 := by
    have hProd : 0 ≤
        (Real.sqrt (gap / (4 * (Ξ + 1))) - δ) *
        (Real.sqrt (gap / (4 * (Ξ + 1))) + δ) :=
      mul_nonneg (sub_nonneg.mpr hRoot) (add_nonneg hRootNonneg hδ.le)
    nlinarith only [hProd]
  have hSquare : δ ^ 2 ≤ gap / (4 * (Ξ + 1)) := by
    rw [Real.sq_sqrt hArg.le] at hSquareLe
    exact hSquareLe
  have hLinUpper : (Λ + 1) * δ ≤ gap / 4 := by
    calc
      (Λ + 1) * δ ≤ (Λ + 1) * (gap / (4 * (Λ + 1))) :=
        mul_le_mul_of_nonneg_left hLinear hL.le
      _ = gap / 4 := by field_simp [ne_of_gt hL]
  have hQuadUpper : (Ξ + 1) * δ ^ 2 ≤ gap / 4 := by
    calc
      (Ξ + 1) * δ ^ 2 ≤ (Ξ + 1) * (gap / (4 * (Ξ + 1))) :=
        mul_le_mul_of_nonneg_left hSquare hQ.le
      _ = gap / 4 := by field_simp [ne_of_gt hQ]
  have hLinBudget : Λ * δ ≤ gap / 4 := by
    nlinarith only [hLinUpper, hδ]
  have hQuadBudget : Ξ * δ ^ 2 ≤ gap / 4 := by
    have hs : 0 ≤ δ ^ 2 := sq_nonneg _
    nlinarith only [hQuadUpper, hs]
  refine ⟨δ, rfl, hδ, ?_, hOne, ?_⟩
  · linarith only [hb, hBcap]
  · linarith only [hLinBudget, hQuadBudget, hgap]

/-- Vanishing exact quadratic-sharp window cost cannot be accounted for
by the unit cap, leaving separate temporal, linear and square-root caps. -/
theorem h3Path_quadraticSharpMin_smallCost_forces_threeCaps244
    (A M b gap Λ Ξ δ : ℝ)
    (hA : 0 < A) (hUnit : M < A)
    (hExact : δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 b gap Λ Ξ)
    (hCost : A * δ ≤ M) :
    A * (b / 2) ≤ M ∨
      A * (gap / (4 * (Λ + 1))) ≤ M ∨
      A * Real.sqrt (gap / (4 * (Ξ + 1))) ≤ M := by
  by_contra hNot
  push_neg at hNot
  have hWidth : δ ≤ M / A := by
    apply (le_div_iff₀ hA).2
    calc
      δ * A = A * δ := by ring
      _ ≤ M := hCost
  have hTime : M / A < b / 2 := by
    apply (div_lt_iff₀ hA).2
    simpa only [mul_comm] using hNot.1
  have hUnitSmall : M / A < (1 : ℝ) := by
    apply (div_lt_iff₀ hA).2
    simpa only [one_mul] using hUnit
  have hLinear : M / A < gap / (4 * (Λ + 1)) := by
    apply (div_lt_iff₀ hA).2
    simpa only [mul_comm] using hNot.2.1
  have hQuadratic : M / A < Real.sqrt (gap / (4 * (Ξ + 1))) := by
    apply (div_lt_iff₀ hA).2
    simpa only [mul_comm] using hNot.2.2
  rw [hExact] at hWidth
  change min (b / 2) (min (1 : ℝ)
    (min (gap / (4 * (Λ + 1)))
      (Real.sqrt (gap / (4 * (Ξ + 1)))))) ≤ M / A at hWidth
  exact (not_lt_of_ge hWidth)
    (lt_min hTime (lt_min hUnitSmall (lt_min hLinear hQuadratic)))

/-- Every positive tolerance admits a sharp asymptotic alternative with
three independent caps, conditional only on exact widths and vanishing
cubic-weighted disjoint costs. The square-root cap is retained intact. -/
theorem h3Path_exactQuadraticSharpClocks_vanishingThreeCapAlternative244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 3 *
          (gap (v k) / (4 * (Λ (v k) + 1))) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 3 *
          Real.sqrt (gap (v k) / (4 * (Ξ (v k) + 1))) ≤ ε := by
  intro ε hε
  have hLarge :=
    h3Path_strictMonoCubicHeight_eventually_above_mass244 v hv (ε / 2)
  have hSmall : ∀ᶠ k : ℕ in atTop,
      δ (v k) * ((v k : ℝ) + 1) ^ 3 < ε :=
    hCollapse.eventually (eventually_lt_nhds hε)
  filter_upwards [hLarge, hSmall] with k hkLarge hkSmall
  have hA : 0 < ((v k : ℝ) + 1) ^ 3 := by positivity
  have hUnit : ε < ((v k : ℝ) + 1) ^ 3 := by
    linarith only [hkLarge]
  have hCost : ((v k : ℝ) + 1) ^ 3 * δ (v k) ≤ ε := by
    calc
      ((v k : ℝ) + 1) ^ 3 * δ (v k) =
          δ (v k) * ((v k : ℝ) + 1) ^ 3 := by ring
      _ ≤ ε := le_of_lt hkSmall
  exact h3Path_quadraticSharpMin_smallCost_forces_threeCaps244
    (((v k : ℝ) + 1) ^ 3) ε (b (v k))
    (gap (v k)) (Λ (v k)) (Ξ (v k)) (δ (v k))
    hA hUnit (hExact k) hCost

/-- A quarter-cubic annular surplus converts the small *linear* clock
cap to a sixth-power lower bound for the physical linear PDE rate. -/
theorem h3Path_quarterGap_quadraticClockLinearCap_forces_sixth244
    (R gap Λ ε : ℝ) (hR : 0 < R) (hΛ : 0 ≤ Λ)
    (hGap : R ^ 3 / 4 ≤ gap)
    (hCap : R ^ 3 * (gap / (4 * (Λ + 1))) ≤ ε) :
    R ^ 6 ≤ 16 * ε * (Λ + 1) := by
  have hZ : 0 < Λ + 1 := by linarith only [hΛ]
  have hCap' : R ^ 3 * gap / (4 * (Λ + 1)) ≤ ε := by
    calc
      R ^ 3 * gap / (4 * (Λ + 1)) =
          R ^ 3 * (gap / (4 * (Λ + 1))) := by ring
      _ ≤ ε := hCap
  have hCross : R ^ 3 * gap ≤ ε * (4 * (Λ + 1)) :=
    (div_le_iff₀ (by positivity : 0 < 4 * (Λ + 1))).mp hCap'
  have hQuarter : R ^ 6 / 4 ≤ R ^ 3 * gap := by
    have hProd : R ^ 3 * (R ^ 3 / 4) ≤ R ^ 3 * gap :=
      mul_le_mul_of_nonneg_left hGap (pow_nonneg hR.le _)
    nlinarith only [hProd]
  nlinarith only [hCross, hQuarter]

/-- Respecting `Ξ*δ²` rather than replacing it by `Ξ*δ` raises the
quadratic obstruction from a sixth-power to a ninth-power rate. -/
theorem h3Path_quarterGap_quadraticClockRootCap_forces_ninth244
    (R gap Ξ ε : ℝ) (hR : 0 < R) (hΞ : 0 ≤ Ξ)
    (hGap : R ^ 3 / 4 ≤ gap)
    (hCap : R ^ 3 * Real.sqrt (gap / (4 * (Ξ + 1))) ≤ ε) :
    R ^ 9 ≤ 16 * ε ^ 2 * (Ξ + 1) := by
  have hZ : 0 < Ξ + 1 := by linarith only [hΞ]
  have hGapPos : 0 < gap := by
    have hR3 : 0 < R ^ 3 := pow_pos hR _
    linarith only [hGap, hR3]
  have hArg : 0 ≤ gap / (4 * (Ξ + 1)) := by positivity
  let q : ℝ := Real.sqrt (gap / (4 * (Ξ + 1)))
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hProdPos : 0 ≤ R ^ 3 * q := mul_nonneg (pow_nonneg hR.le _) hq
  have hε : 0 ≤ ε := by linarith only [hCap, hProdPos]
  have hBound : R ^ 3 * q ≤ ε := by simpa only [q] using hCap
  have hPair : 0 ≤ (ε - R ^ 3 * q) * (ε + R ^ 3 * q) :=
    mul_nonneg (sub_nonneg.mpr hBound) (add_nonneg hε hProdPos)
  have hSq : (R ^ 3 * q) ^ 2 ≤ ε ^ 2 := by
    nlinarith only [hPair]
  have hSqrtSq : q ^ 2 = gap / (4 * (Ξ + 1)) := by
    dsimp only [q]
    exact Real.sq_sqrt hArg
  have hCapSq : R ^ 6 * (gap / (4 * (Ξ + 1))) ≤ ε ^ 2 := by
    calc
      R ^ 6 * (gap / (4 * (Ξ + 1))) = (R ^ 3 * q) ^ 2 := by
        rw [mul_pow, hSqrtSq]
        ring
      _ ≤ ε ^ 2 := hSq
  have hCapDiv : R ^ 6 * gap / (4 * (Ξ + 1)) ≤ ε ^ 2 := by
    calc
      R ^ 6 * gap / (4 * (Ξ + 1)) =
          R ^ 6 * (gap / (4 * (Ξ + 1))) := by ring
      _ ≤ ε ^ 2 := hCapSq
  have hCross : R ^ 6 * gap ≤ ε ^ 2 * (4 * (Ξ + 1)) :=
    (div_le_iff₀ (by positivity : 0 < 4 * (Ξ + 1))).mp hCapDiv
  have hQuarter : R ^ 9 / 4 ≤ R ^ 6 * gap := by
    have hProd : R ^ 6 * (R ^ 3 / 4) ≤ R ^ 6 * gap :=
      mul_le_mul_of_nonneg_left hGap (pow_nonneg hR.le _)
    nlinarith only [hProd]
  nlinarith only [hCross, hQuarter]

/-- Exact quadratic-sharp disjoint clocks yield distinct sixth-order
linear versus ninth-order quadratic barriers, or terminal compression. -/
theorem h3Path_exactQuadraticSharpClocks_threeScaleBarrier244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ)
    (hv : StrictMono v)
    (hExact : ∀ k : ℕ,
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0))
    (hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k))
    (hΛ : ∀ᶠ k : ℕ in atTop, 0 ≤ Λ (v k))
    (hΞ : ∀ᶠ k : ℕ in atTop, 0 ≤ Ξ (v k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 * (b (v k) / 2) ≤ ε ∨
      ((v k : ℝ) + 1) ^ 6 ≤ 16 * ε * (Λ (v k) + 1) ∨
      ((v k : ℝ) + 1) ^ 9 ≤ 16 * ε ^ 2 * (Ξ (v k) + 1) := by
  intro ε hε
  have hAlt := h3Path_exactQuadraticSharpClocks_vanishingThreeCapAlternative244
    v δ b gap Λ Ξ hv hExact hCollapse ε hε
  filter_upwards [hAlt, hQuarter, hΛ, hΞ] with k hk hg hl hq
  rcases hk with ht | hlcap | hqcap
  · exact Or.inl ht
  · exact Or.inr (Or.inl
      (h3Path_quarterGap_quadraticClockLinearCap_forces_sixth244
        ((v k : ℝ) + 1) (gap (v k)) (Λ (v k)) ε
        (by positivity) hl hg hlcap))
  · exact Or.inr (Or.inr
      (h3Path_quarterGap_quadraticClockRootCap_forces_ninth244
        ((v k : ℝ) + 1) (gap (v k)) (Ξ (v k)) ε
        (by positivity) hq hg hqcap))

/-- Physical quarter-cubic snapshot on the *new* exact quadratically
sharp anchored-PDE clock; selected radius and source ceiling are shared. -/
theorem h3Path_cubicHighSnapshot_has_quarterGapQuadraticSharpClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ t + δ < T ∧
      (δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - t) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C)) ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ((n : ℝ) + 1) ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2 := by
  obtain ⟨N, hnN, hHeight⟩ :=
    h3Path_cubicHighSnapshot_has_finiteAnnularHeight244
      hH3 hClass t ht n hCube
  let R : ℝ := (n : ℝ) + 1
  let Q : ℝ := (N : ℝ) + 1
  let A : ℝ := R ^ 3 / 2
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let K : ℝ := ‖G‖
  let B : ℝ :=
    h3PathActualLowRadialDissipation244 Q G -
      h3PathActualLowRadialDissipation244 R G
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := norm_nonneg G
  have hBase : ∀ j : Fin 3, ‖G j‖ ≤ K := by
    intro j
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg G)).1 le_rfl j
  have hCubePos : 0 < R ^ 3 := by dsimp only [R]; positivity
  have hHeight' : 3 * R ^ 3 / 4 < B := by
    simpa only [R, Q, B, G] using hHeight
  have hQuarter : R ^ 3 / 4 < B - A := by
    dsimp only [A]
    linarith only [hHeight']
  have hGap : 0 < B - A := by
    linarith only [hQuarter, hCubePos]
  let b : ℝ := (T - t) / 2
  have hb : 0 < b := by dsimp only [b]; linarith only [ht.2]
  have ht0 : 0 < t := lt_trans hClass.terminal_start.1 ht.1
  have htb : t < t + b := by linarith only [hb]
  have hbT : t + b < T := by
    dsimp only [b]
    linarith only [ht.2]
  obtain ⟨C, hC, hSource⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnStrict244
      hH3 ht0 htb hbT
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C
  let Ξ : ℝ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C
  have hΛ : 0 ≤ Λ :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 R Q K C hK hC
  have hΞ : 0 ≤ Ξ :=
    h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244 R Q C
  obtain ⟨δ, hExact, hδ, hδb, _hδone, hBudget⟩ :=
    h3Path_cubicAnnulusQuadraticSharpPDEWidth_valid244
      b (B - A) Λ Ξ hb hGap hΛ hΞ
  have hEnd : t + δ < T := by linarith only [hδb, hbT]
  have hSourceWindow : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C := by
    intro s hs
    apply hSource s
    constructor
    · exact hs.1
    · linarith only [hs.2, hδb]
  have hFinal :=
    h3Path_actualFiniteAnnulus_integratedCost_of_anchoredPDE244
      hH3 hClass R Q K C A t δ hR hQ hK hA ht hδ hEnd
      hBase hSourceWindow (show A < B from sub_pos.mp hGap) hBudget
  refine ⟨N, K, C, δ, hnN, hK, hC, hδ, hEnd, ?_, hFinal.1, ?_⟩
  · change δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 b (B - A) Λ Ξ
    exact hExact
  · change R ^ 3 / 4 < B - A
    exact hQuarter


/-- Cofinal physical cubic snapshots preserve quarter-cubic annular
surplus and the literal unlinearized quadratic temporal PDE selector. -/
theorem h3Path_noL2Trace_forces_quarterGapQuadraticSharpClocks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        n ≤ N n ∧ 0 ≤ K n ∧ 0 ≤ C n ∧ 0 < δ n ∧
        τ n + δ n < T ∧
        δ n = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N n)
          (h3PathCubicAnnulusActualLinearRate244 N K C n)
          (h3PathCubicAnnulusActualQuadraticRate244 N C n) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        ((n : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N n) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hCube⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ τ n + δ < T ∧
      (δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C)) ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ((n : ℝ) + 1) ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2 :=
    h3Path_cubicHighSnapshot_has_quarterGapQuadraticSharpClock244
      hH3 hClass (τ n) (hτ n) n (hCube n)
  choose N K C δ hAll using hChoice
  refine ⟨τ, N, K, C, δ, hτ, hLimit, ?_⟩
  intro n
  rcases hAll n with ⟨hnN, hK, hC, hδ, hEnd, hExact, hFloor, hGap⟩
  exact ⟨hnN, hK, hC, hδ, hEnd,
    (by simpa only [h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hExact),
    hFloor, (by simpa only [h3PathCubicAnnulusActualGap244] using hGap)⟩

/-- Actual physical no-terminal-L²-trace cubic windows, assuming
finite full terminal H³ dissipation, obey the **quadratically sharp**
three-scale obstruction: terminal time compression, linear sixth-order
rate growth, or quadratic ninth-order rate growth. No branch is excluded. -/
theorem h3Path_noL2Trace_finiteDissipation_quadraticSharpThreeScale244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 6 ≤
          16 * ε * (h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1) ∨
        ((v k : ℝ) + 1) ^ 9 ≤
          16 * ε ^ 2 *
            (h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_forces_quarterGapQuadraticSharpClocks244
      hH3 hClass hMass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hAll n with ⟨_, _, _, hp, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hAll n with ⟨_, _, _, _, he, _, _, _⟩
    exact he
  obtain ⟨v, hv, hCofinal, hSeparate⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  let M : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  have hBound : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤ M := by
    have hFloor (k : ℕ) (r : ℝ)
        (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
        ((v k : ℝ) + 1) ^ 3 / 2 ≤ velocityH3DissipationAt u r := by
      rcases hAll (v k) with ⟨_, _, _, _, hb, _, hAnnulus, _⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
          lt_of_le_of_lt hr.2 hb⟩
      exact (hAnnulus r hr).le.trans
        (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
          hH3 hClass r hrClass ((v k : ℝ) + 1)
            ((N (v k) : ℝ) + 1))
    have hSum := h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      (fun k => ((v k : ℝ) + 1) ^ 3 / 2)
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt
      (fun k => (hTime (v k)).1.le)
      (fun k => (hδ (v k)).le)
      (fun k => (hEnd (v k)).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
      hFloor
    simpa only [M] using hSum
  have hΛ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C n := by
    unfold h3PathCubicAnnulusActualLinearRate244
    rcases hAll n with ⟨_, hK, hC, _, _, _, _, _⟩
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n) hK hC
  have hΞ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C n := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    exact (hAll (v k)).2.2.2.2.2.1
  let f : ℕ → ℝ := fun k =>
    δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)
  have hf (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact mul_nonneg (hδ (v k)).le (by positivity)
  have hSummable : Summable f :=
    h3Path_nonnegativeBoundedRangeSums_summable244 f M hf
      (by simpa only [f] using hBound)
  have hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) := by
    have hTwice := hSummable.tendsto_atTop_zero.const_mul (2 : ℝ)
    have hEq : (fun k : ℕ =>
        δ (v k) * ((v k : ℝ) + 1) ^ 3) =
        (fun k : ℕ => 2 * f k) := by
      funext k
      dsimp only [f]
      ring
    rw [hEq]
    simpa only [mul_zero] using hTwice
  have hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤
        h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    apply Filter.Eventually.of_forall
    intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg.le
  have hΛEv : ∀ᶠ k : ℕ in atTop,
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C (v k) :=
    Filter.Eventually.of_forall (fun k => hΛ (v k))
  have hΞEv : ∀ᶠ k : ℕ in atTop,
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C (v k) :=
    Filter.Eventually.of_forall (fun k => hΞ (v k))
  have hBarrier := h3Path_exactQuadraticSharpClocks_threeScaleBarrier244
    v δ (fun n => (T - τ n) / 2)
    (h3PathCubicAnnulusActualGap244 hH3 τ N)
    (h3PathCubicAnnulusActualLinearRate244 N K C)
    (h3PathCubicAnnulusActualQuadraticRate244 N C)
    hv hExact hCollapse hQuarter hΛEv hΞEv
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, ?_, ?_, hBarrier⟩
  · intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg
  · simpa only [f] using hSummable


end
end PrimeTensor.FirstMonomialTriad
