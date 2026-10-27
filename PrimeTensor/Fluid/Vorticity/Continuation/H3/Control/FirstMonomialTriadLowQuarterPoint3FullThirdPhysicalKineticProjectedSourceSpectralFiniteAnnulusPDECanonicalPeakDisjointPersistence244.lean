import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalHighRadialDissipationCost244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceMeasurability
import Mathlib.Tactic

/-!
# Peak-centred physical H³ persistence and disjoint time-integral cost

The actual strict-time weighted spectral state is strongly continuous.  At a
peak `s`, the spectral norm therefore changes by less than one on some
positive right-hand interval. The fixed kinetic bound controls the H³ mass
inside every fixed radial carrier, so the complementary *integrated* mass
has an explicit floor on that interval:

  HighMass_ρ(U(r)) >= max 0 ((max 0 (‖U(s)‖-1))² - K(ρ) E₀(b)).

For a cofinal sequence of actual spectral peaks with diverging norm, the
floor diverges.  Positive right-hand persistence intervals can be chosen
at each peak, then a strictly increasing subsequence gives *disjoint*
intervals. Actual finite terminal H³ dissipation bounds their finite costs
and forces their widths to zero. No uniform persistence time or divergent
sum of costs is claimed; the disjoint peak windows are distinct from the
original quadratic-sharp annulus windows.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeCanonicalPeakDisjointPersistence244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCanonicalPeakDisjointPersistence244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A spectral norm peak has a positive, strictly preterminal, one-sided
neighborhood where the actual weighted spectral state changes by less than
one. The neighborhood's width is allowed to depend on the peak. -/
theorem h3Path_strictSpectralPeak_unitIncrementWindow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ∃ δ : ℝ, 0 < δ ∧ s + δ < T ∧
      ∀ r : ℝ, r ∈ Set.Icc s (s + δ) →
        ‖h3AuditActualSpectralVelocityTotal hH3 r -
          h3AuditActualSpectralVelocityTotal hH3 s‖ < 1 := by
  have hCont := h3Audit_initialActualSpectralVelocity_continuousAt hH3 hs
  obtain ⟨ε, hε, hClose⟩ :=
    (Metric.continuousAt_iff.mp hCont) 1 (by norm_num)
  let δ : ℝ := min (ε / 2) ((T - s) / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    apply lt_min
    · linarith only [hε]
    · linarith only [hs.2]
  have hEnd : s + δ < T := by
    have hHalf : δ ≤ (T - s) / 2 := min_le_right _ _
    linarith only [hs.2, hHalf]
  refine ⟨δ, hδ, hEnd, ?_⟩
  intro r hr
  have hDist : dist r s < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1)]
    have hSmall : δ ≤ ε / 2 := min_le_left _ _
    linarith only [hr.2, hSmall, hε]
  simpa only [dist_eq_norm] using hClose hDist

/-- A fixed physical kinetic ceiling plus unit spectral continuity yields
an explicit floor for genuine complementary Fourier H³ mass on a right-hand
interval around an arbitrary STRICT physical observation time. -/
theorem h3Path_strictPeak_localHighRadialMassFloor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s : ℝ) (hs : s ∈ Set.Ioo b T) :
    ∃ δ : ℝ, 0 < δ ∧ s + δ < T ∧
      ∀ r : ℝ, r ∈ Set.Icc s (s + δ) →
        max 0 ((max 0
          (‖h3AuditActualSpectralVelocityTotal hH3 s‖ - 1)) ^ 2 -
            h3TerminalRadialSobolevWeightSquareCeiling ρ *
              velocityH3Energy0At u b) ≤
        h3PathActualSpectralHighRadialRemainder244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 r) := by
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hs.1), hs.2⟩
  obtain ⟨δ, hδ, hEnd, hUnit⟩ :=
    h3Path_strictSpectralPeak_unitIncrementWindow244 hH3 s hsAbs
  refine ⟨δ, hδ, hEnd, ?_⟩
  intro r hr
  let G := h3AuditActualSpectralVelocityTotal hH3 r
  let P := h3AuditActualSpectralVelocityTotal hH3 s
  let A : ℝ := max 0 (‖P‖ - 1)
  let L : ℝ := h3TerminalRadialSobolevWeightSquareCeiling ρ *
    velocityH3Energy0At u b
  have hrClass : r ∈ Set.Ioo b T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
  have hNear : ‖G - P‖ < 1 := hUnit r hr
  have hTriangle : ‖P‖ ≤ ‖G‖ + ‖G - P‖ := by
    calc
      ‖P‖ = ‖G + (P - G)‖ := by
        congr 1
        abel
      _ ≤ ‖G‖ + ‖P - G‖ := norm_add_le _ _
      _ = ‖G‖ + ‖G - P‖ := by rw [norm_sub_rev]
  have hA : A ≤ ‖G‖ := by
    dsimp only [A]
    apply max_le (norm_nonneg G)
    linarith only [hTriangle, hNear]
  have hSq : A ^ 2 ≤ ‖G‖ ^ 2 :=
    pow_le_pow_left₀ (le_max_left (0 : ℝ) (‖P‖ - 1)) hA 2
  have hSpectral := h3Path_spectralSupNorm_sq_le_squareEnergy244 G
  have hLow : h3PathActualSpectralLowRadialSquareMass244 ρ G ≤ L := by
    dsimp only [G, L]
    exact h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
      hH3 hClass b hb ρ hρ r hrClass
  have hNonneg : 0 ≤ h3PathActualSpectralHighRadialRemainder244 ρ G :=
    h3Path_actualSpectralHighRadialRemainder_nonneg244 ρ G
  have hBase : A ^ 2 - L ≤
      h3PathActualSpectralHighRadialRemainder244 ρ G := by
    dsimp only [h3PathActualSpectralHighRadialRemainder244]
    linarith only [hSq, hSpectral, hLow]
  change max 0 (A ^ 2 - L) ≤
    h3PathActualSpectralHighRadialRemainder244 ρ G
  exact max_le hNonneg hBase

/-- The explicit nonnegative high-radial mass floor diverges with the
actual spectral SUP norm at its observation times. -/
theorem h3Path_peakSpectralEscape_forces_highFloorEscape244
    (A : ℕ → ℝ) (L : ℝ)
    (hPeak : Tendsto A atTop atTop) :
    Tendsto (fun k : ℕ =>
      max 0 ((max 0 (A k - 1)) ^ 2 - L)) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  have hLate : ∀ᶠ k : ℕ in atTop,
      max (M + L + 3) 2 ≤ A k :=
    hPeak.eventually (eventually_ge_atTop (max (M + L + 3) 2))
  filter_upwards [hLate] with k hk
  have hTwo : 2 ≤ A k := (le_max_right _ _).trans hk
  have hBig : M + L + 3 ≤ A k := (le_max_left _ _).trans hk
  have hMax : max 0 (A k - 1) = A k - 1 :=
    max_eq_right (by linarith only [hTwo])
  rw [hMax]
  have hSq : A k - 1 ≤ (A k - 1) ^ 2 := by
    nlinarith only [hTwo, sq_nonneg (A k - 2)]
  have hBound : M ≤ (A k - 1) ^ 2 - L := by
    linarith only [hBig, hSq]
  exact hBound.trans (le_max_right _ _)

/-- A cofinal family of actual strict-time H³ spectral peaks can be given
positive local high-radial mass-persistence widths. A subsequence of these
NEW peak-centred windows is disjoint. Finite physical terminal dissipation
forces the selected widths to vanish, with all costs explicitly accounted.
This does not assert these windows agree with the quadratic-sharp annuli. -/
theorem h3Path_cofinalSpectralPeaks_disjointHighRadialCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (s : ℕ → ℝ) (hs : ∀ k, s k ∈ Set.Ioo b T)
    (hCofinal : Tendsto s atTop (𝓝 T))
    (hPeak : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop) :
    ∃ (δ H : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => s (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → s (v k) + δ (v k) < s (v l)) ∧
      (∀ k, 0 < δ (v k) ∧ s (v k) + δ (v k) < T) ∧
      (∀ k r, r ∈ Set.Icc (s (v k)) (s (v k) + δ (v k)) →
        H (v k) ≤ h3PathActualSpectralHighRadialRemainder244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      Tendsto (fun k => H (v k)) atTop atTop ∧
      Tendsto (fun k => δ (v k)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m, (∑ k ∈ Finset.range m,
        δ (v k) * (ρ ^ 2 * H (v k))) ≤
        ∫ r in a..T, velocityH3DissipationAt u r) := by
  let L : ℝ := h3TerminalRadialSobolevWeightSquareCeiling ρ *
    velocityH3Energy0At u b
  let H : ℕ → ℝ := fun k => max 0
    ((max 0 (‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ - 1)) ^ 2 - L)
  have hWindow (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ s k + δ < T ∧
      ∀ r : ℝ, r ∈ Set.Icc (s k) (s k + δ) →
        H k ≤ h3PathActualSpectralHighRadialRemainder244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 r) := by
    simpa only [H, L] using
      h3Path_strictPeak_localHighRadialMassFloor244
        hH3 hClass b hb ρ hρ.le (s k) (hs k)
  choose δ hδ hEnd hFloor using hWindow
  obtain ⟨v, hv, hVcofinal, hSeparate⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      s δ T hCofinal hδ hEnd
  have hHEscape : Tendsto (fun k => H (v k)) atTop atTop := by
    have hAll : Tendsto H atTop atTop := by
      dsimp only [H, L]
      exact h3Path_peakSpectralEscape_forces_highFloorEscape244
        (fun k => ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖)
        L hPeak
    exact hAll.comp hv.tendsto_atTop
  have hStart (k : ℕ) : a ≤ s (v k) :=
    (hb.1.trans (hs (v k)).1).le
  have hWidths (k : ℕ) : 0 ≤ δ (v k) := (hδ (v k)).le
  have hEnds (k : ℕ) : s (v k) + δ (v k) ≤ T := (hEnd (v k)).le
  have hAdjacent (k : ℕ) :
      s (v k) + δ (v k) ≤ s (v (k + 1)) :=
    (hSeparate k (k + 1) (Nat.lt_succ_self k)).le
  have hInside (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (s (v k)) (s (v k) + δ (v k))) :
      r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le (lt_trans hb.1 (hs (v k)).1) hr.1,
      lt_of_le_of_lt hr.2 (hEnd (v k))⟩
  have hCosts := h3Path_disjointHighRadialMassFloors_finiteDissipationCost244
    hH3 hClass hDInt ρ hρ.le
    (fun k => s (v k)) (fun k => δ (v k)) (fun k => H (v k))
    hStart hWidths hEnds hAdjacent hInside
    (fun k r hr => hFloor (v k) r hr)
  have hWidthCollapse := h3Path_disjointHighRadialMassEscape_forces_widthCollapse244
    hH3 hClass hDInt ρ hρ
    (fun k => s (v k)) (fun k => δ (v k)) (fun k => H (v k))
    hStart hWidths hEnds hAdjacent hInside
    (fun k r hr => hFloor (v k) r hr)
    (fun k => le_max_left (0 : ℝ) _)
    hHEscape
  exact ⟨δ, H, v, hv, hVcofinal, hSeparate,
    (fun k => ⟨hδ (v k), hEnd (v k)⟩),
    (fun k r hr => hFloor (v k) r hr),
    hHEscape, hWidthCollapse, hCosts⟩


/-- Removing a finite prefix preserves the same cofinal peak sequence.
Disjoint high-mass persistence windows are selected from that original
sequence rather than from a new family of physical source maxima. -/
theorem h3Path_eventuallyCofinalSpectralPeaks_disjointHighRadialCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (s : ℕ → ℝ) (hs : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T)
    (hCofinal : Tendsto s atTop (𝓝 T))
    (hPeak : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop) :
    ∃ (w : ℕ → ℕ) (δ H : ℕ → ℝ),
      StrictMono w ∧
      Tendsto (fun k => s (w k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → s (w k) + δ k < s (w l)) ∧
      (∀ k, 0 < δ k ∧ s (w k) + δ k < T) ∧
      (∀ k r, r ∈ Set.Icc (s (w k)) (s (w k) + δ k) →
        H k ≤ h3PathActualSpectralHighRadialRemainder244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      Tendsto H atTop atTop ∧
      Tendsto δ atTop (𝓝 (0 : ℝ)) ∧
      (∀ m, (∑ k ∈ Finset.range m, δ k * (ρ ^ 2 * H k)) ≤
        ∫ r in a..T, velocityH3DissipationAt u r) := by
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 hs
  let σ : ℕ → ℝ := fun k => s (k₀ + k)
  have hShift : Tendsto (fun k : ℕ => k₀ + k) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop n] with k hk
    omega
  have hσ (k : ℕ) : σ k ∈ Set.Ioo b T := by
    dsimp only [σ]
    exact hk₀ (k₀ + k) (by omega)
  have hσLimit : Tendsto σ atTop (𝓝 T) := by
    have hComposed :
        Tendsto (s ∘ (fun k : ℕ => k₀ + k)) atTop (𝓝 T) :=
      hCofinal.comp hShift
    have hEq : (s ∘ (fun k : ℕ => k₀ + k)) = σ := by
      funext k
      rfl
    rw [hEq] at hComposed
    exact hComposed
  have hσPeak : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (σ k)‖) atTop atTop := by
    have hComposed :
        Tendsto
          ((fun k : ℕ =>
              ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) ∘
            (fun k : ℕ => k₀ + k)) atTop atTop :=
      hPeak.comp hShift
    have hEq :
        ((fun k : ℕ =>
            ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) ∘
          (fun k : ℕ => k₀ + k)) =
        (fun k : ℕ =>
          ‖h3AuditActualSpectralVelocityTotal hH3 (σ k)‖) := by
      funext k
      rfl
    rw [hEq] at hComposed
    exact hComposed
  obtain ⟨δ, H, v, hv, hLimit, hSeparate, hPositive,
      hFloor, hHeight, hWidthZero, hCosts⟩ :=
    h3Path_cofinalSpectralPeaks_disjointHighRadialCost244
      hH3 hClass hDInt b hb ρ hρ σ hσ hσLimit hσPeak
  let w : ℕ → ℕ := fun k => k₀ + v k
  let d : ℕ → ℝ := fun k => δ (v k)
  let Q : ℕ → ℝ := fun k => H (v k)
  have hw : StrictMono w := by
    intro k l hkl
    dsimp only [w]
    have hlt := hv hkl
    omega
  refine ⟨w, d, Q, hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [w, σ] using hLimit
  · intro k l hkl
    simpa only [w, d, σ] using hSeparate k l hkl
  · intro k
    simpa only [w, d, σ] using hPositive k
  · intro k r hr
    have hr' : r ∈ Set.Icc (σ (v k)) (σ (v k) + δ (v k)) := by
      simpa only [w, d, σ] using hr
    exact hFloor k r hr'
  · simpa only [Q] using hHeight
  · simpa only [d] using hWidthZero
  · simpa only [d, Q] using hCosts

/-- Actual canonical projected-source maxima admit a further cofinal
subsequence with genuinely disjoint right-hand high-radial mass persistence
intervals in the EXPLICIT conditional critical-width regime. Their mass
floors diverge and their widths tend to zero under finite H³ dissipation.
The original quadratic-sharp annulus windows and witnesses are unchanged. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeaks_disjointMassPersistence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ ρ : ℝ, 0 < ρ →
        ∃ (w : ℕ → ℕ) (d H : ℕ → ℝ),
          StrictMono w ∧
          Tendsto (fun k => s (w k)) atTop (𝓝 T) ∧
          (∀ k l, k < l → s (w k) + d k < s (w l)) ∧
          (∀ k, 0 < d k ∧ s (w k) + d k < T) ∧
          (∀ k r, r ∈ Set.Icc (s (w k)) (s (w k) + d k) →
            H k ≤ h3PathActualSpectralHighRadialRemainder244 ρ
              (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
          Tendsto H atTop atTop ∧
          Tendsto d atTop (𝓝 (0 : ℝ)) ∧
          (∀ m, (∑ k ∈ Finset.range m, d k * (ρ ^ 2 * H k)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r)) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_finiteDissipation_canonicalWidth_fixedMaximizerJointEscape244
      hH3 hClass hTerminalMass hNoTrace hDInt
  have hsBefore (k : ℕ) : s k < T := by
    have hτT := (hTime (v k)).2
    have hMid : τ (v k) + (T - τ (v k)) / 2 < T := by
      linarith only [hτT]
    exact lt_of_le_of_lt (hPeak k).1.2 hMid
  have hsTendsto : Tendsto s atTop (𝓝 T) := by
    have hGap : Tendsto (fun k : ℕ => T - τ (v k))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub hCofinal :
        Tendsto (fun k : ℕ => T - τ (v k)) atTop (𝓝 (T - T)))
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    have hBound (k : ℕ) : ‖s k - T‖ ≤ T - τ (v k) := by
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hsBefore k).le)]
      linarith only [(hPeak k).1.1]
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun k => norm_nonneg (s k - T)))
      (Filter.Eventually.of_forall hBound) hGap
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η B D hη hB hD hRegime b hb ρ hρ
  have hPeakEscape : Tendsto (fun k =>
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖) atTop atTop :=
    (hJoint η B D hη hB hD hRegime).2
  have hsEventually : ∀ᶠ k : ℕ in atTop, s k ∈ Set.Ioo b T := by
    have hLate := hCofinal.eventually (Ioi_mem_nhds hb.2)
    filter_upwards [hLate] with k hk
    exact ⟨lt_of_lt_of_le hk (hPeak k).1.1, hsBefore k⟩
  exact h3Path_eventuallyCofinalSpectralPeaks_disjointHighRadialCost244
    hH3 hClass hDInt b hb ρ hρ s hsEventually hsTendsto hPeakEscape

end
end PrimeTensor.FirstMonomialTriad
