import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileAnnularPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECofinalWindows244
import Mathlib.Tactic

/-!
# Exact anchored physical PDE clocks for arbitrary terminal H³ viscous heights

An actual high-radial H³ dissipation snapshot at any positive threshold A
admits a finite annulus of height > A/2. The genuine physical Hilbert FTC,
actual projected source ceiling, and the already-established anchored
polarization inequality yield a window of explicitly chosen width

  min((T-t)/4, 1, (initial annular height - A/4)/(2*(Lambda+Xi+1))).

Both the physical coefficient and the initial H³ state are the actual ones.
The positive quarter-height persists throughout this specific interval.
No frequency-uniform source ceiling or temporal regularity is added.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeProfileAnchored244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact version of the positive quadratic clock: keep the chosen minimum,
not merely the existence of an unspecified sufficiently small width. -/
theorem thirdFull_positiveQuadraticPDEMinClock244
    (b Λ Ξ gap : ℝ) (hb : 0 < b)
    (hΛ : 0 ≤ Λ) (hΞ : 0 ≤ Ξ) (hgap : 0 < gap) :
    let δ : ℝ := min (b / 2) (min (1 : ℝ)
      (gap / (2 * (Λ + Ξ + 1))))
    0 < δ ∧ δ < b ∧ δ ≤ 1 ∧
      Λ * δ + Ξ * δ ^ 2 < gap := by
  let Z : ℝ := Λ + Ξ + 1
  have hZ : 0 < Z := by
    dsimp only [Z]
    linarith only [hΛ, hΞ]
  let δ : ℝ := min (b / 2) (min (1 : ℝ) (gap / (2 * Z)))
  have hδ : 0 < δ := by
    dsimp only [δ]
    apply lt_min
    · linarith only [hb]
    · apply lt_min
      · norm_num
      · positivity
  have hδb : δ ≤ b / 2 := by
    dsimp only [δ]
    exact min_le_left _ _
  have hδone : δ ≤ 1 := by
    dsimp only [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδgap : δ ≤ gap / (2 * Z) := by
    dsimp only [δ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hSquare : δ ^ 2 ≤ δ := by
    have hMul : 0 ≤ δ * (1 - δ) :=
      mul_nonneg hδ.le (by linarith only [hδone])
    nlinarith only [hMul]
  have hScaled : Z * δ ≤ gap / 2 := by
    calc
      Z * δ ≤ Z * (gap / (2 * Z)) :=
        mul_le_mul_of_nonneg_left hδgap hZ.le
      _ = gap / 2 := by field_simp [ne_of_gt hZ]
  have hQ : Ξ * δ ^ 2 ≤ Ξ * δ :=
    mul_le_mul_of_nonneg_left hSquare hΞ
  have hBudget : Λ * δ + Ξ * δ ^ 2 < gap := by
    have hUpper : Λ * δ + Ξ * δ ^ 2 ≤ Z * δ := by
      dsimp only [Z]
      nlinarith only [hQ, hδ]
    linarith only [hUpper, hScaled, hgap]
  exact ⟨hδ, by linarith only [hb, hδb], hδone, hBudget⟩

/-- Exact terminal PDE persistence width at a finite spectral annulus. -/
noncomputable def thirdFullProfileAnchoredPDEWidth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (n N : ℕ) (K C A : ℝ) : ℝ :=
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let B : ℝ :=
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1) G -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1) G
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244
    ((n : ℝ) + 1) ((N : ℝ) + 1) K C
  let Ξ : ℝ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
    ((n : ℝ) + 1) ((N : ℝ) + 1) C
  min ((T - t) / 4) (min (1 : ℝ)
    ((B - A / 4) / (2 * (Λ + Ξ + 1))))

/-- Actual anchored finite-band Navier--Stokes persistence. The width is
specified EXACTLY by the terminal half-clock and the physical source-driven
linear/quadratic rate, rather than chosen by abstract continuity alone. -/
theorem thirdFullPhysical_highRadialSnapshot_profileAnchoredPDEClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (A : ℝ) (hA : 0 < A)
    (hHigh : A < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ t + δ < T ∧
      (∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K) ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C) ∧
      (A / 2 < h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t)) ∧
      (δ = thirdFullProfileAnchoredPDEWidth244 hH3 t n N K C A) ∧
      (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C * δ +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C * δ ^ 2 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) - A / 4) ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        A / 4 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (δ * (A / 4) ≤
        ∫ s in t..(t + δ),
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨N, _η, hnN, hη, _hηEnd, hFloor, _hCost⟩ :=
    thirdFullPhysical_highRadialSnapshot_profileAnnularWindow244
      hH3 hClass t ht n A hA hHigh
  let R : ℝ := (n : ℝ) + 1
  let Q : ℝ := (N : ℝ) + 1
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let B : ℝ := h3PathActualLowRadialDissipation244 Q G -
    h3PathActualLowRadialDissipation244 R G
  let K : ℝ := ‖G‖
  let A₀ : ℝ := A / 4
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hK : 0 ≤ K := norm_nonneg G
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hBase : ∀ j : Fin 3, ‖G j‖ ≤ K := by
    intro j
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg G)).1 le_rfl j
  have hAt : A / 2 < B := by
    have htIn : t ∈ Set.Icc t (t + _η) := by
      exact ⟨le_rfl, by linarith only [hη]⟩
    simpa only [B, R, Q, G] using (hFloor t htIn).1
  have hGap : 0 < B - A₀ := by
    dsimp only [A₀]
    linarith only [hAt, hA]
  let b : ℝ := (t + T) / 2
  have ht0 : 0 < t := lt_trans hClass.terminal_start.1 ht.1
  have htb : t < b := by
    dsimp only [b]
    linarith only [ht.2]
  have hbT : b < T := by
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
  let δ : ℝ := min ((b - t) / 2) (min (1 : ℝ)
    ((B - A₀) / (2 * (Λ + Ξ + 1))))
  have hClock : 0 < δ ∧ δ < b - t ∧ δ ≤ 1 ∧
      Λ * δ + Ξ * δ ^ 2 < B - A₀ := by
    simpa only [δ] using
      (thirdFull_positiveQuadraticPDEMinClock244
        (b - t) Λ Ξ (B - A₀)
        (sub_pos.mpr htb) hΛ hΞ hGap)
  obtain ⟨hδ, hδb, hδone, hBudget⟩ := hClock
  have hEnd : t + δ < T := by
    linarith only [hδb, hbT]
  have hSourceWindow : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C := by
    intro s hs
    apply hSource s
    constructor
    · exact hs.1
    · linarith only [hs.2, hδb]
  have hWidthExact : δ = min ((T - t) / 4) (min (1 : ℝ)
      ((B - A₀) / (2 * (Λ + Ξ + 1)))) := by
    have hFirst : (b - t) / 2 = (T - t) / 4 := by
      dsimp only [b]
      ring
    dsimp only [δ]
    rw [hFirst]
  have hFinal :=
    h3Path_actualFiniteAnnulus_integratedCost_of_anchoredPDE244
      hH3 hClass R Q K C A₀ t δ hR hQ hK hA₀ ht hδ hEnd
      hBase hSourceWindow (show A₀ < B from sub_pos.mp hGap)
      hBudget
  refine ⟨N, K, C, δ, hnN, hK, hC, hδ, hδone, hEnd,
    hBase, hSourceWindow, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [B, R, Q, G] using hAt
  · simpa only [thirdFullProfileAnchoredPDEWidth244, B, R, Q, G, A₀, Λ, Ξ] using hWidthExact
  · simpa only [B, R, Q, G, A₀, Λ, Ξ] using hBudget
  · intro s hs
    simpa only [R, Q, A₀] using (hFinal.1 s hs)
  · simpa only [R, Q, A₀] using hFinal.2

end
end PrimeTensor.FirstMonomialTriad
