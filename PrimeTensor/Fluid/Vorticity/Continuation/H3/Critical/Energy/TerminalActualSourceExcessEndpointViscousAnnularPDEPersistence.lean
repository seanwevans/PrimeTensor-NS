import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularLocalization
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEPolarization244
import Mathlib.Tactic

/-!
# Quantitative physical-PDE persistence of a localized H³ annular spike

A finite radial annulus is continuous in physical time for a quantitative
reason: actual projected momentum controls its spectral gradient multiplier.
Combining the already-proved annular PDE variation coefficient with the
kinetic-anchor annular floor produces an EXPLICIT positive persistence
interval and an actual annular integral cost.

The lower persistence time depends on the selected source ceiling and the
selected spectral envelope. Neither is asserted bounded at terminal time.
The interval remains within its original separated fivefold source window.
This is a physical PDE consequence, not a terminal-uniform regularity claim.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A positive annular height A survives over an explicit right-hand
interval on which a nonnegative PDE variation rate cannot consume A.
The factor 1/2 in the rate guard leaves a strictly positive margin. -/
theorem h3Critical_scalar_annularPDE_positivePersistenceRadius
    (A Λ d : ℝ) (hA : 0 < A) (hΛ : 0 ≤ Λ) (hd : 0 < d) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d / 2 ∧
      δ = min (d / 2) (A / (2 * (Λ + 1))) ∧
      Λ * δ < A := by
  have hPlus : 0 < Λ + 1 := by linarith only [hΛ]
  let δ : ℝ := min (d / 2) (A / (2 * (Λ + 1)))
  have hPos : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by linarith only [hd])
      (div_pos hA (by positivity))
  have hFirst : δ ≤ d / 2 := min_le_left _ _
  have hSecond : δ ≤ A / (2 * (Λ + 1)) := min_le_right _ _
  have hBound : (Λ + 1) * δ ≤ A / 2 := by
    calc
      (Λ + 1) * δ ≤ (Λ + 1) * (A / (2 * (Λ + 1))) :=
        mul_le_mul_of_nonneg_left hSecond hPlus.le
      _ = A / 2 := by
        field_simp [ne_of_gt hPlus]
  have hRate : Λ * δ < A := by
    have hSmall : Λ * δ ≤ (Λ + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith : Λ ≤ Λ + 1) hPos.le
    linarith only [hSmall, hBound, hA]
  exact ⟨δ, hPos, hFirst, rfl, hRate⟩

/-- A genuine finite-band physical PDE source ceiling and bounded spectral
coordinates give a quantitative right-hand annular persistence radius.
The cost is an actual integral of the physical Fourier annulus, and its
pointwise upper bound is actual full physical H³ dissipation. -/
theorem h3Critical_physicalAnnulus_PDEControlledPositiveRightWindow
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R Q K C A x d : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hA : 0 < A)
    (hx : x ∈ Set.Ioo a T) (hd : 0 < d) (hEnd : x + d < T)
    (hEnvelope : ∀ r : ℝ, r ∈ Set.Icc x (x + d) →
      ∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 r) j‖ ≤ K)
    (hSource : ∀ r : ℝ, r ∈ Set.Icc x (x + d) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hPeak : 2 * A <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 x) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 x)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d / 2 ∧
      δ = min (d / 2)
        (A / (2 * (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C + 1))) ∧
      x + δ < T ∧
      (∀ r : ℝ, r ∈ Set.Icc x (x + δ) →
        A < h3PathActualLowRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 R
            (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        h3PathActualLowRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 R
            (h3AuditActualSpectralVelocityTotal hH3 r) ≤
          velocityH3DissipationAt u r) ∧
      δ * A ≤
        ∫ r in x..(x + δ),
          h3PathActualLowRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 R
            (h3AuditActualSpectralVelocityTotal hH3 r) := by
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C
  have hC : 0 ≤ C := by
    have hBound := hSource x ⟨le_rfl, le_add_of_nonneg_right hd.le⟩
    exact (norm_nonneg _).trans hBound
  have hΛ : 0 ≤ Λ :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 R Q K C hK hC
  obtain ⟨δ, hδ, hδHalf, hδEq, hRate⟩ :=
    h3Critical_scalar_annularPDE_positivePersistenceRadius A Λ d hA hΛ hd
  have hδLe : δ ≤ d := by linarith only [hδHalf, hd]
  have hEndSmall : x + δ < T := by linarith only [hδLe, hEnd]
  have hSmallEnvelope : ∀ r : ℝ, r ∈ Set.Icc x (x + δ) →
      ∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 r) j‖ ≤ K := by
    intro r hr
    exact hEnvelope r ⟨hr.1, le_trans hr.2 (by linarith only [hδLe])⟩
  have hSmallSource : ∀ r : ℝ, r ∈ Set.Icc x (x + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C := by
    intro r hr
    exact hSource r ⟨hr.1, le_trans hr.2 (by linarith only [hδLe])⟩
  have hHeight : A <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 x) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 x) := by
    linarith only [hPeak, hA]
  have hWidthBudget :
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ <
      (h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 x) -
       h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 x)) - A := by
    dsimp only [Λ] at hRate
    linarith only [hRate, hPeak]
  obtain ⟨hFloor, hCost⟩ :=
    h3Path_actualFiniteAnnulus_integratedCost_of_PDECeiling244
      hH3 hClass R Q K C A x δ hR hQ hK hA.le
      hx hδ hEndSmall hSmallEnvelope hSmallSource hHeight hWidthBudget
  have hFull (r : ℝ) (hr : r ∈ Set.Icc x (x + δ)) :
      h3PathActualLowRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 r) -
        h3PathActualLowRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 r) ≤
        velocityH3DissipationAt u r := by
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hx.1 hr.1, lt_of_le_of_lt hr.2 hEndSmall⟩
    exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass r hrClass R Q
  exact ⟨δ, hδ, hδHalf, by simpa only [Λ] using hδEq,
    hEndSmall, (fun r hr => ⟨hFloor r hr, hFull r hr⟩), hCost⟩

/-- A source window selected by the fivefold highpass construction already
has BOTH envelopes necessary for the explicit annular PDE persistence.
There is no requirement that the old arbitrarily chosen internal width η
itself obey a lower bound: this constructs a NEW PDE-certified subwindow. -/
theorem h3Critical_sourceWindow_activeAnnularSpike_PDEPersistence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (x w p η sSource sState L Q H : ℝ)
    (hx : x ∈ Set.Ioo b T) (hw : 0 < w) (hEnd : x + w < T)
    (hp : x ≤ p) (hη : 0 < η) (hpEnd : p + η ≤ x + w)
    (hMax : ∀ r : ℝ, r ∈ Set.Icc x (x + w) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
        ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 sState‖)
    (hL : 1 ≤ L) (hQ : 0 ≤ Q)
    (hSpike : H < h3PathActualLowRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 p))
    (hThreshold : 8 * velocityH3Energy0At u b * L ^ 8 < H) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (x + w - p) / 2 ∧
      δ = min ((x + w - p) / 2)
        ((H / 4) / (2 * (h3PathFiniteAnnulusPDEVariationCoefficient244
          L Q ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
          ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1))) ∧
      p + δ < T ∧
      (∀ r : ℝ, r ∈ Set.Icc p (p + δ) →
        H / 4 < h3PathActualLowRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 L
            (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        h3PathActualLowRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 L
            (h3AuditActualSpectralVelocityTotal hH3 r) ≤
          velocityH3DissipationAt u r) ∧
      δ * (H / 4) ≤
        ∫ r in p..(p + δ),
          h3PathActualLowRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 L
            (h3AuditActualSpectralVelocityTotal hH3 r) := by
  have hpTail : p ∈ Set.Ioo b T := by
    constructor
    · exact lt_of_lt_of_le hx.1 hp
    · exact lt_of_le_of_lt
        (le_trans (le_add_of_nonneg_right hη.le) hpEnd) hEnd
  have hpClass : p ∈ Set.Ioo a T := ⟨lt_trans hb.1 hpTail.1, hpTail.2⟩
  have hD : 0 < x + w - p := by linarith only [hη, hpEnd]
  have hEndD : p + (x + w - p) < T := by linarith only [hEnd]
  have hE0 : 0 ≤ velocityH3Energy0At u b := velocityH3Energy0At_nonneg u b
  have hHeightPos : 0 < H := by
    have hNonneg : 0 ≤ 8 * velocityH3Energy0At u b * L ^ 8 := by positivity
    exact lt_of_le_of_lt hNonneg hThreshold
  have hA : 0 < H / 4 := by positivity
  have hGap := (h3Critical_physicalLowRadialSpike_forces_halfHeightAnnulus
    hH3 hClass b hb p hpTail L Q H hL hSpike hThreshold).1
  have hHeight : 2 * (H / 4) <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 p) -
      h3PathActualLowRadialDissipation244 L
        (h3AuditActualSpectralVelocityTotal hH3 p) := by
    have hHalf : 2 * (H / 4) = H / 2 := by ring
    rw [hHalf]
    exact hGap
  have hSourceSub (r : ℝ) (hr : r ∈ Set.Icc p (p + (x + w - p))) :
      r ∈ Set.Icc x (x + w) := by
    have hRight : p + (x + w - p) = x + w := by ring
    exact ⟨le_trans hp hr.1, by rw [← hRight]; exact hr.2⟩
  have hEnvelope (r : ℝ) (hr : r ∈ Set.Icc p (p + (x + w - p)))
      (j : Fin 3) :
      ‖(h3AuditActualSpectralVelocityTotal hH3 r) j‖ ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 sState‖ := by
    exact (norm_le_pi_norm (h3AuditActualSpectralVelocityTotal hH3 r) j).trans
      (hMax r (hSourceSub r hr)).2
  have hSource (r : ℝ) (hr : r ∈ Set.Icc p (p + (x + w - p))) :
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
        ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ :=
    (hMax r (hSourceSub r hr)).1
  exact h3Critical_physicalAnnulus_PDEControlledPositiveRightWindow
    hH3 hClass L Q
    ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
    ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
    (H / 4) p (x + w - p)
    (by linarith only [hL]) hQ (norm_nonneg _) hA hpClass hD hEndD
    hEnvelope hSource hHeight

/-- The SAME fivefold cofinal source windows, source peaks and state maxima
now carry an explicit physically compelled right-hand persistence time for
any active high annular spike. This time depends on the actual projected
source maximum and spectral state maximum on that very window. The new
right-hand interval is contained in its ORIGINAL separated source window;
no overlap or unproved terminal-uniform modulus is introduced. -/
theorem h3Critical_noL2Trace_cofinalFivefold_PDEAnnularPersistenceGate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n)
    (R ε : ℕ → ℝ) (hR : ∀ k, 0 < R k) (hε : ∀ k, 0 < ε k)
    (L : ℕ → ℕ) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + w (v k) < t (v l)) ∧
      (∀ k : ℕ,
        8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
          R k ^ 2 * ε k ^ 2 / 8 →
        η k = 0 ∨
        ∃ θ : ℝ, 0 < θ ∧
          θ ≤ (t (v k) + w (v k) - p k) / 2 ∧
          θ = min ((t (v k) + w (v k) - p k) / 2)
            (((R k ^ 2 * ε k ^ 2 / 8) / 4) /
              (2 * (h3PathFiniteAnnulusPDEVariationCoefficient244
                ((L k : ℝ) + 1) ((N k : ℝ) + 1)
                ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
                ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ + 1))) ∧
          p k + θ < T ∧
          (∀ r : ℝ, r ∈ Set.Icc (p k) (p k + θ) →
            (R k ^ 2 * ε k ^ 2 / 8) / 4 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) -
              h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) -
              h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ≤
              velocityH3DissipationAt u r) ∧
          θ * ((R k ^ 2 * ε k ^ 2 / 8) / 4) ≤
            ∫ r in p k..(p k + θ),
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) -
              h3PathActualLowRadialDissipation244 ((L k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      (∀ k : ℕ,
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε k ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε k ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling (R k)) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (0 < η k ∧
          ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
            R k ^ 2 * ε k ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) := by
  obtain ⟨i, t, w, v, sSource, sState, A, B, δ, p, η, N,
      hv, hLimit, hSeparate, _hShortSep, _hInternalSep,
      _hSourceCosts, _hInternalCosts, hWindows, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_synchronizedEndpointViscousCosts
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε
  refine ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hSeparate, ?_, hGate⟩
  intro k hThreshold
  obtain ⟨ht, hw, hEnd, _hPeaks, _hsSource, _hsState, hMax,
    _hA, _hB, _hδ, _hδw, _hWidth, _hFloor,
    hp, hη, hpEnd, hSpike, hZero⟩ := hWindows k
  by_cases hInactive : η k = 0
  · exact Or.inl hInactive
  · right
    have hPositive : 0 < η k := by
      by_contra hNot
      have hNonpos : η k ≤ 0 := le_of_not_gt hNot
      exact hInactive (le_antisymm hNonpos hη)
    have hAtMax : R k ^ 2 * ε k ^ 2 <
        8 * velocityH3DissipationAt u (sState k) := by
      by_contra hNot
      exact hInactive (hZero hNot)
    have hpMem : p k ∈ Set.Icc (p k) (p k + η k) :=
      ⟨le_rfl, le_add_of_nonneg_right hη⟩
    have hCaptured : R k ^ 2 * ε k ^ 2 / 8 <
        h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (p k)) :=
      ((hSpike hAtMax).2 (p k) hpMem).1
    have hTail : t (v k) ∈ Set.Ioo b T :=
      ⟨lt_trans (hc (v k)).1 ht.1, ht.2⟩
    have hL : (1 : ℝ) ≤ (L k : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ (L k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    have hQ : (0 : ℝ) ≤ (N k : ℝ) + 1 := by positivity
    exact h3Critical_sourceWindow_activeAnnularSpike_PDEPersistence
      hH3 hClass b hb
      (t (v k)) (w (v k)) (p k) (η k)
      (sSource k) (sState k)
      ((L k : ℝ) + 1) ((N k : ℝ) + 1)
      (R k ^ 2 * ε k ^ 2 / 8)
      hTail hw hEnd hp hPositive hpEnd hMax hL hQ hCaptured hThreshold

end
end PrimeTensor.Bridge.Euclidean
