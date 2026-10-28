import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalCriticalSourceSpectralAmplification244
import Mathlib.Tactic

/-!
# Expose the exact physical H³ anchor coefficient in canonical annulus clocks

The previously exported canonical annulus constructor only carried `0 ≤ K`,
even though its proof deliberately selected `K = ‖U₃(t)‖` at the actual
physical anchor. That unexported equality prevents justified substitution
of the physical H³ energy into the source–spectral amplification theorem.

This theorem reconstructs the same minimal first-crossing annulus and sharp
physical PDE persistence clock with the exact norm inserted into the width
formula. It also identifies `K² ≤ E₃(t)`, using the genuine three-component
spectral-energy identity. No cofinal coefficient identity is claimed yet;
propagating this exact choice through the disjoint selection is separate work.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- An exact spectral anchor coefficient turns the product-square
amplification into a bound by the genuine physical H³ energy. -/
theorem h3Path_exactAnchor_productSquare_le_physicalEnergySource244
    (K C E : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKE : K ^ 2 ≤ E) :
    (K * C) ^ 2 ≤ E * C ^ 2 := by
  calc
    (K * C) ^ 2 = K ^ 2 * C ^ 2 := by ring
    _ ≤ E * C ^ 2 :=
      mul_le_mul_of_nonneg_right hKE (sq_nonneg C)

/-- The H³ spectral sup norm at a genuine strict preterminal snapshot
is controlled by its exact physical normalized H³ energy. -/
theorem h3Path_actualSpectralAnchor_sq_le_physicalEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
      velocityH3EnergyAt u t := by
  have hExact := h3AuditActualSpectralVelocityTotal_energy_exact hH3 t ht
  have hSup := h3Path_spectralSupNorm_sq_le_squareEnergy244
    (h3AuditActualSpectralVelocityTotal hH3 t)
  linarith only [hExact, hSup]

/-- Squaring the actual annular PDE rate and charging the exact
spectral anchor to physical H³ energy removes the independent witness
coefficient from the polynomial variation envelope. -/
theorem h3Path_exactAnchor_PDELinearRate_sq_le_energySource244
    (R Q K C E : ℝ)
    (hR : 0 ≤ R) (hRQ : R ≤ Q)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKE : K ^ 2 ≤ E) :
    (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C) ^ 2 ≤
      2304 * E * C ^ 2 * (Q + 1) ^ 10 := by
  have hQ : 0 ≤ Q := le_trans hR hRQ
  have hPDEpos : 0 ≤
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 R Q K C hK hC
  have hUpper := h3Path_finiteAnnulusPDEVariation_le_sourceSpectralFifth244
    R Q K C hR hRQ
  have hUpperNonneg : 0 ≤ 48 * |K * C| * (Q + 1) ^ 5 := by
    positivity
  have hSquare :
      (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C) ^ 2 ≤
        (48 * |K * C| * (Q + 1) ^ 5) ^ 2 :=
    (sq_le_sq₀ hPDEpos hUpperNonneg).2 hUpper
  have hProd : (K * C) ^ 2 ≤ E * C ^ 2 :=
    h3Path_exactAnchor_productSquare_le_physicalEnergySource244
      K C E hK hC hKE
  have hScale : (2304 * (Q + 1) ^ 10) * (K * C) ^ 2 ≤
      (2304 * (Q + 1) ^ 10) * (E * C ^ 2) :=
    mul_le_mul_of_nonneg_left hProd (by positivity)
  calc
    (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C) ^ 2 ≤
        (48 * |K * C| * (Q + 1) ^ 5) ^ 2 := hSquare
    _ = (2304 * (Q + 1) ^ 10) * (K * C) ^ 2 := by
      rw [abs_of_nonneg (mul_nonneg hK hC)]
      ring
    _ ≤ (2304 * (Q + 1) ^ 10) * (E * C ^ 2) := hScale
    _ = 2304 * E * C ^ 2 * (Q + 1) ^ 10 := by ring

/-- Canonical physical first-crossing annulus with a *literal* anchor
spectral coefficient, not merely an existential nonnegative K. The
source maximum is attained on the original half-terminal interval and
the actual sharp PDE clock retains its annular persistence floor. -/
theorem h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (C δ : ℝ),
      n ≤ N ∧ 0 ≤ C ∧
      C = h3PathActualProjectedSourceWindowEnvelope244 hH3
        t (t + (T - t) / 2) ∧
      (∃ s : ℝ, s ∈ Set.Icc t (t + (T - t) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C) ∧
      0 < δ ∧ t + δ < T ∧
      δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - t) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 t‖ C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C) ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
        velocityH3EnergyAt u t ∧
      (‖h3AuditActualSpectralVelocityTotal hH3 t‖ * C) ^ 2 ≤
        velocityH3EnergyAt u t * C ^ 2 := by
  obtain ⟨N, hnN, hHeight, _hMinimal⟩ :=
    h3Path_cubicHighSnapshot_has_minimalOuterAnnulus244
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
  let C : ℝ := h3PathActualProjectedSourceWindowEnvelope244 hH3 t (t + b)
  obtain ⟨sMax, hsMax, _hMax, hMaxEq⟩ :=
    h3Path_actualSourceWindowEnvelope_attained244 hH3 ht0 htb hbT
  have hC : 0 ≤ C := by
    dsimp only [C]
    rw [hMaxEq]
    exact norm_nonneg _
  have hSource : ∀ s : ℝ, s ∈ Set.Icc t (t + b) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C := by
    intro s hs
    exact h3Path_actualSourceWindowEnvelope_pointwise_le244
      hH3 ht0 htb hbT s hs
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
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hKenergy : K ^ 2 ≤ velocityH3EnergyAt u t := by
    dsimp only [K, G]
    exact h3Path_actualSpectralAnchor_sq_le_physicalEnergy244 hH3 t htAbs
  have hKCenergy : (K * C) ^ 2 ≤ velocityH3EnergyAt u t * C ^ 2 :=
    h3Path_exactAnchor_productSquare_le_physicalEnergySource244
      K C (velocityH3EnergyAt u t) hK hC hKenergy
  refine ⟨N, C, δ, hnN, hC, rfl, ?_, hδ, hEnd, ?_, hFinal.1, ?_, ?_⟩
  · refine ⟨sMax, hsMax, ?_⟩
    exact hMaxEq.symm
  · change δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 b (B - A) Λ Ξ
    exact hExact
  · simpa only [K, G] using hKenergy
  · simpa only [K, G] using hKCenergy

end
end PrimeTensor.FirstMonomialTriad
