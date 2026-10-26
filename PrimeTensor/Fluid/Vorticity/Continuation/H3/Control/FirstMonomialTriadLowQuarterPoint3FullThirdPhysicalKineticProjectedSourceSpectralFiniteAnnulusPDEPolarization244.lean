import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEGradientTransfer244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusQuantitativeModulus244
import Mathlib.Tactic

/-!
# Physical projected-PDE control of finite-annulus H³ dissipation variations

The actual physical momentum PDE provides a bounded-radius Fourier gradient
*square* increment estimate. Here we take its square root on each coordinate,
polarize the gradient quadratic, and combine both annulus radii.  Crucially,
we never replace a bounded-band gradient increment by the full H³ difference.

For a physical projected-source ceiling C, a weighted spectral coordinate
ceiling K and a nonnegative cutoff rho, the low-radial dissipation satisfies

 |D_<rho(S(s)) - D_<rho(S(t))|
   <= 6 (rho+1)^2 K sqrt(3 W(rho)) C (t-s),

 W(rho) = 1 + rho^2 + rho^4 + rho^6.

The finite annular quadratic is the difference of the two low-radial
quadratics.  Its explicit modulus yields an amplitude-duration criterion and
an integrated lower bound, without assuming a full unbounded H³ derivative.
The source and spectral envelope constants remain window-dependent.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Polarization of the *localized* gradient quadratic, assuming only
localized multiplier differences. No bound on `‖G-H‖` is required. -/
theorem h3Path_lowRadialDissipation_multiplierIncrementStability244
    (ρ K ε : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (G H : H3SpectralVelocityState)
    (hG : ∀ j : Fin 3, ‖G j‖ ≤ K)
    (hH : ∀ j : Fin 3, ‖H j‖ ≤ K)
    (hDiff : ∀ j : Fin 3,
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j - H j)‖ ≤ ε) :
    |h3PathActualLowRadialDissipation244 ρ G -
      h3PathActualLowRadialDissipation244 ρ H| ≤
        6 * (ρ + 1) * K * ε := by
  let M := h3PathLowRadialGradientMultiplierCLM244 ρ hρ
  let F : H3SpectralScalarState → ℝ := fun x => ‖M x‖ ^ 2
  have hFactor : 0 ≤ ρ + 1 := by linarith only [hρ]
  have hEach (j : Fin 3) :
      |F (G j) - F (H j)| ≤ 2 * (ρ + 1) * K * ε := by
    have hMG : ‖M (G j)‖ ≤ (ρ + 1) * K := by
      calc
        ‖M (G j)‖ ≤ (ρ + 1) * ‖G j‖ :=
          h3Path_lowRadialGradientMultiplierApply_norm_le244 ρ hρ (G j)
        _ ≤ (ρ + 1) * K := mul_le_mul_of_nonneg_left (hG j) hFactor
    have hMH : ‖M (H j)‖ ≤ (ρ + 1) * K := by
      calc
        ‖M (H j)‖ ≤ (ρ + 1) * ‖H j‖ :=
          h3Path_lowRadialGradientMultiplierApply_norm_le244 ρ hρ (H j)
        _ ≤ (ρ + 1) * K := mul_le_mul_of_nonneg_left (hH j) hFactor
    have hSum : ‖M (G j)‖ + ‖M (H j)‖ ≤ 2 * (ρ + 1) * K := by
      linarith only [hMG, hMH]
    have hSumNonneg : 0 ≤ ‖M (G j)‖ + ‖M (H j)‖ := by positivity
    have hMD : ‖M (G j) - M (H j)‖ ≤ ε := by
      rw [← map_sub]
      exact hDiff j
    change |‖M (G j)‖ ^ 2 - ‖M (H j)‖ ^ 2| ≤
      2 * (ρ + 1) * K * ε
    calc
      |‖M (G j)‖ ^ 2 - ‖M (H j)‖ ^ 2| =
          |‖M (G j)‖ - ‖M (H j)‖| *
            (‖M (G j)‖ + ‖M (H j)‖) := by
              rw [sq_sub_sq, abs_mul, abs_of_nonneg hSumNonneg]
              ac_rfl
      _ ≤ ‖M (G j) - M (H j)‖ *
            (‖M (G j)‖ + ‖M (H j)‖) :=
          mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) hSumNonneg
      _ ≤ ε * (‖M (G j)‖ + ‖M (H j)‖) :=
          mul_le_mul_of_nonneg_right hMD hSumNonneg
      _ ≤ ε * (2 * (ρ + 1) * K) :=
          mul_le_mul_of_nonneg_left hSum hε
      _ = 2 * (ρ + 1) * K * ε := by ring
  rw [h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ G,
      h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ H]
  simp only [Fin.sum_univ_three]
  change |(F (G 0) + F (G 1) + F (G 2)) -
    (F (H 0) + F (H 1) + F (H 2))| ≤ 6 * (ρ + 1) * K * ε
  calc
    |(F (G 0) + F (G 1) + F (G 2)) -
        (F (H 0) + F (H 1) + F (H 2))| =
        |(F (G 0) - F (H 0)) +
          ((F (G 1) - F (H 1)) + (F (G 2) - F (H 2)))| := by
            congr 1 <;> ring
    _ ≤ |F (G 0) - F (H 0)| +
          (|F (G 1) - F (H 1)| + |F (G 2) - F (H 2)|) := by
            exact
              (abs_add_le
                (F (G 0) - F (H 0))
                ((F (G 1) - F (H 1)) + (F (G 2) - F (H 2)))).trans
              (add_le_add_right
                (abs_add_le (F (G 1) - F (H 1))
                  (F (G 2) - F (H 2)))
                |F (G 0) - F (H 0)|)
    _ ≤ 6 * (ρ + 1) * K * ε := by
      have h0 := hEach (0 : Fin 3)
      have h1 := hEach (1 : Fin 3)
      have h2 := hEach (2 : Fin 3)
      linarith only [h0, h1, h2]

/-- The already-verified PDE bound on the sum of three multiplier increment
squares yields a linear-time upper bound on each multiplier increment. -/
theorem h3Path_actualLowRadialGradientIncrement_norm_le_PDECeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (j : Fin 3) :
    ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ
      ((h3AuditActualSpectralVelocityTotal hH3 s) j -
       (h3AuditActualSpectralVelocityTotal hH3 t) j)‖ ≤
      (ρ + 1) *
        Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
        (C * (t - s)) := by
  let M := h3PathLowRadialGradientMultiplierCLM244 ρ hρ
  let G := h3AuditActualSpectralVelocityTotal hH3 s
  let H := h3AuditActualSpectralVelocityTotal hH3 t
  let W : ℝ := 3 * h3TerminalRadialSobolevWeightSquareCeiling ρ
  let Δ : ℝ := C * (t - s)
  let L : ℝ := (ρ + 1) * Real.sqrt W * Δ
  have hC : 0 ≤ C := by
    have hb := hCeil s ⟨le_rfl, hst⟩
    exact (norm_nonneg _).trans hb
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact mul_nonneg (by norm_num)
      (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le
  have hL : 0 ≤ L := by
    dsimp only [L, Δ]
    positivity
  have hLSq : L ^ 2 =
      (ρ + 1) ^ 2 *
        ((3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
          (C * (t - s)) ^ 2) := by
    dsimp only [L, W, Δ]
    rw [mul_pow, mul_pow, Real.sq_sqrt hW]
    ring
  have hTotal := h3Path_actualLowRadialGradientIncrementSquare_le_PDECeiling244
    hH3 ρ hρ s t C hs ht hst hCeil
  have hNonneg (i : Fin 3) : 0 ≤ ‖M (G i - H i)‖ ^ 2 := sq_nonneg _
  have hEach (i : Fin 3) :
      ‖M (G i - H i)‖ ^ 2 ≤
        ∑ k : Fin 3, ‖M (G k - H k)‖ ^ 2 := by
    fin_cases i <;> simp only [Fin.sum_univ_three]
    · change ‖M (G (0 : Fin 3) - H 0)‖ ^ 2 ≤
        ‖M (G 0 - H 0)‖ ^ 2 + ‖M (G 1 - H 1)‖ ^ 2 +
          ‖M (G 2 - H 2)‖ ^ 2
      nlinarith only [hNonneg 1, hNonneg 2]
    · change ‖M (G (1 : Fin 3) - H 1)‖ ^ 2 ≤
        ‖M (G 0 - H 0)‖ ^ 2 + ‖M (G 1 - H 1)‖ ^ 2 +
          ‖M (G 2 - H 2)‖ ^ 2
      nlinarith only [hNonneg 0, hNonneg 2]
    · change ‖M (G (2 : Fin 3) - H 2)‖ ^ 2 ≤
        ‖M (G 0 - H 0)‖ ^ 2 + ‖M (G 1 - H 1)‖ ^ 2 +
          ‖M (G 2 - H 2)‖ ^ 2
      nlinarith only [hNonneg 0, hNonneg 1]
  have hSq : ‖M (G j - H j)‖ ^ 2 ≤ L ^ 2 := by
    calc
      _ ≤ ∑ k : Fin 3, ‖M (G k - H k)‖ ^ 2 := hEach j
      _ ≤ (ρ + 1) ^ 2 *
          ((3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
            (C * (t - s)) ^ 2) := hTotal
      _ = L ^ 2 := hLSq.symm
  exact (sq_le_sq₀ (norm_nonneg _) hL).mp hSq

/-- Explicit *physical-PDE* temporal modulus for low-radial H³
spectral dissipation. The only state bound is the two-time H³ snapshot
coordinate ceiling, and the only time bound is the actual PDE source. -/
theorem h3Path_actualLowRadialDissipationVariation_le_PDECeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ K : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hG : ∀ j : Fin 3, ‖(h3AuditActualSpectralVelocityTotal hH3 s) j‖ ≤ K)
    (hH : ∀ j : Fin 3, ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    |h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t)| ≤
      6 * (ρ + 1) ^ 2 * K *
        Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
        (C * (t - s)) := by
  have hC : 0 ≤ C := by
    have hb := hCeil s ⟨le_rfl, hst⟩
    exact (norm_nonneg _).trans hb
  have hε : 0 ≤
      (ρ + 1) *
        Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
        (C * (t - s)) := by positivity
  have hBound :=
    h3Path_lowRadialDissipation_multiplierIncrementStability244
      ρ K
      ((ρ + 1) * Real.sqrt
        (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
        (C * (t - s)))
      hρ hK hε
      (h3AuditActualSpectralVelocityTotal hH3 s)
      (h3AuditActualSpectralVelocityTotal hH3 t)
      hG hH
      (fun j => h3Path_actualLowRadialGradientIncrement_norm_le_PDECeiling244
        hH3 ρ hρ s t C hs ht hst hCeil j)
  calc
    _ ≤ 6 * (ρ + 1) * K *
        ((ρ + 1) *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
          (C * (t - s))) := hBound
    _ = 6 * (ρ + 1) ^ 2 * K *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
          (C * (t - s)) := by ring

/-- Explicit nonnegative annular temporal coefficient: an actual physical
PDE source ceiling C and three weighted spectral coordinate ceiling K
control the annular quadratic with this cutoff-dependent rate. -/
noncomputable def h3PathFiniteAnnulusPDEVariationCoefficient244
    (R Q K C : ℝ) : ℝ :=
  6 * K * C *
    ((Q + 1) ^ 2 *
      Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) +
     (R + 1) ^ 2 *
      Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R))

theorem h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
    (R Q K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    0 ≤ h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C := by
  unfold h3PathFiniteAnnulusPDEVariationCoefficient244
  positivity

/-- Finite-annulus dissipation is Lipschitz on the selected strict
physical interval with a completely explicit projected-PDE source coefficient.
This does not assume continuity of the unbounded full H³ dissipation. -/
theorem h3Path_actualFiniteAnnulusDissipationVariation_le_PDECeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R Q K : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hG : ∀ j : Fin 3, ‖(h3AuditActualSpectralVelocityTotal hH3 s) j‖ ≤ K)
    (hH : ∀ j : Fin 3, ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    |(h3PathActualLowRadialDissipation244 Q
         (h3AuditActualSpectralVelocityTotal hH3 s) -
       h3PathActualLowRadialDissipation244 R
         (h3AuditActualSpectralVelocityTotal hH3 s)) -
      (h3PathActualLowRadialDissipation244 Q
         (h3AuditActualSpectralVelocityTotal hH3 t) -
       h3PathActualLowRadialDissipation244 R
         (h3AuditActualSpectralVelocityTotal hH3 t))| ≤
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * (t - s) := by
  have hQDiff := h3Path_actualLowRadialDissipationVariation_le_PDECeiling244
    hH3 Q K hQ hK s t C hs ht hst hG hH hCeil
  have hRDiff := h3Path_actualLowRadialDissipationVariation_le_PDECeiling244
    hH3 R K hR hK s t C hs ht hst hG hH hCeil
  calc
    |(h3PathActualLowRadialDissipation244 Q
         (h3AuditActualSpectralVelocityTotal hH3 s) -
       h3PathActualLowRadialDissipation244 R
         (h3AuditActualSpectralVelocityTotal hH3 s)) -
      (h3PathActualLowRadialDissipation244 Q
         (h3AuditActualSpectralVelocityTotal hH3 t) -
       h3PathActualLowRadialDissipation244 R
         (h3AuditActualSpectralVelocityTotal hH3 t))| =
        |(h3PathActualLowRadialDissipation244 Q
             (h3AuditActualSpectralVelocityTotal hH3 s) -
           h3PathActualLowRadialDissipation244 Q
             (h3AuditActualSpectralVelocityTotal hH3 t)) -
          (h3PathActualLowRadialDissipation244 R
             (h3AuditActualSpectralVelocityTotal hH3 s) -
           h3PathActualLowRadialDissipation244 R
             (h3AuditActualSpectralVelocityTotal hH3 t))| := by
               congr 1 <;> ring
    _ ≤ |h3PathActualLowRadialDissipation244 Q
             (h3AuditActualSpectralVelocityTotal hH3 s) -
           h3PathActualLowRadialDissipation244 Q
             (h3AuditActualSpectralVelocityTotal hH3 t)| +
          |h3PathActualLowRadialDissipation244 R
             (h3AuditActualSpectralVelocityTotal hH3 s) -
           h3PathActualLowRadialDissipation244 R
             (h3AuditActualSpectralVelocityTotal hH3 t)| := by
             simpa only [sub_eq_add_neg, abs_neg] using
               (abs_add_le
                 (h3PathActualLowRadialDissipation244 Q
                   (h3AuditActualSpectralVelocityTotal hH3 s) -
                  h3PathActualLowRadialDissipation244 Q
                   (h3AuditActualSpectralVelocityTotal hH3 t))
                 (-(h3PathActualLowRadialDissipation244 R
                   (h3AuditActualSpectralVelocityTotal hH3 s) -
                   h3PathActualLowRadialDissipation244 R
                   (h3AuditActualSpectralVelocityTotal hH3 t))))
    _ ≤ 6 * (Q + 1) ^ 2 * K *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) *
          (C * (t - s)) +
        6 * (R + 1) ^ 2 * K *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R) *
          (C * (t - s)) := add_le_add hQDiff hRDiff
    _ = h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C *
          (t - s) := by
            unfold h3PathFiniteAnnulusPDEVariationCoefficient244
            ring

/-- Quantitative persistence and interval cost of the actual finite-annulus
physical H³ dissipation, using only the selected physical projected source
ceiling and weighted spectral envelope. The source ceiling is not asserted
uniform as the terminal point is approached. -/
theorem h3Path_actualFiniteAnnulus_integratedCost_of_PDECeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R Q K C A t δ : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (ht : t ∈ Set.Ioo a T) (hδ : 0 < δ) (hEnd : t + δ < T)
    (hEnvelope : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ∀ j : Fin 3, ‖(h3AuditActualSpectralVelocityTotal hH3 s) j‖ ≤ K)
    (hSource : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C)
    (hHeight : A <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t))
    (hWidthBudget :
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ <
        (h3PathActualLowRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 t) -
         h3PathActualLowRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 t)) - A) :
    (∀ s : ℝ, s ∈ Set.Icc t (t + δ) → A <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
    δ * A ≤
      (∫ s in t..(t + δ),
        h3PathActualLowRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        h3PathActualLowRadialDissipation244 R
          (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  let G : ℝ → H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3
  let B : ℝ → ℝ := fun s =>
    h3PathActualLowRadialDissipation244 Q (G s) -
    h3PathActualLowRadialDissipation244 R (G s)
  have hC : 0 ≤ C := by
    have hSrc := hSource t ⟨le_rfl, by linarith only [hδ]⟩
    exact (norm_nonneg _).trans hSrc
  have hΛ : 0 ≤ h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 R Q K C hK hC
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hBase : ∀ j : Fin 3, ‖G t j‖ ≤ K :=
    hEnvelope t ⟨le_rfl, by linarith only [hδ]⟩
  have hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) → A < B s := by
    intro s hs
    have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le htAbs.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
    have hTimeδ : s - t ≤ δ := by linarith only [hs.2]
    have hDiff := h3Path_actualFiniteAnnulusDissipationVariation_le_PDECeiling244
      hH3 R Q K hR hQ hK t s C htAbs hsAbs hs.1 hBase (hEnvelope s hs)
      (fun r hr => hSource r ⟨hr.1, le_trans hr.2 hs.2⟩)
    have hError : B t - B s ≤
        h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * (s - t) := by
      change |B t - B s| ≤ _ at hDiff
      exact (le_abs_self (B t - B s)).trans hDiff
    have hMaxError :
        h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * (s - t) ≤
          h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ :=
      mul_le_mul_of_nonneg_left hTimeδ hΛ
    change h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ <
      B t - A at hWidthBudget
    linarith only [hError, hMaxError, hWidthBudget]
  have hSub : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hB : ContinuousOn B (Set.Ioo a T) := by
    exact h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass R Q hR hQ
  have hInt : IntervalIntegrable B volume t (t + δ) :=
    (hB.mono hSub).intervalIntegrable_of_Icc (by linarith only [hδ])
  have hIntegral := h3Path_localPositiveHeight_forces_integratedCost244
    B t (t + δ) A (by linarith only [hδ]) hInt
    (fun s hs => (hFloor s hs).le)
  constructor
  · exact hFloor
  · change δ * A ≤ ∫ s in t..(t + δ), B s
    calc
      δ * A = ((t + δ) - t) * A := by ring
      _ ≤ ∫ s in t..(t + δ), B s := hIntegral

end
end PrimeTensor.FirstMonomialTriad
