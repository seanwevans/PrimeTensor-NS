import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEPolarization244
import Mathlib.Tactic

/-!
# PDE-controlled finite-annulus persistence without a future H³ spectral envelope

A physical L² projected source ceiling controls bounded-radius gradient
increments, but does not bound the future full H³ state. The previously
proved annular polarization lemma assumed a spectral ceiling at both ends.

Here the polarized quadratic is anchored at the initial Fourier snapshot:
  |‖M G‖² - ‖M H‖²| ≤ (2 K + ε) ε,
when ‖M G‖ ≤ K and ‖M(G-H)‖ ≤ ε. Applying the already-proved
localized projected-PDE increment bound gives a linear-plus-quadratic
annular variation cost. No future H³ spectral envelope is imposed.

The cost remains cutoff- and interval-dependent; it does not imply a
uniform terminal persistence width or integrated blowup.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Hilbert polarization anchored at one endpoint: only the *initial*
multiplier norm and the multiplier difference are needed. -/
theorem h3Path_lowRadialMultiplier_anchoredQuadraticStability244
    (ρ K ε : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (G H : H3SpectralScalarState)
    (hBase :
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ G‖ ≤ K)
    (hDiff :
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G - H)‖ ≤ ε) :
    |‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ G‖ ^ 2 -
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ H‖ ^ 2| ≤
      (2 * K + ε) * ε := by
  let M := h3PathLowRadialGradientMultiplierCLM244 ρ hρ
  have hFuture : ‖M H‖ ≤ K + ε := by
    calc
      ‖M H‖ = ‖M G + (M H - M G)‖ := by
        congr 1
        abel
      _ ≤ ‖M G‖ + ‖M H - M G‖ := norm_add_le _ _
      _ = ‖M G‖ + ‖M (G - H)‖ := by
        rw [norm_sub_rev, ← map_sub]
      _ ≤ K + ε := add_le_add hBase hDiff
  have hSum : ‖M G‖ + ‖M H‖ ≤ 2 * K + ε := by
    linarith only [hBase, hFuture]
  have hSumNonneg : 0 ≤ ‖M G‖ + ‖M H‖ := by positivity
  have hMDiff : ‖M G - M H‖ ≤ ε := by
    rw [← map_sub]
    exact hDiff
  change |‖M G‖ ^ 2 - ‖M H‖ ^ 2| ≤ (2 * K + ε) * ε
  calc
    |‖M G‖ ^ 2 - ‖M H‖ ^ 2| =
        |‖M G‖ - ‖M H‖| * (‖M G‖ + ‖M H‖) := by
          rw [sq_sub_sq, abs_mul, abs_of_nonneg hSumNonneg]
          ac_rfl
    _ ≤ ‖M G - M H‖ * (‖M G‖ + ‖M H‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) hSumNonneg
    _ ≤ ε * (‖M G‖ + ‖M H‖) :=
      mul_le_mul_of_nonneg_right hMDiff hSumNonneg
    _ ≤ ε * (2 * K + ε) := mul_le_mul_of_nonneg_left hSum hε
    _ = (2 * K + ε) * ε := by ring

/-- Three-coordinate anchored polarization of the actual low-radial H³
dissipation. The second spectral state is not assumed H³-bounded by K. -/
theorem h3Path_lowRadialDissipation_anchoredGradientStability244
    (ρ K ε : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (G H : H3SpectralVelocityState)
    (hBase : ∀ j : Fin 3,
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j)‖ ≤ K)
    (hDiff : ∀ j : Fin 3,
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j - H j)‖ ≤ ε) :
    |h3PathActualLowRadialDissipation244 ρ G -
      h3PathActualLowRadialDissipation244 ρ H| ≤
      3 * (2 * K + ε) * ε := by
  let M := h3PathLowRadialGradientMultiplierCLM244 ρ hρ
  let F : H3SpectralScalarState → ℝ := fun x => ‖M x‖ ^ 2
  have hEach (j : Fin 3) :
      |F (G j) - F (H j)| ≤ (2 * K + ε) * ε :=
    h3Path_lowRadialMultiplier_anchoredQuadraticStability244
      ρ K ε hρ hK hε (G j) (H j) (hBase j) (hDiff j)
  rw [h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ G,
    h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ H]
  simp only [Fin.sum_univ_three]
  change |(F (G 0) + F (G 1) + F (G 2)) -
    (F (H 0) + F (H 1) + F (H 2))| ≤ 3 * (2 * K + ε) * ε
  calc
    |(F (G 0) + F (G 1) + F (G 2)) -
        (F (H 0) + F (H 1) + F (H 2))| =
        |(F (G 0) - F (H 0)) +
          ((F (G 1) - F (H 1)) + (F (G 2) - F (H 2)))| := by
            congr 1 <;> ring
    _ ≤ |F (G 0) - F (H 0)| +
          (|F (G 1) - F (H 1)| + |F (G 2) - F (H 2)|) := by
            exact (abs_add_le
              (F (G 0) - F (H 0))
              ((F (G 1) - F (H 1)) + (F (G 2) - F (H 2)))).trans
              (add_le_add_right
                (abs_add_le (F (G 1) - F (H 1))
                  (F (G 2) - F (H 2)))
                |F (G 0) - F (H 0)|)
    _ ≤ 3 * (2 * K + ε) * ε := by
      have h0 := hEach (0 : Fin 3)
      have h1 := hEach (1 : Fin 3)
      have h2 := hEach (2 : Fin 3)
      linarith only [h0, h1, h2]

/-- Exact frequency-dependent rate of a localized gradient multiplier,
induced by the actual physical projected source. -/
noncomputable def h3PathLowRadialPDEGradientRate244 (ρ C : ℝ) : ℝ :=
  (ρ + 1) *
    Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) * C

theorem h3Path_lowRadialPDEGradientRate_nonneg244
    (ρ C : ℝ) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) :
    0 ≤ h3PathLowRadialPDEGradientRate244 ρ C := by
  unfold h3PathLowRadialPDEGradientRate244
  positivity

/-- Actual low-radial H³ dissipation has an anchored, linear-plus-quadratic
PDE modulus. Only the initial weighted spectral coordinates have a ceiling. -/
theorem h3Path_actualLowRadialDissipationVariation_anchoredPDE244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ K : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 s) j‖ ≤ K)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    |h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t)| ≤
      (6 * (ρ + 1) * K * h3PathLowRadialPDEGradientRate244 ρ C) *
        (t - s) +
      (3 * (h3PathLowRadialPDEGradientRate244 ρ C) ^ 2) *
        (t - s) ^ 2 := by
  let V : ℝ := h3PathLowRadialPDEGradientRate244 ρ C
  have hC : 0 ≤ C := by
    have hb := hCeil s ⟨le_rfl, hst⟩
    exact (norm_nonneg _).trans hb
  have hV : 0 ≤ V :=
    h3Path_lowRadialPDEGradientRate_nonneg244 ρ C hρ hC
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  have hε : 0 ≤ V * (t - s) := mul_nonneg hV hd
  have hInit (j : Fin 3) :
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ
        ((h3AuditActualSpectralVelocityTotal hH3 s) j)‖ ≤
        (ρ + 1) * K := by
    calc
      _ ≤ (ρ + 1) * ‖(h3AuditActualSpectralVelocityTotal hH3 s) j‖ :=
        h3Path_lowRadialGradientMultiplierApply_norm_le244
          ρ hρ ((h3AuditActualSpectralVelocityTotal hH3 s) j)
      _ ≤ (ρ + 1) * K :=
        mul_le_mul_of_nonneg_left (hBase j) (by linarith only [hρ])
  have hDiff (j : Fin 3) :
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ
        ((h3AuditActualSpectralVelocityTotal hH3 s) j -
         (h3AuditActualSpectralVelocityTotal hH3 t) j)‖ ≤
        V * (t - s) := by
    have h := h3Path_actualLowRadialGradientIncrement_norm_le_PDECeiling244
      hH3 ρ hρ s t C hs ht hst hCeil j
    simpa only [V, h3PathLowRadialPDEGradientRate244] using
      (show ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ
          ((h3AuditActualSpectralVelocityTotal hH3 s) j -
           (h3AuditActualSpectralVelocityTotal hH3 t) j)‖ ≤
          ((ρ + 1) *
            Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) * C) *
              (t - s) from by
            calc
              _ ≤ (ρ + 1) *
                Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
                  (C * (t - s)) := h
              _ = ((ρ + 1) *
                Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) * C) *
                  (t - s) := by ring)
  have hBound := h3Path_lowRadialDissipation_anchoredGradientStability244
    ρ ((ρ + 1) * K) (V * (t - s)) hρ
    (mul_nonneg (by linarith only [hρ]) hK) hε
    (h3AuditActualSpectralVelocityTotal hH3 s)
    (h3AuditActualSpectralVelocityTotal hH3 t)
    hInit hDiff
  calc
    _ ≤ 3 * (2 * ((ρ + 1) * K) + V * (t - s)) *
          (V * (t - s)) := hBound
    _ = (6 * (ρ + 1) * K * V) * (t - s) +
          (3 * V ^ 2) * (t - s) ^ 2 := by ring

/-- The genuinely quadratic correction to the old linear-in-time annular
PDE variation coefficient. It is nonnegative for every cutoff. -/
noncomputable def h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
    (R Q C : ℝ) : ℝ :=
  3 * ((h3PathLowRadialPDEGradientRate244 Q C) ^ 2 +
    (h3PathLowRadialPDEGradientRate244 R C) ^ 2)

theorem h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
    (R Q C : ℝ) :
    0 ≤ h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C := by
  unfold h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
  positivity

/-- Actual annular dissipation has a PDE-controlled modulus involving only
the spectral norm bound at the starting time, plus a quadratic time term.
No bound on the future full weighted H³ state is assumed. -/
theorem h3Path_actualFiniteAnnulusVariation_anchoredPDE244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R Q K : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 s) j‖ ≤ K)
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
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * (t - s) +
      h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C *
        (t - s) ^ 2 := by
  have hQD := h3Path_actualLowRadialDissipationVariation_anchoredPDE244
    hH3 Q K hQ hK s t C hs ht hst hBase hCeil
  have hRD := h3Path_actualLowRadialDissipationVariation_anchoredPDE244
    hH3 R K hR hK s t C hs ht hst hBase hCeil
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
    _ ≤ (6 * (Q + 1) * K * h3PathLowRadialPDEGradientRate244 Q C) *
          (t - s) +
        (3 * (h3PathLowRadialPDEGradientRate244 Q C) ^ 2) *
          (t - s) ^ 2 +
        ((6 * (R + 1) * K * h3PathLowRadialPDEGradientRate244 R C) *
          (t - s) +
        (3 * (h3PathLowRadialPDEGradientRate244 R C) ^ 2) *
          (t - s) ^ 2) := add_le_add hQD hRD
    _ = h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * (t - s) +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C *
          (t - s) ^ 2 := by
          unfold h3PathFiniteAnnulusPDEVariationCoefficient244
            h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            h3PathLowRadialPDEGradientRate244
          ring

/-- Anchored finite-annulus persistence with a physical projected-PDE ceiling.
Unlike the previous Lipschitz theorem, no future weighted H³ envelope is an
input: the rate incurs a nonnegative quadratic term in elapsed time. -/
theorem h3Path_actualFiniteAnnulus_integratedCost_of_anchoredPDE244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R Q K C A t δ : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (ht : t ∈ Set.Ioo a T) (hδ : 0 < δ) (hEnd : t + δ < T)
    (hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K)
    (hSource : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C)
    (hHeight : A <
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t))
    (hWidthBudget :
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ +
      h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C * δ ^ 2 <
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
  have hΞ : 0 ≤ h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C :=
    h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244 R Q C
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) → A < B s := by
    intro s hs
    have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le htAbs.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
    have hElapsed : 0 ≤ s - t := sub_nonneg.mpr hs.1
    have hElapsedLe : s - t ≤ δ := by linarith only [hs.2]
    have hElapsedSq : (s - t) ^ 2 ≤ δ ^ 2 :=
      pow_le_pow_left₀ hElapsed hElapsedLe 2
    have hDiff := h3Path_actualFiniteAnnulusVariation_anchoredPDE244
      hH3 R Q K hR hQ hK t s C htAbs hsAbs hs.1 hBase
      (fun r hr => hSource r ⟨hr.1, le_trans hr.2 hs.2⟩)
    have hError : B t - B s ≤
        h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * (s - t) +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C *
          (s - t) ^ 2 := by
      change |B t - B s| ≤ _ at hDiff
      exact (le_abs_self (B t - B s)).trans hDiff
    have hMaxError :
        h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * (s - t) +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C *
          (s - t) ^ 2 ≤
        h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C * δ ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hElapsedLe hΛ)
        (mul_le_mul_of_nonneg_left hElapsedSq hΞ)
    change h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C * δ ^ 2 <
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
