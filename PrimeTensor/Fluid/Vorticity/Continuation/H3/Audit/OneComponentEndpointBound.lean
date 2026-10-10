import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.FrontierBoundary

/-!
# A proved part of the one-component endpoint literature bridge

`H3TerminalActualVorticityStrongH3EndpointPath hH3 i` provides pathwise
strong weighted spectral H³ endpoints for the TWO velocity coordinates
appearing in the selected curl component. The published one-velocity-component
continuation theorems require substantially less regularity, but importing
one of those theorems into the project still requires a separate physical
Sobolev-space and strong-solution compatibility proof.

This file proves the first nontrivial bridge entirely inside Lean: a strong
spectral endpoint produces a finite uniform spectral H³ norm bound on some
strict terminal neighborhood; both transverse velocity components can be
bounded on the SAME neighborhood, as can their summed squared norms.

No outside theorem, additional axiom, or Navier--Stokes sign assumption is
used here. This is NOT yet the `H3AuditOnePhysicalEndpointLiteratureBridge`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The pathwise strong endpoint of one complementary velocity component
provides an actual uniform H³ spectral norm bound on a terminal neighborhood.
Unlike a hypothetical continuation criterion, this is proved directly from
the endpoint modulus itself. -/
theorem h3Audit_complementEndpoint_uniformTerminalSpectralNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (hEndpoint : H3TerminalComplementGradientStrongH3EndpointPath hH3 p) :
    ∃ (η M : ℝ), 0 < η ∧ 0 ≤ M ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
        T - t < η →
          ‖h3TerminalComplementSpectralStateAt hH3 p t ht‖ ≤ M := by
  obtain ⟨Ginf, _hRepresentative, hModulus⟩ := hEndpoint
  obtain ⟨η, hη, hNear⟩ := hModulus 1 (by norm_num)
  refine ⟨η, ‖Ginf‖ + 1, hη, by positivity, ?_⟩
  intro t ht hWidth
  have hDistance : dist t T < η := by
    calc
      dist t T = |t - T| := Real.dist_eq t T
      _ = |T - t| := abs_sub_comm t T
      _ = T - t := abs_of_pos (sub_pos.mpr ht.2)
      _ < η := hWidth
  have hDifference :
      ‖h3TerminalComplementSpectralStateAt hH3 p t ht - Ginf‖ < 1 :=
    hNear t ht hDistance
  calc
    ‖h3TerminalComplementSpectralStateAt hH3 p t ht‖ =
        ‖(h3TerminalComplementSpectralStateAt hH3 p t ht - Ginf) + Ginf‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖h3TerminalComplementSpectralStateAt hH3 p t ht - Ginf‖ + ‖Ginf‖ :=
      norm_add_le _ _
    _ ≤ ‖Ginf‖ + 1 := by
      linarith only [hDifference]

/-- A single physical curl-component endpoint controls both of its actual
transverse velocity components with ONE time window and ONE spectral bound. -/
theorem h3Audit_onePhysicalEndpoint_uniformTwoTransverseSpectralNorms
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ (η M : ℝ), 0 < η ∧ 0 ≤ M ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
        T - t < η →
          ‖h3TerminalComplementSpectralStateAt hH3
            (h3TerminalActualVorticityPositiveComplementPair i) t ht‖ ≤ M ∧
          ‖h3TerminalComplementSpectralStateAt hH3
            (h3TerminalActualVorticityNegativeComplementPair i) t ht‖ ≤ M := by
  obtain ⟨ηP, MP, hηP, hMP, hBoundP⟩ :=
    h3Audit_complementEndpoint_uniformTerminalSpectralNorm hH3
      (h3TerminalActualVorticityPositiveComplementPair i) hPhysical.1
  obtain ⟨ηN, MN, hηN, hMN, hBoundN⟩ :=
    h3Audit_complementEndpoint_uniformTerminalSpectralNorm hH3
      (h3TerminalActualVorticityNegativeComplementPair i) hPhysical.2
  refine ⟨min ηP ηN, max MP MN, lt_min hηP hηN,
    le_trans hMP (le_max_left MP MN), ?_⟩
  intro t ht hClose
  constructor
  · exact (hBoundP t ht (lt_of_lt_of_le hClose (min_le_left ηP ηN))).trans
      (le_max_left MP MN)
  · exact (hBoundN t ht (lt_of_lt_of_le hClose (min_le_right ηP ηN))).trans
      (le_max_right MP MN)

/-- The same near-terminal window bounds the sum of the two componentwise
spectral H³ norms squared, an explicit finite quantitative norm budget. -/
theorem h3Audit_onePhysicalEndpoint_uniformTwoTransverseSpectralSquares
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ (η M : ℝ), 0 < η ∧ 0 ≤ M ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
        T - t < η →
          ‖h3TerminalComplementSpectralStateAt hH3
            (h3TerminalActualVorticityPositiveComplementPair i) t ht‖ ^ 2 +
          ‖h3TerminalComplementSpectralStateAt hH3
            (h3TerminalActualVorticityNegativeComplementPair i) t ht‖ ^ 2 ≤ M := by
  obtain ⟨η, B, hη, hB, hBound⟩ :=
    h3Audit_onePhysicalEndpoint_uniformTwoTransverseSpectralNorms hH3 i hPhysical
  refine ⟨η, 2 * B ^ 2, hη, by positivity, ?_⟩
  intro t ht hNear
  obtain ⟨hP, hN⟩ := hBound t ht hNear
  have hPSq := pow_le_pow_left₀
    (norm_nonneg (h3TerminalComplementSpectralStateAt hH3
      (h3TerminalActualVorticityPositiveComplementPair i) t ht)) hP 2
  have hNSq := pow_le_pow_left₀
    (norm_nonneg (h3TerminalComplementSpectralStateAt hH3
      (h3TerminalActualVorticityNegativeComplementPair i) t ht)) hN 2
  nlinarith only [hPSq, hNSq]

end
end Euclidean
end Bridge
end PrimeTensor
