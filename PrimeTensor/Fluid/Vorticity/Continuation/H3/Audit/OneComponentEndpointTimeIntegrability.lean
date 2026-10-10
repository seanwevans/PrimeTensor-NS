import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentEndpointBound

/-!
# Finite-time domination for the one-component endpoint literature audit

A strong terminal weighted H³ spectral endpoint already produces a uniform
near-terminal spectral norm bound. On an interval of finite measure, every
*measurable* nonnegative scalar time density bounded by the squared spectral
norm is therefore integrable. This isolates the remaining Fourier--Sobolev
identification needed to use the Liu--Zhang one-velocity-component criterion:

  S_j(t) = ‖u_j(t)‖_{Ḣ^(3/2)(R³)}².

The present theorem does NOT identify `S_j` with a project spectral integral,
or prove its time measurability or the published theorem's solution-class
hypotheses. The domination and measurability assumptions are intentionally
visible. In particular, no PDE continuation result is derived here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Any measurable nonnegative density dominated by the squared H³ spectral
norm of one component with a strong endpoint is integrable on some terminal
energy-class subinterval. No standalone temporal measurability of the selected
spectral-state map is silently assumed. -/
theorem h3Audit_complementEndpoint_integrable_measurableSpectralDominatedDensity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (p : H3TerminalCurlGradientPair)
    (hEndpoint : H3TerminalComplementGradientStrongH3EndpointPath hH3 p)
    (S : ℝ → ℝ)
    (hSMeas : Measurable S)
    (hSDom : ∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      0 ≤ S t ∧
      S t ≤ ‖h3TerminalComplementSpectralStateAt hH3 p t ht‖ ^ 2) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      IntegrableOn S (Set.Ioo c T) := by
  obtain ⟨η, M, hη, hM, hUniform⟩ :=
    h3Audit_complementEndpoint_uniformTerminalSpectralNorm
      hH3 p hEndpoint
  let m : ℝ := (a + T) / 2
  have hm : m ∈ Set.Ioo a T := by
    dsimp only [m]
    constructor <;> linarith only [hClass.terminal_start.2]
  let c : ℝ := max m (T - η / 2)
  have hc : c ∈ Set.Ioo a T := by
    constructor
    · exact lt_of_lt_of_le hm.1 (le_max_left m (T - η / 2))
    · exact max_lt hm.2 (by linarith only [hη])
  refine ⟨c, hc, ?_⟩
  have hConst : IntegrableOn (fun _ : ℝ => M ^ 2)
      (Set.Ioo c T) :=
    integrableOn_const measure_Ioo_lt_top.ne
  apply Integrable.mono' hConst
  · exact hSMeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htStrict : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hc.1 ht.1), ht.2⟩
    have hTc : T - η / 2 ≤ c := le_max_right m (T - η / 2)
    have hNear : T - t < η := by linarith only [ht.1, hTc, hη]
    have hBound := hUniform t htStrict hNear
    have hSquare :
        ‖h3TerminalComplementSpectralStateAt hH3 p t htStrict‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀
        (norm_nonneg _)
        hBound 2
    obtain ⟨hSNonneg, hSLe⟩ := hSDom t htStrict
    have hUpper : S t ≤ M ^ 2 := le_trans hSLe hSquare
    simpa only [Real.norm_eq_abs, abs_of_nonneg hSNonneg,
      abs_of_nonneg (sq_nonneg M)] using hUpper

/-- Both transverse velocity components support integrable dominated
time densities on ONE common strict terminal subinterval. These are genuine
integrability conclusions, conditional only on the *stated* scalar
measurability and spectral domination, not on a new PDE assumption. -/
theorem h3Audit_onePhysicalEndpoint_twoIntegrable_measurableSpectralDominatedDensities
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (Spos Sneg : ℝ → ℝ)
    (hPosMeas : Measurable Spos)
    (hNegMeas : Measurable Sneg)
    (hPosDom : ∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      0 ≤ Spos t ∧ Spos t ≤
        ‖h3TerminalComplementSpectralStateAt hH3
          (h3TerminalActualVorticityPositiveComplementPair i) t ht‖ ^ 2)
    (hNegDom : ∀ (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T),
      0 ≤ Sneg t ∧ Sneg t ≤
        ‖h3TerminalComplementSpectralStateAt hH3
          (h3TerminalActualVorticityNegativeComplementPair i) t ht‖ ^ 2) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      IntegrableOn Spos (Set.Ioo c T) ∧
      IntegrableOn Sneg (Set.Ioo c T) := by
  obtain ⟨cP, hcP, hPInt⟩ :=
    h3Audit_complementEndpoint_integrable_measurableSpectralDominatedDensity
      hH3 hClass (h3TerminalActualVorticityPositiveComplementPair i)
      hPhysical.1 Spos hPosMeas hPosDom
  obtain ⟨cN, hcN, hNInt⟩ :=
    h3Audit_complementEndpoint_integrable_measurableSpectralDominatedDensity
      hH3 hClass (h3TerminalActualVorticityNegativeComplementPair i)
      hPhysical.2 Sneg hNegMeas hNegDom
  let c := max cP cN
  have hc : c ∈ Set.Ioo a T := by
    constructor
    · exact lt_of_lt_of_le hcP.1 (le_max_left cP cN)
    · exact max_lt hcP.2 hcN.2
  refine ⟨c, hc, ?_, ?_⟩
  · apply hPInt.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left cP cN) ht.1, ht.2⟩
  · apply hNInt.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_right cP cN) ht.1, ht.2⟩

end
end Euclidean
end Bridge
end PrimeTensor
