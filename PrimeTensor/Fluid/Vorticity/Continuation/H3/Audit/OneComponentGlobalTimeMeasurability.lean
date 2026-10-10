import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentLocalTimeContinuity

/-!
# Global Borel measurability of the physical homogeneous Ḣ^(3/2) time density

This closes the purely temporal bridge left open at `e73b5be3`.

On each strict local canonical window, the actual scalar Fourier square
density is continuous in elapsed time. The interval lies inside `(0,T)`;
therefore at each strictly preterminal physical time the density is
continuous in the *ambient* real-time topology. Consequently the density
is continuous on `(0,T)` and, because its definition is identically zero
outside `(0,T)`, it is Borel measurable on all of ℝ.

The existing endpoint domination theorem then yields integrability of
both complementary components without separate temporal-measurability
or spectral-state-measurability premises.

No global H³ bound up to T, no external one-component continuation
criterion, and no additional hypothesis on the physical PDE are used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- A continuous elapsed-time expression on a closed parameter interval is
continuous in ambient physical time at each *interior* point of its image.
The strict inequalities make the closed image interval a neighborhood. -/
private theorem h3Audit_continuousAt_of_elapsedWindow
    (f : ℝ → ℝ) {t τ s : ℝ}
    (hts : t < s)
    (hsEnd : s < t + τ)
    (hf : Continuous (fun q : Set.Icc (0 : ℝ) τ => f (t + (q : ℝ)))) :
    ContinuousAt f s := by
  have hMaps :
      ∀ x : Set.Icc t (t + τ),
        (x : ℝ) - t ∈ Set.Icc (0 : ℝ) τ := by
    intro x
    rcases x.property with ⟨hl, hu⟩
    change 0 ≤ (x : ℝ) - t ∧ (x : ℝ) - t ≤ τ
    constructor <;> linarith
  have hCoordinate : Continuous (fun x : Set.Icc t (t + τ) =>
      (⟨(x : ℝ) - t, hMaps x⟩ : Set.Icc (0 : ℝ) τ)) :=
    (continuous_subtype_val.sub continuous_const).subtype_mk hMaps
  have hTransfer : Continuous (fun x : Set.Icc t (t + τ) =>
      f (t + ((x : ℝ) - t))) := hf.comp hCoordinate
  have hOn : ContinuousOn f (Set.Icc t (t + τ)) := by
    apply (continuousOn_iff_continuous_domRestrict).2
    have hEq :
        (fun x : Set.Icc t (t + τ) => f (t + ((x : ℝ) - t))) =
        (Set.Icc t (t + τ)).domRestrict f := by
      funext x
      simp only [Set.domRestrict_apply]
      congr 1
      ring
    rw [← hEq]
    exact hTransfer
  have hNear : Set.Icc t (t + τ) ∈ 𝓝 s := by
    refine Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo t (t + τ) from ⟨hts, hsEnd⟩)) ?_
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  exact hOn.continuousAt hNear

/-- No global terminal H³ energy ceiling is needed: the actual homogeneous
three-halves density is continuous at *every* strict preterminal time. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_continuousAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousAt
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p) s := by
  obtain ⟨t, S, E, τ, _ht, hts, hsEnd, _hEndS, _hST, hCont⟩ :=
    h3Audit_homogeneousThreeHalvesTimeDensity_exists_localContinuousWindow
      hH3 hs p
  exact h3Audit_continuousAt_of_elapsedWindow
    (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
    hts hsEnd hCont

/-- Globally on the open physical preterminal interval, not merely on
individually selected local canonical windows. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) :
    ContinuousOn
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
      (Set.Ioo (0 : ℝ) T) := by
  apply continuousOn_of_forall_continuousAt
  intro s hs
  exact h3Audit_homogeneousThreeHalvesTimeDensity_continuousAt hH3 p hs

/-- The zero-extended genuine physical Ḣ^(3/2) square density is Borel
measurable on all real times, automatically from the admissible H³ path.
No measurable spectral-state assumption remains in this statement. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_measurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) :
    Measurable
      (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p) := by
  classical
  let F : ℝ → ℝ :=
    h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p
  have hCont : ContinuousOn F (Set.Ioo (0 : ℝ) T) :=
    h3Audit_homogeneousThreeHalvesTimeDensity_continuousOn hH3 p
  have hBorel :
      Measurable
        ((Set.Ioo (0 : ℝ) T).piecewise F (fun _ => (0 : ℝ))) :=
    hCont.measurable_piecewise
      (continuous_const.continuousOn) isOpen_Ioo.measurableSet
  have hEq :
      (Set.Ioo (0 : ℝ) T).piecewise F (fun _ => (0 : ℝ)) = F := by
    funext s
    by_cases hs : s ∈ Set.Ioo (0 : ℝ) T
    · simp [Set.piecewise, hs]
    · simp [Set.piecewise, F,
        h3AuditHomogeneousThreeHalvesVelocityTimeDensity, hs]
  change Measurable F
  rw [← hEq]
  exact hBorel

/-- Single selected complementary component: automatic temporal
measurability discharges the former final named hypothesis. -/
theorem h3Audit_complementEndpoint_homogeneousThreeHalves_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (p : H3TerminalCurlGradientPair)
    (hEndpoint : H3TerminalComplementGradientStrongH3EndpointPath hH3 p) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      IntegrableOn
        (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p)
        (Set.Ioo c T) := by
  exact
    h3Audit_complementEndpoint_homogeneousThreeHalves_integrable_of_timeMeasurable
      hH3 hClass p hEndpoint
      (h3Audit_homogeneousThreeHalvesTimeDensity_measurable hH3 p)

/-- With one genuine physical curl-component endpoint and the existing
preterminal energy class, both transverse physical velocity components
have integrable homogeneous Ḣ^(3/2) square densities on one common late
interval. No time/state measurability assumption is supplied separately. -/
theorem h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      IntegrableOn
        (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
          (h3TerminalActualVorticityPositiveComplementPair i))
        (Set.Ioo c T) ∧
      IntegrableOn
        (h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3
          (h3TerminalActualVorticityNegativeComplementPair i))
        (Set.Ioo c T) := by
  exact
    h3Audit_onePhysicalEndpoint_twoHomogeneousThreeHalves_integrable_of_timeMeasurable
      hH3 hClass i hPhysical
      (h3Audit_homogeneousThreeHalvesTimeDensity_measurable hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      (h3Audit_homogeneousThreeHalvesTimeDensity_measurable hH3
        (h3TerminalActualVorticityNegativeComplementPair i))

end
end Euclidean
end Bridge
end PrimeTensor
