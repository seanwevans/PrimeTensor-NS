import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentPhysicalHomogeneousSobolev

/-!
# Canonical physical homogeneous H^(3/2) seminorm and time-L² criterion

The preceding module defined a Fourier-Sobolev domain directly for physical
real scalar L² fields. Membership is existential: a real L² fractional
velocity derivative whose Fourier transform has the exact `q^(3/4)` symbol.

This file removes the choice of derivative from the observable. Uniqueness
makes a canonical real derivative and its nonnegative seminorm well-defined.
For each actual strict-time velocity coordinate this seminorm is *exactly*
the norm of the real derivative constructed earlier, rather than a newly
assumed scalar density.

The resulting globally zero-extended physical-Sobolev seminorm is continuous
on the strict preterminal interval and Borel measurable on the entire time
line. The two transverse velocity coordinates then satisfy a common
terminal-time L² estimate under one physical curl-component strong endpoint.

This is an internal, Plancherel-defined physical Sobolev domain. No
identification with an independently formalized distributional homogeneous
Sobolev space, no imported published continuation theorem, and no assertion
of unconditional Navier--Stokes regularity is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3AuditIntrinsicSobolevTimeL2
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical real fractional derivative of a physical L² field in the
Fourier Ḣ^(3/2) domain. Uniqueness below shows this does not depend on the
chosen existence witness. -/
noncomputable def h3AuditPhysicalHomogeneousThreeHalvesCanonicalDerivative
    (f : H3ScalarL2)
    (hf : H3AuditPhysicalHomogeneousThreeHalvesSobolev f) :
    H3FourierRealL2 :=
  Classical.choose hf

/-- The canonical derivative satisfies the exact physical Fourier
homogeneous three-halves multiplier relation. -/
theorem h3Audit_physicalHomogeneousThreeHalvesCanonicalDerivative_spec
    (f : H3ScalarL2)
    (hf : H3AuditPhysicalHomogeneousThreeHalvesSobolev f) :
    H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec f
      (h3AuditPhysicalHomogeneousThreeHalvesCanonicalDerivative f hf) := by
  exact Classical.choose_spec hf

/-- Any real physical L² field having the prescribed Fourier derivative
agrees with the canonical derivative. -/
theorem h3Audit_physicalHomogeneousThreeHalvesCanonicalDerivative_eq
    (f : H3ScalarL2)
    (hf : H3AuditPhysicalHomogeneousThreeHalvesSobolev f)
    (D : H3FourierRealL2)
    (hD : H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec f D) :
    h3AuditPhysicalHomogeneousThreeHalvesCanonicalDerivative f hf = D := by
  exact h3Audit_physicalHomogeneousThreeHalvesDerivative_unique
    (h3Audit_physicalHomogeneousThreeHalvesCanonicalDerivative_spec f hf) hD

/-- A nonnegative physical Fourier-Sobolev seminorm attached only to a real
physical L² scalar field and its membership in the intrinsic domain. -/
noncomputable def h3AuditPhysicalHomogeneousThreeHalvesSeminorm
    (f : H3ScalarL2)
    (hf : H3AuditPhysicalHomogeneousThreeHalvesSobolev f) : ℝ :=
  ‖h3AuditPhysicalHomogeneousThreeHalvesCanonicalDerivative f hf‖

/-- The intrinsic seminorm can be computed with *any* real L² fractional
derivative satisfying its Fourier multiplier specification. -/
theorem h3Audit_physicalHomogeneousThreeHalvesSeminorm_eq_norm
    (f : H3ScalarL2)
    (hf : H3AuditPhysicalHomogeneousThreeHalvesSobolev f)
    (D : H3FourierRealL2)
    (hD : H3AuditPhysicalHomogeneousThreeHalvesDerivativeSpec f D) :
    h3AuditPhysicalHomogeneousThreeHalvesSeminorm f hf = ‖D‖ := by
  unfold h3AuditPhysicalHomogeneousThreeHalvesSeminorm
  rw [h3Audit_physicalHomogeneousThreeHalvesCanonicalDerivative_eq f hf D hD]

/-- At a genuine strict-time H³ velocity snapshot, the intrinsic *physical*
seminorm is exactly the previously proved real fractional derivative norm. -/
theorem h3Audit_actualVelocity_intrinsicThreeHalvesSeminorm_eq_realNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditPhysicalHomogeneousThreeHalvesSeminorm
      (velocityH3L2JetAt u t
        (hH3.velocity_h3_integrable t ht)
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes ht)
        (h3JetSlot0
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p))))
      (h3Audit_actualVelocity_physicalHomogeneousThreeHalves_membership
        hH3 p t ht) =
    ‖h3AuditActualVelocityThreeHalvesRealDerivativeAt hH3 p t ht‖ := by
  exact h3Audit_physicalHomogeneousThreeHalvesSeminorm_eq_norm
    _ _ _
    (h3Audit_actualVelocity_physicalHomogeneousThreeHalves_derivativeSpec
      hH3 p t ht)

/-- The actual physical-field Ḣ^(3/2) norm profile, extended by zero outside
`(0,T)`. The defining expression is an intrinsic physical Sobolev seminorm,
not a chosen weighted spectral-state proxy. -/
noncomputable def h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3AuditPhysicalHomogeneousThreeHalvesSeminorm
      (velocityH3L2JetAt u t
        (hH3.velocity_h3_integrable t ht)
        (velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
          hH3.navier_stokes ht)
        (h3JetSlot0
          (h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p))))
      (h3Audit_actualVelocity_physicalHomogeneousThreeHalves_membership
        hH3 p t ht)
  else 0

/-- The intrinsic physical Sobolev seminorm and the real fractional derivative
norm have identical time profiles, without any further measurability premise. -/
theorem h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_realNorm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) :
    h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p t =
      ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3 p t‖ := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) T
  · simp only [h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm,
      h3AuditActualVelocityThreeHalvesRealDerivativeTotal, dif_pos ht]
    exact h3Audit_actualVelocity_intrinsicThreeHalvesSeminorm_eq_realNorm
      hH3 p t ht
  · simp [h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm,
      h3AuditActualVelocityThreeHalvesRealDerivativeTotal, ht]

/-- The intrinsic physical time-seminorm is exactly the actual velocity
Fourier Ḣ^(3/2) seminorm, including at the zero-extended times. -/
theorem h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_fourier
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ) :
    h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p t =
      h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3 p t := by
  calc
    h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p t =
        ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3 p t‖ :=
      h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_realNorm
        hH3 p t
    _ = ‖h3AuditActualVelocityThreeHalvesPhysicalDerivativeTotal hH3 p t‖ :=
      h3Audit_actualVelocityThreeHalvesRealDerivativeTotal_norm_eq hH3 p t
    _ = h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3 p t :=
      h3Audit_actualVelocityThreeHalvesPhysicalDerivativeTotal_norm hH3 p t

/-- The intrinsic physical Ḣ^(3/2) time profile is Borel measurable. -/
theorem h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_measurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) :
    Measurable (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p) := by
  have hEq :
      h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p =
        h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p := by
    funext t
    calc
      h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p t =
          h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3 p t :=
        h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_fourier hH3 p t
      _ = h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p t :=
        h3Audit_actualVelocityFourierSeminorm_eq_timeSeminorm hH3 p t
  rw [hEq]
  exact h3Audit_homogeneousThreeHalvesTimeSeminorm_measurable hH3 p

/-- The physical Fourier-Sobolev seminorm profile is continuous at all
strict preterminal times, using the previously proved homogeneous energy
continuity rather than a new independent time regularity assumption. -/
theorem h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (p : H3TerminalCurlGradientPair) :
    ContinuousOn (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p)
      (Set.Ioo (0 : ℝ) T) := by
  have hEq :
      h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p =
        h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p := by
    funext t
    calc
      h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3 p t =
          h3AuditActualVelocityHomogeneousThreeHalvesFourierSeminorm hH3 p t :=
        h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_fourier hH3 p t
      _ = h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm hH3 p t :=
        h3Audit_actualVelocityFourierSeminorm_eq_timeSeminorm hH3 p t
  rw [hEq]
  unfold h3AuditHomogeneousThreeHalvesVelocityTimeSeminorm
  exact Real.continuous_sqrt.comp_continuousOn
    (h3Audit_homogeneousThreeHalvesTimeDensity_continuousOn hH3 p)

/-- One physical curl-component strong H³ endpoint gives two transverse
*intrinsic physical Fourier-Sobolev* seminorms in time L² on the same strict
terminal interval. This is a conditional regularity criterion, not an
extension theorem or a statement of universal endpoint existence. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicPhysicalThreeHalves_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
        2 (volume.restrict (Set.Ioo c T)) ∧
      MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
        2 (volume.restrict (Set.Ioo c T)) := by
  obtain ⟨c, hc, hP, hN⟩ :=
    h3Audit_onePhysicalEndpoint_twoRealFractionalDerivative_timeL2
      hH3 hClass i hPhysical
  refine ⟨c, hc, ?_, ?_⟩
  · have hEq :
        h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
          (h3TerminalActualVorticityPositiveComplementPair i) =
        (fun t : ℝ =>
          ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3
            (h3TerminalActualVorticityPositiveComplementPair i) t‖) := by
      funext t
      exact h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_realNorm
        hH3 _ t
    rw [hEq]
    exact hP
  · have hEq :
        h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
          (h3TerminalActualVorticityNegativeComplementPair i) =
        (fun t : ℝ =>
          ‖h3AuditActualVelocityThreeHalvesRealDerivativeTotal hH3
            (h3TerminalActualVorticityNegativeComplementPair i) t‖) := by
      funext t
      exact h3Audit_actualVelocity_intrinsicThreeHalvesTimeSeminorm_eq_realNorm
        hH3 _ t
    rw [hEq]
    exact hN

/-- One of the transverse physical velocity components already suffices for
a single-component *analytic* time-L² criterion. Applying a published PDE
continuation theorem still requires a separate local-strong-solution bridge. -/
theorem h3Audit_onePhysicalEndpoint_oneIntrinsicPhysicalThreeHalves_timeL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      MemLp (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
        2 (volume.restrict (Set.Ioo c T)) := by
  obtain ⟨c, hc, hP, _hN⟩ :=
    h3Audit_onePhysicalEndpoint_twoIntrinsicPhysicalThreeHalves_timeL2
      hH3 hClass i hPhysical
  exact ⟨c, hc, hP⟩

end
end Euclidean
end Bridge
end PrimeTensor
