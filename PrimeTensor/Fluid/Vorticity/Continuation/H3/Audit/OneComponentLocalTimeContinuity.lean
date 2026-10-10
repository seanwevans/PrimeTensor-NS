import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentSobolevFunctionalContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Continuity.Minimal
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Path.Continuity

/-!
# Local spectral continuity and homogeneous three-halves time measurability

The path class already assumes continuity of the SCALAR H³ energy at each
strict preterminal time. The existing pressure-free weak+norm argument
transfers this scalar continuity, on a bounded canonical H³ tail, to strong
continuity of the ACTUAL weighted spectral velocity state.

Combine that pre-existing result with the audited continuous homogeneous
three-halves Fourier square functional. On EVERY compact elapsed interval
strictly contained in (0,T), the physical component's homogeneous square
energy is a continuous, hence measurable, function of elapsed time.

This does not yet assemble the local facts into one global Borel statement
on (0,T) or invoke Liu--Zhang continuation. These remain separate proof
obligations. No extra PDE, Fourier-jet continuity, or pressure hypothesis is
introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

noncomputable local instance axisFintypeH3AuditLocalTimeContinuity
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Restrict the genuine Navier--Stokes H³ path to an earlier terminal time.
This avoids inventing any globally bounded H³ tail through the original T. -/
theorem h3Audit_h3PathAdmissible_restrict_terminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hS : 0 < S)
    (hST : S ≤ T) :
    LoggedPreterminalH3PathAdmissible u S := by
  refine ⟨?_, ?_, ?_⟩
  · exact loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hS hST
  · intro r hr
    exact hH3.velocity_h3_integrable r
      ⟨hr.1, lt_of_lt_of_le hr.2 hST⟩
  · intro r hr
    exact hH3.energy_continuousAt r
      ⟨hr.1, lt_of_lt_of_le hr.2 hST⟩

/-- The pressure-free weak-plus-norm theorem turns already-assumed scalar H³
energy continuity into **strong spectral** H³ continuity on any compact
strict-time interval with a bounded canonical *local* tail. `S` may be much
smaller than the original terminal time T; NO bound near T is required. -/
theorem h3Audit_preterminalSpectral_continuousOnElapsed_of_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {S t τ E : ℝ}
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 < τ)
    (hEnd : t + τ < S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t S E) :
    Continuous
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hShort.navier_stokes ht hEnd hTail) := by
  have hCont : CanonicalH3EnergyContinuousOnTail u t S :=
    hShort.canonicalH3EnergyContinuousOnTail ht
  have hPhysical :
      H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hShort.navier_stokes ht hEnd hTail :=
    h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_energyContinuousOnTail
      hShort.navier_stokes ht hτ hEnd hTail hCont
  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_physicalEnergy_pressureFree
      hShort.navier_stokes ht hEnd hE hTail hPhysical

/-- The actual complementary component from the original H³ path agrees
with the canonical physical velocity component from any earlier-terminal
restriction. Different slice integrability/Fourier proofs are irrelevant. -/
theorem h3Audit_complementSpectralAt_eq_elapsedCoordinate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hEnd : t + τ < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (p : H3TerminalCurlGradientPair)
    (q : Set.Icc (0 : ℝ) τ) :
    h3TerminalComplementSpectralStateAt hH3 p (t + (q : ℝ))
      (let hs := h3PreterminalElapsedTime_mem_Ioo ht hEnd q
       ⟨hs.1, lt_of_lt_of_le hs.2 hST⟩) =
    (h3PreterminalTailCanonicalSpectralStateOnElapsed
      hShort.navier_stokes ht hEnd hTail q)
      (h3ClassicalizationFinOfAxis
        (h3TerminalComplementComponentAxisForPair p)) := by
  rfl

/-- The **actual** homogeneous Ḣ^(3/2) time-density is continuous on every
strict local canonical elapsed interval. The ambient H³ path is only assumed
on (0,T); the canonical bound extends merely to an earlier S<T. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_continuousOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hS : 0 < S)
    (hST : S < T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 < τ)
    (hEnd : t + τ < S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (p : H3TerminalCurlGradientPair) :
    Continuous (fun q : Set.Icc (0 : ℝ) τ =>
      h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p
        (t + (q : ℝ))) := by
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hS (le_of_lt hST)
  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)
  have hSpectral :=
    h3Audit_preterminalSpectral_continuousOnElapsed_of_h3Path
      hShort ht hτ hEnd hE hTail
  have hCoord : Continuous (fun q : Set.Icc (0 : ℝ) τ =>
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hShort.navier_stokes ht hEnd hTail q) j) :=
    (continuous_apply j).comp hSpectral
  have hMass : Continuous (fun q : Set.Icc (0 : ℝ) τ =>
      ∫ ξ : H3FourierPoint3,
        h3AuditHomogeneousThreeHalvesFourierSquareDensity
          ((h3PreterminalTailCanonicalSpectralStateOnElapsed
            hShort.navier_stokes ht hEnd hTail q) j) ξ) :=
    continuous_h3Audit_homogeneousThreeHalvesMass.comp hCoord
  have hEq :
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p
          (t + (q : ℝ))) =
      (fun q : Set.Icc (0 : ℝ) τ =>
        ∫ ξ : H3FourierPoint3,
          h3AuditHomogeneousThreeHalvesFourierSquareDensity
            ((h3PreterminalTailCanonicalSpectralStateOnElapsed
              hShort.navier_stokes ht hEnd hTail q) j) ξ) := by
    funext q
    have hs := h3PreterminalElapsedTime_mem_Ioo ht hEnd q
    have hStrict : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hs.1, lt_trans hs.2 hST⟩
    unfold h3AuditHomogeneousThreeHalvesVelocityTimeDensity
    rw [dite_eq_left hStrict]
    change
      (∫ ξ : H3FourierPoint3,
        h3AuditHomogeneousThreeHalvesFourierSquareDensity
          (h3TerminalComplementSpectralStateAt hH3 p (t + (q : ℝ)) hStrict) ξ) =
      ∫ ξ : H3FourierPoint3,
        h3AuditHomogeneousThreeHalvesFourierSquareDensity
          ((h3PreterminalTailCanonicalSpectralStateOnElapsed
            hShort.navier_stokes ht hEnd hTail q) j) ξ
    rw [h3Audit_complementSpectralAt_eq_elapsedCoordinate
      hH3 hShort (le_of_lt hST) ht hEnd hTail p q]
  rw [hEq]
  exact hMass

/-- Hence no separately postulated *time measurability* is necessary on
strict local intervals. The global-time statement is a separate gluing task. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_measurableOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t τ E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hS : 0 < S)
    (hST : S < T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (hτ : 0 < τ)
    (hEnd : t + τ < S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (p : H3TerminalCurlGradientPair) :
    Measurable (fun q : Set.Icc (0 : ℝ) τ =>
      h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p
        (t + (q : ℝ))) :=
  (h3Audit_homogeneousThreeHalvesTimeDensity_continuousOnElapsed
    hH3 hS hST ht hτ hEnd hE hTail p).measurable

/-- Every strict preterminal time has a local interval *around it* on which
the genuine homogeneous three-halves time density is continuous. The witness
is generated from the H³ path's already-proved local canonical restart
window, NOT from terminal H³ control. -/
theorem h3Audit_homogeneousThreeHalvesTimeDensity_exists_localContinuousWindow
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (p : H3TerminalCurlGradientPair) :
    ∃ (t S E τ : ℝ),
      0 < t ∧ t < s ∧ s < t + τ ∧ t + τ < S ∧ S < T ∧
      Continuous (fun q : Set.Icc (0 : ℝ) τ =>
        h3AuditHomogeneousThreeHalvesVelocityTimeDensity hH3 p
          (t + (q : ℝ))) := by
  obtain ⟨t, S, E, ht, hST, hE, hTail,
    hPositiveElapsed, _hRadius, _hMatch, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let τ : ℝ := (s + S) / 2 - t
  have hτ : 0 < τ := by
    dsimp only [τ]
    linarith only [hPositiveElapsed, hsS]
  have hEnd : t + τ < S := by
    dsimp only [τ]
    linarith only [hsS]
  have hsWithin : s < t + τ := by
    dsimp only [τ]
    linarith only [hsS]
  have hSpos : 0 < S := lt_trans ht.1 ht.2
  exact ⟨t, S, E, τ, ht.1, (sub_pos.mp hPositiveElapsed), hsWithin, hEnd, hST,
    h3Audit_homogeneousThreeHalvesTimeDensity_continuousOnElapsed
      hH3 hSpos hST ht hτ hEnd hE hTail p⟩

end
end Euclidean
end Bridge
end PrimeTensor
