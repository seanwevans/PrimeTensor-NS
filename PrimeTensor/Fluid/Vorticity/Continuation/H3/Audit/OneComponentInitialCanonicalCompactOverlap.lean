import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialMildCompactWeakTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCanonicalMildOverlap

/-!
# Initial canonical old/selected overlap and compact distributional data

The canonical selected heat--Leray solution is already continuous in the
weighted three-component spectral H³ topology and has exactly the specified
spectral datum U₀ at time zero.  The initial canonical overlap contract
matches its individual complementary coordinates to the actual old velocity.

All three Fin 3 coordinates occur as complements of the six curl-gradient
pairs. Consequently the canonical overlap gives a whole-velocity strong H³
right trace, without an additional old-solution physical mild equation,
old-solution Picard-ball bound, or initial H³ energy ceiling.

Compact smooth scalar weak-test initial convergence then identifies this
strong trace with the prescribed old physical velocity u(0). It also supplies
the actual H³ energy right limit and the earlier physical zero-jet criterion.
The overlap and distributional initial condition remain explicit; the
terminal actual-vorticity H³ endpoint is independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace

noncomputable section

/-- Every coordinate of a three-component velocity occurs as the
complementary component of a curl-gradient pair. -/
theorem h3Audit_initialComplementPair_covers_fin3 (j : Fin 3) :
    ∃ p : H3TerminalCurlGradientPair,
      h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p) = j := by
  fin_cases j
  · exact ⟨.y_xz, rfl⟩
  · exact ⟨.x_yz, rfl⟩
  · exact ⟨.x_zy, rfl⟩

/-- Coordinatewise canonical old/selected overlap is a *whole* actual
three-component H³ identity on the early physical interval. -/
theorem h3Audit_initialCanonicalOverlap_fullVelocity_eq_selected
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hOverlap : H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (htb : t < b) :
    h3AuditActualSpectralVelocityTotal hH3 t =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ t := by
  obtain ⟨_hb, _hbT, _hbR, hMatches⟩ := hOverlap
  rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
  funext j
  obtain ⟨p, hp⟩ := h3Audit_initialComplementPair_covers_fin3 j
  rw [← hp]
  exact (h3AuditActualSpectralVelocityAt_complement hH3 p t ht).trans
    (hMatches p t ht htb)

/-- Canonical old/selected initial overlap alone supplies the complete old
spectral velocity H³ right trace, with no old-solution mild equation assumed. -/
theorem h3Audit_initialCanonicalOverlap_fullStrongH3Trace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T A b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A)
    (hOverlap : H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b) :
    Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  obtain ⟨hb, hbT, hbR, hMatches⟩ := hOverlap
  let W : ℝ → H3SpectralVelocityState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  have hWContinuous : Continuous W :=
    continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  have hWZero : W 0 = U₀ :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_zero
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀
  have hWTendsto : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
    rw [← hWZero]
    exact hWContinuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hT : 0 < T := lt_trans hb hbT
  have hAgreement :
      h3AuditActualSpectralVelocityTotal hH3 =ᶠ[𝓝[>] (0 : ℝ)] W := by
    filter_upwards [h3Audit_eventually_initialStrictPhysicalTime hT,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht htb
    exact h3Audit_initialCanonicalOverlap_fullVelocity_eq_selected
      hH3 U₀ hA hU₀ ⟨hb, hbT, hbR, hMatches⟩ t ht htb
  exact hWTendsto.congr' hAgreement.symm

/-- Any complete strong H³ initial trace of the actual old velocity also
fixes the limiting positive-time H³ energy, independent of how that trace
was produced. -/
theorem h3Audit_initialStrongH3Trace_energyRightLimit_toSpectral
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (U₀ : H3SpectralVelocityState)
    (hTrace : Tendsto (h3AuditActualSpectralVelocityTotal hH3)
      (𝓝[>] (0 : ℝ)) (𝓝 U₀)) :
    Tendsto (velocityH3EnergyAt u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 + h3SpectralVelocitySquareEnergy U₀)) := by
  have hSpectralEnergy :
      Tendsto
        (fun t : ℝ => h3SpectralVelocitySquareEnergy
          (h3AuditActualSpectralVelocityTotal hH3 t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (h3SpectralVelocitySquareEnergy U₀)) := by
    unfold h3SpectralVelocitySquareEnergy
    apply tendsto_finsetSum
    intro j _
    have hCoordinate :
        Tendsto
          (fun t : ℝ => (h3AuditActualSpectralVelocityTotal hH3 t) j)
          (𝓝[>] (0 : ℝ)) (𝓝 (U₀ j)) :=
      (continuous_apply j).continuousAt.tendsto.comp hTrace
    have hNorm :
        Tendsto
          (fun t : ℝ => ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖)
          (𝓝[>] (0 : ℝ)) (𝓝 ‖U₀ j‖) :=
      continuous_norm.continuousAt.tendsto.comp hCoordinate
    exact hNorm.pow 2
  have hAgreement :
      (fun t : ℝ => 1 + h3SpectralVelocitySquareEnergy
        (h3AuditActualSpectralVelocityTotal hH3 t))
        =ᶠ[𝓝[>] (0 : ℝ)]
      velocityH3EnergyAt u := by
    filter_upwards [h3Audit_eventually_initialStrictPhysicalTime hT]
      with t ht
    exact h3AuditActualSpectralVelocityTotal_energy_exact hH3 t ht
  exact (hSpectralEnergy.const_add 1).congr' hAgreement

/-- A canonical selected initial overlap together with the prescribed
compact distributional initial data, without an old physical mild equation. -/
def H3AuditInitialCanonicalOverlapCompactInitialData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (U₀ : H3SpectralVelocityState) (A : ℝ)
    (hA : 0 < A) (hU₀ : ‖U₀‖ ≤ A) (b : ℝ),
    H3AuditInitialCanonicalMildOverlapAt hH3 U₀ hA hU₀ b ∧
    ∀ (j : Fin 3) (φ : H3WeakTestFunction),
      Tendsto
        (fun t : ℝ => inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
          (h3AuditActualPhysicalZeroJetL2Total hH3 j t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (h3WeakTestFunctionPhysicalL2 φ)
          (velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j))))

/-- The canonical overlap and compact distributional initial condition
produce strong initial physical L² convergence and correct initial H³ energy
continuity, *without* the old-solution signed mild equation or energy ceiling. -/
theorem h3Audit_initialCanonicalCompactOverlap_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalOverlapCompactInitialData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, U₀, A, hA, hU₀,
    b, hOverlap, hWeakCompact⟩ := hData
  have hTrace :=
    h3Audit_initialCanonicalOverlap_fullStrongH3Trace
      hH3 U₀ hA hU₀ hOverlap
  obtain ⟨hb, hbT, _hbR, _hMatches⟩ := hOverlap
  have hT : 0 < T := lt_trans hb hbT
  have hPhysical :=
    h3Audit_initialMildStrongTrace_and_compactWeakInitial_implies_physicalL2Trace
      hH3 hT hInt0 hMeas0 U₀ hTrace hWeakCompact
  have hCompatible :
      U₀ = velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0 :=
    h3Audit_initialStrongH3Trace_identifies_initialSpectral_of_physicalL2
      hH3 hT hInt0 hMeas0 hFourier0 U₀ hTrace hPhysical
  have hInitialEnergy :
      1 + h3SpectralVelocitySquareEnergy U₀ = velocityH3EnergyAt u 0 := by
    rw [hCompatible]
    exact one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
      hFourier0
  have hEnergy :
      Tendsto (velocityH3EnergyAt u)
        (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3EnergyAt u 0)) := by
    simpa only [hInitialEnergy] using
      (h3Audit_initialStrongH3Trace_energyRightLimit_toSpectral
        hH3 hT U₀ hTrace)
  refine ⟨hInt0, hMeas0, hFourier0, ?_, hPhysical⟩
  intro ε hε
  exact hEnergy.eventually
    (Iio_mem_nhds (by linarith :
      velocityH3EnergyAt u 0 < velocityH3EnergyAt u 0 + ε))

/-- Selected canonical overlap and compact-test initial condition suffice for
the two transverse full-time intrinsic physical Sobolev estimates, conditional
on the separate actual terminal vorticity strong H³ endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialCanonicalCompactOverlap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalOverlapCompactInitialData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPhysicalZeroJetL2
    hH3 hClass i hPhysical
    (h3Audit_initialCanonicalCompactOverlap_implies_physicalZeroJetAndEnergyUpper
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
