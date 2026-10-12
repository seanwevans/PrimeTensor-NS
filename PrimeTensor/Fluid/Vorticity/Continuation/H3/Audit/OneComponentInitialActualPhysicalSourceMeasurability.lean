import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualSpectralProjectedSourceBounds
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAutomaticOldTimeMeasurability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Forcing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Diffusion.Continuity

/-!
# Actual physical projected sources: correct Fourier reconstruction and automatic measurability

The previous source candidates omitted inverse Fourier transformation: a
measure-preserving identification of physical and Fourier carrier coordinates
is not the inverse Fourier operator. The parent module is corrected in this
patch to insert `Lp.fourierTransformₗᵢ.symm` for BOTH source terms, preserving
its existing norm inequalities by Plancherel isometry.

This module proves their strong continuity as functions of the weighted
spectral velocity, then proves strong continuity of the actual old spectral
velocity on every strictly positive time, using the already-established
local restart windows. It follows that BOTH corrected physical sources are
automatically strongly measurable on `(0,b]`, without an initial-time trace.

A new conditional comparison contract consequently has no source-measurability
or source-to-H³-energy-inequality hypotheses. Still required: integrability
of actual E₃ on the initial interval, the genuine physical weak momentum
derivative, and epsilon-vanishing selected/old relative-energy residuals.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeInitialInverseFourierSourceMeasurability
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

-- The Fourier carrier is `EuclideanSpace ℝ (Axis Depth.three)`.
-- Its normed group and Fourier-transform instances depend on a finite axis
-- index. A similarly named instance in an imported module is `local`, so
-- it does not propagate to this file.
set_option maxHeartbeats 800000


/-- The corrected inverse-Fourier physical Laplacian depends continuously
on its weighted H³ spectral input. -/
theorem continuous_h3AuditSpectralPhysicalLaplacian :
    Continuous h3AuditSpectralPhysicalLaplacian := by
  have hPi :
      Continuous (fun U : H3SpectralVelocityState =>
        fun j : Fin 3 =>
          h3FromFourierRealL2
            (h3RealPartFourierL2
              ((MeasureTheory.Lp.fourierTransformₗᵢ
                H3FourierPoint3 ℂ).symm
                (h3SpectralScalarLaplacianRawFourierL2 (U j))))) := by
    apply continuous_pi
    intro j
    exact continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm.continuous.comp
          (continuous_h3SpectralScalarLaplacianRawFourierL2.comp
            (continuous_apply j))))
  have hToHilbert :
      Continuous
        (WithLp.toLp (2 : ℝ≥0∞) :
          (Fin 3 → H3ScalarL2) → H3PhysicalRealFinVectorL2Hilbert) :=
    PiLp.continuous_toLp (2 : ℝ≥0∞)
      (fun _ : Fin 3 => H3ScalarL2)
  change Continuous (fun U : H3SpectralVelocityState =>
    (WithLp.toLp (2 : ℝ≥0∞)
      (fun j : Fin 3 =>
        h3FromFourierRealL2
          (h3RealPartFourierL2
            ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ).symm
              (h3SpectralScalarLaplacianRawFourierL2 (U j))))) :
       H3PhysicalRealFinVectorL2Hilbert))
  exact hToHilbert.comp hPi

/-- The corrected inverse-Fourier physical Leray transport depends
continuously on its weighted H³ input, using joint bilinear continuity. -/
theorem continuous_h3AuditSpectralPhysicalLerayForcing :
    Continuous h3AuditSpectralPhysicalLerayForcing := by
  have hPi :
      Continuous (fun U : H3SpectralVelocityState =>
        fun j : Fin 3 =>
          h3FromFourierRealL2
            (h3RealPartFourierL2
              ((MeasureTheory.Lp.fourierTransformₗᵢ
                H3FourierPoint3 ℂ).symm
                (h3RawFinLerayOuterProductDivergenceFourierL2 U U j)))) := by
    apply continuous_pi
    intro j
    have hDiagonal :
        Continuous (fun U : H3SpectralVelocityState => (U, U)) :=
      Continuous.prodMk continuous_id continuous_id
    have hFourier :
        Continuous (fun U : H3SpectralVelocityState =>
          h3RawFinLerayOuterProductDivergenceFourierL2 U U j) := by
      have hComp :=
        (continuous_h3RawFinLerayOuterProductDivergenceFourierL2 j).comp
          hDiagonal
      change Continuous (fun U : H3SpectralVelocityState =>
        h3RawFinLerayOuterProductDivergenceFourierL2 U U j) at hComp
      exact hComp
    exact continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).symm.continuous.comp hFourier))
  have hToHilbert :
      Continuous
        (WithLp.toLp (2 : ℝ≥0∞) :
          (Fin 3 → H3ScalarL2) → H3PhysicalRealFinVectorL2Hilbert) :=
    PiLp.continuous_toLp (2 : ℝ≥0∞)
      (fun _ : Fin 3 => H3ScalarL2)
  change Continuous (fun U : H3SpectralVelocityState =>
    (WithLp.toLp (2 : ℝ≥0∞)
      (fun j : Fin 3 =>
        h3FromFourierRealL2
          (h3RealPartFourierL2
            ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ).symm
              (h3RawFinLerayOuterProductDivergenceFourierL2 U U j)))) :
       H3PhysicalRealFinVectorL2Hilbert))
  exact hToHilbert.comp hPi

/-- Generic local-interval continuity transfer, in the actual H³ spectral
carrier rather than the physical L² velocity carrier. -/
private theorem h3Audit_initialSpectral_continuousAt_of_elapsedWindow
    (f : ℝ → H3SpectralVelocityState)
    {t τ s : ℝ}
    (hts : t < s)
    (hsEnd : s < t + τ)
    (hf : Continuous (fun q : Set.Icc (0 : ℝ) τ =>
      f (t + (q : ℝ)))) :
    ContinuousAt f s := by
  have hMaps : ∀ x : Set.Icc t (t + τ),
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
      (isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo t (t + τ)
        from ⟨hts, hsEnd⟩)) ?_
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  exact hOn.continuousAt hNear

/-- The actual old weighted spectral velocity is strongly continuous at
every strictly positive preterminal time; no initial trace is needed. -/
theorem h3Audit_initialActualSpectralVelocity_continuousAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousAt (h3AuditActualSpectralVelocityTotal hH3) s := by
  obtain ⟨t, S, E, ht, hST, hE, hTail,
    hElapsed, _hRadius, _hMatch, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let τ : ℝ := (s + S) / 2 - t
  have hτ : 0 < τ := by
    dsimp only [τ]
    linarith only [hElapsed, hsS]
  have hEnd : t + τ < S := by
    dsimp only [τ]
    linarith only [hsS]
  have hsWithin : s < t + τ := by
    dsimp only [τ]
    linarith only [hsS]
  have hSpos : 0 < S := lt_trans ht.1 ht.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSpos
      (le_of_lt hST)
  have hSpectral : Continuous
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hShort.navier_stokes ht hEnd hTail) :=
    h3Audit_preterminalSpectral_continuousOnElapsed_of_h3Path
      hShort ht hτ hEnd hE hTail
  have hEq :
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3AuditActualSpectralVelocityTotal hH3 (t + (q : ℝ))) =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hShort.navier_stokes ht hEnd hTail := by
    funext q
    exact h3Audit_actualSpectralVelocityTotal_eq_canonicalElapsed
      hH3 hShort (le_of_lt hST) ht hEnd hTail q
  apply h3Audit_initialSpectral_continuousAt_of_elapsedWindow
    (h3AuditActualSpectralVelocityTotal hH3)
    (sub_pos.mp hElapsed) hsWithin
  rw [hEq]
  exact hSpectral

/-- Complete strong continuity of the actual spectral state on `(0,T)`. -/
theorem h3Audit_initialActualSpectralVelocity_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ContinuousOn (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
  apply continuousOn_of_forall_continuousAt
  intro s hs
  exact h3Audit_initialActualSpectralVelocity_continuousAt hH3 hs

/-- Both corrected inverse-Fourier physical source paths are automatically
measurable on an initial interval, regardless of their behavior at zero. -/
theorem h3Audit_initialActualSpectralSources_aestronglyMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hbT : b < T) :
    AEStronglyMeasurable
      (h3AuditInitialActualSpectralLaplacianTotal hH3)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)) ∧
    AEStronglyMeasurable
      (h3AuditInitialActualSpectralLerayTotal hH3)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)) := by
  have hSub : Set.Ioc (0 : ℝ) b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have hU : ContinuousOn
      (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Ioc (0 : ℝ) b) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub
  have hLap : ContinuousOn
      (h3AuditInitialActualSpectralLaplacianTotal hH3)
      (Set.Ioc (0 : ℝ) b) := by
    have hComp := continuous_h3AuditSpectralPhysicalLaplacian.comp_continuousOn hU
    apply hComp.congr
    intro s hs
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      dite_eq_left (hSub hs), Function.comp_apply]
  have hForce : ContinuousOn
      (h3AuditInitialActualSpectralLerayTotal hH3)
      (Set.Ioc (0 : ℝ) b) := by
    have hComp := continuous_h3AuditSpectralPhysicalLerayForcing.comp_continuousOn hU
    apply hComp.congr
    intro s hs
    simp only [h3AuditInitialActualSpectralLerayTotal,
      dite_eq_left (hSub hs), Function.comp_apply]
  exact ⟨hLap.aestronglyMeasurable measurableSet_Ioc,
    hForce.aestronglyMeasurable measurableSet_Ioc⟩

/-- Therefore actual initial projected source integrability and quantitative
mass control no longer require a separate measurability premise. -/
theorem h3Audit_initialActualSpectralSources_integrable_of_H3Energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hE : IntervalIntegrable (velocityH3EnergyAt u) volume 0 b) :
    IntervalIntegrable (h3AuditInitialActualSpectralLaplacianTotal hH3)
      volume 0 b ∧
    IntervalIntegrable (h3AuditInitialActualSpectralLerayTotal hH3)
      volume 0 b ∧
    IntervalIntegrable
      (fun t => h3AuditInitialActualSpectralLaplacianTotal hH3 t -
        h3AuditInitialActualSpectralLerayTotal hH3 t) volume 0 b ∧
    (∫ t in (0 : ℝ)..b,
        ‖h3AuditInitialActualSpectralLaplacianTotal hH3 t -
          h3AuditInitialActualSpectralLerayTotal hH3 t‖) ≤
        (3 + h3AuditInitialLerayEnergyCoefficient) *
          ∫ t in (0 : ℝ)..b, velocityH3EnergyAt u t := by
  obtain ⟨hDMeas, hNMeas⟩ :=
    h3Audit_initialActualSpectralSources_aestronglyMeasurable hH3 b hbT
  exact h3Audit_initialActualSpectralSources_integrable_and_budget
    hH3 b hb hbT hE hDMeas hNMeas

/-- A physical initial-value criterion with the reconstructed diffusion and
Leray forcing already fixed by the actual weighted H³ field. Their bounds,
strong measurability, and Bochner integrability are no longer hypotheses. -/
def H3AuditInitialCanonicalActualSpectralSourcesRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    IntervalIntegrable (velocityH3EnergyAt u) volume 0 b ∧
    ∃ K : ℝ,
      (∀ (Φ : H3PhysicalRealFinVectorSchwartz) (t : ℝ),
        t ∈ Set.Ioo (0 : ℝ) b →
          HasDerivAt
            (fun x : ℝ =>
              ((innerSL ℝ)
                (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
                (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
            (((innerSL ℝ)
              (h3AuditInitialActualSpectralLaplacianTotal hH3 t -
                h3AuditInitialActualSpectralLerayTotal hH3 t))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) t) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|))

/-- The corrected source constructors and the proven measurability and norm
bounds discharge the older two-source comparison hypotheses. -/
theorem h3Audit_initialActualSpectralSources_implies_diffusionLerayData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalActualSpectralSourcesRelativeEnergyData hH3) :
    H3AuditInitialCanonicalDiffusionLerayRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, hE, K, hDeriv, hEpsilon⟩ := hData
  obtain ⟨hD, hN, _, _⟩ :=
    h3Audit_initialActualSpectralSources_integrable_of_H3Energy
      hH3 b hb hbT hE
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR,
    h3AuditInitialActualSpectralLaplacianTotal hH3,
    h3AuditInitialActualSpectralLerayTotal hH3,
    K, hD, hN, hDeriv, hEpsilon⟩

/-- Compact physical weak comparison and initial L²/H³ upper traces follow
from actual reconstructed sources, initial H³-energy integrability, the
strictly positive momentum derivative, and the still-separate residual. -/
theorem h3Audit_initialActualSpectralSources_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalActualSpectralSourcesRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialDiffusionLeray_implies_compactWeakComparisonData
    hH3 (h3Audit_initialActualSpectralSources_implies_diffusionLerayData hH3 hData)

theorem h3Audit_initialActualSpectralSources_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalActualSpectralSourcesRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialDiffusionLeray_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialActualSpectralSources_implies_diffusionLerayData hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
