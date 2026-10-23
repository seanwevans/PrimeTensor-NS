import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopSelectedPhysicalOverlap244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Energy.Gronwall
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Global.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Restart.Radius
import Mathlib.Tactic

/-!
# Projected-RHS weak FTC replaces selected/old physical agreement

The prior selected-spectral bridge required pointwise identity of a classical
selected mild restart with the old physical velocity.  The already formalized
weak--strong Grönwall theorem derives this identity from a *single* scalar
old projected-RHS weak-FTC condition on [0,q], with common restart data.

We package exact positive-time slab geometry, then supply this condition to
the old/selected pointwise uniqueness theorem.  Thus the actual physical
velocity has its eighth Fourier moment at each such time, and the terminal
D₃ alternative needs no separate physical-agreement, spectral-realization,
or high-moment assumptions.

A stronger global projected-RHS weak-FTC frontier (or the independent global
old-pressure weak-energy frontier) fills the uniqueness premise wherever
geometrical restart-slab coverage is available.  Neither global frontier nor
restart-slab coverage is claimed from bare H³ admissibility in this file.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- The physical time has an earlier positive restart anchor, a canonical
H³ tail, and a positive selected half-slab lying strictly before terminal T.
This is geometric and contains NO uniqueness assumption. -/
def h3PathVelocityGeometricSlabCoveredAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (_hClass : PreterminalH3EnergyClass u a T)
    (_ht : t ∈ Set.Ioo a T) : Prop :=
  ∃ (t₀ E Q : ℝ)
    (_ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (_hE : 1 ≤ E)
    (_hTail : CanonicalH3TailDataFrom u t₀ T E)
    (_hQ : 0 < Q)
    (_hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (_hEnd : t₀ + Q < T)
    (s : Set.Icc (Q / 2) Q),
    t = t₀ + (s : ℝ)

/-- Minimal analytic slab condition: the scalar old projected-RHS weak FTC
holds on precisely [0,s]. It is not necessary to assume uniqueness of the
selected and old velocities or weak FTC on the entire restart radius. -/
def h3PathVelocityWeakFTCSlabCoveredAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (_hClass : PreterminalH3EnergyClass u a T)
    (_ht : t ∈ Set.Ioo a T) : Prop :=
  ∃ (t₀ E Q : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t₀ + Q < T)
    (s : Set.Icc (Q / 2) Q),
    t = t₀ + (s : ℝ) ∧
      (let hsPos : 0 < (s : ℝ) :=
        lt_of_lt_of_le (half_pos hQ) s.property.1
       let hsEnd : t₀ + (s : ℝ) < T :=
        lt_of_le_of_lt (add_le_add_right s.property.2 t₀) hEnd
       H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
         hH3.navier_stokes ht₀ hsPos hsEnd hTail)

/-- Scalar weak FTC + the existing L²-relative-energy Grönwall theorem
supplies pointwise selected/old equality, and hence the existing physical
spectral realization, on a single positive physical slice. -/
theorem h3Path_selectedPhysicalOverlap_of_weakFTCSlab244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hWeak : h3PathVelocityWeakFTCSlabCoveredAt244 hH3 hClass ht) :
    h3PathVelocitySelectedPhysicalOverlapAt244 hH3 hClass ht := by
  rcases hWeak with
    ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, hEnd, s, hTime, hWeakFTC⟩
  have hsPos : 0 < (s : ℝ) :=
    lt_of_lt_of_le (half_pos hQ) s.property.1
  have hsEnd : t₀ + (s : ℝ) < T := by
    calc
      t₀ + (s : ℝ) ≤ t₀ + Q := add_le_add_right s.property.2 t₀
      _ < T := hEnd
  have hsRadius :
      (s : ℝ) ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    s.property.2.trans hQR.le
  have hLocal :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hH3.navier_stokes ht₀ hsPos hsEnd hTail := hWeakFTC
  have hAgree :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1) (s : ℝ)
        hH3.navier_stokes ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementAt_of_allProjectedRHSWeakFTC
      (tau := (s : ℝ)) (q := (s : ℝ))
      hH3.navier_stokes ht₀ hsPos hsEnd hE hTail hsRadius hLocal
      ⟨hsPos, le_rfl⟩
  exact ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, hEnd, s, hTime, hAgree⟩

/-- Actual physical order-eight velocity moments from an old scalar weak
FTC on the matching positive elapsed interval, without assuming agreement. -/
theorem h3Path_velocityRawEightMoments_of_weakFTCSlab244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hWeak : h3PathVelocityWeakFTCSlabCoveredAt244 hH3 hClass ht) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  exact h3Path_velocityRawEightMoments_of_selectedSlabRealization244
    hH3 hClass ht
    (h3Path_selectedSlabRealized_of_physicalOverlap244
      hH3 hClass ht
      (h3Path_selectedPhysicalOverlap_of_weakFTCSlab244
        hH3 hClass ht hWeak))

/-- Scalar weak FTC on one positive slab per strict physical time gives the
full physical lower-dissipation versus eighth-moment terminal alternative. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_weakFTCSlabCoverage244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hWeak : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityWeakFTCSlabCoveredAt244 hH3 hClass ht) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_physicalOverlap244
    hH3 hClass hs hEscape
  intro t ht
  exact h3Path_selectedPhysicalOverlap_of_weakFTCSlab244
    hH3 hClass ht (hWeak t ht)

/-- The global scalar projected-RHS weak-FTC frontier supplies the local
minimal FTC condition wherever a valid half-slab already covers the time. -/
theorem h3Path_weakFTCSlab_of_geometricSlab_and_globalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hGeom : h3PathVelocityGeometricSlabCoveredAt244 hH3 hClass ht)
    (hGlobal : H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier) :
    h3PathVelocityWeakFTCSlabCoveredAt244 hH3 hClass ht := by
  rcases hGeom with
    ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, hEnd, s, hTime⟩
  have hsPos : 0 < (s : ℝ) :=
    lt_of_lt_of_le (half_pos hQ) s.property.1
  have hsEnd : t₀ + (s : ℝ) < T := by
    calc
      t₀ + (s : ℝ) ≤ t₀ + Q := add_le_add_right s.property.2 t₀
      _ < T := hEnd
  have hsRadius :
      (s : ℝ) ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    s.property.2.trans hQR.le
  let q : Set.Icc (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨(s : ℝ), hsPos.le, hsRadius⟩
  have hRadius :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u T t₀ hH3.navier_stokes ht₀ hE hTail :=
    hGlobal E hE u T t₀ hH3.navier_stokes ht₀ hTail
  have hLocal :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hH3.navier_stokes ht₀ hsPos hsEnd hTail :=
    hRadius q hsPos hsEnd
  exact ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, hEnd, s, hTime, hLocal⟩

/-- Under geometric restart coverage, the existing global projected-RHS
weak-FTC uniqueness theorem gives the physical terminal escape alternative. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_geometricSlabs_and_globalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hGeom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityGeometricSlabCoveredAt244 hH3 hClass ht)
    (hGlobal : H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_weakFTCSlabCoverage244
    hH3 hClass hs hEscape
  intro t ht
  exact h3Path_weakFTCSlab_of_geometricSlab_and_globalWeakFTC244
    hH3 hClass ht (hGeom t ht) hGlobal

/-- Independent weak-energy uniqueness route: the existing old-pressure
frontier also converts mere geometric slab coverage to physical agreement. -/
theorem h3Path_selectedPhysicalOverlap_of_geometricSlab_and_globalOldPressure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hGeom : h3PathVelocityGeometricSlabCoveredAt244 hH3 hClass ht)
    (hOld : H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    h3PathVelocitySelectedPhysicalOverlapAt244 hH3 hClass ht := by
  rcases hGeom with
    ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, hEnd, s, hTime⟩
  have hsPos : 0 < (s : ℝ) :=
    lt_of_lt_of_le (half_pos hQ) s.property.1
  have hsEnd : t₀ + (s : ℝ) < T := by
    calc
      t₀ + (s : ℝ) ≤ t₀ + Q := add_le_add_right s.property.2 t₀
      _ < T := hEnd
  have hsRadius :
      (s : ℝ) ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    s.property.2.trans hQR.le
  let q : Set.Ioc (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨(s : ℝ), hsPos, hsRadius⟩
  have hRadius :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontierOnRestartRadius
        E u T t₀ hH3.navier_stokes ht₀ hE hTail :=
    hOld E hE u T t₀ hH3.navier_stokes ht₀ hTail
  have hAgreement :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u T t₀ hH3.navier_stokes ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_oldPressureWeakEnergy
      hH3.navier_stokes ht₀ hE hTail hRadius
  have hAt :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1) (s : ℝ)
        hH3.navier_stokes ht₀ hE hTail :=
    hAgreement q hsEnd
  exact ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, hEnd, s, hTime, hAt⟩

/-- Old-pressure weak-energy uniqueness is an independent sufficient route
to the same necessary physical terminal escape alternative. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_geometricSlabs_and_globalOldPressure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hGeom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityGeometricSlabCoveredAt244 hH3 hClass ht)
    (hOld : H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_physicalOverlap244
    hH3 hClass hs hEscape
  intro t ht
  exact h3Path_selectedPhysicalOverlap_of_geometricSlab_and_globalOldPressure244
    hH3 hClass ht (hGeom t ht) hOld

end
end PrimeTensor.FirstMonomialTriad
