import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceIdentification
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Leray.Weak.Determining
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Solenoidal weak FTC implies a full physical-Hilbert momentum derivative

The actual physical projected RHS has now been identified with the canonical
Navier--Stokes RHS on every strictly positive old restart window.  The next
missing step is NOT another physical PDE reconstruction: it is extending the
weak time evolution from divergence-free compact tests to all physical L²
probes, including arbitrary Schwartz vectors.

This file proves the functional-analytic upgrade without postulating a strong
old velocity time derivative.  If the physical velocity path and projected RHS
are Leray-fixed and the scalar weak FTC holds against all divergence-free
compact test vectors, density determines the Hilbert Bochner integral exactly.
Continuity of the RHS then implies an ordinary strong `HasDerivAt` for the
velocity path.  Pairing that derivative against an arbitrary Schwartz vector
proves the *unrestricted* scalar derivative formula needed at initial time.

The solenoidal scalar FTC is an explicit input.  The earlier instantaneous
Navier--Stokes weak PDE identity alone does not justify temporal FTC or
interchange of spatial integration and differentiation.  Those remain
separate analytic obligations.  The subsequent initial H³-energy integral and
vanishing relative-energy residual also remain independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeInitialSolenoidalWeakFTCStrongDerivative
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/-- A solenoidal scalar weak FTC on a positive closed time interval, for
physical Hilbert paths `F` (velocity) and `G` (projected RHS). -/
def H3AuditPhysicalSolenoidalWeakFTCOn
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (a b : ℝ) : Prop :=
  ∀ (φ : H3WeakTestVector),
    H3WeakTestVectorDivergenceFree φ →
      ∀ r : ℝ, r ∈ Set.Icc a b →
        inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ) (F r - F a) =
          ∫ s in a..r,
            inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ) (G s)

/-- Leray-fixed vectors are determined by their solenoidal weak pairings.
In particular a solenoidal weak FTC determines the *entire* Hilbert-valued
Bochner evolution, not merely its divergence-free test pairings. -/
theorem h3Audit_physicalSolenoidalWeakFTC_implies_HilbertEvolution
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (a b : ℝ) (hab : a < b)
    (hGContinuous : ContinuousOn G (Set.Icc a b))
    (hFfixed : ∀ r : ℝ, r ∈ Set.Icc a b →
      H3PhysicalRealFinVectorL2HilbertLerayFixed (F r))
    (hGfixed : ∀ r : ℝ,
      H3PhysicalRealFinVectorL2HilbertLerayFixed (G r))
    (hWeak : H3AuditPhysicalSolenoidalWeakFTCOn F G a b)
    (r : ℝ) (hr : r ∈ Set.Icc a b) :
    F r = F a + ∫ s in a..r, G s := by
  have hSub : Set.Icc a r ⊆ Set.Icc a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hr.2⟩
  have hGInt : IntervalIntegrable G volume a r :=
    (hGContinuous.mono hSub).intervalIntegrable_of_Icc hr.1
  let L := h3PhysicalRealFinVectorL2HilbertLerayDefectContinuousLinearMap
  have hComm :
      L (∫ s in a..r, G s) = ∫ s in a..r, L (G s) := by
    exact (L.intervalIntegral_comp_comm hGInt).symm
  have hGZero (s : ℝ) : L (G s) = 0 := by
    have hs := (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff
      (G s)).2 (hGfixed s)
    unfold h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule at hs
    change L (G s) = 0 at hs
    exact hs
  have hIntegralFixed :
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (∫ s in a..r, G s) := by
    rw [← mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff]
    change L (∫ s in a..r, G s) = 0
    rw [hComm]
    have hZero : (fun s : ℝ => L (G s)) =
        (fun _s : ℝ => (0 : H3SpectralFinVectorState)) := by
      funext s
      exact hGZero s
    rw [hZero]
    simp
  have hRightFixed :
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (F a + ∫ s in a..r, G s) :=
    (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff _).1
      (h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule.add_mem
        ((mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff _).2
          (hFfixed a ⟨le_rfl, hab.le⟩))
        ((mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff _).2
          hIntegralFixed))
  apply h3PhysicalRealFinVectorL2Hilbert_eq_of_lerayFixed_of_divergenceFreeWeakTest_pairings_eq
    (F r) (F a + ∫ s in a..r, G s)
    (hFfixed r hr) hRightFixed
  intro φ hφ
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  have hPairComm :
      inner ℝ ψ (∫ s in a..r, G s) =
        ∫ s in a..r, inner ℝ ψ (G s) := by
    change ((innerSL ℝ) ψ) (∫ s in a..r, G s) =
      ∫ s in a..r, ((innerSL ℝ) ψ) (G s)
    exact (((innerSL ℝ) ψ).intervalIntegral_comp_comm hGInt).symm
  calc
    inner ℝ ψ (F r) =
        inner ℝ ψ (F a) + inner ℝ ψ (F r - F a) := by
      rw [inner_sub_right]
      abel
    _ = inner ℝ ψ (F a) +
          (∫ s in a..r, inner ℝ ψ (G s)) := by
      rw [hWeak φ hφ r hr]
    _ = inner ℝ ψ (F a) +
          inner ℝ ψ (∫ s in a..r, G s) := by
      rw [hPairComm]
    _ = inner ℝ ψ (F a + ∫ s in a..r, G s) := by
      rw [inner_add_right]

/-- A solenoidal weak FTC and Leray-fixedness give the actual strong
physical L² time derivative at every strict interior time.  The only FTC
used is the standard Hilbert-valued Bochner FTC for a continuous source. -/
theorem h3Audit_physicalSolenoidalWeakFTC_implies_HilbertHasDerivAt
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (a b : ℝ) (hab : a < b)
    (hGContinuous : ContinuousOn G (Set.Icc a b))
    (hFfixed : ∀ r : ℝ, r ∈ Set.Icc a b →
      H3PhysicalRealFinVectorL2HilbertLerayFixed (F r))
    (hGfixed : ∀ r : ℝ,
      H3PhysicalRealFinVectorL2HilbertLerayFixed (G r))
    (hWeak : H3AuditPhysicalSolenoidalWeakFTCOn F G a b)
    (r : ℝ) (hr : r ∈ Set.Ioo a b) :
    HasDerivAt F (G r) r := by
  have hAt : ∀ y ∈ Set.Ioo a b, ContinuousAt G y := by
    intro y hy
    exact ContinuousWithinAt.continuousAt
      (hGContinuous y ⟨hy.1.le, hy.2.le⟩)
      (Icc_mem_nhds hy.1 hy.2)
  have hSub : Set.Icc a r ⊆ Set.Icc a b := by
    intro y hy
    exact ⟨hy.1, hy.2.trans hr.2.le⟩
  have hInt : IntervalIntegrable G volume a r :=
    (hGContinuous.mono hSub).intervalIntegrable_of_Icc hr.1.le
  have hMeas : StronglyMeasurableAtFilter G (𝓝 r)
      (volume : Measure ℝ) := by
    exact ContinuousAt.stronglyMeasurableAtFilter
      (μ := (volume : Measure ℝ)) isOpen_Ioo hAt r hr
  have hIntegralDerivative :
      HasDerivAt (fun y : ℝ => ∫ s in a..y, G s) (G r) r :=
    intervalIntegral.integral_hasDerivAt_right hInt hMeas (hAt r hr)
  let J : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    fun y => F a + ∫ s in a..y, G s
  have hJDerivative : HasDerivAt J (G r) r := by
    dsimp only [J]
    exact hIntegralDerivative.const_add (F a)
  have hEventually : F =ᶠ[𝓝 r] J := by
    filter_upwards [Icc_mem_nhds hr.1 hr.2] with y hy
    exact h3Audit_physicalSolenoidalWeakFTC_implies_HilbertEvolution
      F G a b hab hGContinuous hFfixed hGfixed hWeak y hy
  exact hJDerivative.congr_of_eventuallyEq hEventually

/-- Once the Hilbert derivative has been recovered from only solenoidal
compact tests, *every* Schwartz test obeys the unrestricted scalar momentum
derivative required by the initial weak-FTC interface. -/
theorem h3Audit_physicalSolenoidalWeakFTC_implies_SchwartzHasDerivAt
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (a b : ℝ) (hab : a < b)
    (hGContinuous : ContinuousOn G (Set.Icc a b))
    (hFfixed : ∀ r : ℝ, r ∈ Set.Icc a b →
      H3PhysicalRealFinVectorL2HilbertLerayFixed (F r))
    (hGfixed : ∀ r : ℝ,
      H3PhysicalRealFinVectorL2HilbertLerayFixed (G r))
    (hWeak : H3AuditPhysicalSolenoidalWeakFTCOn F G a b)
    (Φ : H3PhysicalRealFinVectorSchwartz)
    (r : ℝ) (hr : r ∈ Set.Ioo a b) :
    HasDerivAt
      (fun x : ℝ =>
        ((innerSL ℝ) (F x))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
      (((innerSL ℝ) (G r))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) r := by
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ
  have hStrong := h3Audit_physicalSolenoidalWeakFTC_implies_HilbertHasDerivAt
    F G a b hab hGContinuous hFfixed hGfixed hWeak r hr
  have hMapped : HasDerivAt
      (fun x : ℝ => ((innerSL ℝ) ψ) (F x))
      (((innerSL ℝ) ψ) (G r)) r :=
    (ContinuousLinearMap.hasFDerivAt ((innerSL ℝ) ψ)).comp_hasDerivAt
      r hStrong
  have hPathEq :
      (fun x : ℝ => ((innerSL ℝ) (F x)) ψ) =
        (fun x : ℝ => ((innerSL ℝ) ψ) (F x)) := by
    funext x
    simp only [innerSL_apply_apply]
    exact (real_inner_comm (F x) ψ).symm
  have hCoefficientEq :
      ((innerSL ℝ) (G r)) ψ = ((innerSL ℝ) ψ) (G r) := by
    simp only [innerSL_apply_apply]
    exact (real_inner_comm (G r) ψ).symm
  change HasDerivAt (fun x : ℝ => ((innerSL ℝ) (F x)) ψ)
    (((innerSL ℝ) (G r)) ψ) r
  rw [hPathEq, hCoefficientEq]
  exact hMapped

/-- The actual diffusion-minus-Leray source is Leray-fixed at *every*
strictly positive physical time, by identification with the old canonical
projected RHS on a positive restart window. -/
theorem h3Audit_initialActualProjectedRHS_lerayFixed_at_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s) := by
  obtain ⟨t, S, E, ht, hST, _hE, hTail,
    hElapsed, _hRadius, _hMatch, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let τ : ℝ := s - t
  have hτ : 0 < τ := by
    dsimp only [τ]
    exact hElapsed
  have hEnd : t + τ < S := by
    dsimp only [τ]
    linarith only [hsS]
  have hSpos : 0 < S := lt_trans ht.1 ht.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSpos
      (le_of_lt hST)
  let q : Set.Icc (0 : ℝ) τ := ⟨τ, hτ.le, le_rfl⟩
  have hTime : t + (q : ℝ) = s := by
    dsimp only [q, τ]
    ring
  have hIdent :=
    h3Audit_initialActualSpectralProjectedRHS_eq_oldPhysicalOnElapsed
      hH3 hShort (le_of_lt hST) ht hEnd hTail q
  rw [← hTime, hIdent]
  exact h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_lerayFixed
    hShort.navier_stokes ht hEnd hTail q


/-- The physical old velocity, not merely its spectral encoder, is
Leray-fixed at every strict preterminal time.  Its zero-order physical jet
is definitionally the same jet as the old canonical restart package. -/
theorem h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3AuditInitialOldPhysicalHilbertTotal hH3 s) := by
  obtain ⟨t, S, E, ht, hST, _hE, hTail,
    hElapsed, _hRadius, _hMatch, hsS⟩ :=
    hH3.exists_localCanonicalRestartWindowAt hs
  let τ : ℝ := s - t
  have hτ : 0 < τ := hElapsed
  have hEnd : t + τ < S := by
    dsimp only [τ]
    linarith only [hsS]
  have hSpos : 0 < S := lt_trans ht.1 ht.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSpos
      (le_of_lt hST)
  let q : Set.Icc (0 : ℝ) τ := ⟨τ, hτ.le, le_rfl⟩
  have hTime : t + (q : ℝ) = s := by
    dsimp only [q, τ]
    ring
  have hsShort : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) S :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q
  have hsT : t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hsShort.1, lt_of_lt_of_le hsShort.2 (le_of_lt hST)⟩
  have hPhysical :
      h3AuditInitialOldPhysicalHilbertTotal hH3 (t + (q : ℝ)) =
        h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hShort.navier_stokes ht hEnd hTail q := by
    apply PiLp.ext
    intro j
    change h3AuditActualPhysicalZeroJetL2Total hH3 j (t + (q : ℝ)) =
      h3PreterminalCanonicalL2JetOnElapsed
        hShort.navier_stokes ht hEnd hTail (h3JetSlot0 j) q
    rw [h3AuditActualPhysicalZeroJetL2Total_eq_at hH3 j _ hsT]
    rfl
  rw [← hTime, hPhysical]
  exact h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
    hShort.navier_stokes ht hEnd hTail q

/-- The zero-extended actual physical projected RHS is Leray-fixed even
outside the open preterminal interval, where both sources are zero. -/
theorem h3Audit_initialActualProjectedRHS_lerayFixed_allTimes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s) := by
  by_cases hs : s ∈ Set.Ioo (0 : ℝ) T
  · exact h3Audit_initialActualProjectedRHS_lerayFixed_at_positiveTime
      hH3 s hs
  · have hZero : H3PhysicalRealFinVectorL2HilbertLerayFixed
        (0 : H3PhysicalRealFinVectorL2Hilbert) :=
      (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff _).1
        (Submodule.zero_mem _)
    simpa only [h3AuditInitialActualSpectralLaplacianTotal,
      h3AuditInitialActualSpectralLerayTotal, dif_neg hs,
      sub_self] using hZero

/-- Automatic source continuity on any closed interval contained in
strictly positive physical time.  No continuity at time zero is needed. -/
theorem h3Audit_initialActualProjectedRHS_continuousOn_strictInterval
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hbT : b < T) :
    ContinuousOn
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      (Set.Icc a b) := by
  have hSub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ha hs.1,
      lt_of_le_of_lt hs.2 hbT⟩
  have hU : ContinuousOn
      (h3AuditActualSpectralVelocityTotal hH3) (Set.Icc a b) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSub
  have hD : ContinuousOn
      (h3AuditInitialActualSpectralLaplacianTotal hH3)
      (Set.Icc a b) := by
    have hComp := continuous_h3AuditSpectralPhysicalLaplacian.comp_continuousOn hU
    apply hComp.congr
    intro s hs
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      dite_eq_left (hSub hs), Function.comp_apply]
  have hN : ContinuousOn
      (h3AuditInitialActualSpectralLerayTotal hH3)
      (Set.Icc a b) := by
    have hComp := continuous_h3AuditSpectralPhysicalLerayForcing.comp_continuousOn hU
    apply hComp.congr
    intro s hs
    simp only [h3AuditInitialActualSpectralLerayTotal,
      dite_eq_left (hSub hs), Function.comp_apply]
  exact hD.sub hN

/-- The *actual* old physical velocity satisfies the unrestricted Schwartz
scalar time derivative provided only the solenoidal compact weak FTC on one
strict interval. Leray-fixedness of velocity and RHS, and source continuity,
are derived from the genuine positive-time H³ Navier--Stokes path. -/
theorem h3Audit_initialActualProjectedRHS_schwartzHasDerivAt_of_solenoidalWeakFTC
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (hWeak : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      a b)
    (Φ : H3PhysicalRealFinVectorSchwartz)
    (s : ℝ) (hs : s ∈ Set.Ioo a b) :
    HasDerivAt
      (fun x : ℝ =>
        ((innerSL ℝ) (h3AuditInitialOldPhysicalHilbertTotal hH3 x))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
      (((innerSL ℝ)
        (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) s := by
  have hCont := h3Audit_initialActualProjectedRHS_continuousOn_strictInterval
    hH3 a b ha hab hbT
  have hF : ∀ r : ℝ, r ∈ Set.Icc a b →
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3AuditInitialOldPhysicalHilbertTotal hH3 r) := by
    intro r hr
    exact h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
      hH3 r ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hbT⟩
  exact h3Audit_physicalSolenoidalWeakFTC_implies_SchwartzHasDerivAt
    (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (fun r : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLerayTotal hH3 r)
    a b hab hCont hF
    (h3Audit_initialActualProjectedRHS_lerayFixed_allTimes hH3)
    hWeak Φ s hs

end
end Euclidean
end Bridge
end PrimeTensor
