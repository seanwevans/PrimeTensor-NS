import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopSelectedEightMomentBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Spectral.State.Old.Bridge
import Mathlib.Tactic

/-!
# Transfer local selected/old physical uniqueness to eighth physical moments

At an interior preterminal time, the intrinsic physical H³ spectral velocity
state and the old canonical spectral elapsed-time snapshot are literally the
same Fourier encoding of the same physical velocity. Their apparent difference
is only the choice of H³ integrability/Fourier-compatibility proof.

The existing selected/old overlap theorem upgrades pointwise agreement of the
smooth selected restart with the old physical velocity to equality of their
weighted H³ spectral states. Combining these two statements turns a local
*physical* agreement condition into the selected spectral realization used
by the previous eighth-moment obstruction theorem.

This file does NOT deduce the pointwise physical agreement from generic H³
admissibility. That is a uniqueness/restart input and the actual next frontier.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3SelectedPhysicalOverlap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- An old canonical spectral snapshot is the actual intrinsic physical H³
spectral state at the same absolute time. Both are defined using the same
`velocityH3SpectralStateAt`, so the particular integrability witnesses are
irrelevant. No mild-solution agreement is assumed here. -/
theorem h3Path_physicalSpectral_eq_oldCanonicalElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t t₀ Q E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t₀ + Q < T)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (q : Set.Icc (0 : ℝ) Q)
    (hTime : t = t₀ + (q : ℝ)) :
    h3TerminalVelocitySpectralStateAt hH3 t
        (show t ∈ Set.Ioo (0 : ℝ) T from
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hH3.navier_stokes ht₀ hEnd hTail q := by
  subst t
  rfl

/-- The new, weaker realization condition uses physical-space agreement on
ONE strict positive restart slab, rather than postulating an equality of
weighted Fourier H³ states. The old absolute endpoint is retained explicitly. -/
def h3PathVelocitySelectedPhysicalOverlapAt244
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
    H3PreterminalSelectedPhysicalAgreementAt
      (one_pos : (0 : ℝ) < 1)
      (s : ℝ)
      hH3.navier_stokes ht₀ hE hTail

/-- The established selected/old spectral overlap theorem, together with
the definitional old/physical snapshot identity, transfers a local pointwise
selected/old velocity equality into the exact spectral identity. -/
theorem h3Path_selectedSlabRealized_of_physicalAgreement244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t t₀ E Q : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t₀ + Q < T)
    (s : Set.Icc (Q / 2) Q)
    (hTime : t = t₀ + (s : ℝ))
    (hAgree : H3PreterminalSelectedPhysicalAgreementAt
      (one_pos : (0 : ℝ) < 1) (s : ℝ)
      hH3.navier_stokes ht₀ hE hTail) :
    h3PathVelocitySelectedSlabRealizedAt244 hH3 hClass ht := by
  let q : Set.Icc (0 : ℝ) Q :=
    ⟨(s : ℝ), (lt_of_lt_of_le (by positivity : 0 < Q / 2) s.property.1).le,
      s.property.2⟩
  have hqPos : 0 < (q : ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < Q / 2) s.property.1
  have hRadius :
      h3PreterminalElapsedToSelectedUnitRadius hQR.le q =
      h3SelectedProjectedRHSSlabRadius hE hQ hQR s := by
    apply Subtype.ext
    rfl
  have hOld :
      h3TerminalVelocitySpectralStateAt hH3 t
        (show t ∈ Set.Ioo (0 : ℝ) T from
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hH3.navier_stokes ht₀ hEnd hTail q :=
    h3Path_physicalSpectral_eq_oldCanonicalElapsed244
      hH3 hClass ht ht₀ hEnd hTail q hTime
  have hSelectedOld :=
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_physicalAgreement
      hH3.navier_stokes ht₀ hEnd hE hTail hQR.le q hqPos hAgree
  refine ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, s, hTime, ?_⟩
  calc
    h3TerminalVelocitySpectralStateAt hH3 t
          (show t ∈ Set.Ioo (0 : ℝ) T from
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) =
        h3PreterminalTailCanonicalSpectralStateOnElapsed
          hH3.navier_stokes ht₀ hEnd hTail q := hOld
    _ = h3PreterminalSelectedUnitSpectralStateOnRadius
          hH3.navier_stokes ht₀ hE hTail
          (h3PreterminalElapsedToSelectedUnitRadius hQR.le q) :=
        hSelectedOld.symm
    _ = h3PreterminalSelectedUnitSpectralStateOnRadius
          hH3.navier_stokes ht₀ hE hTail
          (h3SelectedProjectedRHSSlabRadius hE hQ hQR s) := by
        rw [hRadius]

/-- The local physical-overlap condition is enough for the selected-spectral
realization condition of the preceding module. -/
theorem h3Path_selectedSlabRealized_of_physicalOverlap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hOverlap : h3PathVelocitySelectedPhysicalOverlapAt244 hH3 hClass ht) :
    h3PathVelocitySelectedSlabRealizedAt244 hH3 hClass ht := by
  rcases hOverlap with
    ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, hEnd, s, hTime, hAgree⟩
  exact h3Path_selectedSlabRealized_of_physicalAgreement244
    hH3 hClass ht ht₀ hE hTail hQ hQR hEnd s hTime hAgree

/-- Physical uniqueness on a covering family of positive-time restart slabs
supplies every eighth velocity Fourier moment at every strict time. -/
theorem h3Path_velocityRawEightMoments_of_physicalOverlapCoverage244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hOverlap : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocitySelectedPhysicalOverlapAt244 hH3 hClass ht) :
    ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  intro t ht
  exact h3Path_velocityRawEightMoments_of_selectedSlabRealization244
    hH3 hClass ht
    (h3Path_selectedSlabRealized_of_physicalOverlap244
      hH3 hClass ht (hOverlap t ht))

/-- The lower-order dissipation/eighth velocity moment obstruction now asks
for local pointwise selected/old physical uniqueness on a positive slab at
each strict time. No high-moment or spectral equality axiom is added. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_physicalOverlap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hOverlap : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocitySelectedPhysicalOverlapAt244 hH3 hClass ht) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_selectedSlabCoverage244
    hH3 hClass hs hEscape
  intro t ht
  exact h3Path_selectedSlabRealized_of_physicalOverlap244
    hH3 hClass ht (hOverlap t ht)

end
end PrimeTensor.FirstMonomialTriad
