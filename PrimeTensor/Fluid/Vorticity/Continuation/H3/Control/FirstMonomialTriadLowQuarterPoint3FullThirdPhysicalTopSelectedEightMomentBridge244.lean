import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopSecondRadialRepresentative244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product
import Mathlib.Tactic

/-!
# Transfer selected positive-time eighth moments to actual physical velocity

The selected mild state on every positive terminal-half slab has all finite
raw Fourier velocity moments. This alone does not assert that the actual
physical velocity slice is that selected state: the equality requires an
independent selected/old/physical spectral identification.

At a strict physical slice we retain the exact spectral equality as a
transparent condition. Once supplied, order-eight integrability transfers
immediately, and the physical terminal alternative needs no separate
moment-integrability or radial-representative hypothesis.

The selected realization condition is **not** deduced from mere H³
admissibility in this file. The next task is to discharge it using physical
restart overlap and spectral uniqueness. No unconditional regularity theorem
is claimed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- A literal selected mild spectral slice realizes an actual physical
velocity state. The two states are compared as complete weighted H³
spectral vectors, rather than merely as physical weak distributions. -/
def h3PathVelocitySelectedSlabRealizedAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) : Prop :=
  ∃ (t₀ E Q : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (s : Set.Icc (Q / 2) Q),
    t = t₀ + (s : ℝ) ∧
    h3TerminalVelocitySpectralStateAt hH3 t
      (show t ∈ Set.Ioo (0 : ℝ) T from
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) =
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hH3.navier_stokes ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)

/-- Exact selected-slice agreement transfers an eighth raw Fourier
moment to each *actual* physical velocity coordinate. -/
theorem h3Path_velocityRawEightMoments_of_selectedSlabEquality244
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
    (s : Set.Icc (Q / 2) Q)
    (hEq :
      h3TerminalVelocitySpectralStateAt hH3 t
        (show t ∈ Set.Ioo (0 : ℝ) T from
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) =
      h3PreterminalSelectedUnitSpectralStateOnRadius
        hH3.navier_stokes ht₀ hE hTail
        (h3SelectedProjectedRHSSlabRadius hE hQ hQR s)) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  change ∀ k : Fin 3,
    H3RawFourierMomentIntegrable (8 : ℝ)
      (h3TerminalVelocitySpectralStateAt hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ k)
  intro k
  rw [hEq]
  exact h3PreterminalSelectedUnitSpectralStateOnSlab_natMoment_integrable
    8 hH3.navier_stokes ht₀ hE hTail hQ hQR s k

/-- A positive selected realization of one physical time slice closes the
order-eight Fourier-moment premise at precisely that slice. -/
theorem h3Path_velocityRawEightMoments_of_selectedSlabRealization244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hSelected :
      h3PathVelocitySelectedSlabRealizedAt244 hH3 hClass ht) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  rcases hSelected with
    ⟨t₀, E, Q, ht₀, hE, hTail, hQ, hQR, s, _hTime, hEq⟩
  exact h3Path_velocityRawEightMoments_of_selectedSlabEquality244
    hH3 hClass ht ht₀ hE hTail hQ hQR s hEq

/-- Selected spectral coverage of the strict physical interval is sufficient
for the original velocity eighth-moment input, without an independent
raw high-moment axiom. -/
theorem h3Path_velocityRawEightMoments_of_selectedSlabCoverage244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hSelected : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocitySelectedSlabRealizedAt244 hH3 hClass ht) :
    ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  intro t ht
  exact h3Path_velocityRawEightMoments_of_selectedSlabRealization244
    hH3 hClass ht (hSelected t ht)

/-- Selected spectral coverage substitutes for all raw-eighth-moment input
assumptions in the physical second-dissipation/eighth-moment alternative.
The selected-to-physical equality is the only added spectral bridge. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_selectedSlabCoverage244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hSelected : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocitySelectedSlabRealizedAt244 hH3 hClass ht) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_noRep244
    hH3 hClass hs hEscape
  intro t ht
  exact h3Path_velocityRawEightMoments_of_selectedSlabRealization244
    hH3 hClass ht (hSelected t ht)

end
end PrimeTensor.FirstMonomialTriad
