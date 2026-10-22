import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopEightMomentReduction244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low
import Mathlib.Tactic

/-!
# Kinetic closure of the raw Fourier L² branches of the eighth-moment escape

The exact physical kinetic budget controls every raw Fourier velocity L²
component. Its H³-path monotonicity provides a finite ceiling on any later
strict tail, without assuming an independent bound on raw L². Only the raw
Fourier L¹ factors and the order-eight moments can remain unbounded in the
six-input Young envelope. We derive an explicit L¹-or-eighth-moment terminal
alternative, and separately show how a spectral H³ norm ceiling controls the
remaining L¹ input via the already-proved deweighting inequality.

All moment-integrability premises remain explicit. None of these statements
excludes terminal escape by itself.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- On a later strict interval, physical kinetic monotonicity gives a
uniform bound for the actual raw Fourier L² norm of one velocity component.
No assumption about eighth moments or positivity of fourth dissipation. -/
theorem h3Path_rawVelocityFourierL2_le_sqrtKineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ‖h3SpectralScalarRawFourierL2 (U j)‖ ≤
      Real.sqrt (velocityH3Energy0At u s) := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hSquare :
      ‖h3SpectralScalarRawFourierL2 (U j)‖ ^ 2 ≤
        velocityH3Energy0At u t :=
    sq_norm_h3TerminalVelocityRawFourierL2_le_energy0
      hH3 hClass ht j
  have hAnti :
      AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3 hClass
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u s :=
    hAnti hs ht hst
  have hKineticNonneg : 0 ≤ velocityH3Energy0At u s :=
    velocityH3Energy0At_nonneg u s
  have hRoot :
      (Real.sqrt (velocityH3Energy0At u s)) ^ 2 =
        velocityH3Energy0At u s := Real.sq_sqrt hKineticNonneg
  have hRootNonneg : 0 ≤ Real.sqrt (velocityH3Energy0At u s) :=
    Real.sqrt_nonneg _
  have hNormNonneg : 0 ≤ ‖h3SpectralScalarRawFourierL2 (U j)‖ :=
    norm_nonneg _
  nlinarith only [hSquare, hKinetic, hRoot, hRootNonneg, hNormNonneg]

/-- Conjugation does not alter the kinetic ceiling. -/
theorem h3Path_rawVelocityFourierConjL2_le_sqrtKineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ‖h3SpectralScalarRawFourierConjL2 (U j)‖ ≤
      Real.sqrt (velocityH3Energy0At u s) := by
  simpa only [norm_h3SpectralScalarRawFourierConjL2_eq_rawFourierL2] using
    h3Path_rawVelocityFourierL2_le_sqrtKineticAnchor244
      hH3 hClass hs ht hst j

/-- The actual raw Fourier L¹ mass of a physical velocity coordinate, extended
by zero outside the strict interval. Unlike raw L², it is NOT automatically
uniformly bounded by kinetic energy. -/
noncomputable def h3PathVelocityRawFourierL1MassComponent244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ioo a T then
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    h3SpectralScalarRawFourierL1Mass
      (h3TerminalVelocitySpectralStateAt hH3 t htAbs j)
  else 0

/-- The zero extension agrees with the physical raw Fourier L¹ mass at a
strict physical time. -/
theorem h3Path_velocityRawFourierL1MassComponent_eq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    h3PathVelocityRawFourierL1MassComponent244 hH3 hClass j t =
      h3SpectralScalarRawFourierL1Mass
        (h3TerminalVelocitySpectralStateAt hH3 t htAbs j) := by
  unfold h3PathVelocityRawFourierL1MassComponent244
  simp only [dite_eq_left ht]

/-- If the ONLY remaining low-order input (Fourier L¹) has a common ceiling
on the strict tail, kinetic monotonicity automatically supplies the other two
low inputs. Hence the six-factor obstruction is an eighth-moment escape. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMoment_of_rawFourierL1Ceiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hL1 : ∀ t (ht : t ∈ Set.Ioo a T), s < t →
      ∀ j : Fin 3,
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let U : H3SpectralFinVectorState :=
        h3TerminalVelocitySpectralStateAt hH3 t htAbs
      h3SpectralScalarRawFourierL1Mass (U j) ≤ B) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r := by
  let C : ℝ := max B (Real.sqrt (velocityH3Energy0At u s))
  apply h3Path_unboundedPhysicalTop_forces_eightMoment_of_lowFourierCeiling244
    (B := C) hH3 hClass hs hEscape hMom
  intro t ht hst k
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hRaw :
      ‖h3SpectralScalarRawFourierL2 (U k)‖ ≤
        Real.sqrt (velocityH3Energy0At u s) :=
    h3Path_rawVelocityFourierL2_le_sqrtKineticAnchor244
      hH3 hClass hs ht (le_of_lt hst) k
  have hConj :
      ‖h3SpectralScalarRawFourierConjL2 (U k)‖ ≤
        Real.sqrt (velocityH3Energy0At u s) := by
    rw [norm_h3SpectralScalarRawFourierConjL2_eq_rawFourierL2]
    exact hRaw
  have hL1Bound : h3SpectralScalarRawFourierL1Mass (U k) ≤ B :=
    hL1 t ht hst k
  exact ⟨hConj.trans (le_max_right _ _),
    hRaw.trans (le_max_right _ _),
    hL1Bound.trans (le_max_left _ _)⟩

/-- Physical fourth-radial mass escape forces at least one of TWO genuine
high-frequency alternatives: unbounded raw Fourier L¹ velocity mass, or
cofinal unbounded order-eight Fourier velocity moment. The kinetic Fourier
L² channels are excluded without any extra bound assumption. -/
theorem h3Path_unboundedPhysicalTop_forces_rawL1_or_eightMomentEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧ ∃ j : Fin 3,
      K < h3PathVelocityRawFourierL1MassComponent244 hH3 hClass j r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  classical
  by_cases hUnbounded :
      ∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawFourierL1MassComponent244 hH3 hClass j r
  · exact Or.inl hUnbounded
  · right
    push Not at hUnbounded
    obtain ⟨B, hB⟩ := hUnbounded
    apply h3Path_unboundedPhysicalTop_forces_eightMoment_of_rawFourierL1Ceiling244
      hH3 hClass hs hEscape hMom
    intro t ht hst j
    have hTail : t ∈ Set.Ioo s T := ⟨hst, ht.2⟩
    have hBound := hB t hTail j
    simpa only [h3Path_velocityRawFourierL1MassComponent_eq244
      hH3 hClass ht j] using hBound

/-- A single physical spectral H³ ceiling also controls raw Fourier L¹ via
existing Sobolev deweighting; combined with kinetic monotonicity it forces the
necessary terminal escape into the order-eight moment alone. The ceiling is
still an explicit analytic assumption, not inferred from the PDE. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMoment_of_spectralH3Ceiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hSpectral : ∀ t (ht : t ∈ Set.Ioo a T), s < t →
      ∀ j : Fin 3,
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let U : H3SpectralFinVectorState :=
        h3TerminalVelocitySpectralStateAt hH3 t htAbs
      ‖U j‖ ≤ B) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r := by
  apply h3Path_unboundedPhysicalTop_forces_eightMoment_of_rawFourierL1Ceiling244
    (B := h3RawFourierL1DeweightingCoefficient * B)
    hH3 hClass hs hEscape hMom
  intro t ht hst j
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hBound : ‖U j‖ ≤ B := hSpectral t ht hst j
  exact (h3SpectralScalarRawFourierL1Mass_le_norm (U j)).trans
    (mul_le_mul_of_nonneg_left hBound
      h3RawFourierL1DeweightingCoefficient_nonneg)

end
end PrimeTensor.FirstMonomialTriad
