import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticLowBandSourceLipschitz
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryAnnularClockRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEPolarization244
import Mathlib.Tactic

/-!
# Kinetic-only physical time modulus for actual H3 finite-annulus dissipation

The verified physical Hilbert FTC and kinetic Bernstein estimates give a
uniform-in-time, cutoff-dependent Lipschitz modulus for each weighted H3
Fourier low band. This module applies the actual sharp-gradient Fourier
multiplier to that time modulus. The frequency support identity is proved,
not assumed: the radial gradient multiplier annihilates the exact
complementary high-band Fourier projector.

Kinetic energy controls BOTH endpoint low-band states. Thus ordinary
polarization produces a LINEAR time bound on the bounded-frequency H3
viscous quadratic, without any full-H3 or full-source maxima. Subtracting
two natural-radius low bands gives the physical finite-annulus time modulus.
The outer cutoff is still allowed to grow; no uniform terminal H3 trace or
Navier--Stokes continuation conclusion is made.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeKineticAnnular244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceKineticAnnular244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The sharp radial-gradient Fourier multiplier sees only the natural
low-pass projection, exactly as L2 equivalence classes. This removes the
uncontrolled H3 high-frequency state from the gradient increment. -/
theorem thirdFullKinetic_gradientMultiplier_ignoresHighRadial244
    (R : ℕ) (G : H3SpectralScalarState) :
    h3PathLowRadialGradientMultiplierCLM244 ((R : ℝ) + 1) (by positivity) G =
      h3PathLowRadialGradientMultiplierCLM244 ((R : ℝ) + 1) (by positivity)
        (G - thirdFullSpectralHighRadialApply244 R G) := by
  let ρ : ℝ := (R : ℝ) + 1
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  change h3PathLowRadialGradientMultiplierApply244 ρ hρ G =
    h3PathLowRadialGradientMultiplierApply244 ρ hρ
      (G - thirdFullSpectralHighRadialApply244 R G)
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ G,
    h3Path_lowRadialGradientMultiplierApply_ae244 ρ hρ
      (G - thirdFullSpectralHighRadialApply244 R G),
    thirdFullSpectralScalarLowRadial_ae244 R G
  ] with ξ hWhole hProjected hLow
  rw [hWhole, hProjected, hLow]
  by_cases hξ : ξ ∈ h3TerminalRadialFrequencyBelow ρ
  · have hξR : ξ ∈ h3TerminalRadialFrequencyBelow ((R : ℝ) + 1) := by
      simpa only [ρ] using hξ
    simp only [h3PathLowRadialGradientMultiplier244, if_pos hξ,
      Set.indicator_of_mem hξR]
  · have hξR : ξ ∉ h3TerminalRadialFrequencyBelow ((R : ℝ) + 1) := by
      simpa only [ρ] using hξ
    simp [h3PathLowRadialGradientMultiplier244, hξ, hξR]

/-- Exact finite-band H3 dissipation is invariant when its input is
replaced by the weighted low-pass spectral velocity at the same cutoff. -/
theorem thirdFullKinetic_lowRadialDissipation_eq_projected244
    (R : ℕ) (G : H3SpectralVelocityState) :
    h3PathActualLowRadialDissipation244 ((R : ℝ) + 1) G =
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (thirdFullSpectralVelocityLowRadialApply244 R G) := by
  let ρ : ℝ := (R : ℝ) + 1
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hCoordinate (j : Fin 3) :
      h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j) =
      h3PathLowRadialGradientMultiplierCLM244 ρ hρ
        ((thirdFullSpectralVelocityLowRadialApply244 R G) j) := by
    simpa only [ρ, thirdFullSpectralVelocityLowRadialApply244,
      thirdFullSpectralVelocityHighRadialApply244, Pi.sub_apply] using
      (thirdFullKinetic_gradientMultiplier_ignoresHighRadial244 R (G j))
  change h3PathActualLowRadialDissipation244 ρ G =
    h3PathActualLowRadialDissipation244 ρ
      (thirdFullSpectralVelocityLowRadialApply244 R G)
  rw [h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ G,
    h3Path_actualLowRadialDissipation_eq_multiplierNormSquares244 ρ hρ
      (thirdFullSpectralVelocityLowRadialApply244 R G)]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hCoordinate j]

/-- The ACTUAL weighted low-band H3 state has a uniform kinetic ceiling
at every later time. This bounds both endpoints of the dissipation
polarization, rather than just its initial endpoint. -/
theorem thirdFullPhysical_kineticLowBandStateCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo b T) :
    ‖thirdFullSpectralVelocityLowRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖ ≤
      thirdFullFiniteBandH3WeightCeiling244 R *
        Real.sqrt (velocityH3Energy0At u b) := by
  let U := h3AuditActualSpectralVelocityTotal hH3 t
  let E := velocityH3Energy0At u b
  let F : H3SpectralFinVectorState :=
    fun j => h3SpectralScalarRawFourierL2 (U j)
  have hRaw : ‖F‖ ≤ Real.sqrt E := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg E)).2
    intro j
    exact h3Critical_actual_rawVelocityFourierL2_norm_le_kineticAnchor
      hH3 hClass b hb t ht j
  have hWeight :
      ‖thirdFullSpectralVelocityLowRadialApply244 R U‖ ≤
        thirdFullFiniteBandH3WeightCeiling244 R * ‖F‖ :=
    thirdFullSpectralVelocityLowRadial_norm_le_raw244 R U
  exact hWeight.trans
    (mul_le_mul_of_nonneg_left hRaw
      (thirdFullFiniteBandH3WeightCeiling_nonneg244 R))

/-- Exact physical kinetic-only variation coefficient for bounded-frequency
H3 dissipation. Both state amplitude and projected-PDE time rate are paid
by the same earlier physical kinetic anchor. -/
noncomputable def thirdFullPhysicalKineticLowBandDissipationRate244
    (R : ℕ) (E : ℝ) : ℝ :=
  6 * ((R : ℝ) + 2) *
    (thirdFullFiniteBandH3WeightCeiling244 R * Real.sqrt E) *
    (((R : ℝ) + 2) *
      (thirdFullFiniteBandH3WeightCeiling244 R *
        thirdFullPhysicalKineticLowBandSourceCeiling244 ((R : ℝ) + 1) E))

theorem thirdFullPhysicalKineticLowBandDissipationRate_nonneg244
    (R : ℕ) (E : ℝ) :
    0 ≤ thirdFullPhysicalKineticLowBandDissipationRate244 R E := by
  unfold thirdFullPhysicalKineticLowBandDissipationRate244
  have hW := thirdFullFiniteBandH3WeightCeiling_nonneg244 R
  have hC := thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244
    ((R : ℝ) + 1) E
  have hRadius : 0 ≤ (R : ℝ) + 2 := by positivity
  have hA : 0 ≤
      thirdFullFiniteBandH3WeightCeiling244 R * Real.sqrt E :=
    mul_nonneg hW (Real.sqrt_nonneg E)
  have hB : 0 ≤ ((R : ℝ) + 2) *
      (thirdFullFiniteBandH3WeightCeiling244 R *
        thirdFullPhysicalKineticLowBandSourceCeiling244 ((R : ℝ) + 1) E) :=
    mul_nonneg hRadius (mul_nonneg hW hC)
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hRadius) hA) hB

/-- The true low-radial H3 dissipation has a global-in-time LIPSCHITZ
modulus on every anchored strict tail, with no full-H3 state/source ceilings.
The only time-dependent quantity on the RHS is elapsed time. -/
theorem thirdFullPhysical_kineticLowRadialDissipationLipschitz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R : ℕ) (s t : ℝ) (hs : s ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo b T) (hst : s ≤ t) :
    |h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)| ≤
      thirdFullPhysicalKineticLowBandDissipationRate244 R
        (velocityH3Energy0At u b) * (t - s) := by
  let ρ : ℝ := (R : ℝ) + 1
  let E : ℝ := velocityH3Energy0At u b
  let W : ℝ := thirdFullFiniteBandH3WeightCeiling244 R
  let C : ℝ := thirdFullPhysicalKineticLowBandSourceCeiling244 ρ E
  let K : ℝ := W * Real.sqrt E
  let V : ℝ := (ρ + 1) * (W * C)
  let U : ℝ → H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3
  let G := thirdFullSpectralVelocityLowRadialApply244 R (U s)
  let H := thirdFullSpectralVelocityLowRadialApply244 R (U t)
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hW : 0 ≤ W := thirdFullFiniteBandH3WeightCeiling_nonneg244 R
  have hC : 0 ≤ C := thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 ρ E
  have hK : 0 ≤ K := mul_nonneg hW (Real.sqrt_nonneg E)
  have hV : 0 ≤ V := mul_nonneg (by dsimp only [ρ]; positivity)
    (mul_nonneg hW hC)
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  have hG : ‖G‖ ≤ K :=
    thirdFullPhysical_kineticLowBandStateCeiling244
      hH3 hClass b hb R s hs
  have hH : ‖H‖ ≤ K :=
    thirdFullPhysical_kineticLowBandStateCeiling244
      hH3 hClass b hb R t ht
  have hLip : ‖G - H‖ ≤ W * (C * (t - s)) :=
    thirdFullPhysical_kineticLowRadialH3Lipschitz244
      hH3 hClass b hb R s t hs ht hst
  have hDiff (j : Fin 3) :
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j - H j)‖ ≤
        V * (t - s) := by
    have hCoord : ‖G j - H j‖ ≤ ‖G - H‖ := by
      simpa only [Pi.sub_apply] using (norm_le_pi_norm (G - H) j)
    calc
      ‖h3PathLowRadialGradientMultiplierCLM244 ρ hρ (G j - H j)‖ ≤
          (ρ + 1) * ‖G j - H j‖ :=
        h3Path_lowRadialGradientMultiplierApply_norm_le244
          ρ hρ (G j - H j)
      _ ≤ (ρ + 1) * ‖G - H‖ :=
        mul_le_mul_of_nonneg_left hCoord (by dsimp only [ρ]; positivity)
      _ ≤ (ρ + 1) * (W * (C * (t - s))) :=
        mul_le_mul_of_nonneg_left hLip (by dsimp only [ρ]; positivity)
      _ = V * (t - s) := by dsimp only [V]; ring
  have hStable := h3Path_lowRadialDissipation_multiplierIncrementStability244
    ρ K (V * (t - s)) hρ hK (mul_nonneg hV hd)
    G H (fun j => (norm_le_pi_norm G j).trans hG)
    (fun j => (norm_le_pi_norm H j).trans hH) hDiff
  change |h3PathActualLowRadialDissipation244 ρ
      (thirdFullSpectralVelocityLowRadialApply244 R (U s)) -
    h3PathActualLowRadialDissipation244 ρ
      (thirdFullSpectralVelocityLowRadialApply244 R (U t))| ≤
      6 * (ρ + 1) * K * (V * (t - s)) at hStable
  rw [← thirdFullKinetic_lowRadialDissipation_eq_projected244 R (U s),
    ← thirdFullKinetic_lowRadialDissipation_eq_projected244 R (U t)] at hStable
  have hAlgebra : 6 * (ρ + 1) * K * (V * (t - s)) =
      thirdFullPhysicalKineticLowBandDissipationRate244 R E * (t - s) := by
    dsimp only [V, K, W, C, ρ,
      thirdFullPhysicalKineticLowBandDissipationRate244]
    ring
  change |h3PathActualLowRadialDissipation244 ρ (U s) -
      h3PathActualLowRadialDissipation244 ρ (U t)| ≤
    thirdFullPhysicalKineticLowBandDissipationRate244 R E * (t - s)
  calc
    |h3PathActualLowRadialDissipation244 ρ (U s) -
        h3PathActualLowRadialDissipation244 ρ (U t)| ≤
        6 * (ρ + 1) * K * (V * (t - s)) := hStable
    _ = thirdFullPhysicalKineticLowBandDissipationRate244 R E * (t - s) := hAlgebra

/-- A true finite annulus bounded by TWO natural Fourier radii has a
KINETIC-ONLY linear PDE time modulus. This replaces the prior full-H3
state/source attained-maxima coefficient at natural cutoffs. -/
theorem thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (R Q : ℕ) (s t : ℝ) (hs : s ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo b T) (hst : s ≤ t) :
    |(h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s)) -
      (h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t))| ≤
      (thirdFullPhysicalKineticLowBandDissipationRate244 Q
          (velocityH3Energy0At u b) +
        thirdFullPhysicalKineticLowBandDissipationRate244 R
          (velocityH3Energy0At u b)) * (t - s) := by
  let U : ℝ → H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3
  let Dq : ℝ → ℝ := fun x => h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1) (U x)
  let Dr : ℝ → ℝ := fun x => h3PathActualLowRadialDissipation244 ((R : ℝ) + 1) (U x)
  let Lq : ℝ := thirdFullPhysicalKineticLowBandDissipationRate244 Q
    (velocityH3Energy0At u b)
  let Lr : ℝ := thirdFullPhysicalKineticLowBandDissipationRate244 R
    (velocityH3Energy0At u b)
  have hQ : |Dq s - Dq t| ≤ Lq * (t - s) :=
    thirdFullPhysical_kineticLowRadialDissipationLipschitz244
      hH3 hClass b hb Q s t hs ht hst
  have hR : |Dr s - Dr t| ≤ Lr * (t - s) :=
    thirdFullPhysical_kineticLowRadialDissipationLipschitz244
      hH3 hClass b hb R s t hs ht hst
  change |(Dq s - Dr s) - (Dq t - Dr t)| ≤ (Lq + Lr) * (t - s)
  calc
    |(Dq s - Dr s) - (Dq t - Dr t)| =
        |(Dq s - Dq t) - (Dr s - Dr t)| := by congr 1 <;> ring
    _ ≤ |Dq s - Dq t| + |Dr s - Dr t| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (Dq s - Dq t) (-(Dr s - Dr t)))
    _ ≤ Lq * (t - s) + Lr * (t - s) := add_le_add hQ hR
    _ = (Lq + Lr) * (t - s) := by ring

/-- A pointwise finite-annulus spike at NATURAL radial endpoints has a
KINETIC-ONLY explicit physical persistence width and a true terminal H3
viscous cost. Unlike the earlier annular PDE rate, its clock does not use
attained full-H3 source/state maxima. It does retain the selected outer
frequency Q, which is not claimed uniformly bounded near T. -/
theorem thirdFullPhysical_kineticNaturalAnnularRightTailCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m x : ℝ) (hm : m ∈ Set.Ioo b T) (hx : x ∈ Set.Ioo m T)
    (R Q : ℕ) (A : ℝ) (hA : 0 < A)
    (hPeak : 2 * A <
      h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 x) -
      h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 x)) :
    ∃ δ : ℝ, 0 < δ ∧
      δ = min ((T - x) / 4)
        (A / (2 *
          (thirdFullPhysicalKineticLowBandDissipationRate244 Q
            (velocityH3Energy0At u b) +
           thirdFullPhysicalKineticLowBandDissipationRate244 R
            (velocityH3Energy0At u b) + 1))) ∧
      x + δ < T ∧
      (∀ r : ℝ, r ∈ Set.Icc x (x + δ) →
        A < h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((R : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) ≤
          velocityH3DissipationAt u r) ∧
      δ * A ≤ ∫ r in m..T, velocityH3DissipationAt u r ∂volume := by
  let U : ℝ → H3SpectralVelocityState := h3AuditActualSpectralVelocityTotal hH3
  let D : ℝ → ℝ := velocityH3DissipationAt u
  let Ann : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((Q : ℝ) + 1) (U r) -
    h3PathActualLowRadialDissipation244 ((R : ℝ) + 1) (U r)
  let Λ : ℝ :=
    thirdFullPhysicalKineticLowBandDissipationRate244 Q
      (velocityH3Energy0At u b) +
    thirdFullPhysicalKineticLowBandDissipationRate244 R
      (velocityH3Energy0At u b)
  have hΛ : 0 ≤ Λ := add_nonneg
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 Q _)
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 R _)
  have hd : 0 < (T - x) / 2 := by linarith only [hx.2]
  obtain ⟨δ, hδ, hδHalf, hδEq, hRate⟩ :=
    h3Critical_scalar_annularPDE_positivePersistenceRadius
      A Λ ((T - x) / 2) hA hΛ hd
  have hδEnd : x + δ < T := by linarith only [hδHalf, hx.2]
  have hxTail : x ∈ Set.Ioo b T :=
    ⟨lt_trans hm.1 hx.1, hx.2⟩
  have hxClass : x ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hxTail.1, hxTail.2⟩
  have hRadR : 0 ≤ (R : ℝ) + 1 := by positivity
  have hRadQ : 0 ≤ (Q : ℝ) + 1 := by positivity
  have hFloor (r : ℝ) (hr : r ∈ Set.Icc x (x + δ)) : A < Ann r := by
    have hrTail : r ∈ Set.Ioo b T :=
      ⟨lt_of_lt_of_le hxTail.1 hr.1, lt_of_le_of_lt hr.2 hδEnd⟩
    have hVar := thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244
      hH3 hClass b hb R Q x r hxTail hrTail hr.1
    change |Ann x - Ann r| ≤ Λ * (r - x) at hVar
    have hError : Ann x - Ann r ≤ Λ * (r - x) :=
      (le_abs_self (Ann x - Ann r)).trans hVar
    have hElapsed : r - x ≤ δ := by linarith only [hr.2]
    have hBound : Λ * (r - x) ≤ Λ * δ :=
      mul_le_mul_of_nonneg_left hElapsed hΛ
    change 2 * A < Ann x at hPeak
    linarith only [hError, hBound, hRate, hPeak]
  have hSub : Set.Icc x (x + δ) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hxClass.1 hr.1, lt_of_le_of_lt hr.2 hδEnd⟩
  have hFull (r : ℝ) (hr : r ∈ Set.Icc x (x + δ)) :
      Ann r ≤ D r := by
    have hrClass : r ∈ Set.Ioo a T := hSub hr
    exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass r hrClass ((R : ℝ) + 1) ((Q : ℝ) + 1)
  have hAnnInt : IntervalIntegrable Ann volume x (x + δ) := by
    have hCont : ContinuousOn Ann (Set.Ioo a T) :=
      h3Path_finiteAnnularDissipation_continuousOn244
        hH3 hClass ((R : ℝ) + 1) ((Q : ℝ) + 1) hRadR hRadQ
    exact (hCont.mono hSub).intervalIntegrable_of_Icc
      (by linarith only [hδ])
  have hAnnCost : δ * A ≤ ∫ r in x..(x + δ), Ann r ∂volume := by
    have hCost := h3Path_localPositiveHeight_forces_integratedCost244
      Ann x (x + δ) A (by linarith only [hδ]) hAnnInt
      (fun r hr => (hFloor r hr).le)
    calc
      δ * A = ((x + δ) - x) * A := by ring
      _ ≤ ∫ r in x..(x + δ), Ann r ∂volume := hCost
  have hmClass : m ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hm.1, hm.2⟩
  have hDtail : IntervalIntegrable D volume m T := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hmClass.2.le] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hmClass.1.le.trans hrIcc.1, hrIcc.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hDwindow : IntervalIntegrable D volume x (x + δ) := by
    apply hDInt.mono_set
    intro r hr
    have hrIcc : r ∈ Set.Icc x (x + δ) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hδ.le)] using hr
    have hrAll : r ∈ Set.Icc a T :=
      ⟨hxClass.1.le.trans hrIcc.1, hrIcc.2.trans hδEnd.le⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hrAll
  have hAnnLeD : (∫ r in x..(x + δ), Ann r ∂volume) ≤
      ∫ r in x..(x + δ), D r ∂volume := by
    apply intervalIntegral.integral_mono_on
      (le_add_of_nonneg_right hδ.le) hAnnInt hDwindow
    intro r hr
    exact hFull r hr
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc m T)] D := by
    filter_upwards [] with r
    exact velocityH3DissipationAt_nonneg u r
  have hWindowTail : (∫ r in x..(x + δ), D r ∂volume) ≤
      ∫ r in m..T, D r ∂volume :=
    intervalIntegral.integral_mono_interval
      hx.1.le (le_add_of_nonneg_right hδ.le) hδEnd.le hNonneg hDtail
  refine ⟨δ, hδ, ?_, hδEnd, ?_, ?_⟩
  · simpa only [Λ, show ((T - x) / 2) / 2 = (T - x) / 4 by ring] using hδEq
  · intro r hr
    exact ⟨hFloor r hr, hFull r hr⟩
  · exact (hAnnCost.trans hAnnLeD).trans hWindowTail

end
end PrimeTensor.FirstMonomialTriad
