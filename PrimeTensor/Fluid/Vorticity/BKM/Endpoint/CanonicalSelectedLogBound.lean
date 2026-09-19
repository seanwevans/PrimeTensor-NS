import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.SelectedActualGradientBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Encoded.Canonical.Energy.Restart.Closure

/-!
# BKM endpoint: canonical-energy logarithmic selected bound

The complete selected low/middle/high estimate is now available pointwise for
the actual logged velocity gradient.

The high and middle pieces can be put directly into the canonical BKM
logarithmic form by choosing the upper cutoff scale to be the normalized
canonical H³ energy

    E(t) = velocityH3EnergyAt u t.

Because `E(t) ≥ 1`, the selected scale is exactly `E(t)`, and

    logb 2 E(t) = log E(t) / log 2.

The low-frequency contribution is different: it depends on the physical
zeroth-order `L²` mass.  That quantity must be controlled uniformly on the
tail, not by the instantaneous H³ energy.  This file therefore isolates the
precise remaining input as a scalar bound `L`.

The result is the canonical pointwise logarithmic estimate conditional only on

    ‖u_j(t)‖₂ ≤ L.

A later kinetic-energy checkpoint will supply one time-independent `L` from
the tail anchor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointCanonicalSelectedLogBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Universal coefficient multiplying the vorticity-logarithm contribution. -/
noncomputable def h3BKMCanonicalMiddleLogCoefficient : ℝ :=
  (8 * (Real.log 2)⁻¹ + 4)
    * h3BKMDyadicKernelUnitMassConstant

/--
Time-independent coefficient in the canonical selected logarithmic gradient
bound, once `L` controls the physical zeroth-order velocity `L²` mass.
-/
noncomputable def h3BKMCanonicalSelectedLogGradientConstant
    (L : ℝ) : ℝ :=
  1
    + h3BKMLowGradientUnitL2Constant * L
    + (2 * Real.pi) * h3BKMQuarterTailMomentConstant
    + h3BKMCanonicalMiddleLogCoefficient

theorem h3BKMCanonicalMiddleLogCoefficient_nonneg :
    0 ≤ h3BKMCanonicalMiddleLogCoefficient := by

  have hlog2 :
      0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)

  have hinv :
      0 ≤ (Real.log (2 : ℝ))⁻¹ :=
    inv_nonneg.mpr hlog2.le

  unfold h3BKMCanonicalMiddleLogCoefficient

  exact
    mul_nonneg
      (by nlinarith)
      h3BKMDyadicKernelUnitMassConstant_nonneg

theorem h3BKMCanonicalSelectedLogGradientConstant_nonneg
    {L : ℝ}
    (hL : 0 ≤ L) :
    0 ≤ h3BKMCanonicalSelectedLogGradientConstant L := by

  have hLow :
      0 ≤ h3BKMLowGradientUnitL2Constant * L :=
    mul_nonneg
      h3BKMLowGradientUnitL2Constant_nonneg
      hL

  have hHigh :
      0 ≤
        (2 * Real.pi)
          * h3BKMQuarterTailMomentConstant :=
    mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_nonneg)
      h3BKMQuarterTailMomentConstant_nonneg

  have hMiddle :
      0 ≤ h3BKMCanonicalMiddleLogCoefficient :=
    h3BKMCanonicalMiddleLogCoefficient_nonneg

  unfold h3BKMCanonicalSelectedLogGradientConstant

  linarith [hLow, hHigh, hMiddle]

/--
One genuine encoded H³ component is bounded by the canonical normalized H³
energy itself.
-/
theorem norm_velocityH3SpectralScalarAt_le_canonicalEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ‖velocityH3SpectralScalarAt
        u t hInt hMeas hFourier j‖
      ≤
    velocityH3EnergyAt u t := by

  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hInt hMeas hFourier

  have hCoordinate :
      ‖U j‖ ≤ ‖U‖ :=
    h3SpectralVelocity_coordinate_norm_le U j

  have hEnergy :
      ‖U‖ ≤ velocityH3EnergyAt u t :=
    norm_velocityH3SpectralStateAt_le_energyCeiling
      hFourier
      (one_le_velocityH3EnergyAt u t)
      le_rfl

  exact hCoordinate.trans hEnergy

/--
The selected middle logarithmic term, at canonical cutoff scale, is controlled
by the universal middle coefficient times the standard BKM factor

    (1 + |g(t)|) (1 + log E(t)).
-/
theorem h3BKM_selectedMiddleTerm_canonicalEnergy_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t) :
    2
        * (4 * Real.logb 2
            (h3BKMUpperCutoffScale
              (velocityH3EnergyAt u t))
          + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant)
      ≤
    h3BKMCanonicalMiddleLogCoefficient
      * (1 + |g t|)
      * (1 + Real.log (velocityH3EnergyAt u t)) := by

  let E : ℝ := velocityH3EnergyAt u t
  let K : ℝ := h3BKMDyadicKernelUnitMassConstant
  let q : ℝ := (Real.log (2 : ℝ))⁻¹

  have hE :
      1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3EnergyAt u t

  have hlogE :
      0 ≤ Real.log E :=
    Real.log_nonneg hE

  have hg :
      0 ≤ g t :=
    h3BKM_vorticityEnvelope_nonneg hEnvelope

  have hK :
      0 ≤ K := by
    dsimp only [K]
    exact h3BKMDyadicKernelUnitMassConstant_nonneg

  have hlog2 :
      0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)

  have hq :
      0 ≤ q := by
    dsimp only [q]
    exact inv_nonneg.mpr hlog2.le

  have hScale :
      h3BKMUpperCutoffScale E = E := by
    unfold h3BKMUpperCutoffScale
    exact max_eq_right hE

  have hWidth :
      8 * q * Real.log E + 4
        ≤
      (8 * q + 4) * (1 + Real.log E) := by
    nlinarith [mul_nonneg hq hlogE]

  have hGK :
      0 ≤ g t * K :=
    mul_nonneg hg hK

  have hMiddle0 :
      (g t * K) * (8 * q * Real.log E + 4)
        ≤
      (g t * K) * ((8 * q + 4) * (1 + Real.log E)) :=
    mul_le_mul_of_nonneg_left hWidth hGK

  have hCoeff :
      0 ≤ (8 * q + 4) * K :=
    mul_nonneg
      (by nlinarith)
      hK

  have hgOne :
      g t ≤ 1 + g t := by
    linarith

  have hGrow :
      g t * (1 + Real.log E)
        ≤
      (1 + g t) * (1 + Real.log E) := by
    exact
      mul_le_mul_of_nonneg_right
        hgOne
        (by linarith)

  have hMiddle1 :
      ((8 * q + 4) * K)
          * (g t * (1 + Real.log E))
        ≤
      ((8 * q + 4) * K)
          * ((1 + g t) * (1 + Real.log E)) :=
    mul_le_mul_of_nonneg_left hGrow hCoeff

  have hAbs :
      |g t| = g t :=
    abs_of_nonneg hg

  change
    2
        * (4 * Real.logb 2
            (h3BKMUpperCutoffScale E)
          + 2)
        * (g t * K)
      ≤
    ((8 * q + 4) * K)
      * (1 + |g t|)
      * (1 + Real.log E)

  rw [hScale, hAbs]

  unfold Real.logb
  rw [div_eq_mul_inv]

  change
    2
        * (4 * (Real.log E * q) + 2)
        * (g t * K)
      ≤
    ((8 * q + 4) * K)
      * (1 + g t)
      * (1 + Real.log E)

  calc
    2
        * (4 * (Real.log E * q) + 2)
        * (g t * K)
        =
      (g t * K) * (8 * q * Real.log E + 4) := by
        ring

    _ ≤
      (g t * K)
        * ((8 * q + 4) * (1 + Real.log E)) :=
      hMiddle0

    _ =
      ((8 * q + 4) * K)
        * (g t * (1 + Real.log E)) := by
      ring

    _ ≤
      ((8 * q + 4) * K)
        * ((1 + g t) * (1 + Real.log E)) :=
      hMiddle1

    _ =
      ((8 * q + 4) * K)
        * (1 + g t)
        * (1 + Real.log E) := by
      ring

/--
Canonical-energy selected BKM logarithmic estimate for one actual logged
velocity derivative, assuming a uniform zeroth-order physical `L²` bound `L`.

This is the exact algebraic endpoint needed after kinetic-energy control.
-/
theorem one_add_abs_loggedVelocityComponent_spatial_d_le_canonicalSelectedBKM
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {g : ℝ → ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (L : ℝ)
    (hL : 0 ≤ L)
    (hLow :
      ∀ j : Fin 3,
        ‖velocityH3L2JetAt
            u t hInt hMeas
            (h3JetSlot0 j)‖
          ≤ L)
    (j i : Fin 3)
    (x : Point3) :
    1
        +
      abs
        (spatial3.d
          (h3AxisOfFin3 i)
          (loggedVelocityComponent
            u t (h3AxisOfFin3 j))
          x)
      ≤
    h3BKMCanonicalSelectedLogGradientConstant L
      * (1 + |g t|)
      * (1 + Real.log (velocityH3EnergyAt u t)) := by

  let E : ℝ := velocityH3EnergyAt u t

  have hComponent :
      ‖velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j‖
        ≤ E := by
    dsimp only [E]
    exact
      norm_velocityH3SpectralScalarAt_le_canonicalEnergy
        hFourier j

  have hSelected :=
    norm_loggedVelocityComponent_spatial_d_le_selectedBKM
      hNS ht hFourier hEnvelope
      E j i hComponent x

  have hSelectedAbs :
      abs
          (spatial3.d
            (h3AxisOfFin3 i)
            (loggedVelocityComponent
              u t (h3AxisOfFin3 j))
            x)
        ≤
      h3BKMLowGradientUnitL2Constant
          *
        ‖velocityH3L2JetAt
            u t hInt hMeas
            (h3JetSlot0 j)‖
        +
      2
        * (4 * Real.logb 2
            (h3BKMUpperCutoffScale E)
          + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant)
        +
      (2 * Real.pi)
        * h3BKMQuarterTailMomentConstant := by

    simpa only [Real.norm_eq_abs] using hSelected

  have hLowTerm :
      h3BKMLowGradientUnitL2Constant
          *
        ‖velocityH3L2JetAt
            u t hInt hMeas
            (h3JetSlot0 j)‖
        ≤
      h3BKMLowGradientUnitL2Constant * L :=
    mul_le_mul_of_nonneg_left
      (hLow j)
      h3BKMLowGradientUnitL2Constant_nonneg

  have hMiddle :=
    h3BKM_selectedMiddleTerm_canonicalEnergy_le
      hEnvelope

  have hE :
      1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3EnergyAt u t

  have hlogE :
      0 ≤ Real.log E :=
    Real.log_nonneg hE

  have hg :
      0 ≤ g t :=
    h3BKM_vorticityEnvelope_nonneg hEnvelope

  have hAbs :
      |g t| = g t :=
    abs_of_nonneg hg

  let F : ℝ :=
    (1 + |g t|) * (1 + Real.log E)

  have hFone :
      1 ≤ F := by
    dsimp only [F]
    rw [hAbs]
    nlinarith [mul_nonneg hg hlogE]

  let C0 : ℝ :=
    1
      + h3BKMLowGradientUnitL2Constant * L
      + (2 * Real.pi) * h3BKMQuarterTailMomentConstant

  have hC0 :
      0 ≤ C0 := by
    dsimp only [C0]
    have hLowNonneg :
        0 ≤ h3BKMLowGradientUnitL2Constant * L :=
      mul_nonneg
        h3BKMLowGradientUnitL2Constant_nonneg
        hL
    have hHighNonneg :
        0 ≤
          (2 * Real.pi)
            * h3BKMQuarterTailMomentConstant :=
      mul_nonneg
        (mul_nonneg (by norm_num) Real.pi_nonneg)
        h3BKMQuarterTailMomentConstant_nonneg
    linarith [hLowNonneg, hHighNonneg]

  have hC0Grow :
      C0 ≤ C0 * F := by
    have h :=
      mul_le_mul_of_nonneg_left hFone hC0
    simpa only [mul_one] using h

  have hBase :
      1
          +
        abs
          (spatial3.d
            (h3AxisOfFin3 i)
            (loggedVelocityComponent
              u t (h3AxisOfFin3 j))
            x)
        ≤
      C0
        +
      2
        * (4 * Real.logb 2
            (h3BKMUpperCutoffScale E)
          + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by

    dsimp only [C0]

    linarith

  have hMiddleF :
      2
          * (4 * Real.logb 2
              (h3BKMUpperCutoffScale E)
            + 2)
          * (g t * h3BKMDyadicKernelUnitMassConstant)
        ≤
      h3BKMCanonicalMiddleLogCoefficient * F := by
    simpa only [F, E, mul_assoc] using hMiddle

  calc
    1
        +
      abs
        (spatial3.d
          (h3AxisOfFin3 i)
          (loggedVelocityComponent
            u t (h3AxisOfFin3 j))
          x)
        ≤
      C0
        +
      2
        * (4 * Real.logb 2
            (h3BKMUpperCutoffScale E)
          + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      hBase

    _ ≤
      C0 * F
        +
      h3BKMCanonicalMiddleLogCoefficient * F :=
      add_le_add hC0Grow hMiddleF

    _ =
      h3BKMCanonicalSelectedLogGradientConstant L
        * F := by
      dsimp only [
        C0,
        h3BKMCanonicalSelectedLogGradientConstant
      ]
      ring

    _ =
      h3BKMCanonicalSelectedLogGradientConstant L
        * (1 + |g t|)
        * (1 + Real.log (velocityH3EnergyAt u t)) := by
      simp only [F, E, mul_assoc]

end

end Euclidean
end Bridge
end PrimeTensor
