import PrimeTensor.Fluid.Vorticity.Continuation.H3.Pressure.Cancel.Higher
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Pressure.Classical.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Velocity.Increment.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldJetCompactWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge.Energy

/-!
# Close the gauge-sensitive zeroth-order H³ pressure cancellation

The positive-order pressure blocks were closed by ordinary whole-space
integration by parts because their scalar pressure potentials already belong to
physical `L²`.  At order zero the potential is `p` itself, so that argument is
not gauge invariant: pressure is determined only up to a spatial constant and
there is no reason to require the chosen representative to lie in global
`L²`.

The correct zeroth-order argument uses only the pressure gradient.

* the split-pressure gradient belongs to physical `L²`;
* every compactly supported smooth divergence-free test vector annihilates a
  classical scalar gradient by the existing ordinary-distribution theorem;
* compact smooth divergence-free tests have closed span equal to the physical
  Leray-fixed `L²` submodule;
* the old velocity slice is Leray-fixed, hence belongs to that closed span.

Therefore the physical `L²` pairing of the old velocity with the split-pressure
gradient is zero.  The zeroth H³ pressure contribution is exactly twice that
pairing, so it vanishes without ever choosing an `L²` gauge for the pressure.

Together with `H3PathPressureCancellationHigher`, this closes the full pressure
cancellation package and removes pressure from the active continuation
frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathPressureCancellationZero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathPressureCancellationZero :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Gauge-safe weak gradient annihilation -/

/-- A classical `C¹` scalar gradient annihilates every compactly supported
smooth divergence-free test vector.  This is the generic classical form of the
ordinary-distribution pressure annihilation theorem already used by the
endpoint weak formulation. -/
private theorem h3ClassicalGradient_pairing_eq_zero_of_testDivergenceFree_pressure0
    {q : ScalarField3}
    (hq : SpatialC1 q)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d (h3AxisOfFin3 i) q x)
        ∂volume
      =
    0 := by

  have hDist :
      ∑ i : Fin 3,
        (((Distribution.lineDerivCLM
          (axisDirection (h3AxisOfFin3 i)) :
            H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
          (h3WeakDistributionOfFun q))
          (φ i))
        =
      0 :=
    h3DistributionGradient_pairing_eq_zero_of_testDivergenceFree
      q φ hφ

  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (spatial3.d (h3AxisOfFin3 i) q x)
        ∂volume)
        =
      ∑ i : Fin 3,
        (((Distribution.lineDerivCLM
          (axisDirection (h3AxisOfFin3 i)) :
            H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
          (h3WeakDistributionOfFun q))
          (φ i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      exact
        h3WeakDistributionOfFun_lineDeriv_apply_eq_integral_spatial3_d
          hq
          (h3AxisOfFin3 i)
          (φ i)
    _ = 0 := hDist

/-! ## Zeroth-order path cancellation -/

/-- The gauge-sensitive zeroth-order pressure contribution vanishes at every
strict H³ energy-class time.

The proof packages the pressure gradient and velocity slice in the genuine
physical `PiLp 2` Hilbert space.  Gradient annihilation is first established on
compact smooth divergence-free generators, extended to their closed span by a
continuous linear functional, and then applied to the Leray-fixed old velocity
slice. -/
theorem h3PathEnergyClassProducesPressure0Cancellation_closed :
    H3PathEnergyClassProducesPressure0Cancellation := by

  intro u T hH3 a hClass t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  /- Use a local canonical H³ tail only to obtain the quotient-safe old
     physical velocity state and its already-proved Leray fixedness. -/
  rcases
    hH3.exists_localCanonicalRestartWindowAt htAbs
  with
    ⟨
      t₀,
      S,
      E,
      ht₀,
      hST,
      hE,
      hTail,
      hq0,
      hqR,
      hts,
      htS
    ⟩

  have hS : 0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes
      hS
      (le_of_lt hST)

  let q : ℝ := t - t₀

  have hTime :
      t₀ + q = t := by
    dsimp only [q]
    exact hts

  have hqPos : 0 < q := by
    dsimp only [q]
    exact hq0

  have hEnd :
      t₀ + q < S := by
    rw [hTime]
    exact htS

  let qClosed : Set.Icc (0 : ℝ) q :=
    ⟨q, ⟨hqPos.le, le_rfl⟩⟩

  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNSShort ht₀ hEnd hTail qClosed

  have hVLeray :
      H3PhysicalRealFinVectorL2HilbertLerayFixed V := by
    dsimp only [V]
    exact
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
        hNSShort ht₀ hEnd hTail qClosed

  have hVClosed :
      V ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    rw [
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
    ]
    exact
      (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff V).2
        hVLeray

  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht

  have hSplitPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_navierStokes
        hClass ht

  have hp1 : SpatialC1 (p t) :=
    (hSplitPDE.regularity.pressure_spatial_two t htAbs).of_le
      (by norm_num)

  have hGradMem
      (i : Fin 3) :
      MemLp
        (spatial3.d (h3AxisOfFin3 i) (p t))
        2
        (volume : Measure Point3) := by
    dsimp only [p]
    simpa only [momentumPressure0Component] using
      (h3PathEnergyClassProducesPressure0MemLp2_closed
        u T hH3 a hClass t ht (h3AxisOfFin3 i))

  let G : H3PhysicalRealFinVectorL2Hilbert :=
    WithLp.toLp (2 : ℝ≥0∞)
      (fun i : Fin 3 =>
        (hGradMem i).toLp
          (spatial3.d (h3AxisOfFin3 i) (p t)))

  have hGae
      (i : Fin 3) :
      ((G i : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d (h3AxisOfFin3 i) (p t) := by
    dsimp only [G]
    change
      (((hGradMem i).toLp
          (spatial3.d (h3AxisOfFin3 i) (p t)) : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d (h3AxisOfFin3 i) (p t)
    exact
      MeasureTheory.MemLp.coeFn_toLp
        (hGradMem i)

  have hWeakPair
      (φ : H3WeakTestVector)
      (hφ : H3WeakTestVectorDivergenceFree φ) :
      inner ℝ
          G
          (h3WeakTestVectorPhysicalL2Hilbert φ)
        =
      0 := by

    rw [
      inner_h3PhysicalRealFinVectorL2Hilbert_weakTestVector
    ]

    calc
      (∑ i : Fin 3,
        inner ℝ
          (G i)
          (h3WeakTestFunctionPhysicalL2 (φ i)))
          =
        ∑ i : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (spatial3.d (h3AxisOfFin3 i) (p t) x)
            ∂volume := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [
          hGae i,
          h3WeakTestFunctionPhysicalL2_ae (φ i)
        ] with x hGx hφx
        rw [hGx, hφx]
        simp [mul_comm]
      _ = 0 :=
        h3ClassicalGradient_pairing_eq_zero_of_testDivergenceFree_pressure0
          hp1 φ hφ

  /- Extend generator annihilation to the whole closed solenoidal span. -/
  let L : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] ℝ :=
    innerSL ℝ G

  have hGeneratorKer :
      h3DivergenceFreeWeakTestPhysicalL2Set
        ⊆
      L.ker := by
    intro Φ hΦ
    rcases hΦ with ⟨φ, hφ, rfl⟩
    change L (h3WeakTestVectorPhysicalL2Hilbert φ) = 0
    dsimp only [L]
    simpa only [innerSL_apply_apply] using
      hWeakPair φ hφ

  have hSpanKer :
      h3DivergenceFreeWeakTestPhysicalL2Span
        ≤
      L.ker := by
    unfold h3DivergenceFreeWeakTestPhysicalL2Span
    exact Submodule.span_le.mpr hGeneratorKer

  have hClosedSpanKer :
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
        ≤
      L.ker := by
    unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
    exact
      Submodule.topologicalClosure_minimal
        h3DivergenceFreeWeakTestPhysicalL2Span
        hSpanKer
        (ContinuousLinearMap.isClosed_ker L)

  have hLV : L V = 0 :=
    hClosedSpanKer hVClosed

  have hVG :
      inner ℝ V G = 0 := by
    dsimp only [L] at hLV
    simpa only [innerSL_apply_apply, real_inner_comm] using hLV

  /- Identify the old velocity Hilbert representative with the actual old
     velocity slice at the target absolute time. -/
  have hTimeClosed :
      t₀ + (qClosed : ℝ) = t := by
    simpa only [qClosed] using hTime

  have hVae
      (i : Fin 3) :
      ((V i : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u t (h3AxisOfFin3 i) := by
    have hOld :=
      h3PreterminalCanonicalL2JetOnElapsed_slot0_ae_eq_old_pressureFree
        hNSShort ht₀ hEnd hTail qClosed i
    rw [hTimeClosed] at hOld
    simpa only [
      V,
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed,
      PiLp.toLp_apply
    ] using hOld

  let pairAxis : PrimeTensor.Axis Depth.three → ℝ :=
    fun j =>
      ∫ x : Point3,
        loggedVelocityComponent u t j x
          * spatial3.d j (p t) x
        ∂volume

  have hInnerEq :
      inner ℝ V G
        =
      ∑ i : Fin 3,
        pairAxis (h3AxisOfFin3 i) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hVae i, hGae i] with x hVx hGx
    rw [hVx, hGx]
    simp [RCLike.inner_apply, mul_comm]

  have hAxisPair :
      (∑ j : PrimeTensor.Axis Depth.three,
        pairAxis j)
        =
      0 := by
    calc
      (∑ j : PrimeTensor.Axis Depth.three, pairAxis j)
          =
        ∑ i : Fin 3,
          pairAxis (h3AxisOfFin3 i) :=
        (sum_fin3_comp_h3AxisOfFin3 pairAxis).symm
      _ = inner ℝ V G := hInnerEq.symm
      _ = 0 := hVG

  unfold velocityH3PressureDerivative0At
  unfold spatialEnergyPairing
  unfold momentumPressure0Component

  change
    (∑ j : PrimeTensor.Axis Depth.three,
      2 * pairAxis j)
      =
    0

  rw [← Finset.mul_sum]
  rw [hAxisPair]
  ring

/-! ## Full pressure closure and reduced continuation interface -/

/-- Full H³ pressure cancellation is now automatic on every admissible H³
path. -/
theorem h3PathEnergyClassProducesPressureCancellation_closed :
    H3PathEnergyClassProducesPressureCancellation :=
  h3PathEnergyClassProducesPressureCancellation_of_orderZero
    h3PathEnergyClassProducesPressure0Cancellation_closed

/-- With both diffusion and all four pressure blocks closed, the active BKM
continuation theorem no longer has any scalar-sign hypothesis. -/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities
    (hLow : H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative : H3PathEnergyClassProducesOrderEnergyDerivativeIdentities) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_pressure0Cancellation
      hLow
      hDerivative
      h3PathEnergyClassProducesPressure0Cancellation_closed

end

end Euclidean
end Bridge
end PrimeTensor
