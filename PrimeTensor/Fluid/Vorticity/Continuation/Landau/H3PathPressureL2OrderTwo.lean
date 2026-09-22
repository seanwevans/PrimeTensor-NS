import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPressurePhysicalL2Second
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathPressureL2OrderOne

/-!
# Close order-two pressure L² on the old H³ path

The selected canonical pressure third derivatives are now known to belong to
physical `L²`.  The lower pressure closures already established equality of the
selected, old chosen, and canonical split pressure gradients on the local
restart overlap.

Those are equalities of scalar fields.  Applying `congrArg (spatial3.d k)` and
then `congrArg (spatial3.d i)` transports them two spatial derivatives higher,
without any new analytic estimate.  Hence every `momentumPressure2Component`
of the canonical split pressure belongs to physical `L²` at every strict H³
energy-class time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PathPressureL2OrderTwo
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathPressureL2OrderTwo :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every order-two pressure component of the canonical split pressure belongs
 to physical `L²` at every strict H³ energy-class time. -/
theorem h3PathEnergyClassProducesPressure2MemLp2_closed :
    ∀
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T : ℝ),
        LoggedPreterminalH3PathAdmissible u T →
        ∀ a : ℝ,
          ∀ hClass : PreterminalH3EnergyClass u a T,
            ∀ t : ℝ,
              ∀ ht : t ∈ Set.Ioo a T,
                ∀ i k j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumPressure2Component
                      (h3EnergyClassSplitPressureAt hClass ht)
                      t i k j)
                    2
                    (volume : Measure Point3) := by

  intro u T hH3 a hClass t ht i k j

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

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

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNSShort ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E := by
    dsimp only [U₀]
    exact
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNSShort ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNSShort ht₀ hE hTail

  have hSelectedRel :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) q))))
        2
        (volume : Measure Point3) := by
    have h :=
      h3SelectedRestartPressureSpatialDerivative_three_memLp2
        (t := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ hq0 hqR i k j
    simpa only [
      W,
      U₀,
      hA,
      hU₀,
      h3PreterminalTailCanonicalSelectedRestart
    ] using h

  let pAbs :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3PreterminalTailCanonicalSelectedPressureAbsolute
      hNSShort ht₀ hE hTail

  have hRelAbs0 :
      spatial3.d
          j
          ((h3RawFinPressureRealC1OfPath W) q)
        =
      spatial3.d
          j
          (pAbs t) := by
    dsimp only [
      pAbs,
      h3PreterminalTailCanonicalSelectedPressureAbsolute,
      W,
      q
    ]

  have hRelAbs1 :
      spatial3.d k
          (spatial3.d j
            ((h3RawFinPressureRealC1OfPath W) q))
        =
      spatial3.d k
          (spatial3.d j
            (pAbs t)) :=
    congrArg (spatial3.d k) hRelAbs0

  have hRelAbs :
      spatial3.d i
          (spatial3.d k
            (spatial3.d j
              ((h3RawFinPressureRealC1OfPath W) q)))
        =
      spatial3.d i
          (spatial3.d k
            (spatial3.d j
              (pAbs t))) :=
    congrArg (spatial3.d i) hRelAbs1

  have hSelectedAbs :
      MemLp
        (spatial3.d i
          (spatial3.d k
            (spatial3.d j
              (pAbs t))))
        2
        (volume : Measure Point3) := by
    rw [← hRelAbs]
    exact hSelectedRel

  let pChosen :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNSShort

  have hChosenSelected0 :
      spatial3.d j (pChosen t)
        =
      spatial3.d j (pAbs t) := by
    dsimp only [pChosen, pAbs]
    funext x
    have h :=
      h3PreterminalTailCanonicalSelectedPressureGradient_eq_old_on_strictOverlap
        hNSShort
        ht₀
        hE
        hTail
        hq0
        hqR
        (by linarith)
        x
        j
    rw [hTime] at h
    exact h

  have hChosenSelected1 :
      spatial3.d k
          (spatial3.d j (pChosen t))
        =
      spatial3.d k
          (spatial3.d j (pAbs t)) :=
    congrArg (spatial3.d k) hChosenSelected0

  have hChosenSelected :
      spatial3.d i
          (spatial3.d k
            (spatial3.d j (pChosen t)))
        =
      spatial3.d i
          (spatial3.d k
            (spatial3.d j (pAbs t))) :=
    congrArg (spatial3.d i) hChosenSelected1

  let pSplit :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht

  have hSplitPDEFull :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pSplit
        T := by
    dsimp only [pSplit]
    exact
      h3EnergyClassSplitPressureAt_navierStokes
        hClass ht

  have hSplitPDEShort :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pSplit
        S :=
    hSplitPDEFull.mono_terminal
      hS
      (le_of_lt hST)

  have hChosenPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pChosen
        S := by
    dsimp only [pChosen]
    exact Classical.choose_spec hNSShort

  have htShort :
      t ∈ Set.Ioo (0 : ℝ) S :=
    ⟨htAbs.1, htS⟩

  have hSplitChosen0 :
      spatial3.d j (pSplit t)
        =
      spatial3.d j (pChosen t) := by
    funext x
    exact
      (preterminalNavierStokes3_pressureGradient_eq
        hChosenPDE
        hSplitPDEShort
        htShort
        x
        j).symm

  have hSplitChosen1 :
      spatial3.d k
          (spatial3.d j (pSplit t))
        =
      spatial3.d k
          (spatial3.d j (pChosen t)) :=
    congrArg (spatial3.d k) hSplitChosen0

  have hSplitChosen :
      spatial3.d i
          (spatial3.d k
            (spatial3.d j (pSplit t)))
        =
      spatial3.d i
          (spatial3.d k
            (spatial3.d j (pChosen t))) :=
    congrArg (spatial3.d i) hSplitChosen1

  have hSplitSelected :
      spatial3.d i
          (spatial3.d k
            (spatial3.d j (pSplit t)))
        =
      spatial3.d i
          (spatial3.d k
            (spatial3.d j (pAbs t))) :=
    hSplitChosen.trans hChosenSelected

  unfold momentumPressure2Component
  unfold momentumPressure1Component
  unfold momentumPressure0Component
  rw [hSplitSelected]
  exact hSelectedAbs

end

end Euclidean
end Bridge
end PrimeTensor
