import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedPressurePhysicalL2Zero
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Old.Pressure

/-!
# Close order-zero pressure L² on the old H³ path

The selected canonical pressure gradient is now known to belong to physical
`L²`.  The existing strict-overlap pressure theorem identifies that gradient
with the old preterminal pressure gradient.  Finally, pressure-gradient
uniqueness identifies the old chosen pressure with the canonical split pressure
`h3EnergyClassSplitPressureAt` used by the H³ energy frontier.

Thus the order-zero member of `H3PathEnergyClassProducesPressureMemLp2` is
closed outright.  No new pressure estimate is introduced here; this is only
selected-to-old transfer plus pressure-witness uniqueness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3PathPressureL2OrderZero
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathPressureL2OrderZero :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every order-zero pressure component of the canonical split pressure belongs
 to physical `L²` at every strict H³ energy-class time. -/
theorem h3PathEnergyClassProducesPressure0MemLp2_closed :
    ∀
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T : ℝ),
        LoggedPreterminalH3PathAdmissible u T →
        ∀ a : ℝ,
          ∀ hClass : PreterminalH3EnergyClass u a T,
            ∀ t : ℝ,
              ∀ ht : t ∈ Set.Ioo a T,
                ∀ j : PrimeTensor.Axis Depth.three,
                  MemLp
                    (momentumPressure0Component
                      (h3EnergyClassSplitPressureAt hClass ht)
                      t j)
                    2
                    (volume : Measure Point3) := by

  intro u T hH3 a hClass t ht j

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

  have hq :
      q = t - t₀ := rfl

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
        (spatial3.d
          j
          ((h3RawFinPressureRealC1OfPath W) q))
        2
        (volume : Measure Point3) := by
    have h :=
      h3SelectedRestartPressureSpatialDerivative_memLp2
        (s := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j
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

  have hRelAbs :
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

  have hSelectedAbs :
      MemLp
        (spatial3.d j (pAbs t))
        2
        (volume : Measure Point3) := by
    rw [← hRelAbs]
    exact hSelectedRel

  let pChosen :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNSShort

  have hChosenSelected :
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

  have hSplitChosen :
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

  have hSplitSelected :
      spatial3.d j (pSplit t)
        =
      spatial3.d j (pAbs t) :=
    hSplitChosen.trans hChosenSelected

  unfold momentumPressure0Component
  rw [hSplitSelected]
  exact hSelectedAbs

end

end Euclidean
end Bridge
end PrimeTensor
