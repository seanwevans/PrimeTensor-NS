import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderThreeSelectedForcingThirdCoordinatePhysicalL2Identification

/-!
# Selected forcing third derivative: open restart-interval L² continuity

The previous checkpoint identifies the transported physical package with the
literal ordered third spatial derivative of the selected real Leray forcing
and proves strong continuity on every positive terminal slab `[q/2,q]`
strictly inside the restart radius.

This file removes the slab parameter.  The literal third forcing derivative is
packaged directly on the whole open restart interval.  Around an arbitrary
interior point `s₀`, choose

    Q = min (3 s₀ / 2) ((s₀ + R) / 2).

Then

    Q / 2 < s₀ < Q < R,

so the already-proved slab path is continuous on a neighborhood of `s₀`.
Extending the slab path with `Set.IccExtend` gives a globally continuous local
model, and the direct open-interval package agrees with that model near `s₀`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedForcingThirdCoordinateOpenL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderThreeSelectedForcingThirdCoordinateOpenL2Continuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Literal selected Leray-forcing third derivative, packaged directly on the
whole open restart interval. -/
noncomputable def h3SelectedRestartRealLerayForcingThirdCoordinateL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    H3ScalarL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  (h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
      hν U₀ hA hU₀ q.property.1 q.property.2 i a b c).toLp
    (spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (fun x : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ)) (W (q : ℝ)) i x).re))))

/-- The direct open-interval package has the literal forcing third derivative
as its a.e. representative. -/
theorem h3SelectedRestartRealLerayForcingThirdCoordinateL2_ae
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (((h3SelectedRestartRealLerayForcingThirdCoordinateL2
          hν U₀ hA hU₀ q i a b c : H3ScalarL2) : Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    spatial3.d a
      (spatial3.d b
        (spatial3.d c
          (fun x : Point3 =>
            (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              (W (q : ℝ)) (W (q : ℝ)) i x).re)))) := by
  dsimp only
  unfold h3SelectedRestartRealLerayForcingThirdCoordinateL2
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
        hν U₀ hA hU₀ q.property.1 q.property.2 i a b c)

/-- Whenever an open restart time lies in one positive terminal slab, the
direct open package equals the corresponding slab package. -/
theorem h3SelectedRestartRealLerayForcingThirdCoordinateL2_eq_onSlab
    {ν A Q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Ioo (0 : ℝ) (h3FinHeatLerayRestartRadius ν A))
    (hqQ : (q : ℝ) ∈ Set.Icc (Q / 2) Q)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    h3SelectedRestartRealLerayForcingThirdCoordinateL2
        hν U₀ hA hU₀ q i a b c
      =
    h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
      hν U₀ hA hU₀ hQ hQR i a b c
      ⟨(q : ℝ), hqQ⟩ := by
  apply MeasureTheory.Lp.ext

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hOpen :=
    h3SelectedRestartRealLerayForcingThirdCoordinateL2_ae
      hν U₀ hA hU₀ q i a b c

  have hSlab :
      (((h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
          hν U₀ hA hU₀ hQ hQR i a b c
          ⟨(q : ℝ), hqQ⟩ : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (fun x : Point3 =>
              (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (W (q : ℝ)) (W (q : ℝ)) i x).re)))) := by
    unfold h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
    exact
      MeasureTheory.MemLp.coeFn_toLp
        (h3SelectedRestartRealLerayForcing_spatial_d_three_memLp2
          hν U₀ hA hU₀
          (by
            have hHalf : 0 < Q / 2 := by positivity
            exact lt_of_lt_of_le hHalf hqQ.1)
          (lt_of_le_of_lt hqQ.2 hQR)
          i a b c)

  filter_upwards [hOpen, hSlab] with x hxOpen hxSlab
  exact hxOpen.trans hxSlab.symm

/-- Elementary local-slab geometry for an arbitrary interior restart time. -/
private theorem exists_h3SelectedRestartForcingThirdCoordinateLocalSlab
    {R q : ℝ}
    (hq0 : 0 < q)
    (hqR : q < R) :
    ∃ Q : ℝ,
      0 < Q ∧
      Q < R ∧
      Q / 2 < q ∧
      q < Q := by
  let Q : ℝ :=
    min
      (3 * q / 2)
      ((q + R) / 2)

  have hqQ : q < Q := by
    dsimp only [Q]
    apply lt_min
    · linarith
    · linarith

  have hQR : Q < R := by
    dsimp only [Q]
    exact
      lt_of_le_of_lt
        (min_le_right
          (3 * q / 2)
          ((q + R) / 2))
        (by linarith)

  have hQ0 : 0 < Q :=
    lt_trans hq0 hqQ

  have hQltTwoQ : Q < 2 * q := by
    calc
      Q ≤ 3 * q / 2 := by
        dsimp only [Q]
        exact min_le_left _ _
      _ < 2 * q := by
        linarith

  have hHalfQq : Q / 2 < q := by
    linarith

  exact ⟨Q, hQ0, hQR, hHalfQq, hqQ⟩

set_option maxHeartbeats 2000000

/-- Local form of open-interval forcing-third-derivative continuity. -/
private theorem continuousAt_h3SelectedRestartRealLerayForcingThirdCoordinateL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three)
    (q₀ : Set.Ioo
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius ν A)) :
    ContinuousAt
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartRealLerayForcingThirdCoordinateL2
          hν U₀ hA hU₀ q i a b c)
      q₀ := by
  obtain ⟨Q, hQ0, hQR, hHalfQq₀, hq₀Q⟩ :=
    exists_h3SelectedRestartForcingThirdCoordinateLocalSlab
      q₀.property.1 q₀.property.2

  have hHalfLe : Q / 2 ≤ Q := by
    linarith

  let Fslab : Set.Icc (Q / 2) Q → H3ScalarL2 :=
    h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
      hν U₀ hA hU₀ hQ0 hQR i a b c

  have hFslab : Continuous Fslab := by
    dsimp only [Fslab]
    exact
      continuous_h3SelectedRestartRealLerayForcingThirdCoordinateL2OnSlab
        hν U₀ hA hU₀ hQ0 hQR i a b c

  let Y : ℝ → H3ScalarL2 :=
    Set.IccExtend hHalfLe Fslab

  have hY : Continuous Y := by
    dsimp only [Y]
    exact hFslab.Icc_extend'

  let G :
      Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν A) → H3ScalarL2 :=
    fun q => Y (q : ℝ)

  have hG : Continuous G := by
    dsimp only [G]
    exact hY.comp continuous_subtype_val

  have hNearReal :
      Set.Ioo (Q / 2) Q ∈ 𝓝 (q₀ : ℝ) :=
    Ioo_mem_nhds hHalfQq₀ hq₀Q

  have hNear :
      ∀ᶠ q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) in 𝓝 q₀,
        (q : ℝ) ∈ Set.Ioo (Q / 2) Q :=
    continuous_subtype_val.continuousAt hNearReal

  have hEq :
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartRealLerayForcingThirdCoordinateL2
          hν U₀ hA hU₀ q i a b c)
        =ᶠ[𝓝 q₀]
      G := by
    filter_upwards [hNear] with q hq

    have hqClosed :
        (q : ℝ) ∈ Set.Icc (Q / 2) Q :=
      ⟨hq.1.le, hq.2.le⟩

    have hDirect :=
      h3SelectedRestartRealLerayForcingThirdCoordinateL2_eq_onSlab
        hν U₀ hA hU₀ hQ0 hQR q hqClosed i a b c

    dsimp only [G, Y]
    rw [Set.IccExtend_of_mem hHalfLe Fslab hqClosed]
    simpa only [Fslab] using hDirect

  exact
    hG.continuousAt.congr_of_eventuallyEq hEq

/-- The literal selected Leray-forcing third derivative is strongly continuous
on the whole open restart interval. -/
theorem continuous_h3SelectedRestartRealLerayForcingThirdCoordinateL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun q : Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A) =>
        h3SelectedRestartRealLerayForcingThirdCoordinateL2
          hν U₀ hA hU₀ q i a b c) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  exact
    continuousAt_h3SelectedRestartRealLerayForcingThirdCoordinateL2
      hν U₀ hA hU₀ i a b c q₀

end

end Euclidean
end Bridge
end PrimeTensor
