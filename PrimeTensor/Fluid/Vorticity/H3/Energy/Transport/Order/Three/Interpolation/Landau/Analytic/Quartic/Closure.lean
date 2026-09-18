import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.CutoffLimit

/-!
# Whole-space quartic Landau integration by parts

The cutoff identity is already available at every positive radius:

    ∫ χ_R g⁴
      =
    -3 ∫ χ_R v g² (∂ₐg)
      - boundary_R.

Along the canonical radii `Rₙ = n+1`:

* dominated convergence removes `χ_R` from the two integrable bulk terms;
* the quartic boundary error tends to zero;
* uniqueness of limits therefore yields

    ∫ g⁴ = -3 ∫ v g² (∂ₐg).

This discharges the generic
`WholeSpaceQuarticDerivativeIntegrationByParts` frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

noncomputable local instance axisFintypeH3LandauQuarticClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The standard whole-space quartic derivative integration-by-parts frontier
follows from the smooth expanding-cutoff construction. -/
theorem wholeSpaceQuarticDerivativeIntegrationByParts_cutoff :
    WholeSpaceQuarticDerivativeIntegrationByParts := by
  intro v a h hv hG hEnv hg4 hdg2

  let g : ScalarField3 :=
    spatial3.d a v

  let dg : ScalarField3 :=
    spatial3.d a g

  let quartic : ScalarField3 :=
    fun x : Point3 =>
      (g x) ^ 4

  let bulk : ScalarField3 :=
    fun x : Point3 =>
      v x * ((g x) ^ 2 * dg x)

  have hgC1 :
      SpatialC1 g := by
    simpa [g] using
      hG

  have hg4' :
      MeasureTheory.MemLp
        g
        (ENNReal.ofReal 4)
        volume := by
    simpa [g] using
      hg4

  have hdg2' :
      MeasureTheory.MemLp
        dg
        (ENNReal.ofReal 2)
        volume := by
    simpa [dg, g] using
      hdg2

  have hQuarticInt :
      MeasureTheory.Integrable
        quartic
        volume := by
    dsimp [quartic]

    exact
      integrable_pow_four_of_memLp_four
        hg4'

  have hEnvelopeInt :
      LandauQuarticEnvelopeIntegrable
        v
        g
        dg
        h :=
    landauQuarticEnvelopeIntegrable_of_memLp_four_two
      hv.continuous.aestronglyMeasurable
      hEnv
      hg4'
      hdg2'

  have hBulkMeas :
      AEStronglyMeasurable
        bulk
        volume := by
    dsimp [bulk]

    exact
      hv.continuous.aestronglyMeasurable.mul
        (
          (hg4'.aestronglyMeasurable.pow 2).mul
            hdg2'.aestronglyMeasurable
        )

  have hBulkInt :
      MeasureTheory.Integrable
        bulk
        volume := by
    apply
      (
        MeasureTheory.integrable_norm_iff
          hBulkMeas
      ).mp

    simpa [
      bulk,
      Real.norm_eq_abs
    ] using
      hEnvelopeInt.1

  have hQuarticLimit :
      Tendsto
        (h3LandauQuarticCutoffIntegral quartic)
        atTop
        (𝓝
          (
            ∫ x : Point3,
              quartic x
          )) :=
    tendsto_h3LandauQuarticCutoffIntegral
      hQuarticInt

  have hBulkLimit :
      Tendsto
        (h3LandauQuarticCutoffIntegral bulk)
        atTop
        (𝓝
          (
            ∫ x : Point3,
              bulk x
          )) :=
    tendsto_h3LandauQuarticCutoffIntegral
      hBulkInt

  have hRadiusLimit :
      Tendsto
        h3LandauQuarticRadius
        atTop
        atTop := by
    unfold h3LandauQuarticRadius

    exact
      tendsto_atTop_add_const_right
        atTop
        (1 : ℝ)
        tendsto_natCast_atTop_atTop

  have hBoundaryLimitR :
      Tendsto
        (h3LandauQuarticBoundaryError
          v g a)
        atTop
        (𝓝 0) :=
    tendsto_h3LandauQuarticBoundaryError_zero
      hv
      hgC1
      hEnv
      hg4'
      a

  have hBoundaryLimit :
      Tendsto
        (fun n : ℕ =>
          h3LandauQuarticBoundaryError
            v g a
            (h3LandauQuarticRadius n))
        atTop
        (𝓝 0) :=
    hBoundaryLimitR.comp
      hRadiusLimit

  have hIdentity :
      ∀ n : ℕ,
        h3LandauQuarticCutoffIntegral
            quartic
            n
          =
        -3
            *
          h3LandauQuarticCutoffIntegral
            bulk
            n
          -
        h3LandauQuarticBoundaryError
          v g a
          (h3LandauQuarticRadius n) := by
    intro n

    have hCutoff :=
      h3LandauQuarticCutoff_expandedIBP
        (h3LandauQuarticRadius_pos n)
        hv
        hgC1
        a
        (fun x : Point3 => by
          rfl)

    have hBoundaryEq :=
      h3LandauQuarticBoundaryError_eq
        v g a
        (h3LandauQuarticRadius_pos n)

    rw [hBoundaryEq]

    simpa [
      h3LandauQuarticCutoffIntegral,
      quartic,
      bulk,
      dg,
      g,
      mul_assoc
    ] using
      hCutoff

  have hNegThree :
      Tendsto
        (fun _ : ℕ => (-3 : ℝ))
        atTop
        (𝓝 (-3 : ℝ)) :=
    tendsto_const_nhds

  have hBulkScaled :
      Tendsto
        (fun n : ℕ =>
          (-3 : ℝ)
            *
          h3LandauQuarticCutoffIntegral
            bulk
            n)
        atTop
        (𝓝
          (
            (-3 : ℝ)
              *
            (
              ∫ x : Point3,
                bulk x
            )
          )) :=
    hNegThree.mul
      hBulkLimit

  have hRightLimit :
      Tendsto
        (fun n : ℕ =>
          (-3 : ℝ)
              *
            h3LandauQuarticCutoffIntegral
              bulk
              n
            -
          h3LandauQuarticBoundaryError
            v g a
            (h3LandauQuarticRadius n))
        atTop
        (𝓝
          (
            (-3 : ℝ)
              *
            (
              ∫ x : Point3,
                bulk x
            )
          )) := by
    have hSub :=
      hBulkScaled.sub
        hBoundaryLimit

    simpa only [sub_zero] using
      hSub

  have hQuarticRightLimit :
      Tendsto
        (h3LandauQuarticCutoffIntegral quartic)
        atTop
        (𝓝
          (
            (-3 : ℝ)
              *
            (
              ∫ x : Point3,
                bulk x
            )
          )) := by
    exact
      hRightLimit.congr'
        (
          Filter.Eventually.of_forall
            (fun n =>
              (hIdentity n).symm)
        )

  have hLimitEq :
      (
        ∫ x : Point3,
          quartic x
      )
        =
      (-3 : ℝ)
        *
      (
        ∫ x : Point3,
          bulk x
      ) :=
    tendsto_nhds_unique
      hQuarticLimit
      hQuarticRightLimit

  unfold LandauQuarticIntegrationByParts

  simpa [
    quartic,
    bulk,
    dg,
    g
  ] using
    hLimitEq

end

end Euclidean
end Bridge
end PrimeTensor
