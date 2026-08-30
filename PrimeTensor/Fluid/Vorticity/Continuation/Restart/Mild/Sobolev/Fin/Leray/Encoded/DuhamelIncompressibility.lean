import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.ProjectionIncompressibility

/-!
# Duhamel incompressibility through the bounded Leray projector

`ProjectionIncompressibility` proves that every retarded heat--Leray
integrand is Fourier divergence-free.  Passing that fact directly through the
Bochner interval integral by the divergence symbol would be the wrong
functional-analytic move: multiplication by the derivative symbol is
unbounded on the ambient weighted `L²` state.

Instead use the bounded projector itself.

The lifted finite Leray operator already satisfies

    ‖P G‖ ≤ 6 ‖G‖.

This file packages that operator as a complex continuous linear map.  Since
every divergence-free state is Leray-fixed, every Duhamel integrand is fixed
by `P`.  Continuous linear maps commute with Bochner interval integrals, so

    P (∫ K(s) ds) = ∫ P(K(s)) ds = ∫ K(s) ds.

Finally every Leray-fixed state is divergence-free because every state in the
range of `P` is divergence-free.

Thus the genuine H³ heat--Leray Duhamel term preserves incompressibility using
only the already-required interval-integrability hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Interval ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3FinLerayDuhamelIncompressibility
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Linearity of one Leray matrix-entry multiplier -/

/-- One scalar Leray matrix-entry multiplier is complex homogeneous. -/
theorem h3SpectralScalarLerayCoefficientApply_smul
    (i j : Fin 3)
    (c : ℂ)
    (G : H3SpectralScalarState) :
    h3SpectralScalarLerayCoefficientApply i j (c • G)
      =
    c • h3SpectralScalarLerayCoefficientApply i j G := by
  apply MeasureTheory.Lp.ext

  have hOut :=
    h3SpectralScalarLerayCoefficientApply_ae
      i j (c • G)
  have hG :=
    h3SpectralScalarLerayCoefficientApply_ae
      i j G
  have hInputSmul :=
    MeasureTheory.Lp.coeFn_smul c G
  have hOutputSmul :=
    MeasureTheory.Lp.coeFn_smul
      c
      (h3SpectralScalarLerayCoefficientApply i j G)

  filter_upwards [
    hOut,
    hG,
    hInputSmul,
    hOutputSmul
  ] with ξ hOutξ hGξ hInputSmulξ hOutputSmulξ

  rw [
    hOutξ,
    hOutputSmulξ,
    hInputSmulξ
  ]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hGξ]
  ring

/-! ## The finite Leray projector as a bounded linear operator -/

/-- The full finite Leray multiplier is complex homogeneous. -/
theorem h3SpectralFinLerayApply_smul
    (c : ℂ)
    (G : H3SpectralFinVectorState) :
    h3SpectralFinLerayApply (c • G)
      =
    c • h3SpectralFinLerayApply G := by
  funext i
  unfold h3SpectralFinLerayApply
  simp only [Pi.smul_apply]
  simp_rw [h3SpectralScalarLerayCoefficientApply_smul]
  rw [Finset.smul_sum]

/-- The lifted finite Leray projector as a complex linear map. -/
noncomputable def h3SpectralFinLerayLinearMap :
    H3SpectralFinVectorState →ₗ[ℂ]
      H3SpectralFinVectorState where
  toFun := h3SpectralFinLerayApply
  map_add' := h3SpectralFinLerayApply_add
  map_smul' := h3SpectralFinLerayApply_smul

@[simp]
theorem h3SpectralFinLerayLinearMap_apply
    (G : H3SpectralFinVectorState) :
    h3SpectralFinLerayLinearMap G
      =
    h3SpectralFinLerayApply G := rfl

/-- The existing `6`-bound upgrades the Leray linear map to a continuous
linear map. -/
noncomputable def h3SpectralFinLerayContinuousLinearMap :
    H3SpectralFinVectorState →L[ℂ]
      H3SpectralFinVectorState :=
  h3SpectralFinLerayLinearMap.mkContinuous
    6
    (fun G =>
      norm_h3SpectralFinLerayApply_le G)

@[simp]
theorem h3SpectralFinLerayContinuousLinearMap_apply
    (G : H3SpectralFinVectorState) :
    h3SpectralFinLerayContinuousLinearMap G
      =
    h3SpectralFinLerayApply G := rfl

/-! ## Fixed-point characterization needed for integration -/

/-- A state fixed by the finite Leray projector is divergence-free.

This direction uses the range theorem from
`ProjectionIncompressibility`; no converse algebra is repeated here. -/
theorem h3SpectralFinDivergenceFree_of_lerayFixed
    {G : H3SpectralFinVectorState}
    (hG :
      h3SpectralFinLerayApply G = G) :
    H3SpectralFinDivergenceFree G := by
  rw [← hG]
  exact
    h3SpectralFinLerayApply_divergenceFree G

/-- Every retarded heat--Leray Duhamel integrand is fixed by the finite Leray
projector. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_lerayFixed
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (s : ℝ) :
    h3SpectralFinLerayApply
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V s)
      =
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν t hν U V s := by
  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (h3SpectralFinHeatLerayDuhamelIntegrand_divergenceFree
        hν U V s)

/-! ## Bochner interval integration -/

/-- The genuine heat--Leray Duhamel integral is Leray-fixed whenever its
already-required Banach-valued interval-integrability hypothesis holds. -/
theorem h3SpectralFinHeatLerayDuhamel_lerayFixed
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        volume
        0
        t) :
    h3SpectralFinLerayApply
        (h3SpectralFinHeatLerayDuhamel
          ν t hν U V)
      =
    h3SpectralFinHeatLerayDuhamel
      ν t hν U V := by
  unfold h3SpectralFinHeatLerayDuhamel

  rw [intervalIntegral.integral_of_le ht]

  change
    h3SpectralFinLerayContinuousLinearMap
        (∫ s in Set.Ioc (0 : ℝ) t,
          h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s)
      =
    ∫ s in Set.Ioc (0 : ℝ) t,
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V s

  calc
    h3SpectralFinLerayContinuousLinearMap
        (∫ s in Set.Ioc (0 : ℝ) t,
          h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s)
        =
      ∫ s in Set.Ioc (0 : ℝ) t,
        h3SpectralFinLerayContinuousLinearMap
          (h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s) := by
          symm
          exact
            ContinuousLinearMap.integral_comp_comm
              h3SpectralFinLerayContinuousLinearMap
              hInt.1
    _ =
      ∫ s in Set.Ioc (0 : ℝ) t,
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V s := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with s
            change
              h3SpectralFinLerayApply
                  (h3SpectralFinHeatLerayDuhamelIntegrand
                    ν t hν U V s)
                =
              h3SpectralFinHeatLerayDuhamelIntegrand
                ν t hν U V s
            exact
              h3SpectralFinHeatLerayDuhamelIntegrand_lerayFixed
                hν U V s

/-- Therefore the genuine heat--Leray Duhamel integral is Fourier
divergence-free. -/
theorem h3SpectralFinHeatLerayDuhamel_divergenceFree
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        volume
        0
        t) :
    H3SpectralFinDivergenceFree
      (h3SpectralFinHeatLerayDuhamel
        ν t hν U V) := by
  exact
    h3SpectralFinDivergenceFree_of_lerayFixed
      (h3SpectralFinHeatLerayDuhamel_lerayFixed
        hν ht U V hInt)

end
end Euclidean
end Bridge
end PrimeTensor
