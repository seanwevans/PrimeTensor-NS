import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Endpoint.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# One-sided FTC at the nonlinear retarded endpoint

The dynamic endpoint theorem proves that the physical retarded nonlinear
forcing tends from the left to the instantaneous unheated Leray--divergence
forcing.  The retarded path itself is already defined at the endpoint and has
exactly that value.

This file packages the endpoint statement in the form required by Mathlib's
one-sided fundamental theorem of calculus:

* the retarded path is `ContinuousWithinAt` on `Iic t` at `t`;
* for positive terminal time it is continuous on the whole closed interval
  `[0,t]`;
* consequently the upper-bound primitive

      r ↦ ∫ s in 0..r, H_{t-s} F(U(s),V(s))

  has left derivative at `r=t` equal to the instantaneous unheated forcing

      F(U(t),V(t)).

The terminal heat time `t` is frozen in this primitive.  Thus this theorem
isolates exactly the moving-upper-endpoint contribution to the Duhamel
derivative.  The remaining diagonal step is to control the simultaneous
variation of the terminal heat parameter itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathC0EndpointFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The dynamic left limit and the exact endpoint value glue to genuine
continuity within the left half-line `Iic t`. -/
theorem continuousWithinAt_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Iic_endpoint
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousWithinAt
      (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x)
      (Set.Iic t)
      t := by
  let F : ℝ → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
      ν t U V i x

  have hEndpoint :
      F t
        =
      h3RawFinLerayOuterProductDivergenceC0Representative
        (U t) (V t) i x := by
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_endpoint
        ν t U V i x

  have hLeft :
      Tendsto
        F
        (𝓝[Set.Iio t] t)
        (𝓝
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (U t) (V t) i x)) := by
    dsimp only [F]
    exact
      tendsto_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_endpoint
        hν U V hU hV i x

  have hLeft' :
      Tendsto
        F
        (𝓝[Set.Iio t] t)
        (𝓝 (F t)) := by
    rw [hEndpoint]
    exact hLeft

  have hPoint :
      Tendsto
        F
        (𝓝[{t}] t)
        (𝓝 (F t)) := by
    rw [nhdsWithin_singleton, tendsto_pure_left]
    intro s hs
    exact mem_of_mem_nhds hs

  have hIic :
      Set.Iic t = Set.Iio t ∪ {t} := by
    ext s
    simp only [
      Set.mem_Iic,
      Set.mem_union,
      Set.mem_Iio,
      Set.mem_singleton_iff
    ]
    constructor
    · intro hs
      rcases lt_or_eq_of_le hs with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq
    · intro hs
      rcases hs with hlt | heq
      · exact le_of_lt hlt
      · exact le_of_eq heq

  show
    Tendsto
      F
      (𝓝[Set.Iic t] t)
      (𝓝 (F t))

  rw [hIic, nhdsWithin_union]
  exact hLeft'.sup hPoint

/-- For continuous input paths, the physical retarded nonlinear forcing is
continuous on the full closed source-time interval `[a,t]`. -/
theorem continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Icc
    {ν a t : ℝ}
    (hν : 0 < ν)
    (_hat : a < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousOn
      (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i x)
      (Set.Icc a t) := by
  intro s hs

  by_cases hst : s = t

  · subst s
    exact
      (continuousWithinAt_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Iic_endpoint
        hν U V hU hV i x).mono
        (by
          intro r hr
          exact hr.2)

  · have hlt : s < t :=
      lt_of_le_of_ne hs.2 hst

    exact
      (continuousAt_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        hν hlt U V hU hV i x).continuousWithinAt

/-- The frozen-terminal retarded primitive has one-sided derivative at its
upper endpoint equal to the instantaneous unheated nonlinear forcing. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_primitive_hasDerivWithinAt_endpoint
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖U s‖ ≤ MU)
    (hV : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivWithinAt
      (fun r : ℝ =>
        ∫ s in (0 : ℝ)..r,
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν t U V i x s)
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (U t) (V t) i x)
      (Set.Iic t)
      t := by
  let F : ℝ → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
      ν t U V i x

  have hInt :
      IntervalIntegrable
        F
        volume
        0
        t := by
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_intervalIntegrable_of_continuous
        hν ht.le hMU hMV
        U V hUcont hVcont hU hV i x

  have hContEnd :
      ContinuousWithinAt
        F
        (Set.Iic t)
        t := by
    dsimp only [F]
    exact
      continuousWithinAt_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Iic_endpoint
        hν U V hUcont hVcont i x

  have hContIcc :
      ContinuousOn
        F
        (Set.Icc (0 : ℝ) t) := by
    dsimp only [F]
    exact
      continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Icc
        hν ht U V hUcont hVcont i x

  have hMeasIcc :
      AEStronglyMeasurable
        F
        (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    hContIcc.aestronglyMeasurable measurableSet_Icc

  have hIoi :
      Set.Ioi (0 : ℝ) ∈ 𝓝 t :=
    Ioi_mem_nhds ht

  have hNearInter :
      Set.Iic t ∩ Set.Ioi (0 : ℝ)
        ∈
      𝓝[Set.Iic t] t :=
    inter_mem_nhdsWithin (Set.Iic t) hIoi

  have hNear :
      Set.Icc (0 : ℝ) t
        ∈
      𝓝[Set.Iic t] t := by
    refine mem_of_superset hNearInter ?_
    intro s hs
    exact ⟨hs.2.le, hs.1⟩

  have hMeas :
      StronglyMeasurableAtFilter
        F
        (𝓝[Set.Iic t] t)
        volume := by
    exact ⟨Set.Icc (0 : ℝ) t, hNear, hMeasIcc⟩

  have hFTC :
      HasDerivWithinAt
        (fun r : ℝ => ∫ s in (0 : ℝ)..r, F s)
        (F t)
        (Set.Iic t)
        t :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (s := Set.Iic t)
      (t := Set.Iic t)
      hInt
      hMeas
      hContEnd

  have hEndpoint :
      F t
        =
      h3RawFinLerayOuterProductDivergenceC0Representative
        (U t) (V t) i x := by
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_endpoint
        ν t U V i x

  rw [hEndpoint] at hFTC
  simpa only [F] using hFTC

end

end Euclidean
end Bridge
end PrimeTensor
