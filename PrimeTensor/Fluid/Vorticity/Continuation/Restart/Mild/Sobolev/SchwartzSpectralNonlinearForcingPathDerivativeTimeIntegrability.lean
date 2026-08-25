import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingPathDerivativePointwiseBound
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Time integrability of the pointwise nonlinear derivative path

The previous module gives, at every interior source time `0 < s < t`, the
uniform spatial estimate

    ‖D_j K_{t-s}(x)‖ ≤ M∂(s),

where `M∂` is the already-proved integrable `(t-s)⁻¹/²` scalar majorant.

This file spends that estimate on the time variable.  Once the retarded
pointwise derivative path is strongly measurable on `(0,t)`, domination by
`M∂` gives genuine Bochner integrability there, and atomlessness upgrades this
to `IntervalIntegrable` on `0..t` without imposing any condition at the
singular endpoint `s = t`.

A convenience theorem also accepts continuity on `(0,t)`.  Consequently the
next layer can focus entirely on proving time continuity/measurability of the
retarded derivative representative for continuous spectral paths; no endpoint
estimate has to be reopened.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathDerivativeTimeIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The pointwise first spatial derivative of the retarded nonlinear heat
kernel, viewed as a function of the source time `s`. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
    ν (t - s) (U s) (V s) i j x

/-- The retarded pointwise derivative path inherits the scalar derivative
majorant at every interior source time. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_le_pathMajorant
    {ν t MU MV s : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (hU : ‖U s‖ ≤ MU)
    (hV : ‖V s‖ ≤ MV)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x s‖
      ≤
    h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV s := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_pathMajorant
      hν hMU hMV U V hs hU hV i j x

/-- Strong measurability on the open retarded interval plus the established
pointwise derivative majorant gives genuine Bochner integrability on `(0,t)`.
-/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_integrableOn_Ioo_of_aestronglyMeasurable
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖U s‖ ≤ MU)
    (hV :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖V s‖ ≤ MV)
    (i j : Fin 3)
    (x : H3FourierPoint3)
    (hMeas :
      AEStronglyMeasurable
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i j x)
        (volume.restrict (Set.Ioo (0 : ℝ) t))) :
    IntegrableOn
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x)
      (Set.Ioo (0 : ℝ) t)
      volume := by
  have hMajorantIoo :
      IntegrableOn
        (h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV)
        (Set.Ioo (0 : ℝ) t)
        volume := by
    rw [
      ← integrableOn_Ioc_iff_integrableOn_Ioo,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le ht
    ]
    exact
      h3NonlinearForcingHeatFirstDerivativePathMajorant_intervalIntegrable
        (MU := MU) (MV := MV) hν ht

  refine hMajorantIoo.mono' hMeas ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_le_pathMajorant
      hν hMU hMV U V hs (hU s hs) (hV s hs) i j x

/-- The same result in the interval-integral form used by the Duhamel layer.
The endpoint `s = t` costs nothing because Lebesgue measure has no atoms. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_aestronglyMeasurable
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖U s‖ ≤ MU)
    (hV :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖V s‖ ≤ MV)
    (i j : Fin 3)
    (x : H3FourierPoint3)
    (hMeas :
      AEStronglyMeasurable
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i j x)
        (volume.restrict (Set.Ioo (0 : ℝ) t))) :
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x)
      volume
      0
      t := by
  rw [
    intervalIntegrable_iff_integrableOn_Ioc_of_le ht,
    integrableOn_Ioc_iff_integrableOn_Ioo
  ]
  exact
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_integrableOn_Ioo_of_aestronglyMeasurable
      hν ht hMU hMV U V hU hV i j x hMeas

/-- Continuity on the open retarded interval is enough to discharge the
measurability premise of the preceding theorem. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_continuousOn
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖U s‖ ≤ MU)
    (hV :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ‖V s‖ ≤ MV)
    (i j : Fin 3)
    (x : H3FourierPoint3)
    (hCont :
      ContinuousOn
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i j x)
        (Set.Ioo (0 : ℝ) t)) :
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x)
      volume
      0
      t := by
  apply
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_aestronglyMeasurable
      hν ht hMU hMV U V hU hV i j x
  exact hCont.aestronglyMeasurable measurableSet_Ioo

end

end Euclidean
end Bridge
end PrimeTensor
