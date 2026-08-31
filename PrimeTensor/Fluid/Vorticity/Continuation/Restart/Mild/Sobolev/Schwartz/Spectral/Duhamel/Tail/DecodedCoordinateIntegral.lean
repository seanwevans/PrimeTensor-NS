import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.PhysicalIntertwiningAE
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Integral.Bridge

/-!
# Coordinatewise decoded Duhamel integral identity

The finite-vector decoder already commutes exactly with the spectral Bochner
Duhamel integral.  For the temporal derivative argument we ultimately work one
velocity coordinate at a time, so this file extracts that vector identity
through the continuous coordinate projection.

The result stays entirely at the quotient-safe physical `L²` level:

    decode (D(t)_i)
      =
    ∫ s in 0..t, decode (K(t,s)_i).

No point evaluation is performed here.  The next checkpoint will combine this
exact `L²` identity with the source-time/spatial almost-everywhere
intertwining theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailDecodedCoordinateIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact coordinatewise form of the decoded spectral Duhamel Bochner
integral. -/
theorem h3SpectralScalarDecodeComplexL2_duhamel_eq_intervalIntegral
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t)
    (i : Fin 3) :
    h3SpectralScalarDecodeComplexL2
        ((h3SpectralFinHeatLerayDuhamel ν t hν U V) i)
      =
    ∫ s in (0 : ℝ)..t,
      h3SpectralScalarDecodeComplexL2
        ((h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V s) i) := by
  have hVector :=
    h3SpectralFinHeatLerayDuhamel_decodeComplexL2_eq_intervalIntegral
      hν U V hInt

  have hDecodedInt :
      IntervalIntegrable
        (fun s : ℝ =>
          h3SpectralFinVectorDecodeComplexL2
            (h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s))
        volume
        0
        t := by
    constructor
    · exact
        h3SpectralFinVectorDecodeComplexL2CLM.integrable_comp hInt.1
    · exact
        h3SpectralFinVectorDecodeComplexL2CLM.integrable_comp hInt.2

  let πi :
      H3ComplexPhysicalFinVectorL2 →L[ℂ] H3ComplexPhysicalScalarL2 :=
    ContinuousLinearMap.proj i

  calc
    h3SpectralScalarDecodeComplexL2
        ((h3SpectralFinHeatLerayDuhamel ν t hν U V) i)
        =
      h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V) i := by
          rfl
    _ =
      (∫ s in (0 : ℝ)..t,
        h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s)) i := by
          exact congrArg (fun Z => Z i) hVector
    _ =
      ∫ s in (0 : ℝ)..t,
        (h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s)) i := by
          change
            πi
              (∫ s in (0 : ℝ)..t,
                h3SpectralFinVectorDecodeComplexL2
                  (h3SpectralFinHeatLerayDuhamelIntegrand
                    ν t hν U V s))
              =
            ∫ s in (0 : ℝ)..t,
              πi
                (h3SpectralFinVectorDecodeComplexL2
                  (h3SpectralFinHeatLerayDuhamelIntegrand
                    ν t hν U V s))
          symm
          exact πi.intervalIntegral_comp_comm hDecodedInt
    _ =
      ∫ s in (0 : ℝ)..t,
        h3SpectralScalarDecodeComplexL2
          ((h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s) i) := by
          rfl

end

end Euclidean
end Bridge
end PrimeTensor
