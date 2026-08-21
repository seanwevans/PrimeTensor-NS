import PrimeTensor.Bridge.Real.Tangent.Classification

/-!
# Scalar logarithmic semantics of the native derivative

The native derivative definition uses a multiplicative tangent morphism `D`.
The real tangent classification proves that every scale-controlled such morphism
is uniquely represented by one real scalar

    slope D.

Combining that classification with the existing logarithmic derivative bridge
removes the final tangent-map-valued term from the first-order expansion.

For every logarithmic perturbation tending to zero,

    L(f(x*h_n)) - L(f(x))
      = slope(D) * L(h_n) + o_dyadic(L(h_n)).

Thus the regular native first derivative has exactly one ordinary real
coefficient in canonical logarithmic coordinates.
-/

namespace PrimeTensor
namespace Bridge
namespace MulDifferential

/--
Canonical real scalar coefficient associated with a scale-controlled native
derivative candidate.
-/
noncomputable def scalarCoefficient
    (D : PrimeTensor.MulTangentMap) : ℝ :=
  PrimeTensor.Bridge.MulTangentMap.slope D

/--
The logarithmic response of a controlled derivative candidate is its scalar
coefficient times the logarithmic perturbation.
-/
theorem logValue_derivativeModel_eq_scalar_mul
    {D : PrimeTensor.MulTangentMap}
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D)
    (h : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.MulReal.logValue
        (D h)
      =
    scalarCoefficient D *
      PrimeTensor.Bridge.MulReal.logValue h := by

  unfold scalarCoefficient

  exact
    PrimeTensor.Bridge.MulTangentMap.logValue_apply_eq_slope_mul
      hControlled
      h

/--
Canonical scalar residual in logarithmic coordinates.
-/
noncomputable def scalarLogResidual
    (f : PrimeTensor.MulReal → PrimeTensor.MulReal)
    (x : PrimeTensor.MulReal)
    (D : PrimeTensor.MulTangentMap)
    (h : PrimeTensor.MulReal.Seq)
    (n : Depth) : ℝ :=
  (
    PrimeTensor.Bridge.MulReal.logValue
        (f (x * h n)) -
      PrimeTensor.Bridge.MulReal.logValue
        (f x)
  ) -
  scalarCoefficient D *
    PrimeTensor.Bridge.MulReal.logValue
      (h n)

/--
For a controlled tangent model, the previously established tangent-map
residual is exactly the scalar logarithmic residual.
-/
theorem realLogResidual_eq_scalarLogResidual
    (f : PrimeTensor.MulReal → PrimeTensor.MulReal)
    (x : PrimeTensor.MulReal)
    (D : PrimeTensor.MulTangentMap)
    (h : PrimeTensor.MulReal.Seq)
    (n : Depth)
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D) :
    PrimeTensor.Bridge.MulDifferential.realLogResidual
        f x D h n
      =
    scalarLogResidual f x D h n := by

  unfold
    PrimeTensor.Bridge.MulDifferential.realLogResidual
    scalarLogResidual
    PrimeTensor.Bridge.MulTangentMap.logResponse

  rw [
    PrimeTensor.Bridge.MulDifferential.logValue_derivativeModel_eq_scalar_mul
      hControlled
      (h n)
  ]

/--
A native derivative with scale-controlled tangent model has the canonical
one-scalar first-order logarithmic expansion.

For every perturbation whose logarithmic coordinate tends to zero, the residual

    L(f(x*h_n)) - L(f(x)) - c * L(h_n)

is dyadic-scale little-o of `L(h_n)`, where

    c = scalarCoefficient D = slope D.
-/
theorem hasMulDerivativeAt_scalar_log_expansion
    {f : PrimeTensor.MulReal → PrimeTensor.MulReal}
    {x : PrimeTensor.MulReal}
    {D : PrimeTensor.MulTangentMap}
    (hDeriv :
      PrimeTensor.MulDifferential.HasMulDerivativeAt
        f x D)
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D) :
    ∀ h : PrimeTensor.MulReal.Seq,
      Filter.Tendsto
        (
          fun n : Depth =>
            PrimeTensor.Bridge.MulReal.logValue
              (h n)
        )
        PrimeTensor.Bridge.Depth.tailFilter
        (nhds 0) →
      PrimeTensor.Bridge.RealLogScaleLittleO
        (
          fun n =>
            (
              PrimeTensor.Bridge.MulReal.logValue
                  (f (x * h n)) -
                PrimeTensor.Bridge.MulReal.logValue
                  (f x)
            ) -
            scalarCoefficient D *
              PrimeTensor.Bridge.MulReal.logValue
                (h n)
        )
        (
          fun n =>
            PrimeTensor.Bridge.MulReal.logValue
              (h n)
        ) := by

  intro h hLogZero

  have hLittle :=
    PrimeTensor.Bridge.MulDifferential.hasMulDerivativeAt_log_expansion
      hDeriv
      h
      hLogZero

  have hFun :
      (
        fun n : Depth =>
          (
            PrimeTensor.Bridge.MulReal.logValue
                (f (x * h n)) -
              PrimeTensor.Bridge.MulReal.logValue
                (f x)
          ) -
          PrimeTensor.Bridge.MulReal.logValue
            (D (h n))
      )
        =
      (
        fun n : Depth =>
          (
            PrimeTensor.Bridge.MulReal.logValue
                (f (x * h n)) -
              PrimeTensor.Bridge.MulReal.logValue
                (f x)
          ) -
          scalarCoefficient D *
            PrimeTensor.Bridge.MulReal.logValue
              (h n)
      ) := by

    funext n

    rw [
      PrimeTensor.Bridge.MulDifferential.logValue_derivativeModel_eq_scalar_mul
        hControlled
        (h n)
    ]

  rw [hFun] at hLittle

  exact hLittle

/--
Equivalent packaged scalar first-order semantics.
-/
def HasScalarLogDerivativeAt
    (f : PrimeTensor.MulReal → PrimeTensor.MulReal)
    (x : PrimeTensor.MulReal)
    (c : ℝ) : Prop :=
  ∀ h : PrimeTensor.MulReal.Seq,
    Filter.Tendsto
      (
        fun n : Depth =>
          PrimeTensor.Bridge.MulReal.logValue
            (h n)
      )
      PrimeTensor.Bridge.Depth.tailFilter
      (nhds 0) →
    PrimeTensor.Bridge.RealLogScaleLittleO
      (
        fun n =>
          (
            PrimeTensor.Bridge.MulReal.logValue
                (f (x * h n)) -
              PrimeTensor.Bridge.MulReal.logValue
                (f x)
          ) -
          c *
            PrimeTensor.Bridge.MulReal.logValue
              (h n)
      )
      (
        fun n =>
          PrimeTensor.Bridge.MulReal.logValue
            (h n)
      )

/--
Every native derivative with scale-controlled tangent model determines an
ordinary real scalar logarithmic derivative coefficient.
-/
theorem hasScalarLogDerivativeAt_of_hasMulDerivativeAt
    {f : PrimeTensor.MulReal → PrimeTensor.MulReal}
    {x : PrimeTensor.MulReal}
    {D : PrimeTensor.MulTangentMap}
    (hDeriv :
      PrimeTensor.MulDifferential.HasMulDerivativeAt
        f x D)
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D) :
    HasScalarLogDerivativeAt
      f x
      (scalarCoefficient D) := by

  exact
    PrimeTensor.Bridge.MulDifferential.hasMulDerivativeAt_scalar_log_expansion
      hDeriv
      hControlled

end MulDifferential
end Bridge
end PrimeTensor
