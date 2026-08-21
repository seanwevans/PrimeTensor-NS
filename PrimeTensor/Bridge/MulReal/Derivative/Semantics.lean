import PrimeTensor.Bridge.MulReal.Negligible.Semantics

/-!
# Multiplicative derivative semantics in logarithmic coordinates

The native derivative

    HasMulDerivativeAt f x D

is formulated without subtraction or additive zero:

* perturbations `h` approach the multiplicative pivot `1`;
* the actual response is `f (x * h) / f x`;
* the model response is `D h`;
* their ratio is negligible relative to `h`.

The bridge developed so far gives:

* `h -> 1` intrinsically iff `logValue (h n) -> 0`;
* the log of a response ratio is an ordinary difference;
* intrinsic negligibility implies strict real logarithmic scale-little-o.

This file combines those facts into the first complete conventional-coordinate
semantics of `HasMulDerivativeAt`.

No claim is made here that the logged tangent map is yet a globally defined
real-linear map on all of `ℝ`.  The theorem is instead stated exactly on the
canonical logarithmic coordinates of intrinsic perturbations.
-/

namespace PrimeTensor
namespace Bridge

namespace MulTangentMap

/--
Canonical real logarithmic coordinate of a native multiplicative tangent
response.
-/
noncomputable def logResponse
    (D : PrimeTensor.MulTangentMap)
    (h : PrimeTensor.MulReal) : ℝ :=
  PrimeTensor.Bridge.MulReal.logValue (D h)

@[simp]
theorem logResponse_one
    (D : PrimeTensor.MulTangentMap) :
    logResponse D 1 = 0 := by

  unfold logResponse

  rw [
    D.map_one,
    PrimeTensor.Bridge.MulReal.logValue_one
  ]

/--
A native multiplicative tangent morphism becomes additive in logarithmic
coordinates.
-/
theorem logResponse_mul
    (D : PrimeTensor.MulTangentMap)
    (a b : PrimeTensor.MulReal) :
    logResponse D (a * b) =
      logResponse D a + logResponse D b := by

  unfold logResponse

  rw [
    D.map_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul
  ]

/--
Native tangent inversion becomes ordinary negation in logarithmic coordinates.
-/
theorem logResponse_inv
    (D : PrimeTensor.MulTangentMap)
    (a : PrimeTensor.MulReal) :
    logResponse D a⁻¹ =
      - logResponse D a := by

  unfold logResponse

  rw [
    D.map_inv,
    PrimeTensor.Bridge.MulReal.logValue_inv
  ]

end MulTangentMap

namespace MulDifferential

/--
The ordinary real logarithmic first-order residual associated with a native
multiplicative derivative candidate.

For perturbation `h n`, the residual is

    [L(f(x*h_n)) - L(f(x))] - L(D(h_n)).

This is the conventional-coordinate form of the native error ratio

    response(f,x,h)_n / D(h_n).
-/
noncomputable def realLogResidual
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
  PrimeTensor.Bridge.MulTangentMap.logResponse
    D (h n)

/--
Real logarithmic first-order semantics of a derivative candidate.

Every intrinsic perturbation whose logarithmic coordinate tends to zero has a
logged residual that is little-o of the logged perturbation in the exact
dyadic-scale sense inherited from the native scale hierarchy.
-/
def HasRealLogFirstOrderAt
    (f : PrimeTensor.MulReal → PrimeTensor.MulReal)
    (x : PrimeTensor.MulReal)
    (D : PrimeTensor.MulTangentMap) : Prop :=
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
          realLogResidual f x D h n
      )
      (
        fun n =>
          PrimeTensor.Bridge.MulReal.logValue
            (h n)
      )

/--
The log of the native first-order error ratio is exactly the ordinary
real-log residual.
-/
theorem logValue_firstOrderError_eq_realLogResidual
    (f : PrimeTensor.MulReal → PrimeTensor.MulReal)
    (x : PrimeTensor.MulReal)
    (D : PrimeTensor.MulTangentMap)
    (h : PrimeTensor.MulReal.Seq)
    (n : Depth) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.MulReal.ratio
            (
              PrimeTensor.MulDifferential.response
                f x h n
            )
            (D (h n))
        )
      =
    realLogResidual f x D h n := by

  rw [
    PrimeTensor.Bridge.MulReal.logValue_ratio,
    PrimeTensor.Bridge.MulDifferential.logValue_response
  ]

  rfl

/--
Every intrinsic multiplicative derivative has an exact real logarithmic
first-order interpretation.

This is the bridge theorem combining the native derivative definition with the
completed logarithmic convergence and little-o semantics.
-/
theorem hasMulDerivativeAt_to_realLogFirstOrder
    {f : PrimeTensor.MulReal → PrimeTensor.MulReal}
    {x : PrimeTensor.MulReal}
    {D : PrimeTensor.MulTangentMap}
    (hDeriv :
      PrimeTensor.MulDifferential.HasMulDerivativeAt
        f x D) :
    PrimeTensor.Bridge.MulDifferential.HasRealLogFirstOrderAt
      f x D := by

  intro h hLogZero

  have hPivot :
      PrimeTensor.MulDifferential.ApproachesPivot h :=
    (
      PrimeTensor.Bridge.MulDifferential.approachesPivot_iff_logValue_tendsto_zero
        h
    ).2 hLogZero

  have hFirst :
      PrimeTensor.MulDifferential.FirstOrderEquivalent
        h
        (
          PrimeTensor.MulDifferential.response
            f x h
        )
        (
          fun n => D (h n)
        ) :=
    hDeriv h hPivot

  have hLittle :=
    PrimeTensor.Bridge.MulDifferential.firstOrderEquivalent_to_realLogScaleLittleO
        hFirst

  have hFun :
      (
        fun n : Depth =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              PrimeTensor.MulReal.ratio
                (
                  PrimeTensor.MulDifferential.response
                    f x h n
                )
                (D (h n))
            )
      )
        =
      (
        fun n : Depth =>
          PrimeTensor.Bridge.MulDifferential.realLogResidual
            f x D h n
      ) := by

    funext n

    exact
      PrimeTensor.Bridge.MulDifferential.logValue_firstOrderError_eq_realLogResidual
        f x D h n

  rw [hFun] at hLittle

  exact hLittle

/--
Expanded user-facing form of the bridge theorem.

For every logged perturbation tending to zero, the real residual

    L(f(x*h_n)) - L(f(x)) - L(D(h_n))

is logarithmically little-o of `L(h_n)`.
-/
theorem hasMulDerivativeAt_log_expansion
    {f : PrimeTensor.MulReal → PrimeTensor.MulReal}
    {x : PrimeTensor.MulReal}
    {D : PrimeTensor.MulTangentMap}
    (hDeriv :
      PrimeTensor.MulDifferential.HasMulDerivativeAt
        f x D) :
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
            PrimeTensor.Bridge.MulReal.logValue
              (D (h n))
        )
        (
          fun n =>
            PrimeTensor.Bridge.MulReal.logValue
              (h n)
        ) := by

  intro h hLogZero

  exact
    PrimeTensor.Bridge.MulDifferential.hasMulDerivativeAt_to_realLogFirstOrder
        hDeriv
        h
        hLogZero

end MulDifferential

end Bridge
end PrimeTensor
