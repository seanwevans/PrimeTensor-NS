# Physical projected momentum: smooth approximation stability

Baseline: `d219441e`, following the differentiated solenoidal weak momentum
interface. The actual old velocity `U` and projected source `R` are continuous
with values in the physical real L² Hilbert space on every compact positive-time
window. Their FTC defect `D(a,b)` was isolated and proved to be Leray-fixed and
determined by solenoidal compact tests.

## A quantitative mollification criterion

On `[a,b]` with `0<a<b<T`, suppose `Vε` and `Wε` are continuous Hilbert-valued
approximations such that `Vε'(t)=Wε(t)` for `a<t<b`, and

  sup_[a,b] ‖U(t)-Vε(t)‖₂ ≤ ε,
  sup_[a,b] ‖R(t)-Wε(t)‖₂ ≤ ε.

Then the vector-valued FTC and interval-integral estimate give

  ‖D(a,b)‖₂ ≤ (2 + b-a) ε.

This bound is new relative to the previous weak-FTC equivalences: it permits an
analytic proof through consistent smooth approximations. Arbitrarily small ε
implies `D(a,b)=0`; the same approximants restricted to any prefix `[a,r]` imply
zero defect on that prefix and therefore solenoidal weak FTC.

The outstanding step is constructing a regularization pair with the exact
identity `Vε'=Wε` and simultaneous uniform convergence to the **actual** old
velocity and its **actual** projected Navier–Stokes source. It must follow from
the physical distributional momentum equation; arbitrary independent smooth
approximations of U and R do NOT have the needed derivative identity.

No unconditional weak FTC or 3D Navier–Stokes regularity claim is made.
