# Finite Z³ Galerkin flow: first constructive ODE bridge

**Base:** `eaf13270852f04701f67b087d6b7bf3e84223e87`

## Mathematical claim attempted in Lean

For each finite frequency set S and finite coefficient datum x₀, define
X_S = (S → ℂ³). For n ∈ S let

    F_S(x)_n = -μ |n|² x_n - i P_n Σ_{p,q∈S, p+q=n} (q·x_p)x_q.

This is the exact existing Leray-projected full quadratic Galerkin field,
including collision outputs. It is a polynomial in the real and imaginary
components of finitely many coefficients, and hence C∞ as a map X_S → X_S.
Finite-dimensional Picard–Lindelöf therefore yields a solution on some
open time interval about a. The new module attempts to formalize that
C¹ argument and invoke Mathlib's theorem
`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`.

**Important:** the algebraic proof is straightforward, but the `fun_prop`
normalization of complex inner products, finite sums and `starProjection`
must actually be accepted by the pinned Lean version. The module is an
*unverified Lean candidate until the run script passes*. The script never
commits or pushes a failed candidate.

## Next mathematical theorem: uniform lifespan

The cutoff-dependent local interval is insufficient. The next theorem must
apply the existing cutoff-independent persistence estimate to a maximal
finite ODE solution and show continuation through

    τ = (log 2 - log(9/5)) / 100.

For all times t ≤ a + τ, the existing comparison gives

    Σ_{n∈S} exp((log 2 - 100(t-a)) |n|₁) |u_n(t)| ≤ 100

when its strict initial analytic 2-ball hypothesis holds. Since the radius
is at least log(9/5) > 0, this gives a cutoff-independent bound in a
fixed Wiener norm. For any *particular finite S*, norm equivalence on X_S
then prevents finite-time blow-up; polynomial ODE continuation extends the
flow to the entire common interval. Crucially, the norm-equivalence
constant may depend on S: only the final existence interval must not.

The finite local existence theorem is NOT a proof of the last step. An
explicit continuation/compactness lemma and conversion of finite-state
ODE derivatives to coefficientwise `HasDerivAt` remain open.

After that: derive coefficientwise interval integrability automatically,
then use existing strong ODE → Duhamel and residual lemmas. Cutoff limit,
Hermitian reality, solenoidal invariance, and the whole-space H³ problem
remain separate mathematical tasks.

## Lean repair: dependent subtype evaluation

The first compilation attempted to unfold the zero-extension before
`fun_prop`, exposing a dependent `if n ∈ S` in the differentiation goal.
This is a fixed membership proposition, not a time- or state-dependent
branch. The repair proves `ContDiff ℝ 1` of each zero-extended coefficient
by cases on membership, registers that result with `fun_prop`, and keeps
the extension opaque while differentiating the exact finite quadratic
field. It does not alter the vector field, the time interval, or the
mathematical existence claim.

This patched Lean proof is unverified until the pinned project compiler
accepts it.

## Second Lean repair: fixed collision indicators and finite output coordinates

The following obstruction remained after the zero-extension C¹ lemma:
`fun_prop` unfolded the finite extension and tried to infer `Fintype` for
the entire Z³ lattice; it also treated the fixed test `p + q = n` as an
unsolved differentiability step. This was a proof decomposition problem.

The revised proof gives a coordinatewise real-C¹ lemma for the exact
Galerkin field. It splits each constant collision test with `by_cases`,
combines `ContDiff.sum` for both finite input sums, uses `ContDiff.inner`
for the complex physical inner product, `ContDiff.smul` for quadratic
transport, and `ContinuousLinearMap.restrictScalars` for the complex
Leray projector. Finally `contDiff_pi` assembles the finite field.
No Fourier coefficient, collision, projection, or mathematical hypothesis
is changed. Lean must still verify the proof on the pinned project version.
