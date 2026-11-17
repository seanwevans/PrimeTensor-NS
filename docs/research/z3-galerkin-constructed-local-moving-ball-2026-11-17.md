# Constructed local Z³ Galerkin moving-ball bridge

**Baseline:** `0500b4a2086631763b4a5908bae9cce82adc8d0e`

## Mathematical advance

The previous source commits genuine *local* Picard--Lindelöf existence of the
finite coefficient ODE, with vector field exactly equal to the complete
complex Leray Fourier convolution plus viscosity. The cutoff-independent
moving analytic-ball theorem, established at `eaf132708`, still takes an
actual coefficientwise strong path as a hypothesis.

This change **eliminates that path hypothesis on a strictly positive initial
interval**. Starting from any finite state `x0` with strict
`W_log(2)(extend_S x0) < 100`, and `μ ≥ 0`, the new theorem constructs
`α : ℝ → X_S`, a positive interval `[a,a+δ]`, and establishes both the genuine
finite ODE on the interval and

```
W_{log(2)-100(t-a)}(extend_S α(t)) ≤ 100,
for every t ∈ [a,a+δ],    0 < δ ≤ (log 2 - log(9/5))/100.
```

Here `X_S = {n // n ∈ S} → ℂ³`, and `δ` **may depend on S and x0**. The
constant 100 and the enclosing analytic-radius window do not depend on S.

The derivative lift is through coordinate projections of the finite Pi-space,
not a fictitious `Fintype` instance on all of ℤ³. Membership in S remains
fixed during differentiation; zero extension has the exact old meaning.

## The actual next theorem: a common lifespan

Let τ = `(log 2 - log(9/5))/100`. For each finite S, consider the maximal
solution `α_S` from the strict initial analytic ball.

1. Apply the existing moving-ball persistence to every compact subinterval
   `[a,b]` of its maximal lifetime with `b ≤ a+τ`. The anchor remains the
   **original** `a`; do not restart with a new log(2) analytic hypothesis.
2. The moving radius satisfies `r_a(t) ≥ log(9/5) > 0`. Thus every retained
   coefficient obeys `‖α_S(t)_n‖ ≤ 100` (in fact an exponential frequency
   envelope). For each fixed finite S this bounds the state norm in X_S.
3. The exact finite polynomial Leray field is continuous, so it is bounded
   on the closed state ball for this S. As the maximal right endpoint is
   approached, `α_S` is Lipschitz; it has a finite endpoint limit.
4. Local C¹ ODE existence at that limit, together with local uniqueness,
   extends the solution beyond a hypothetical endpoint `< a+τ`. Therefore
   every finite S has a solution through `[a,a+τ]`.
5. Only after the uniform existence interval is available should one derive
   automatic coefficientwise integrability, exact Duhamel, and cutoff-limit
   compactness.

**Important:** The endpoint extension can use S-dependent norms and
Lipschitz constants. Uniformity of the *interval* comes from the analytic
barrier, not a uniform Euclidean dimension estimate. The real-valued
periodic/Hermitian/solenoidal constraints and the bridge to the whole-space
H³ problem remain separate obligations. No arbitrary-H³ continuation follows.

## Verification policy

- The accompanying Lean proof is a candidate and has not been run against the
  pinned project toolchain in the authoring environment.
- Audit source registry, proof index, full Lean build, and baseline audit are
  mandatory before commit or push.
- No `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide` proof escapes.
- No `FIX-NOTES.txt` and no repository-root shell script.
