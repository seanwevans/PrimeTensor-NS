# PrimeTensor-NS

Lean 4 / mathlib formalization of a continuation program for the three-dimensional incompressible Navier–Stokes equations on `ℝ³`.

The current development studies **necessary terminal behavior under hypothetical failure of smooth H³ continuation** and turns the negation of those behaviors into explicit continuation criteria.

This repository does **not** prove finite-time blowup and does **not** prove unconditional global regularity.

## Current endpoint setting

The strongest terminal results currently use a logged preterminal H³ path together with:

- a preterminal H³ energy class;
- an actual-vorticity strong H³ endpoint path for one component;
- raw velocity Fourier `L²` Cauchy convergence at the endpoint.

These are retained hypotheses in the endpoint compactness theorems below. The conclusions should therefore be read conditionally on this setting.

## Canonical top-order dissipation tail

Let

```text
Tail₃(t, R)
```

denote the canonical top-order H³ dissipation mass outside radial frequency `R`.

At every fixed strict preterminal time `t < T`,

```text
Tail₃(t, n + 1) → 0
```

as `n → ∞`.

The endpoint issue is therefore not whether a fixed preterminal state has a high-frequency tail. Every fixed-time tail vanishes. The issue is whether that decay is **uniform as `t → T`**.

Define terminal uniform tail vanishing by:

```text
for every ε > 0,
there exist N and η > 0 such that

  t < T,
  dist(t, T) < η,
  n ≥ N

imply

  Tail₃(t, n + 1) < ε.
```

This is equivalent to canonical top-order radial-tail tightness.

Under the retained endpoint hypotheses, uniform tail vanishing implies smooth continuation across `T`.

Conversely, hypothetical nonextension forces failure of this uniformity even though the fixed-time tail still vanishes at every strict preterminal time.

So the present compactness obstruction is a genuinely terminal one:

```text
fixed-time tail decay
    +
failure of uniformity as t → T.
```

## Canonical cutoff scale

For `ε > 0`, define the least natural cutoff index

```text
Nε(t)
  =
min { n : ℕ | Tail₃(t, n + 1) < ε }.
```

`Nε(t)` is finite at every fixed strict time.

Terminal uniform tail vanishing is exactly equivalent to:

```text
for every ε > 0,
Nε(t) is bounded on some terminal neighborhood of T.
```

Under the retained endpoint hypotheses, local boundedness of every `Nε` is therefore a continuation criterion.

Hypothetical nonextension forces the complementary behavior: for some fixed `ε > 0`, the scale `Nε(t)` is unbounded in **every** terminal neighborhood.

More strongly, for every prescribed natural profile

```text
g : ℕ → ℕ,
```

one can select strict terminal times `τₙ → T` such that

```text
dist(τₙ, T) < 1 / (n + 1)
```

and

```text
g(n) < Nε(τₙ).
```

This is a cofinality statement obtained by selecting the times according to `g`.

It is **not** a physical-time growth estimate. In particular, the formalization does not infer a lower bound of the form

```text
Nε(t) ≥ F(T - t).
```

## Coercive spectral weights

The radial-tail criterion has a weighted formulation.

Let

```text
w : ℝ → ℝ
```

be any real radial weight satisfying only

```text
w(r) → +∞  as r → +∞.
```

No monotonicity assumption and no global sign assumption are required.

A finite uniform terminal bound for the corresponding extended weighted top-order dissipation moment implies canonical radial-tail tightness and hence smooth continuation under the retained endpoint hypotheses.

Equivalently, hypothetical nonextension rules out such a uniform ceiling for **every** coercive radial weight.

The formalization also constructs one common terminal radial-escape sequence along which the extended weighted top-order dissipation moment diverges for every such weight.

Polynomial higher moments and positive exponential radial weights occur as special cases of this more general coercive-weight mechanism.

## Neutral endpoint alternatives

The formalized results are deliberately stated neutrally.

Typical endpoint alternatives have the form

```text
smooth continuation across T
```

or

```text
a fixed positive tail tolerance develops an unbounded
canonical cutoff scale near T.
```

A stronger form replaces the second branch by arbitrary-profile cofinal escape of the cutoff scale.

Another equivalent style uses universal divergence of coercively weighted top-dissipation moments along a terminal sequence.

None of these alternatives asserts that the nonextension branch actually occurs.

## Current frontier

The project has reduced the surviving terminal obstruction to frequency-space compactness of the top-order H³ dissipation.

The remaining problem is to obtain a continuation-producing compactness statement from the Navier–Stokes dynamics themselves—for example, terminal uniform radial-tail control or a uniform bound for one coercive weighted top-dissipation moment—without assuming the desired continuation conclusion.

The current endpoint theorems also retain the actual-vorticity strong H³ endpoint-path and raw velocity Fourier `L²` Cauchy hypotheses described above.

Earlier energy-growth, BKM, transport, Landau, moment-cascade, and balance-channel results remain part of the formal development, but they are now intermediate infrastructure rather than the cleanest statement of the present endpoint criterion.

## Interpretation

These are **conditional obstruction and continuation theorems**.

For example,

```text
no smooth continuation
  ->
some Nε(t) is locally unbounded near T
```

does not establish nonextension.

Its contrapositive value is that an independent estimate preventing that terminal frequency escape yields continuation.

Likewise, divergence of weighted moments on a hypothetical nonextension branch should not be read as a claim that such a branch exists.

## Build

```bash
lake build
```
