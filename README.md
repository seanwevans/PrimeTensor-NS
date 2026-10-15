# PrimeTensor-NS

Lean 4 / mathlib formalization of a continuation program for the three-dimensional incompressible Navier–Stokes equations on `ℝ³`.

The development formalizes **conditional terminal behavior and continuation criteria** for H³ paths, alongside exact physical Schwartz energy identities. These results are not an a-priori estimate for every Navier–Stokes solution.

This repository does **not** prove finite-time blowup and does **not** prove unconditional global regularity.

## Current endpoint setting

The strongest terminal results currently use a logged preterminal H³ path together with:

- a preterminal H³ energy class;
- an actual-vorticity strong H³ endpoint path for one component;
- raw velocity Fourier `L²` Cauchy convergence at the endpoint.

These are retained hypotheses in the endpoint spectral-tail theorems below. The conclusions should therefore be read conditionally on this setting.

**Known-criterion warning:** despite its name, `H3TerminalActualVorticityStrongH3EndpointPath` supplies strong weighted spectral H³ terminal endpoints for **two physical velocity components**. A published one-component criterion of [Liu–Zhang (2024)](https://doi.org/10.1137/23M1623124) gives continuation for a compatible local strong Navier–Stokes solution from one velocity component in `L²_t Ḣ^{3/2}_x`. Our intrinsic positive-start time-`L²` bridge is largely formalized, but compatibility with that external theorem and its continuation conclusion is **not** proved in Lean. Consequently the retained-hypothesis nonextension branch is likely redundant for compatible strong solutions, not an independently established new regularity scenario.

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

## Current frontier: known analytic estimates versus new PDE control

The spectral-tail and coercive-weight results are **conditional continuation criteria and logical consequences of their failure**, not a derivation of terminal compactness from Navier–Stokes dynamics. Uniform high-frequency tail control is not itself equivalent to whole-trajectory spatial precompactness on `ℝ³` (translations matter). Cofinal cutoff escape does not supply a physical-time growth rate.

The *complete signed 243-slot first monomial* `M` has derivative orders `(3,2,2)`. The **existence** of a universal critical-half inequality is already known mathematically from Hölder, homogeneous Sobolev embedding `Ḣ^{3/4}(ℝ³) ⊂ L⁴`, and interpolation:

```text
|M(u)| <= C_* ||u||_{Ḣ^{1/2}} ||u||_{Ḣ^4}^2
       <= C_*' sqrt(1 + E0(u)+E1(u)+E2(u)+E3(u)) D(u).
```

The sharp five-order coefficient-one Schwartz interpolation and shape-orbit identities are **proved in Lean**; the displayed universal `L⁴` / fractional-Sobolev bound is **not yet proved in Lean for the exact project definitions**. Consequently the normalized shape quotient is mathematically bounded, and conditional strict-excess witnesses can refute only coefficients below a suitable finite threshold.

Even when formalized, the critical-half inequality does **not** establish arbitrary-data global regularity: the coefficient `C_* ||u||_{Ḣ^{1/2}}` cannot generally be absorbed into viscosity without smallness or a genuinely stronger dynamical estimate. Any new closing argument must exploit structure of the **true** Navier–Stokes nonlinearity not supplied by generic Hölder/Sobolev estimates; see [Tao's averaged-model obstruction](https://arxiv.org/abs/1402.0290).

Next priorities: formalize the known critical-half inequality with actual Schwartz derivatives and constants; complete the one-component literature-eligibility bridge on a positive-start interval; and look for a genuinely new PDE-specific a-priori control. See the [October 15 theorem-boundary correction](docs/audit/critical-half-roadmap-correction-2026-10-15.md).

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

## Audit and consolidation

The [consolidation checkpoint](docs/audit/README.md) records the successful
`1c4104d6` build baseline, the distinction between terminal extension and genuine
post-terminal restart, and the five sources awaiting separate coverage review.
The [proof documentation guide](proof/README.md) explains the generated source
index and the partial prose-fragment coverage.
