# PrimeTensor-NS

A machine-checked Lean 4 research program toward a global \(H^3\) bound for the three-dimensional incompressible Navier–Stokes equations on \(\mathbb{R}^3\).

The project combines a multiplicative/logarithmic representation layer with a classical Euclidean PDE layer, an explicit \(H^3\) energy analysis, Beale–Kato–Majda-style continuation machinery, and a Fourier/heat-semigroup construction of canonical local restarts.

The central design principle is to make proof boundaries explicit. Analytic statements that have not yet been closed are represented as named propositions and interfaces.

## What is formalized

### Multiplicative PrimeTensor layer

PrimeTensor begins with a positive, multiplicative carrier and develops logarithmic coordinates that turn intrinsic multiplication, inversion, and the multiplicative pivot into the corresponding additive real operations. 
This gives a subtraction-free representation of several familiar Euclidean quantities.

For example, the three components of classical vorticity are represented natively by ratios of multiplicative derivatives, and their logarithms recover the ordinary curl components exactly.

This layer is mathematically equivalent to ordinary real coordinates where the log bridge is available; it should be viewed as an alternative formal representation, not by itself as a new regularity theorem.

### Classical Euclidean Navier–Stokes bridge

The project defines and relates:

- velocity and vorticity fields on \(\mathbb{R}^3\);
- incompressibility and the momentum equation;
- spatial derivatives through order three;
- concrete \(H^3\)-type energy functionals;
- transport, diffusion, and pressure contributions;
- terminal continuation and restart predicates.

### Explicit \(H^3\) transport analysis

The transport term is expanded order by order.

The current Landau/Gagliardo–Nirenberg route obtains the concrete estimate

\[
|T_{H^3}(t)| \le 4422\,h(t)\,E_{H^3}(t),
\]

with the coefficient decomposed as

\[
0 + 6 + 18 + 4398 = 4422,
\qquad
4398 = 24 + 4374,
\qquad
4374 = 729 \cdot 6.
\]

The third-order interpolation bookkeeping is written in a collision-safe form: when derivative indices coincide, individual \(H^3\) energy domination is used rather than an invalid assumption that several possibly identical summands have an unweighted sum bounded by the total energy.

The scalar Landau step includes the explicit bound

\[
\|g\|_{L^4}^2 \le 3h\,\|\partial g\|_{L^2},
\]

derived through quartic integration by parts and cancellation without dividing by a quantity that may vanish.

### BKM / continuation factorization

The continuation side is factored into recognizable analytic pieces:

1. a finite preterminal \(H^3\) seed;
2. an \(L^1_tL^\infty_x\)-style vorticity bound;
3. propagation of \(H^3\) control to a terminal tail;
4. a local restart with a uniform lifespan;
5. continuation through the terminal time.

The repository deliberately isolates the genuinely hard global statement as a named proposition:

`SeededPreterminalNavierStokesForcesVorticityL1Linf`

In the source it is explicitly described as the dangerous a-priori statement and is **not asserted as a theorem**.

### Spectral \(H^3\) restart construction

A second major branch constructs a canonical local restart in Fourier space using:

- weighted spectral \(H^3\) states;
- the heat semigroup;
- the Leray projection;
- bilinear convolution estimates;
- Banach fixed-point / Picard construction;
- real-valued and divergence-free spectral realizability;
- Duhamel restart identities;
- positive-time heat smoothing.

The current classicalization frontier is represented by:

`H3SchwartzCanonicalRestartClassicalization`

This asks the selected Banach-fixed-point spectral path to admit the required real pointwise spacetime representative, with spatial \(C^3\) regularity, time/mixed regularity, the Navier–Stokes equation with pressure, compatibility with the canonical \(L^2\) Fourier decoder, and gluing to the preterminal solution.

### Quarter-Hölder second-Duhamel endpoint analysis

The most developed current path attacks the endpoint regularity needed for classicalization.

A raw second heat moment has the terminal singularity

\[
(t-s)^{-1}.
\]

The forcing is split at the terminal value,

\[
N(s)=\bigl(N(s)-N(t)\bigr)+N(t).
\]

For the difference term the selected mild path is shown to have a local \(1/4\)-Hölder modulus, which transfers to the nonlinear forcing:

\[
\|N(s)-N(t)\|_{L^1_\xi}
\lesssim
(t-s)^{1/4}.
\]

The cancelled second-moment singularity is therefore

\[
(t-s)^{-3/4},
\]

which is integrable at the endpoint.

The implementation then separates and closes:

- the old-history contribution;
- the terminal half-tail;
- the frozen terminal forcing;
- the heat primitive for the frozen term;
- the time/frequency Fubini exchange;
- the combined selected forcing budget.

This is an explicit Lean realization of an analytic-semigroup endpoint-cancellation strategy.

## What is not yet proved

Several major mathematical boundaries are intentionally represented by named propositions. The most important current examples include:

- `SeededPreterminalNavierStokesForcesVorticityL1Linf`;
- `H3SchwartzCanonicalRestartClassicalization`;
- high-level whole-space analytic interfaces used by the Landau/BKM route where their concrete hypotheses have not yet been discharged.

These are ordinary Lean propositions passed as hypotheses to downstream theorems.

## Verification status

The project currently targets:

- **Lean:** `leanprover/lean4:v4.34.0-rc1`
- **mathlib:** pinned by `lake-manifest.json`

## Build

Install Lean then:

```bash
git clone https://github.com/seanwevans/PrimeTensor-NS.git
cd PrimeTensor-NS

lake env lean PrimeTensor.lean
lake build
```

The root `PrimeTensor.lean` file is the aggregate import surface.
