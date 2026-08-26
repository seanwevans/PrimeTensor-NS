# PrimeTensor-NS

A machine-checked Lean 4 research program toward a global H<sup>3</sup> bound for the three-dimensional incompressible Navier–Stokes equations on ℝ<sup>3</sup>.

The project combines a multiplicative/logarithmic representation layer with a classical Euclidean PDE layer, an explicit H<sup>3</sup> energy analysis, Beale–Kato–Majda-style continuation machinery, and a Fourier/heat-semigroup construction of canonical local restarts.

The central design principle is to make proof boundaries explicit. Analytic statements that have not yet been closed are represented as named propositions and interfaces.

## What is formalized

### Multiplicative PrimeTensor layer

PrimeTensor begins with a positive, multiplicative carrier and develops logarithmic coordinates that turn intrinsic multiplication, inversion, and the multiplicative pivot into the corresponding additive real operations.
This gives a subtraction-free representation of several familiar Euclidean quantities.

For example, the three components of classical vorticity are represented natively by ratios of multiplicative derivatives, and their logarithms recover the ordinary curl components exactly.

This layer is mathematically equivalent to ordinary real coordinates where the log bridge is available; it should be viewed as an alternative formal representation, not by itself as a new regularity theorem.

### Classical Euclidean Navier–Stokes bridge

The project defines and relates:

- velocity and vorticity fields on ℝ<sup>3</sup>;
- incompressibility and the momentum equation;
- spatial derivatives through order three;
- concrete H<sup>3</sup>-type energy functionals;
- transport, diffusion, and pressure contributions;
- terminal continuation and restart predicates.

### Explicit H<sup>3</sup> transport analysis

The transport term is expanded order by order.

The current Landau/Gagliardo–Nirenberg route obtains the concrete estimate

<p align="center">|T<sub>H<sup>3</sup></sub>(t)| ≤ 4422 h(t) E<sub>H<sup>3</sup></sub>(t),</p>

with the coefficient decomposed as

<p align="center">0 + 6 + 18 + 4398 = 4422,<br>
4398 = 24 + 4374,<br>
4374 = 729 · 6.</p>

The third-order interpolation bookkeeping is written in a collision-safe form: when derivative indices coincide, individual H<sup>3</sup> energy domination is used rather than an invalid assumption that several possibly identical summands have an unweighted sum bounded by the total energy.

The scalar Landau step includes the explicit bound

<p align="center">‖g‖<sub>L<sup>4</sup></sub><sup>2</sup> ≤ 3h ‖∂g‖<sub>L<sup>2</sup></sub>,</p>

derived through quartic integration by parts and cancellation without dividing by a quantity that may vanish.

### BKM / continuation factorization

The continuation side is factored into recognizable analytic pieces:

1. a finite preterminal H<sup>3</sup> seed;
2. an L<sub>t</sub><sup>1</sup>L<sub>x</sub><sup>∞</sup>-style vorticity bound;
3. propagation of H<sup>3</sup> control to a terminal tail;
4. a local restart with a uniform lifespan;
5. continuation through the terminal time.

The repository deliberately isolates the genuinely hard global statement as a named proposition:

`SeededPreterminalNavierStokesForcesVorticityL1Linf`

In the source it is explicitly described as the dangerous a-priori statement and is **not asserted as a theorem**.

### Spectral H<sup>3</sup> restart construction

A second major branch constructs a canonical local restart in Fourier space using:

- weighted spectral H<sup>3</sup> states;
- the heat semigroup;
- the Leray projection;
- bilinear convolution estimates;
- Banach fixed-point / Picard construction;
- real-valued and divergence-free spectral realizability;
- Duhamel restart identities;
- positive-time heat smoothing.

The current classicalization frontier is represented by:

`H3SchwartzCanonicalRestartClassicalization`

This asks the selected Banach-fixed-point spectral path to admit the required real pointwise spacetime representative, with spatial C<sup>3</sup> regularity, time/mixed regularity, the Navier–Stokes equation with pressure, compatibility with the canonical L<sup>2</sup> Fourier decoder, and gluing to the preterminal solution.

### Quarter-Hölder second-Duhamel endpoint analysis

The most developed current path attacks the endpoint regularity needed for classicalization.

A raw second heat moment has the terminal singularity

<p align="center">(t − s)<sup>−1</sup>.</p>

The forcing is split at the terminal value,

<p align="center">N(s) = (N(s) − N(t)) + N(t).</p>

For the difference term the selected mild path is shown to have a local 1/4-Hölder modulus, which transfers to the nonlinear forcing:

<p align="center">‖N(s) − N(t)‖<sub>L<sub>ξ</sub><sup>1</sup></sub> ≲ (t − s)<sup>1/4</sup>.</p>

The cancelled second-moment singularity is therefore

<p align="center">(t − s)<sup>−3/4</sup>,</p>

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

## Numerical experiments

The maintained probe in
`experiments/prime_tensor_diagonal_obstruction.py` demonstrates why the raw
same-depth finite coupling cannot be used without input-dependent precision
scheduling. It constructs continued-fraction convergents to
`log(3) / log(2)` and shows, with arbitrary-precision arithmetic, how atomic
dyadic rounding errors are amplified on the diagonal. This is a diagnostic
for the scheduling issue discussed in
`PrimeTensor/Fluid/Coupling/Tail/Input.lean`; it is not part of the Lean build
and is not evidence against the intended finite coupling target.

Install the experiment dependency and run the probe from the repository root:

```bash
python3 -m pip install -r experiments/requirements.txt
python3 experiments/prime_tensor_diagonal_obstruction.py
```
