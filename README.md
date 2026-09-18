# PrimeTensor-NS

A Lean 4 research formalization of a continuation strategy for the three-dimensional incompressible Navier–Stokes equations on ℝ³, centered on explicit H³ energy estimates, a Landau/Gagliardo–Nirenberg transport analysis, and a Fourier/heat-semigroup restart construction.

The repository also contains a positive multiplicative/logarithmic representation layer. Where the logarithmic bridge is available, that layer is related back to ordinary real-valued PDE quantities; it should be read as an alternative formal representation, not as a shortcut around the classical analytic difficulties.

## Current proof status

### Landau / H³ transport side

The whole-space analytic machinery used by the explicit Landau estimate has been substantially internalized.

The repository now includes machine-checked proofs of:

- the whole-space C¹ ∩ H¹ → L⁶ Sobolev step on `Point3`, obtained through expanding smooth cutoffs;
- the derived L⁴ interpolation step;
- quartic whole-space integration by parts through a compact-cutoff argument;
- decay of the quartic cutoff boundary error;
- the scalar Landau inequality used by the third-order interpolation terms;
- explicit order-by-order H³ transport bookkeeping.

The transport estimate has the concrete coefficient

|T_H³(t)| ≤ 4422 h(t) E_{H³}(t)

with the bookkeeping decomposition

0 + 6 + 18 + 4398 = 4422  
4398 = 24 + 4374  
4374 = 729 · 6

The collision cases in the third-order derivative sums are handled explicitly; the proof does not assume that several potentially identical H³ summands can each be charged independently to the total energy.

### Transport integration by parts: current reduction

The lower-order whole-space transport integration-by-parts packages are no longer independent assumptions.

From canonical H³ data and the velocity-gradient envelope, the repository derives:

- order-zero transport IBP;
- order-one transport IBP;
- order-two transport IBP.

At order three, the canonical PDE pairing package already gives integrability of the full differentiated transport pairing. The exact decomposition

D³u · D³((u · ∇)u) = D³u · C₃ + D³u · (u · ∇D³u)

combined with independently proved commutator-pairing integrability recovers integrability of the pure transported-third-derivative pairing.

Accordingly, the verified Landau tail interface has been reduced to

```lean
H3ThirdDerivativeTransportFluxVanishesAt u t
  ∧
VelocityGradientEnvelope u h t
```

at each strict tail time.

In other words, the transport-side whole-space frontier is no longer a collection of order-zero-through-three IBP assumptions. It has been reduced to the top-order boundary-at-infinity cancellation together with the gradient envelope.

The active development immediately beyond that verified reduction is aimed at internalizing the L¹-integrability of the top-order flux divergence from the already available PDE pairing data, without introducing an artificial D⁴u ∈ L² requirement.

### Continuation / restart side

The restart/classicalization side is much further developed than the older monolithic `H3SchwartzCanonicalRestartClassicalization` description suggests.

The spectral construction includes:

- weighted Fourier H³ states;
- the heat semigroup;
- Leray projection;
- convolution estimates;
- a Banach fixed-point / Picard construction;
- real-valued and divergence-free realizability;
- Duhamel identities;
- positive-time smoothing;
- physical L² decoding;
- selected-versus-old overlap machinery.

The later physical-tail development factors classicalization and continuation into explicit local pieces rather than one opaque frontier. It contains pressure-free weak formulations, spatial integration by parts against real Schwartz tests, selected/old weak–strong comparison, temporal weak FTC identities, endpoint continuity reductions, and physical H³ L²-jet arguments.

A particularly important later reduction proves that, under the retained canonical H³ tail hypotheses,

full physical H³ L²-jet continuity ↔ scalar physical H³-energy continuity.

The pressure-free curl / weak-FTC route now supplies the abstract continuation statement `H3ControlProducesExtension` from the terminal H³ control side, so the Landau-facing continuation theorem no longer needs a separate abstract local-well-posedness or restart-lifespan hypothesis.

## Remaining high-level analytic interfaces

The current Landau/BKM factorization still exposes several major mathematical interfaces as hypotheses.

### `H3SeedProducesEnergyClass`

Promotes a finite H³ seed into the high-order preterminal energy class used by the later energy argument.

### `EnergyClassProducesCanonicalH3Data`

Produces the canonical H³ tail package used by the explicit transport, PDE-pairing, and continuation machinery.

### `EnergyClassProducesLandauTransportAnalytic`

Supplies the remaining Landau tail data. After the recent transport reductions, its transport content is concentrated at the top-order scalar-flux cancellation together with the velocity-gradient envelope.

### `VorticityControlsGradientLogarithmically`

The BKM/Landau endpoint estimate converting vorticity control into the velocity-gradient control required by the H³ growth inequality.

### `SeededPreterminalNavierStokesForcesVorticityL1Linf`

The genuinely global a-priori statement that every seeded preterminal solution has the required finite L¹ₜL∞ₓ-type vorticity control.

This last proposition is intentionally isolated in the source. It is **not** asserted as a theorem. Even after the continuation/restart machinery is closed, proving this a-priori statement would be a separate global-regularity problem.

With the first four interfaces supplied, the repository proves the seeded vorticity criterion implies extension. To conclude that every seeded preterminal solution extends, the additional a-priori vorticity interface is still required.

## Build

Install Lean via `elan`, then:

```bash
git clone https://github.com/seanwevans/PrimeTensor-NS.git
cd PrimeTensor-NS

lake env lean PrimeTensor.lean
lake build
```

`PrimeTensor.lean` is the aggregate import surface for the library.
