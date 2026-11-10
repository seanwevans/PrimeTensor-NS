# Critical five-thirds weighted full-H3 dissipation: exact cubic endpoint

Base commit: `b39a27e059a48ecef89d7ed38716e34b130e3f50`.

## Established input

On a strict terminal tail of a hypothetical nonextendible admissible H3
energy-class solution, the existing physical PDE theorem supplies

`1 <= B * d^8 * D3(t)^3`, where `d = T - t > 0`,
`B = 81 * h3PathSqrtEnergyRiccatiCoefficient^8 * E0(b)`, and
`0 <= D3(t) <= D_full(t)`.

The preceding commit established a `d^(3/2)` continuation criterion by
converting a squared cubic rate into a quintic-square lower bound. The exact
critical exponent is `5/3`.

## Scalar endpoint argument

Set `C = max B 1 >= 1`. Then `B <= C^3` and

`1 <= B * d^8 * D3^3 <= (C * d^(8/3) * D3)^3`.

The quantity inside the final cube is nonnegative. Taking its monotone
cube gives

`1 <= C * d^(8/3) * D3`.

Using `d^(8/3) = d * d^(5/3)`, and dividing by `d > 0`,

`1/d <= C * d^(5/3) * D3 <= C * d^(5/3) * D_full`.

The constant **cannot** in general be removed by shrinking the terminal tail:
the exponent `5/3` is an exact endpoint. This is why the proof carries the
fixed positive coefficient through the integrability comparison, rather
than borrowing the later-tail smallness argument from the `3/2` case.

## Continuation and limitation

The harmonic function `1/(T-t)` is nonintegrable on every strict terminal
tail. If `d^(5/3) D_full` were integrable on any strict subtail, multiplying it
by the fixed `C` would preserve integrability and contradict the harmonic
lower bound. Contraposition yields smooth continuation through T. An
energy-tail corollary follows by restricting to a strict subtail.

The result is a **conditional continuation criterion**, not unconditional
regularity. The cubic rate alone does not exclude a path with
`D3(t) ~ d^(-8/3)`. It therefore gives no analogous obstruction to
integrability for a larger weight exponent. For instance, `d^2 D3` for
that scalar profile behaves like `d^(-2/3)`, which is integrable. This
illustrates sharpness **of the cubic-rate mechanism**, not an actual
Navier--Stokes singularity construction.

## Declarations and verification

- `thirdFullKinetic_scalar_cubicRate_harmonicCriticalFiveThirds244`
- `thirdFullPhysical_noExtension_harmonicCriticalFiveThirdsDissipation244`
- `thirdFullPhysical_noExtension_criticalFiveThirdsDissipation_nonintegrable244`
- `thirdFullPhysical_criticalFiveThirdsDissipation_strictTail_forcesContinuation244`
- `thirdFullPhysical_criticalFiveThirdsDissipation_energyTail_forcesContinuation244`

These contain no proof placeholders or new axioms. Run `lake env lean` for
the file, `lake build` for its module, and the registered audit checks;
source-level scanning cannot substitute for Lean kernel verification.
