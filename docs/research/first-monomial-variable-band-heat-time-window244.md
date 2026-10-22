# Temporal exhaustion in the two-band linear heat model

Base checkpoint: `a2e971a9`, simultaneous near-Young gap collapse and unbounded pointwise heat concentration.

## Relative spectral heat orbit

For the two radial weights `q1=1`, `q2=n²`, Fourier squared amplitudes decay as `exp(-2 q t)`. Starting at masses `x=n⁹`, `y=1`, divide out the common `exp(-2t)`. The normalized Young gap is invariant under common positive rescaling, and the relative high-band mass is therefore exactly

    y(t) = exp(-2(n²-1)t).

The new Lean module defines this exponential relative mass and the corresponding rational normalized gap. The important exact algebraic difference formula for two positive high-band masses `y <= z` is

    R(z)-R(y) = x (r²-1)² (z-y) (x²-r⁴ y z) /
       [ (x+y)(x+r⁴y)(x+z)(x+r⁴z) ].

Thus when `r⁴ y z <= x²`, relative high-mass attenuation cannot increase R. For the family `r=n²`, `x=n⁹`, and `0<y,z<=1`, that condition holds for every n>=2. The resulting actual two-band HEAT orbit obeys

    0 <= R(0)-R(t) <= R(0) <= 1/n      for every t>=0.

But at t=0, the instantaneous signed heat concentration rate is at least n/128. This is not a contradiction: an arbitrarily large derivative can persist only over an increasingly short effective window when the bounded gap is decreasing. The Lean theorem establishes the net change and monotonicity directly; **it does not assert an explicit uniform duration bound or an integral identity**.

## Why this matters

An instantaneous rate that diverges does not independently guarantee a macroscopic accumulated concentration change. The near-Young gap can tend to zero even as the initial rate diverges. Any physical Navier–Stokes endpoint argument needs an integrated or otherwise time-coherent mechanism, not merely a pointwise high rate.

These models are finite spectral distributions evolving under heat, not realizations of the complete nonlinear Navier–Stokes PDE. No unconditional continuation claim is made.
