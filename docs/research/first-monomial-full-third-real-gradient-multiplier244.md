# Full-third actual physical gradient Fourier multiplier on the coherent tube

Base checkpoint: `0ca62dbf` — localize full third real Schwartz trilinear Fourier integrals to coherent tube.

This proof increment uses the real, divergence-free Schwartz field from `b36aa55f`
(and its exact Fourier recovery and 12-center support geometry) and the exact
seven-directional-derivative gradient Fourier identity already in the repo.

For an arbitrary 3+3+1 slot with Schwartz components `j,m,n` and seven genuine
Euclidean directions `a,b,c,d,e,k,v`, it identifies the *actual* Fourier kernel
with the product of its seven frequency inner products and the three Fourier
amplitudes of the constructed REAL velocity. The dependent middle momentum
is `q = -(p+r)`, transported exactly through `WithLp`.

It then proves this physical 3+3+1 kernel vanishes outside any chosen coherent
twelve-center tube if its window radius is small enough, and proves the equality
of the entire absolutely convergent Hilbert-space integral with its indicator
restriction to that tube. The packet width can be selected uniformly for all
component and derivative slots.

## Remaining work and scope

This is an actual gradient SLOT identification, not merely an abstract cubic
multiplier. It has not yet assembled all four physical gradient patterns and all
five axis index sums, nor the separate 3+2+2 interpolation channel. The full
`fullThirdSchwartzFourierCoefficient244` is thus **not yet** proved to equal a
signed integral over 12 coherent sectors. Even after that identification, a
strict global sign requires checking the exact phase and noncancellation of the
total integral; the local `-192` coefficient is insufficient by itself.

No Navier--Stokes continuation or global regularity assertion is made.

## Build

Run the included registration script, `proof/generate_index.py` and `--check`,
`proof/check_fragment.py --all`, individual Lean compilation, theorem audit and
full `lake build`. This ZIP is statically checked but not Lean-compiled in the
artifact environment.
