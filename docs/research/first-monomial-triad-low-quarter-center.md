# Concrete sharp-center recovery on a Schwartz Fourier field

Checkpoint: `b3ddfcad` (complete vector-valued Schwartz six-packet field).

The exact center separation is established for the concrete parameter t=1/4.
At this parameter the separation radius equals 1/16, and the six integer-lattice
centers lie outside one another's radius-1/16 frequency balls. Since each
cutoff equals one at its own center, its six-by-six matrix of center values
is the Kronecker delta.

The positive packet sum therefore equals the prescribed A, B, C polarizations
at p, q, r respectively. The reflected packet contributions vanish at these
three positive centers. As a result the actual Hermitian, divergence-free
vector-valued Schwartz Fourier field reproduces the exact sharp six-order
symbol, with its nonzero imaginary coefficient.

This is an important nonvacuity result for the concrete Schwartz field, but
it is **not yet an integrated noncancellation theorem**. A pointwise nonzero
symbol implies only a local sign under continuity. Passing to the full
integrated first-monomial pairing requires accounting for all resonant
frequency sectors, their phases, the positivity of packet weights, and
Lebesgue integration. In particular, this module makes no conclusion about
Navier-Stokes continuation or singularities.
