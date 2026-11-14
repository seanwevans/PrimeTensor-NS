# Cutoff-uniform frozen diffusion commutator — `fc128140c`

The actual time-dependent physical Laplacian is `L(t)`, the frozen left state is
`L(x)`, and `Q_ρ` is the sharp physical highpass.

For every contractive real continuous linear map `Q` on the physical Hilbert
space, and every ordered positive-time subinterval `[x,s]`, one has the exact
Bochner identity

`Q(∫ L) − (s−x)Q(L(x)) = Q(∫ (L(t)−L(x)) dt)`.

Thus if `‖L(t)−L(x)‖ ≤ η` throughout the interval,

`‖Q(∫ L) − (s−x)Q(L(x))‖ ≤ (s−x)η`.

The **same time radius** works for all contractive `Q`; there is no growing
frequency constant in this estimate. The physical transfer theorem includes
an explicit **continuous-linear identification certificate** matching a
chosen `Q` with the actual physical sharp highpass. Contractivity is already
established in the repository, but the real-linear CLM realization is not
established by this patch. Neither the identifying certificate nor the
source oscillation should be mistaken for a new Navier–Stokes assumption.

The exact frozen-viscous/Leray energy ledger then gives

`ε − K[2τ d_ρ + 2‖H‖ τ η] + K(‖A‖²+‖B‖²) < 2K⟨H+A,B⟩`.

All terms are actual physical L² terms in the physical theorem. Both
quadratic costs are retained, and the frozen diffusion work is already known
nonnegative. The next step is to construct the real-linear sharp-cutoff CLM
from the established Fourier/physical Plancherel isometry, and to use
positive-time H³ continuity to provide `η → 0` on fixed interior windows.

**Critical limitation:** Interior continuity gives no uniform modulus as
`x ↑ T`; that terminal-uniform estimate remains open. No H³ continuation
claim is made here.

The file also proves actual physical Laplacian `ContinuousAt`, and then a
fixed-positive-time uniform-in-cutoff `δ` theorem, conditional on the
real-linear sharp-highpass CLM certificate.
