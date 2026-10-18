# Full-third Hermitian axis packet: exact inverse Fourier realization

**Base:** `aef7db15` — construct full third Hermitian solenoidal axis Schwartz packet.

The committed six-window packet is a vector-valued Schwartz map on the physical
frequency-coordinate carrier `Axis Depth.three → ℝ`.  The existing full
third-order energy and Fourier identity operate instead on the Euclidean
Hilbert space `H3FourierPoint3` (`EuclideanSpace ℝ (Axis Depth.three)`).
This module transports the packet's coordinate Schwartz functions along the
canonical `PiLp.continuousLinearEquiv` and uses mathlib's exact inverse Fourier
transform on the Hilbert carrier.

Its recovery theorem identifies the Fourier transform of each resulting
**complex spatial Schwartz component** exactly with the original six-packet
component evaluated at `WithLp.ofLp ξ`. The assembled vector therefore
retains exact Fourier divergence zero and exact Hermitian conjugate reflection.
Neither statement assumes a distributional approximation, freezes the moving
projection germ, or discards the seventh-order Fourier phase.

## Theorems

- `thirdFullAxisSixFourierComponent_apply244`
- `thirdFullAxisHilbertFourierComponent_apply244`
- `thirdFullAxisInverseSchwartz_fourier_component244`
- `thirdFullAxisInverseSchwartz_fourier_vector244`
- `thirdFullAxisInverseSchwartz_fourier_divergence244`
- `thirdFullAxisInverseSchwartz_fourier_hermitian244`

## Unresolved analytical obligations

The inverse Fourier field is currently complex-valued. Prove spatial realness
from the Hermitian spectral symmetry, then build a real scalar Schwartz family
with this Fourier transform. After that, identify the *complete* signed
third-order physical Fourier integral with the actual packet's 12 coherent
sectors (including the Fourier measure normalizations and changes of variables).
The previously proved negative local integral for one labeled sector alone
does not imply global noncancellation, much less Navier–Stokes regularity.

## CI

Run the included module registration, `python3 proof/generate_index.py`,
`python3 proof/generate_index.py --check`, `python3 proof/check_fragment.py --all`,
compile the new module and audit, and run `lake build`. Commit `proof/order.txt`.
The patch preparation environment does not have Lean/mathlib to validate these
statements; the local Lean compile is a required gate.
