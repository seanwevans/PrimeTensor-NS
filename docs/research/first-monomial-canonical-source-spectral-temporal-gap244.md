# Canonical projected source: raw Leray bilinear difference and spectral temporal gap

Parent: `a08a3374` (canonical source temporal diffusion/Leray split).

## Exact new Fourier estimate

For actual weighted H³ spectral states `U,V`, the preexisting pointwise bilinearity
and the raw Fourier coordinate estimate imply

`‖L_F(U,U)_i - L_F(V,V)_i‖₂ ≤ (576 π C₃)(‖U‖+‖V‖)‖U−V‖`.

This is an actual `Lp`-class identity, proved using the raw amplitude almost-everywhere
representatives, not merely smooth representatives. It is a coordinatewise Fourier
statement. The bridge to the *physical* inverse-Fourier Leray difference remains
a separate operator-subtraction task; this package does not claim that bridge.

## Canonical physical spectral displacement

The existing physical source bound, already connected to the actual inverse-Fourier
Leray and Laplacian candidates, gives:

If `‖P(s)‖ ≥ 6 A + 4 C_L A² + 1`, then either `‖U₃(t)‖ > A`
or `‖U₃(s) − U₃(t)‖ > A` (A≥0).

The same *preselected* canonical source maximizers in half-terminal windows
and the same finite-dissipation disjoint clock anchors produce, conditional on
noncompression, linear sixth-order control, and critical ninth/eighth width:

* for every fixed threshold M, eventually anchor spectral norm ≥ M OR
  spectral temporal displacement ≥ M;
* bounded anchor spectral norm implies the spectral displacement diverges;
* bounded spectral displacement implies the anchor spectral norm diverges.

No terminal-uniform spectral/source modulus, dissipation contradiction, L² trace
from H³ nonextension, or unconditional regularity is asserted.
