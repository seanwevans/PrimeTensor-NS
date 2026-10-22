# Physical inverse-Bessel reduction of the raw Fourier L¹ terminal obstruction

Base: `bd399d67` (kinetic Fourier-L² branch excluded).

Existing `integral_h3RawFourier_natMoment_le_bessel_mul_norms` at p=0 proves
`L1(F) ≤ C_B (‖F_raw‖₂ + ‖|ξ|² F_raw‖₂)`. Its genuine scalar spectral-state
specialization uses the canonical raw Fourier L² state and any actual order-two
Fourier L² representative, with an a.e. representative equality.

Existing physical kinetic monotonicity gives `‖F_raw(t)‖₂ ≤ √E0(s)` for
s ≤ t < T. Therefore

    raw_L1(U_j(t)) ≤ C_B [√E0(s) + ‖|ξ|² û_j(t)‖₂].

With an explicit strict-tail norm ceiling B for every physical second-radial
Fourier state, the resulting L¹ ceiling closes the final lower-order input
branch in the previously formalized six-factor Young escape alternative:

    top D3 escape + eighth-moment integrability + second-radial L² ceiling
      => cofinal raw eighth-order velocity-moment escape.

The norm ceiling is not inferred from kinetic energy alone. A follow-up
should identify the second-radial Fourier representative with the physical
order-two energy block (which the repo already identifies spectrally), and
then analyze whether that block has a terminal-uniform bound or is an
independent lower-order growth obstruction. Nothing here excludes the
Navier–Stokes terminal escape or asserts an unconditional regularity result.
