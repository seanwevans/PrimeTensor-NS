# Fixed radial spectral carrier and terminal complementary mass

**Base:** `15742ba5` (the commit named fixed spectral-coordinate escape).

The base GitHub commit only changed `proof/order.txt` and did not contain the
spectral-coordinate module in the original ZIP. This package includes the
missing coordinate source and its audit registrar as well as the next module.

Write `G(t) = h3AuditActualSpectralVelocityTotal hH3 t` and let

    K(ρ) = 1 + ρ² + ρ⁴ + ρ⁶,
    Lρ(G) = ∫_{|D(ξ)|<ρ} Σ(j=0..2) |G_j(ξ)|² dξ,
    Hρ(G) = Σ(j=0..2) ‖G_j‖² - Lρ(G).

The low-radial mass uses the preexisting weighted spectral difference
functional with zero comparison state. The existing Fourier bound proves

    Lρ(G) ≤ K(ρ) * RawL2SquareDefect(G, 0).

Under a uniform terminal raw Fourier L² square ceiling `E`, the low-radial
mass is bounded by `K(ρ) E` for every fixed ρ. Finite-product selection from
the prior fixed-coordinate theorem gives a **single fixed spectral coordinate**
whose L² norm escapes on every subtail when a positive-mass physical terminal
L² trace is absent. Thus the *algebraic* complementary radial mass `Hρ(G)`
is cofinally unbounded for each fixed ρ. No uniform-in-ρ rate is inferred.

## Open proof obligations

1. Bridge the raw Fourier norm-square ceiling in the main theorem directly to
   the already established physical kinetic energy balance and Plancherel
   identification. This is expected to remove an explicit `hRaw` input.
2. State and prove that `Hρ` equals the genuine integral over `|D(ξ)|≥ρ`
   using integrability, measurable-set complement decomposition, and exact
   energy representation. The present module deliberately calls it a
   *remainder* until that identity is formalized.
3. The result is conditional on absence of strong physical L² terminal
   convergence; it does not follow merely from nonextension in H³.

The new module has no `sorry`, `admit`, or `axiom`. It must still pass the
project's Lean environment and complete build before being considered checked.
