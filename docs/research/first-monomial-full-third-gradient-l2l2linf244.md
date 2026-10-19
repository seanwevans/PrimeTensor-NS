# Real 3–3–1 gradient continuity in the natural 2–2–∞ exponents

Base commit: `1313b9a8` — derive full third Schwartz gradient continuity from jet differences.

The previously proved 2–4–4 gradient channel convergence requires a **third**
derivative factor to converge in L⁴. H³ convergence alone only yields L²
third derivatives. The natural estimate is instead

    |∫ A(x) B(x) C(x) dx| ≤ ‖A‖₂ ‖B‖₂ supₓ |C(x)|.

The new Lean theorem `schwartzTripleIntegral_abs_le_L2L2Linf244` proves this
for real Schwartz functions directly from the project's real L² Hölder
inequality and a pointwise bound. `fullGradientTriple_tendsto_of_L2L2LinfJets244`
uses exact trilinear telescoping, with an L² difference for each third-jet
and a vanishing L∞ gauge for the first jet. It does not presume the integral
limit. The five-axis theorem then transfers this to the complete physical
3–3–1 gradient channel.

The project already has a verified L² root reverse triangle inequality;
that bridges the undifferenced third-jet norm automatically.

**Precise remaining obligation:** prove the first-jet pointwise difference
gauge tends to zero under the physical H³ Sobolev approximation topology,
and identify the Schwartz limit `g` with the actual physical velocity
transport. The required H³-to-W¹,∞ Sobolev embedding is analytically valid
in dimension three, but this package does not formally establish the carrier
and approximation bridge. The signed top cubic remains a conditional
continuation/nonextension criterion, not a solution to Navier–Stokes.
