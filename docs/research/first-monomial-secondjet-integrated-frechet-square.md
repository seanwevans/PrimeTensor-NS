# Integrated second-jet Frechet-coordinate-square inequality

Base: `1697226d`.

For a physical C¹ scalar g with L² gradient and coordinates, integration of the previously proved pointwise estimate yields

    ∫ ‖Dg‖² ≤ card(Axis Depth.three) · Σₐ ∫ (∂ₐg)².

Every genuine second-derivative Schwartz jet meets these hypotheses after an explicit volume-preserving pullback to Point3. Consequently

    ∫ ‖D(∂ᵢ∂ₖfⱼ)‖² ≤ card(Axis Depth.three) · Σₐ ∫ (∂ₐ∂ᵢ∂ₖfⱼ)².

The sup-norm carrier gives card = 3, not 1. The full 27-slot summation/reindexing into E3 and the sixth-power GN estimate are separate steps.

No new axioms or `sorry`; local Lean compilation required.
