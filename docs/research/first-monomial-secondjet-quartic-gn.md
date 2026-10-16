# Genuine 27-slot quartic Gagliardo–Nirenberg inequality

**Base:** `2a7b3943`, `bound 27-slot sixth Schwartz mass by Sobolev E3`.

Combine two actual Schwartz-space theorems:

- The 27-jet coefficient-one real interpolation `(Σ∫ (D²f)^4)^2 ≤ E2 * Σ∫ (D²f)^6`.
- The proved sixth-mass Sobolev estimate `ofReal(Σ∫ (D²f)^6) ≤ (S² * ofReal(card(Axis three) * E3))³`.

The new module proves their unconditional composition in `ENNReal`, then converts back to a finite real Sobolev coefficient (`S`) and proves the full real quartic GN estimate:

    (Σ_27 ∫ (D²f)^4)^2 ≤ S^6 * E2(f) * (card(Axis three) * E3(f))^3.

The only three-dimensional loss is from the physical `Point3` sup norm, not finite-family aggregation. The normalized coefficient is `card(Axis.three)^3 * S^6`, numerically `27 * S^6`.

No new PDE hypotheses, no mixed-partial commutation, and no division by a zero mass. Lean compilation must be checked in the target repository.
