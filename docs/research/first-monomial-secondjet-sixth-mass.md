# Exact sixth-power Schwartz mass from the 27-slot Sobolev aggregate

**Base:** `26787bdd` (`close 27-slot homogeneous Sobolev against E3`).

For each Euclidean Schwartz field g, Mathlib's finite L6 norm identity gives

    (eLpNorm g 6)^6 = ofReal(∫ g^6).

A finite sum of nonnegative extended masses obeys

    Σ b_p^3 ≤ (Σ b_p)^3.

Applying this to all 27 ordered second-derivative Schwartz jets, without
commuting derivative operators, yields

    ofReal(Σ_27 ∫ (D²f)^6) ≤ (Σ_27 (eLpNorm (D²f) 6)^2)^3
                              ≤ (S² * ofReal(card(Axis.three) * E3(f)))^3.

Here S is the established physical homogeneous Sobolev constant. The
`card(Axis.three)` factor (three) comes from the Point3 sup norm.

This completes the sixth-mass input for the *already proved* coefficient-one
27-slot fourth-power interpolation; combining the two into a real-valued
quartic Gagliardo–Nirenberg bound is the next task. There is no PDE conclusion.
