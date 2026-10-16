# 243-slot 2-4-4 Hölder: exact global energy accounting

Parent: `bf30e0f7` (explicit fourth-power normalization).

The established discrete Hölder inequality and 243-slot multiplicity identities
imply, conditional on the **explicitly stated** real norm identification of
three arrays `a`, `b`, `c` with the actual physical slot masses,

    M(f)^4 <= 16 * n^6 * E3(f)^2 * Q4(f)^2,

where `n = card(Axis Depth.three)`, `Q4` is the 27-slot second-jet quartic
mass, and `E3` is the 81-slot third-jet square mass. The analytic GN theorem
already available in the repository supplies

    Q4(f)^2 <= S^6 * E2(f) * (n*E3(f))^3.

Thus

    M(f)^4 <= 16 * n^9 * S^6 * E2(f) * E3(f)^5.

This is a genuine coefficient/exponent calculation but **not** an unconditional
monomial inequality yet: the physical real Holder weight conversion is
still a separate obligation. `hSlot`, `hThird`, `hMiddle`, and `hCross`
are exactly the visible inputs recording it. They are not new axioms or
assumed automatic from the ENNReal Holder theorem.

The quartic interpolation's E2-E3^3 powers, and the discrete Holder's
E3^2 factor, explain the resulting E3^5 power. This should not be read as
a Navier--Stokes continuation theorem.

Validation: `lake env lean` on the new module, audit Lean check, full `lake build`.
