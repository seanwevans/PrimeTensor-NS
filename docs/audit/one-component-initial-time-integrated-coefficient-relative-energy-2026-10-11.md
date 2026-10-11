# Initial time-integrated coefficient relative-energy criterion

Base: `94d77e37` — derive initial uniqueness with variable time coefficients.

The previous theorem controls `κ(t) ∫₀ᵗ e(s) ds`, while weak-energy
calculations ordinarily produce the source integral `∫₀ᵗ κ(s)e(s) ds`.
For each epsilon-approximant, the new criterion assumes:

- the nonnegative scalar old/selected energy is integrable and positive-time continuous;
- `κ(s) ≤ K` throughout `[0,b]`, with `κ e` integrable on `[0,b]`;
- `|R|` is integrable with mass at most epsilon;
- the integrated comparison inequality is available only on `(0,b]`.

Interval-integral monotonicity bounds `∫ κe ≤ K∫e`. Existing
positive-time residual theorems then derive the initial zero scalar trace,
full comparison uniqueness, the canonical compact weak-test overlap, initial
L² trace and H³ upper trace. The full-time two-component conclusion still
requires the separately postulated strong-H³ terminal actual vorticity path.

**Not proved:** The comparison inequality, coefficient bound/product
integrability, and epsilon-small residuals from the actual old Navier--Stokes
weak formulation. The new module adds no axioms or sorry placeholders.
