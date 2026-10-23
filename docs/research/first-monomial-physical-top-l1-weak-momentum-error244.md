# Physical projected FTC from merely L¹ scalar derivative errors

Base commit: `14420d7b`.

## Analytic strengthening

The previous `IntegrableWeakMomentumError244` required continuous time profiles
for each scalar error and a continuous common majorant. The new interface
requires only interval integrability of the scalar error and the majorant;
the bound holds almost everywhere on the spacetime time slice:

    |e_phi(t)| ≤ g(t) ‖phi‖_L² (for a.e. t in (a,b]).

The scalar pointwise differentiated momentum identity is still required for
all interior physical times, so applying the ordinary FTC is legitimate. The
interval integral inequality, together with the already proved Leray-fixed
compact-solenoidal density theorem, yields

    ‖U(r)-U(a)-∫_a^r R(t)dt‖_L² ≤ ∫_a^r g(t)dt.

If the integrated mass may be made arbitrarily small uniformly over prefixes,
then physical solenoidal weak FTC follows. The old continuous-error criterion
is proved to imply the new L¹ criterion.

## Precise remaining frontier

This does NOT prove that the separated classical preterminal PDE yields a
pointwise derivative of the spatially tested velocity, or an L¹ scalar
residual. The unresolved step is constructing such derivatives by temporal
or distributional testing and canceling the old-versus-canonical pressure
scalar distributions **before** estimating temporal error mass. Product-space
Fubini hypotheses should not be silently inferred from separate time/space
continuity. No unconditional NSE regularity assertion follows.
