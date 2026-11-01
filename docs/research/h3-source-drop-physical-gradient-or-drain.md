# Source-driven highpass collapse forces actual velocity gradients or energy drain

Base `c722fb2b`, signed H³ physical endpoint-rate source-drop obstruction.

## PDE-based two-endpoint physical alternative

The committed theorem yields, for two strict physical times `t ≤ s` and a
highpass Fourier source peak with nonnegative margin `P` over the kinetic
barrier, a source-drop signed-rate alternative if

    A² [3 R² W₃(R) (C(s-t))² + 2K] < R² P².

Here `A = 3+C_L(‖U(t)‖+‖U(s)‖)` and `C` bounds the ACTUAL projected momentum
source on `[t,s]`. If high-radial dissipation falls to `M` at time `s`, then
at `t` or `s` either

    E'(r) < -K/2   OR   Transport(r) < -K/2.

The exact physical H³ Landau commutator is available for every actual
spatial-gradient cap at a single strict time. Splice a hypothetical
constant cap `H≥0` at just that time into the established canonical gradient
envelope at all other times, then the already-closed PDE estimates yield

    -Transport(r) ≤ 4422 (1+H) E(r).

This gives a genuine first-spatial-derivative conclusion: if the two endpoint
physical H³ energies are both at most `Emax` and

    4422 (1+H) Emax ≤ K/2,

then a source drop meeting the strict gap inequality forces one of:

- `E'(t) < -K/2` or `E'(s) < -K/2`, or
- some real velocity coordinate gradient at `t` or `s` is strictly greater
  than `H` in absolute value.

The last theorem states the equivalent persistence obstruction: endpoint H³
energy-slope lower bounds, genuine pointwise spatial-gradient caps, endpoint
H³ energy ceilings and a strict source margin together preclude a dissipation
drop. Nothing is asserted about the interior gradient of `[t,s]`.

This strengthens the earlier *signed-transport* branch to a **physical spatial
derivative spike**, not just an increase in a chosen abstract gradient
envelope or an unspecified spectral norm. It does not prove a uniform
terminal spectral envelope or global regularity. The source-gap hypothesis
and endpoint H³ ceilings must still be established on moving terminal clocks.

## Lean declarations

- `h3Critical_oneTimeGradientEnvelope_negTransport_le`
- `h3Critical_adverseTransport_forces_actualGradientAbove`
- `h3Critical_sourceDrop_endpointEnergyDrain_or_actualGradientSpike`
- `h3Critical_sourceDrop_gradientAndSlopeCaps_preclude_drop`

The ZIP was statically verified; actual Lean compilation is only available in
the pinned user toolchain.
