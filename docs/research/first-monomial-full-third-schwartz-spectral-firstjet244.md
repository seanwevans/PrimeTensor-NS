# Spectral H³ first-jet control for full third Schwartz gradient transport

Base: `a968d39f` — natural `L² × L² × L∞` signed gradient continuity.

The repository already proves for every scalar weighted H³ spectral state S
and every physical x and derivative axis i:

`|∂ᵢ RealRep(S)(x)| ≤ C₁ ‖S‖_{weighted H³}`.

Apply this to S_n−S. Under an explicit exact identity matching the physical
Schwartz derivative difference with `∂ᵢ RealRep(S_n−S)`, this proves

`|∂ᵢ(f_n−g)(x)| ≤ C₁ ‖S_n−S‖`.

With `‖S_n−S‖ ≤ 1` for all n, we also obtain the uniform envelope

`|∂ᵢ f_n(x)| ≤ C₁(‖S‖+1)`.

Thus spectral H³ norm convergence supplies the vanishing uniform first-jet
gauge δ_n=C₁ ‖S_n−S‖. Combining this with L² convergence of the ordered
third derivative jets and the committed natural-gradient Hölder bound gives
continuity of all twelve complete gradient contributions across the 243
five-axis slots. The PDE-facing theorem transfers the conclusion into the
five-observable closure contract.

## Honest scope

The spectral first-jet comparison is an EXPLICIT matching property of the
Schwartz pullbacks and the chosen H³ spectral states. Its proof from a
canonical physical H³ graph-density construction, plus the physical target
identification and the strong monomial second-jet convergence, are separate
obligations. No unconditional Navier–Stokes continuation is asserted.
