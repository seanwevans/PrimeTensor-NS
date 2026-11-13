# Selected outer H³ carriers: early-time anchored nonlinear slope

Intended local base: `02bb2ea2d` (signed Young-width growth versus physical source-slope payment).

## Mathematical advance

Let `M(t)` be the ORIGINAL physical sharp highpass kinetic mass, `Y(t)` the
ORIGINAL nonlinear annular Young-width cost, `a = (rho² + sigma²)/2`,
`w = (rho²)^3`, `B` the anchored low-band kinetic source ceiling, and `P`
the original outer viscous baseline. The exact physical annular deficit is

`G(t) = w*(a*M(t)-B)^2 - M(t)*(Y(t)+w*P)`.

The previous signed gate used a later-time Young term in the coefficient
multiplying `M(x)-M(s)`. Algebraically re-anchoring the Young term gives

`G(x)-G(s) = (M(x)-M(s))*Q_x(x,s) + M(s)*(Y(s)-Y(x))`, with

`Q_x(x,s) = w*a*(a*(M(x)+M(s))-2*B) - (Y(x)+w*P)`.

**Important:** `Q_x` uses `Y(x)`, *not* `Y(s)`. The previous snapshot Fourier
envelope for `Y(x)` now applies directly; no bound on later-time `Y(s)` is
inserted. The signed positive Young increment is multiplied by the later
mass `M(s)`.

## Genuine physical source control

Unconditional strong physical Hilbert FTC and the actual source majorant give

`|M(s)-M(x)| <= A_x`, where

`H_x = (3+C_L)*((1+6E0(b))*(T-x)+3*integral_x^T D_H3)` and
`A_x = H_x*(2*||U(x)||+H_x)`.

For every `0 <= rho <= sigma <= R`, the original snapshot H3 residual,
physical velocity, low-frequency kinetic source ceiling and outer viscous
baseline give the explicit upper bound

`|Q_x(x,s)| <= C_x(R,A_x)`.

Unlike the older finite-radius lemma, this envelope incorporates the
*actual* physical source-budget mass excursion `A_x` in its kinetic cap
`||U(x)||² + A_x`; there is no artificial `A_x <= 1` restriction.

Consequently, any positive deficit loss `epsilon < G(x)-G(s)` yields

`epsilon/2 < A_x*C_x(R,A_x)` **or**
`epsilon/2 < M(s)*(Y(s)-Y(x))`.

The second alternative, since `M(s) >= 0` and `epsilon > 0`, implies
`Y(s) > Y(x)` — positive growth of the exact nonlinear Young-width cost.

The selected half-tail theorem uses `R = sigma`, eliminating a free radial
ceiling. The cofinal theorem combines the result with the preceding
sixth-power compression gate and establishes `H_(x_k) -> 0` under finite
H3 dissipation. It does **not** show `A_(x_k)*C_(x_k)(sigma_k,A_k) -> 0`.

## Remaining gap

The source budget tends to zero unweighted, but the physical snapshot H3
spectrum and its moving finite-radius envelope can diverge. A continuation
obstruction requires new quantitative PDE structure controlling that product
(or a direct bound on signed Young-width growth). The new theorem does not
assert a Navier–Stokes continuation theorem or a contradiction with finite
H3 dissipation.

## Formal status

All declarations in the new Lean source have tactic proofs and no introduced
axioms or placeholders. **Compilation has not been run** in the pinned Lean
4/mathlib project environment; treat proof status as unverified until the
project's local `lake env lean` and `lake build` commands succeed.
