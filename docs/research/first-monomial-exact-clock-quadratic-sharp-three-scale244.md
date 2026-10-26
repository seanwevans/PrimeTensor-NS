# Quadratically sharp physical cubic PDE clocks: three-scale obstruction

Baseline: `73b3e7c6` (`master`).

## Why a new exact clock is necessary

The preceding selector `min(b/2, 1, gap/(2*(Λ+Ξ+1)))` overestimated the
quadratic temporal variation `Ξ*δ²` by `Ξ*δ`, using `δ<=1`. The resulting
sixth-order total-rate obstruction does not distinguish a genuine quadratic
rate spike from a linear one.

The existing physical anchored finite-annulus variation theorem proves
`|B(t+h)-B(t)| <= Λ*h + Ξ*h²`. We now use the exact selector

`δ = min(b/2, 1, gap/(4*(Λ+1)), sqrt(gap/(4*(Ξ+1))))`.

When `b,gap>0` and `Λ,Ξ>=0`, this selector satisfies `δ>0`, `δ<b`,
`δ<=1`, and `Λ*δ+Ξ*δ² < gap` with ample slack. The proof retains the
actual selected annulus radius `N`, source ceiling `C`, starting state
ceiling `K`, and strict quarter-cubic annulus gap `gap > R³/4`.

## Distinct sixth and ninth powers

On a cofinal disjoint sequence `v`, assume *additional* terminal H³
integrability. Its finite total physical dissipation bounds the sum of
`δ(v(k))*R_k³/2`, hence `δ(v(k))*R_k³ -> 0` for `R_k=v(k)+1`.
The three exact caps and `R_k³/4 <= gap_k` then give, for every `ε>0`,
eventually:

- geometric: `R_k³*(T-τ_k)/4 <= ε`, or
- linear: `R_k^6 <= 16*ε*(Λ_k+1)`, or
- quadratic: `R_k^9 <= 16*ε²*(Ξ_k+1)`.

The ninth-order exponent comes from squaring the separate quadratic
square-root cap, not from a new PDE bound. The physical theorem uses
fresh quadratically sharp selected windows and never assumes these are
identical to the old linearly normalized windows.

## Limits of the theorem

The three-scale statement is conditional on the no-terminal-L²-trace
branch, positive terminal kinetic mass, and finite full H³ terminal
dissipation. It neither excludes geometric compression nor bounds
source or cutoff amplification; it is not a proof of global regularity.

## Validation

This patch is source-only and has not been compiled with Lean in the
packaging environment. Run the module and full Lean build, regenerate
`proof/order.txt` using `proof/generate_index.py`, check the index,
and compile the audit. No `.sh` is distributed.
