# Signed LowMax flux: backward physical annular charge on the same kinetic gap

**Base:** `30f84322d630764ab91fa02b6a91cca00186940f` — exact in-gap
annular charging for strict-interior snapshots, plus a genuine right-endpoint
case for closed-gap samples.

## Resolving the terminal side of the selected gap

Let `[x,y]` be an ORIGINAL strict physical kinetic gap and suppose the adverse
signed sixth-flux observation selected for the viscous branch is **exactly**
`z=y`. The previous forward certified annular PDE window rooted at `y` is not
inside `[x,y]` and cannot be charged to that gap. Changing the signed-flux
observation time without preserving the adverse signed margin would be invalid.

Use the certified window only to select the SAME finite natural outer cutoff
`N >= R` for which the actual annular H3 dissipation at `y` exceeds `H/2`.
The existing theorem
`thirdFullPhysical_kineticNaturalAnnularDissipationLipschitz244` gives, for
all `r in [x,y]`,

`|Ann_N,R(r) - Ann_N,R(y)| <= Lambda*(y-r)`, where

`Lambda = L_N(E0(b)) + L_R(E0(b)) >= 0`.

Here each `L_Q(E0(b))` is the exact previously verified *kinetic-only* finite
band dissipation Lipschitz coefficient; `b` is an earlier real physical energy
anchor and `x,y in (b,T)`. No full-H3 time derivative or terminal-uniform source
ceiling is introduced.

Choose the **explicit backward PDE width**

`epsilon = min((y-x)/2, H/(8*(Lambda+1))) > 0`.

It satisfies `x < y-epsilon < y` and `Lambda*epsilon <= H/8`, hence

`Ann_N,R(r) > H/4` for all `r in [y-epsilon,y]`.

Applying the previously verified finite-annulus continuity/integrability and
physical dissipation domination yields

`epsilon*(H/4) <= integral_(y-epsilon)^y Ann_N,R(r) dr
                 <= integral_x^y D3(r) dr`.

The final bound uses **explicit** interval integrability of the actual full
H3 dissipation. It is not inferred from a pointwise viscous spike.

## Closed-gap signed-flux alternative

Combine this backward result with the previously proved forward in-gap result
when `z<y`. The selected adverse time is still `z=s` or `z=t` in the same
original closed gap. Thus either the genuine amplitude-weighted recovery/PDE
clock exceeds `eta/2`, or there is a positive certified width `epsilon` charged
on a subinterval of the SAME original kinetic gap with

`epsilon * [H_R(V,W,eta)/4] <= integral_x^y D3(r) dr`,

where the previously proved exact height

`H_R = ((R+1)^2*(eta/4)^2)/(2*(A_R(V,W)^2+1))`.

For `z<y`, the forward interval is truncated before `y`; for `z=y`, the newly
proved backward interval starts strictly after `x`. There is no longer an
unresolved right-endpoint alternative on the kinetic-anchored, finite
full-dissipation branch.

## Cofinal obstruction, kept quantitative

Along a cofinal separated family of original gaps with vanishing full viscous
integrals `D_k`, any compatible nonnegative widths and heights with

`epsilon_k * H_k/4 <= D_k`

obey `epsilon_k * H_k/4 -> 0`. This conclusion does **not** imply that widths
alone vanish if the height can decay (and `A_R` contains a growing seventh
power of the cutoff and cubic Schwartz amplitude). Nor does it prove a
contradiction to finite dissipation without an independent noncompression
lower bound or quantitative adverse-flux margin.

## Verification

The registrar checks five public declarations (one definition, four theorems)
without placeholders and writes the global imports and audit checks. Regenerate
`proof/generate_index.py` before compiling and use the project-pinned Lean
build. The static archive checks do not constitute Lean elaboration.
