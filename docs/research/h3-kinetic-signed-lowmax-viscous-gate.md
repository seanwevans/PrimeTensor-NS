# Native signed sixth-flux: actual H3 viscous gate

Baseline: `6869f59ed9fb47b21bd4fb3b43ed64a0f30f8c2b`, which has
already proved that an adverse imaginary signed LowMax(R) sixth flux
increment forces at least one of the genuine physical observation-time
weighted H3 high-radial tails to pay `η/4` after removing the recovery and
projected-source L1 charges, with exact coefficient
`A=243[2(R+1)]⁷C₀(1+‖V‖+‖W‖)³`.

## New physical computation

The preexisting physical fourth-derivative H3 dissipation coercivity is
`(R+1)²‖P_R U(t)‖² ≤ D₃(t)` at each original strict H3 energy-class time.
Multiplying the positive tail bound by itself and applying this coercivity
gives, at the SAME physical time,

`(R+1)²(η/4)² ≤ A²D₃(t)` or
`(R+1)²(η/4)² ≤ A²D₃(s)`.

No new physical time is chosen and no high-radial L² norm is equated to the
sum-of-component Fourier square energy: the existing exact norm comparison
and physical coercivity supply that step.

### Unconditional alternative

For any positive adverse signed flux excursion `η`, independently of whether
recoveries or source clocks are small, the new theorem states

- `η/2 < A [‖V-U(t)‖ + C_R∫_[x,y]‖source‖ + ‖U(s)-W‖]`, **or**
- `((R+1)η/4)² ≤ A²D₃(t)` **or** the same inequality with `D₃(s)`.

If the first cost is at most η/2, a second theorem combines the two
alternatives into an endpoint *sum* charge:

`((R+1)η/4)² ≤ A²[D₃(t)+D₃(s)]`.

The time endpoints `s,t` are literally the adverse Schwartz recovery
observation times in the same physical gap. Each lies in the genuine H3
energy-class interval `(a,T)`. The full dissipation need not be uniformly
bounded or continuous through the terminal horizon.

## Next unresolved mathematical obligation

A pointwise spike is NOT an integrated viscous cost. Establishing a common
positive persistence width, at the **same** observation times and cutoff,
would require a proven physical PDE/time regularity estimate. The previously
synchronized endpoint viscous charges cannot be used to eliminate the spike
without this extra argument. For cofinal moving cutoffs, the factor `A_R`
also grows as `(R+1)^7` and must remain in all estimates.

## Verification

The registrar registers both public theorems with `#check` and `#print axioms`.
Run `proof/generate_index.py` before targeted Lean and full project build.
Source/ZIP checks here are not Lean kernel elaboration.
