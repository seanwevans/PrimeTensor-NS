# Sharp critical-half signed balance obstruction

Base commit: `31a01a44` (`prove sharp coefficient-one physical Schwartz H3 interpolation`).

This module applies the **proved** adjacent-energy inequalities for genuine
real Schwartz velocity components: `E1² ≤ E0 E2` and `E2² ≤ E1 E3`.
The resulting cubic interpolation is unconditional. The earlier critical-half
balanced-shape lemma no longer needs free interpolation hypotheses.

For any positive balancing scale `λ` with `λ⁶ E3 = E0 > 0`, a hypothetical
uniform solenoidal critical-half coefficient `C ≥ 0` necessarily satisfies

    M(f)^12 ≤ (2 C)^12 D(f)^12 E0(f)^5 E3(f).

Here `M` is the signed, complete physical 243-slot first monomial, `D` is
the actual fourth-derivative dissipation, and `E0`, `E3` are the genuine
complete end-point H³ quadratic blocks. The factor `2` comes exactly from
the square root of the four-block upper bound `4 E0`, not a dimension loss.

The balanced excess is `M^12 - (2 C)^12 D^12 E0^5 E3`. A solenoidal profile
with positive `E0`, an actual balancing scale, and strictly positive excess
would rule out that coefficient. Importantly, **no assumption on the sign of
`M` is needed**: under `f ↦ -f`, the signed cubic monomial reverses sign
and the degree-36 balanced excess is unchanged. Hence either the witness or
its negative supplies a positive-monomial violation.

These theorems do **not** assert a strict-excess witness or formally prove a finite uniform coefficient in Lean. Standard Sobolev analysis nevertheless guarantees **some finite universal coefficient exists mathematically**, so a strict-excess witness can only refute a particular too-small proposed coefficient. The next hard-mathematics task is a decisive
analysis of the actual signed 243-slot nonlinear monomial relative to these
fixed endpoint masses.
