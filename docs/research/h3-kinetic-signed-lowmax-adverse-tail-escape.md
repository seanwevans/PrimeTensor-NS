# Signed sixth-flux adverse excursion forces actual high-H3 tail charge

**Baseline:** `5156e9abd153dc97d097af69cab31b240d67ddeb`.

For a fixed native low-maximum radius `R`, the previous genuine signed complex
flux bound pays three separate charges:

* Schwartz recovery defect `E = ‖V - U(t)‖ + ‖U(s) - W‖`,
* Actual projected physical momentum source clock `S = C_R ∫_[x,y] ‖source(r)‖ dr`,
* The two actual high-H3 tails `H = ‖P_R U(t)‖ + ‖P_R U(s)‖`.

Here the observation times `s,t` lie in the same genuine strict physical gap
`[x,y]`, the coefficient `C_R` is the exact low-band H3 Fourier multiplier
ceiling, and `V,W` are independently chosen Schwartz H3 representatives.

Define the exact signed-flux amplitude coefficient

`A_R(V,W) = 243[2(R+1)]^7 C_0 (1+‖V‖+‖W‖)^3`.

The existing signed flux Lipschitz plus actual PDE gap modulus gives

`|Im Φ_R(v) - Im Φ_R(w)| ≤ A_R(V,W) (E + S + H)`.

**New consequence.** If the real signed imaginary excursion exceeds `η > 0`
and the other two charges satisfy `A_R(V,W) (E+S) ≤ η/2`, then

`η/2 ≤ A_R(V,W)(‖P_R U(t)‖ + ‖P_R U(s)‖)`.

Thus at least one of the TWO actual high-H3 tails must obey

`η/4 ≤ A_R(V,W) ‖P_R U(t)‖` or
`η/4 ≤ A_R(V,W) ‖P_R U(s)‖`.

This is a quantitative, phase-sensitive, physical high-frequency escape
alternative. We neither replace `Im` by a signed scalar ansatz nor assert a
full H3 terminal bound from low-band freezing. The amplitude factor is kept:
small unweighted approximation errors/source action are NOT automatically
small in the cubic weighted cost without amplitude control. The radius is fixed
and its exponent seven is explicit. The result does not close a terminal
Navier--Stokes continuation proof on its own.

**Next hard-math obligation:** derive a joint weighted smallness theorem from
the original kinetic gap witness/recovery sequence, or rule out the tail
alternative using the synchronized endpoint viscous charges. Both require
tracking the actual time and frequency quantifiers and must not be silently
assumed.

Verification is by the repository's Lean build and audit script, not by this
research note or static ZIP inspection.
