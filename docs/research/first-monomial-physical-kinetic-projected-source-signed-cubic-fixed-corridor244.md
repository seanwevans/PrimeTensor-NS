# Fixed cofinal H³ signed-cubic corridor from the physical kinetic-trace alternative

**Base:** `644c6804` — isolate high H3 energy or sign-definite canonical cubic barrier.

## Input and logical scope

Let `u` be a `LoggedPreterminalH3PathAdmissible` velocity with
`PreterminalH3EnergyClass u a T`, positive canonical terminal kinetic energy,
and no strong physical kinetic `L²` endpoint trace. The last hypothesis is
independent of hypothetical H³ nonextension; no implication between them
is assumed.

The physical signed balance supplies a *fixed cofinal channel*:
for arbitrary preterminal `b` and rate `B`, either the physical H³ energy
slope is below `-B E` arbitrarily close to `T`, or the full signed physical
transport is above `B E` in the adverse orientation. The selected branch is
fixed before choosing `b` or `B`.

In the second case, the actual Fourier/physical third-order identity gives

    B <= 48*C1*sqrt(E)
      OR 4*G3(S(t)) < -B*E
      OR 12*M3(S(t)) < -B*E,

where `S(t)=h3PathWeightedSpectralState244 u T hH3 t` is the genuine
physical H³ spectral state, `G3` is the 972-term gradient commutator, and
`M3` is the signed 243-slot interpolation monomial. No pointwise sign
assumption on either spectral term is made.

## New selection and quantitative witness

The three predicates are antitone in the requested real threshold:
`B <= K sqrt(E)` directly, and the signed predicates because `E >= 1`.
The already-proved binary cofinal-selection theorem applies twice, yielding
one fixed cofinal member. A diagonalization in each of the resulting four
possible physical channels selects one sequence `t_n` satisfying

    a < t_n < T,  |t_n-T| < 1/(n+1),  t_n -> T,

and **one** of the following conditions for every `n`:

1. `(n+1)*E(t_n) < -E'(t_n)`;
2. `(n+1)^2 <= (48*C1)^2 * E(t_n)`;
3. `4*G3(S(t_n)) < -(n+1)*E(t_n)`;
4. `12*M3(S(t_n)) < -(n+1)*E(t_n)`.

The index of the channel is fixed *outside* all `n` quantifiers.
The second alternative implies quadratic divergence of full physical H³
energy along the selected sequence; the last two imply a genuinely
negative signed canonical cubic constituent normalized by actual H³ energy.

## Unresolved analytic gap

The new sequence is *not* asserted to be the earlier moving-radial
high-frequency mass / dissipation sequence. The proof constructs a new
terminal witness from cofinality, rather than extracting a subsequence
of the existing radial witness. Hence it does not, by itself, give a
simultaneous high-frequency concentration + fixed signed cubic witness.
To close the no-kinetic-trace branch one must constrain **all** surviving
fixed corridors, or establish extra compatibility that couples the genuine
PDE transport channel to radial dissipation on the same times.
