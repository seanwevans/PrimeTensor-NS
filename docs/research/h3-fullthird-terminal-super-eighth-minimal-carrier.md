# Physical kinetic eighth-power barrier at the minimal terminal H³ carrier

Baseline commit: `c51bf1326976247edc8eeb6c088fb2c53969f0c2`.

## Exact physical bound

Let `hH3` be the actual logged physical H³ path and `hClass` its energy
class, with a fixed strict-time anchor `b` and a later snapshot `t`. At the
least outer integer `N ≥ n` whose annular viscous dissipation exceeds `A/2`,

    A/2 < D_low(N+1, G(t)) - D_low(n+1, G(t))
        ≤ 4 (N+2)^8 RawMass_[n+1,N+1](G(t))
        ≤ 4 (N+2)^8 E₀(b).

Therefore `A < 8 (N+2)^8 E₀(b)`. The middle bound is the proved physical
weighted H³ dissipation-to-raw kinetic mass comparison. The final bound
uses the Plancherel bridge and antitonicity of the *order-zero* kinetic
energy on the physical tail. No H³ pointwise ceiling or endpoint trace is
assumed.

## Quantitative super-eighth escape

Let `M(n)>0` be any prescribed profile such that

    M(n) / (n+1)^8 -> +∞.

For each fixed physical kinetic anchor `b`, the same minimal first-crossing
annuli from the preceding committed theorem satisfy, eventually,

    M(v(k)) < 8 (N(v(k))+2)^8 E₀(b).

Since `v` is strictly increasing, the profile hypothesis transfers to the
selected subsequence. Consequently

    (N(v(k))+2) / (v(k)+1) -> +∞.

Thus the minimal carrier itself must escape at a superlinear relative
frequency scale. It is not an artifact of selecting an overly large outer
cutoff.

## Same physical witnesses

The resulting theorem reuses the exact `τ,N,K,C,δ,v` witnesses selected in
`thirdFullPhysical_noH3Trace_minimalCarrier_sourceClock_or_physicalRates244`:

- pairwise-disjoint cofinal physical times;
- the minimal first annular crossing;
- the attained compact-time projected-source norm envelope;
- the exact anchored PDE persistence width and summable real viscous costs;
- the same terminal-clock versus physical quintic/eighth-power alternatives;
- the same physical source observation versus spectral amplification branch.

**Logical limitation:** The profile `M` is chosen before selecting the
terminal witnesses. The conclusion is a conditional *necessary frequency
escape*, not a contradiction or a proof of global Navier–Stokes regularity.
The mass in an individual last shell remains only strictly positive; no
uniform shell-mass lower bound has been assumed or proved. In particular,
this does not yet exclude either terminal-clock compression or a physical
source/transport concentration.

## Further hard-math target

Control the high-frequency flux of the *attained physical source* into the
minimal carrier, rather than bounding the source by its norm alone. Relate
the carrier's order-zero mass and its time-dependent transport to a signed,
integrated PDE budget. This is where a nontrivial exclusion of arbitrary
frequency escape would need additional cancellation or coercivity.

## Lean elaboration repair (fix 1)

The scalar kinetic-cost proof now rewrites the product algebraically instead of using `convert` with an unnecessary sequence-focus combinator. In the endpoint corollary, the profile limit is explicitly changed to its composed function form, and the outer-radius limit is transported through a pointwise equality `Q + 1 = N + 2`. The theorems and assumptions are unchanged.
