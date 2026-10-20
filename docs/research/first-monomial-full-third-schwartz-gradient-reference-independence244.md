# H³ gradient completion: independence of the Schwartz reference family

Base commit: `a40f3e1e` (`derive full 972 gradient gauge vanishing from H3 energy Cauchy`).

## Analytical issue

The previous checkpoint proves that **a** jointly spectral-H³/Schwartz
E₂/E₃-Cauchy family has a limit of its complete 3–3–1 gradient channel.
This is insufficient for a canonical functional unless arbitrary matched
approximants yield the same number.

The two-profile modulus supplies a nonnegative envelope for the difference
of 972 actual spatial triples. For two independent families approximating
the same weighted H³ velocity, existing exact second-/third-jet matching
gives cross E₂/E₃ difference energies tending to zero. The existing
Gagliardo–Nirenberg bridge turns this into mixed L²/L⁴ cross-graph
convergence; in particular every third-jet L² difference tends to zero.

Each family's E₂/E₃ Cauchy property independently supplies global bounds
for all undifferenced third-jet L² roots. Weighted spectral convergence
supplies global bounds for the first-jet spectral states and implies their
pairwise weighted-H³ differences tend to zero. Thus, on every one of the
four triples at every ordered five-index slot, the previous modulus
is bounded by a fixed multiple of

    mixedJetGraph(f_n,g_n) + Σ_j ‖V_n(j) - W_n(j)‖,

which tends to zero. Finite-sum continuity transfers this to the entire
972-term envelope. The complete gradient limits therefore agree.

## Exposed Lean results

- `fullSchwartzGradientSpectralPairEnvelope_cross_tendsto_zero244`: cross-family
  gauge vanishing from energy equivalence, not from an assumed gradient limit.
- `H3MatchedSchwartzGradientCompletion244`: stores the zero/second/third exact
  matching evidence, convergent spectral states, and the gradient limit.
- `h3MatchedSchwartzGradientCompletion_limit_unique244`: gradient reference
  independence for any two records over a common weighted H³ state.
- `exists_h3MatchedSchwartzGradientCompletion244`: constructs the record from
  existing matched density and the automatic gradient-gauge theorem.
- `weightedH3CanonicalGradientTransport244`: canonical completed gradient.
- `weightedH3CanonicalGradientTransport_tendsto244`: any matched family converges
  to that canonical scalar.

## Scope

This proves a choice-independent **completed** gradient functional on weighted
H³ spectral velocities. It does not identify that functional with the
separately defined physical velocity's third-order gradient transport, nor
does it establish fourth-order dissipation approximation or global regularity.
The next proof should identify the completed 3–3–1 integral with the physical
L²×L²×L∞ pairing at a genuine admissible time-slice.
