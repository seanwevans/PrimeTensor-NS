# Kinetic control and the normalized quartic coefficient

Based on `c204a1e9`. Implementation:
`PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/KineticQuartic.lean`.

The previous criterion retained the entire normalized remainder R/E.
The closed orderwise energy derivative identities already prove that E₀ is
nonincreasing on an energy-class tail (a,T). Fixing b in (a,T) therefore
gives E₀(t) ≤ E₀(b) for b < t < T without another analytic assumption.

For B ≥ 1 and ε = 2,

    R = B + (3B + (81/8) B⁴) E₀
      ≤ (1 + (105/8) E₀(b)) B⁴.

Here B ≤ B⁴, and 3B + (81/8)B⁴ ≤ 14B⁴. The coefficient 105/8 is a
convenient upper bound, not an optimized constant. The exact PDE balance
and positivity of E give

    E′ ≤ [(1 + (105/8) E₀(b)) B⁴/E] E.

Consequently integrability of B⁴/E on (b,T) supplies continuation whenever
|T_H3| ≤ B E. A final theorem uses B = 4422(1 + |h|) from the closed
gradient-envelope estimate. There is no extra kinetic-bound hypothesis.

The remaining assumption is still temporal: integrability of B⁴/E.
For the coarse coefficient proportional to sqrt(E), this requires control
of a quantity growing like E. The kinetic identity alone does not provide
that control. No unconditional regularity result, improved Fourier estimate,
or strict comparison with all earlier continuation criteria is claimed.

The new results are included in the root imports and selected contract/axiom
audit. Packaging checks source coverage, generated index, compatibility
paths, and whitespace. Lean compilation must run via the local baseline;
Lean is unavailable in the packaging environment.

## Direct versus absorbed growth

The follow-up based on `6aafe8d0` stays in the same Lean module. Both the
exact balance and the anchored absorption theorem apply at every strict
subtail time. With C = 1 + (105/8) E₀(b), they yield

    E′ ≤ min(B, C B⁴/E) E.

For B > 0 and E > 0, the absorbed coefficient is strictly smaller than B
if and only if C B³ < E. This scalar equivalence is proved separately.
Thus the minimum never worsens the direct pointwise coefficient. It allows
the choice of estimate to vary in time without choosing a single branch
for the entire tail. The continuation theorem assumes integrability of
this minimum; it does not separately assume integrability of either branch.
A specialization supplies B from the closed gradient-envelope estimate.

This combines existing estimates and identifies their exact comparison
threshold. It does not prove the required time-integrability bound, nor
establish that this condition is strictly weaker on actual PDE solutions.
In particular the coarse B proportional to sqrt(E) is not improved at
large E by the quartic branch. A sharper analytic input remains necessary.

## Nonextension obstruction

The adaptive theorem has the matching contrapositive. If no
`SmoothContinuationExtension` exists, then on every strict anchored subtail
the coefficient

    min(B, (1 + (105/8) E₀(b)) B⁴/E)

is nonintegrable, provided the transport bound and B ≥ 1 hold there. This is
a neutral obstruction statement: it does not select the direct or absorbed
branch and does not assert that either branch diverges separately.

## Exact remainder branch

The latest refinement keeps the exact anchored remainder

    B + (3B + (81/8)B⁴) E₀(b)

before replacing it by `(1 + (105/8) E₀(b)) B⁴`. A second adaptive criterion
uses the minimum of B and this exact remainder divided by E. It is therefore
pointwise at least as sharp as the coefficient bound. The previous coarse
criterion remains available for estimates stated only in terms of B⁴/E.

The exact-coefficient continuation theorem has the matching contrapositive:
under nonextension, its minimum coefficient is nonintegrable on every strict
anchored subtail. This preserves the sharper lower-order dependence in the
obstruction statement.

The exact branch also has a scalar activation threshold. For B>0 and E>0,
its coefficient is strictly below direct B exactly when

    1 + (3 + (81/8) B³) E₀(b) < E.

This threshold is stated independently of the PDE path and can be used to
identify the absorbed region without replacing the exact coefficient by the
coarser `(105/8)` bound.

The exact coefficient is formally bounded by the simplified coefficient
`((1 + (105/8) E₀(b)) B⁴)/E` whenever B≥1, E₀(b)≥0, and E>0. Thus the
exact adaptive criterion is pointwise at least as strong as the sharpened
coarse criterion.

The exact adaptive continuation theorem is now specialized to
`B(t)=4422(1+|h(t)|)` under the existing closed `VelocityGradientEnvelope`
hypothesis. Its only new temporal premise is integrability of the exact
minimum coefficient on the anchored tail.

The gradient specialization also has its exact contrapositive: under
nonextension, the exact minimum coefficient built from `4422(1+|h|)` is
nonintegrable on every strict anchored subtail.

Finally, for any B and `0 < ε ≤ 2`, the exact remainder at ε=2 is
no larger than the remainder at ε. Thus the fixed full absorption budget used
above is optimal within this one-parameter family for the remainder bound.

The exact branch is packaged as a neutral dichotomy on each anchored tail:
either a `SmoothContinuationExtension` exists, or the exact adaptive minimum
coefficient is nonintegrable. The gradient-envelope specialization supplies
this alternative directly from the closed PDE transport estimate.

The gradient dichotomy now has a universal strict-subtail form: either one
continuation extension exists, or the exact adaptive coefficient is
nonintegrable on every later tail inside the energy-class interval.

The exact normalized coefficient is monotone in the anchored kinetic ceiling
M. Combined with the closed antitone `E₀` estimate, moving the anchor later
can only lower the exact coefficient on the remaining tail.

The scalar monotonicity now lifts to anchors: if `b < c < t` on the energy
class tail, the coefficient anchored at c is no larger than the coefficient
anchored at b. This follows from the closed antitone kinetic-energy identity.

The scalar exact adaptive dichotomy is also universal over strict subtails:
either one continuation extension exists, or the exact minimum coefficient is
nonintegrable on every later anchored tail. The transport and coefficient
hypotheses are inherited by restriction, so this does not introduce a new
analytic assumption.

## Fixed-anchor later-tail obstruction

The exact adaptive coefficient retains a fixed kinetic-energy anchor b
while the integrability interval is restricted to any later (c,T).

Integrability on one later tail implies continuation. Under
nonextension, the fixed-anchor coefficient is nonintegrable on
every later strict subtail.

This also applies to the closed gradient-envelope coefficient.
Later kinetic anchors decrease the adaptive minimum pointwise.

These are conditional continuation/obstruction statements.

## Two-anchor obstruction and activation threshold

For every interior kinetic anchor b and later start c, the exact adaptive
nonextension obstruction holds on (c,T) with the kinetic ceiling fixed at b.
This quantifies over both anchors simultaneously; it does not introduce new
PDE estimates or temporal assumptions. The gradient-envelope version uses
the closed coefficient B(t) = 4422(1+|h(t)|).

For B>0 and E>0 the exact absorbed coefficient is below direct B exactly
when E > 1 + (3 + (81/8) B^3) E0(b). Below or at this threshold the
adaptive minimum is direct B, and strictly above it the absorbed branch
is selected. Kinetic monotonicity lowers the threshold at later anchors,
so an already active absorbed branch remains active after reanchoring.

These results refine the conditional continuation/nonextension alternative;
they do not establish finite-time blowup or unconditional continuation.

## Uniform exact adaptive regimes

The exact threshold partitions the adaptive coefficient pointwise:
when E(t) is at or below 1 + (3 + 81 B(t)^3 / 8) E0(b), the
minimum is B(t); when E(t) is strictly above that threshold,
it is the exact normalized absorption coefficient.

If either branch is selected throughout a later strict tail, its
integrability alone implies H3-path continuation. Conversely,
nonextension forces that selected coefficient to be nonintegrable.
The corresponding conditional obstruction holds on all later tails
when the same regime persists throughout the original anchored tail.

These are regime-dependent consequences of the existing adaptive
criterion, not assertions that either regime must eventually persist.

## Mixed exact adaptive regimes

The exact minimum is a sum of threshold-selected direct and absorbed
contributions. At any time exactly one contribution is selected (at equality
the direct one). This identity accommodates arbitrary temporal switching.

Integrability of both selected contributions on one fixed-anchor later tail
implies continuation. Therefore, under nonextension, on every two-anchor
subtail at least one selected contribution is nonintegrable. Which contribution
fails is allowed to depend on the subtail. The same obstruction is available
for B(t) = 4422(1 + |h(t)|) under the closed gradient-envelope hypothesis.

This decomposes an existing conditional obstruction; it does not establish
that either regime dominates, nor unconditional continuation or blowup.

## Persistent selected-share obstruction

On a fixed kinetic anchor, integrability of each of the two selected
coefficients on possibly different strict subtails would imply their joint
integrability on the common later tail. This contradicts the previously
established nonextension obstruction. Therefore, under nonextension, at
least one *fixed selected share* is nonintegrable on every later subtail.
The responsible share may depend on the kinetic anchor. The gradient-
envelope specialization has the same conclusion.

This is a measure-theoretic strengthening of the existing conditional
alternative. It does not imply pointwise eventual regime selection and
establishes neither unconditional continuation nor blowup.

## Order of selected shares across kinetic anchors

The selected direct coefficient is pointwise nonincreasing when the
kinetic anchor advances, because the exact activation threshold falls.
Whenever the earlier anchor already selects absorption, later anchors
also select absorption and their exact absorbed coefficient is no larger.

Without earlier activation, the selected absorbed coefficient need not be
monotone: it can change from zero to positive under later anchoring.
This scalar obstruction prevents treating the two selected shares as
symmetric. No integral-transfer or anchor-independent regime assertion
is claimed without additional measurability and analytic information.

## Selected-share compensation under reanchoring

Let D_b and A_b denote the threshold-selected direct and absorbed
coefficients computed using kinetic anchor b. For b < c, the exact minimum
is antitone in the kinetic ceiling, hence D_c + A_c <= D_b + A_b.
Equivalently, A_c - A_b <= D_b - D_c: any selected absorbed-share gain
is offset by direct-share loss. In particular, when absorption newly
activates at c, its coefficient is strictly smaller than the earlier
direct coefficient B. This is pointwise, does not require temporal
measurability, and does not yet transfer integrability between anchors.

## Selected-share integrability transfer across anchors

The selected direct coefficient is nonnegative and decreases when the kinetic
anchor advances. With explicit measurability of the later selected direct
coefficient, its integrability transfers from an earlier anchor on a fixed
terminal subtail. Under nonextension, an earlier direct-integrable share then
forces every later anchor's selected absorbed share to be nonintegrable on
every terminal subtail. Thus either no direct share becomes integrable at
any anchor or some direct-integrable anchor forces persistent absorbed
obstructions at all later anchors. This is conditional on measurability;
pointwise order alone does not prove it. No unconditional continuation or
blowup is claimed.

## Tail-local selected-share measurability

The closed H3 derivative identities show that canonical H3 energy is
continuous on every strict energy-class tail. Assuming measurable B, the
threshold-selection region is null measurable with respect to the restricted
time measure, so the selected direct coefficient is almost everywhere
strongly measurable on that tail. The direct-share integrability transfer and
the anchor-synchronized nonextension obstruction now use this local result,
without demanding globally measurable energy or selected-share functions.
Measurability of B is retained explicitly; the temporal integrability
obstruction is not discharged by measurability alone.

## Canonical square-root-gradient anchor synchronization

The canonical H3 path supplies the spatial-gradient envelope
h(t) = C1 sqrt(E_H3(t)), with C1 the spectral first-derivative
constant. Closed energy derivative identities yield continuity of E_H3
on each admissible terminal interval. Consequently the coefficient
B(t) = 4422(1+|h(t)|) is continuous there and selected direct shares are
almost everywhere strongly measurable for the restricted tail measure.

Direct-share integrability thus transfers to later kinetic anchors
without requiring global measurability of the energy or a separately
measurable envelope. Under nonextension, either no anchored direct share
is integrable on a later subtail, or one anchor has an integrable direct
share and every later kinetic anchor has a persistently nonintegrable
selected absorbed share. This is a conditional obstruction, not a proof
of temporal integrability or unconditional continuation.

## Canonical absorbed-regime coefficient ceiling

The canonical square-root-gradient coefficient B(t) = 4422(1+C1 sqrt(E(t)))
obeys B(t) >= K sqrt(E(t)) with positive K = 4422 C1. The exact
quartic activation threshold consequently forces 81 M K^2 B(t) < 8
on the absorbed region, where M=E0(b) is the anchor kinetic mass.
The threshold-selected absorbed coefficient A_b(t) therefore satisfies
81 M K^2 A_b(t) <= 8 at every time, including direct-selection times.
For strictly positive anchor mass, A_b is bounded by 8/(81 M K^2).
This is pointwise; temporal integrability additionally needs measurable
selection and the finite-time interval. No unconditional continuation or
finite-time blowup is concluded.

## Integrability of canonical selected absorption

On an H3 energy-class tail, the canonical energy and square-root-gradient
coefficient are continuous. The full exact absorption quotient is continuous
there because the normalized H3 energy stays at least one; the threshold
selected absorbed share is therefore almost everywhere strongly measurable
on each strict terminal interval. If the fixed kinetic anchor b has E0(b)>0,
the earlier quartic activation ceiling makes the selected absorbed share
uniformly bounded by 8/(81 E0(b) (4422 C1)^2). The interval has finite volume,
so this selected absorbed share is integrable on every strict later subtail.

Consequently, hypothetical nonextension forces the selected *direct* share
to be nonintegrable on every later subtail of each positive-kinetic-mass
anchor. Neither positive kinetic mass at every anchor nor integrability of
the direct share is claimed without proof; no unconditional result follows.

## Canonical absorption activation energy threshold

The canonical coefficient B(t)=4422(1+C1 sqrt(E(t))) dominates
K sqrt(E(t)), where K=4422 C1>0. For kinetic mass M=E0(b)>=0,
the strict absorbed activation inequality forces both
81 M K^2 B(t)<8 and 81 M K^3 sqrt(E(t))<8.
Contrapositively, if either corresponding weighted expression is at least
8, the exact threshold selects direct transport: its selected share equals
B(t) and the selected absorbed share vanishes. Thus for any *positive*
kinetic mass anchor, absorbed activation is confined to a bounded H3-energy
region. These are pointwise facts; they do not establish that high energies
occur, persist, or contribute a finite terminal integral. The conditional
continuation/nonextension alternatives remain unresolved.

## High-energy localization of canonical selected direct obstruction

For every real cutoff L, split the canonical selected direct coefficient into
its restrictions to E_H3(t) <= L and E_H3(t) > L, using complementary indicator
functions. On the first region, the exact direct share is bounded above by
4422 (1 + C1 sqrt(L)). The H3 energy derivative identities and canonical
transport coefficient imply both restrictions are measurable relative to any
strict terminal-tail measure. Since such tails have finite measure, the
bounded-energy selected direct restriction is integrable on each tail.

At any kinetic anchor with E0(b)>0, the previously proved absorbed-share
integrability and selected continuation criterion show that, under
hypothetical nonextension, the high-energy direct restriction must be
nonintegrable on every strict subtail, for every fixed cutoff L. This is a
conditional localization, not an assertion of blowup or of the integrability
of the remaining high-energy share.

## High-energy square-root H3 moment obstruction

For any fixed energy cutoff L, the high-energy part of the canonical
selected direct coefficient is bounded by 4422 times the sum of the
high-energy time indicator and C1 times the high-energy indicator of
sqrt(E_H3). The first term is integrable on each finite terminal interval,
independently of regime switching. Both indicators are measurable relative
to the restricted tail measure by continuity of canonical H3 energy.

Consequently, integrability of the high-energy sqrt(E_H3) moment would imply
integrability of the high-energy selected direct coefficient. At an anchor
with E0(b)>0, hypothetical nonextension and the preceding localization
therefore force the high-energy sqrt(E_H3) moment to be nonintegrable on
every strict terminal subtail for every fixed cutoff L. This is a necessary
conditional obstruction, not a demonstration of blowup or a universal
regularity theorem. The remaining frontier is quantitative control of this
high-energy residence-time-weighted square-root moment.

## Terminal Riccati high-energy clock

The previously closed Riccati lower bound under hypothetical nonextension,
2 <= K (T-t) sqrt(E_H3(t)) with fixed K>0, forces every finite H3 energy
cutoff to be exceeded throughout a sufficiently late final time interval.
For each cutoff L, a positive window q satisfying K q sqrt(max(L,0))<2
excludes E_H3(t)<=L whenever 0<T-t<q. On that final interval, the
high-energy cutoff sqrt(E_H3) moment coincides pointwise with the full
sqrt(E_H3) profile. The established Riccati nonintegrability theorem then
forces nonintegrability of the high-energy moment on every strict terminal
tail under nonextension, independently of positive kinetic mass at any
anchor. These are conditional necessary conditions, not a construction of
blowup or a proof of unconditional continuation. The direct-share route
still requires positive kinetic anchor mass where indicated.

## Eventual exact direct selection on the terminal clock

Hypothetical H3 nonextension forces the canonical normalized energy beyond
any fixed cutoff throughout a sufficiently late final interval by the already
closed Riccati terminal clock. At any fixed kinetic anchor with positive mass
M=E0(b), the exact quartic threshold admits a finite energy cutoff beyond
which 81 M (4422 C1)^3 sqrt(E_H3(t)) >= 8, forcing the direct regime.
Consequently the selected direct share equals the full canonical gradient
transport coefficient and the selected absorbed share vanishes at *every*
time on a sufficiently late strict terminal interval. The direct-selection
set has the full measure T-c there. The selected direct share also inherits
the known positive harmonic terminal lower bound on this final interval.
These assertions are conditional on hypothetical nonextension and positive
anchor kinetic mass; they neither establish nor exclude finite-time blowup.

## Selected direct transport and the exact dissipation defect

The closed physical H3 energy identity states E'(t)+2D(t)=-T_H3(t).
Under hypothetical nonextension, an already established strict terminal
sequence has E'(sigma_n) -> +infinity and hence signed full-dissipation
transport excess -T_H3(sigma_n)-2D(sigma_n) -> +infinity. Eventual
canonical direct selection at each positive-kinetic-mass anchor can be
synchronized with the *same* sequence: eventually the selected direct
coefficient is exactly 4422(1+C1 sqrt(E(sigma_n))) and selected absorption
is zero. Therefore every later tail contains an exactly direct-selected
time where the signed full-dissipation transport excess exceeds any
prescribed real bound. Conversely, an upper bound on this signed excess
at all sufficiently late direct-selected times for one positive-mass
anchor would imply smooth continuation. These remain conditional results:
no bound of this type is asserted for all Navier--Stokes paths, and no
unconditional regularity or blowup result is claimed.
