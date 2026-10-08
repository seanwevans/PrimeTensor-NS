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
