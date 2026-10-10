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

## L1 obstruction on exactly direct-selected times

Define q(t) = max(0, (-transport_H3(t)-2*dissipation_H3(t))/E_H3(t)).
The exact PDE balance identifies q with positive logarithmic H3-energy growth.
For a fixed kinetic anchor b, restrict q to the set on which the selected
canonical direct coefficient equals the full canonical transport coefficient.
On a hypothetical nonextendible path and any anchor with E0(b)>0, earlier
results force this set to contain a full final time interval. The previously
proved nonintegrability of q on every terminal energy-class tail then implies
nonintegrability of this *direct-selected restricted* q on every strict later
tail. Conversely, if one such restricted rate is integrable on one terminal
tail at a positive-mass anchor, smooth continuation follows. This is a
conditional L1 obstruction, not a newly proved dissipative transport bound,
and it establishes neither unconditional regularity nor blowup.

## Integrable dissipation-margin envelope frontier

The exact H3 PDE balance gives E'(t)+2D(t)=-transport_H3(t). For a fixed
positive-kinetic-mass anchor, any hypothetical nonextendible path eventually
selects the entire direct transport coefficient on a final interval. Suppose
an integrable real-valued temporal remainder r(t) and any epsilon>=0 bound
the adverse nonlinear transport on all sufficiently late directly selected
times by

    -transport_H3(t) <= (2-epsilon) D(t) + r(t) E(t).

Nonnegative dissipation implies E'(t)<=r(t)E(t) on that final interval;
the already-closed linear-growth continuation theorem then supplies a smooth
extension. Contrapositively, nonextension forces a strict violation of this
bound on every terminal interval, for every integrable remainder r and every
nonnegative epsilon at every positive-kinetic-mass anchor. A constant r=M
is a special case. This is a *conditional criterion* only: no new PDE
transport estimate is asserted, and neither universal continuation nor
finite-time blowup is proved.

## Minimal normalized dissipation-margin excess rate

For any real margin epsilon, define q_epsilon(t) as the positive part of
(-transport_H3(t) - (2-epsilon) D_H3(t)) / E_H3(t). The exact physical
H3 balance makes this the positive part of (E'_H3(t) + epsilon D_H3(t))
/ E_H3(t) on each H3 energy-class interval. It is nonnegative and is
pointwise minimal among nonnegative coefficients r satisfying

    -transport_H3(t) <= (2-epsilon) D_H3(t) + r(t) E_H3(t).

As epsilon increases, q_epsilon increases, because D_H3 is nonnegative.
For epsilon >= 0 the rate dominates the known full-dissipation positive
logarithmic growth rate. If q_epsilon is integrable on one terminal H3
energy-class interval, the exact balance and the existing scalar linear
growth theorem imply smooth continuation. Conversely, hypothetical
nonextension forces q_epsilon nonintegrable on every strict later tail for
all epsilon >= 0. This anchor-independent family identifies an exact
minimal PDE margin requirement; it does NOT prove such an estimate is
satisfied, nor establish global regularity or blowup.

## Explicit spectral dissipation-gap frontier

The existing H3 nonlinear commutator bound gives -transport_H3 <= B(t) E(t),
where B(t)=4422(1+C1 sqrt(E_H3(t))). Define the spectral dissipation gap

    g_epsilon(t) = max(0, B(t) - (2-epsilon) D(t)/E(t)).

The exact minimal normalized transport margin excess q_epsilon is pointwise
bounded by g_epsilon on H3 energy-class times, because the actual transport
pairing may enjoy cancellation beyond the commutator bound. For epsilon>=0,
integrability of g_epsilon on a terminal energy-class interval gives the
established H3 continuation criterion. Under hypothetical nonextension,
g_epsilon must instead fail L1 on every late energy-class tail, and it must
strictly exceed every proposed integrable comparison function somewhere
on each such tail. At any positive kinetic anchor, a violation can be chosen
at a time with exact direct coefficient selection and zero selected absorption.
This is a conditional quantitative dissipation/transport gap frontier, not
a proof that the gap is integrable or that nonextension occurs. The genuine
missing estimate must improve commutator control or show that enough of the
full dissipation compensates the nonlinear term.

## Unbounded normalized spectral transport shortfall

Remove the finite 4422 constant baseline from the zero-margin spectral
commutator/dissipation gap. The remaining normalized nonlinear *spectral*
shortfall is S(t)=4422*C1*sqrt(E_H3(t))-2*D_H3(t)/E_H3(t), and the gap is
max(0,4422+S(t)). Under hypothetical nonextension, existing all-envelope
witnesses force S(t) to exceed every finite threshold on every strict
terminal tail. At a positive kinetic anchor the witness can be chosen in
the exact selected direct regime, with zero selected absorption. A single
physical-clock sequence t_n in (T-1/(n+1),T) can be selected with S(t_n)>n,
S(t_n)->+infinity, and exact direct selection at each sample.

The shortfall is the overestimate from the established H3 commutator bound,
not the actual signed nonlinear transport. None of these statements prove
that the commutator bound is sharp, that shortfall integrability fails for
an actual solution without the hypothetical no-extension premise, or that
finite-time blowup occurs.

## Simultaneous actual transport excess and spectral shortfall

Under hypothetical H3 nonextension, the existing constant-margin theorem
at any positive-mass kinetic anchor yields arbitrarily late exact direct-
selected times at which -transport_H3(t)-2*D_H3(t)>R*E_H3(t), for any
prescribed constant R. Taking R=4422+max(M,0) forces both the actual minimal
normalized zero-margin excess q_0=max(0,(-transport-2D)/E) and the baseline-free
spectral shortfall S=4422*C1*sqrt(E)-2D/E above M, at *the same* time.
Here S is only the commutator envelope minus dissipation; the actual signed
transport may be strictly below its commutator bound. Selecting one witness
inside each (T-1/(n+1),T) produces an explicit physical-clock sequence
converging to T with both q_0 and S tending to +infinity and direct
selection exact at every sample, while the selected absorbed share vanishes.
The synchronization is conditional on hypothetical nonextension and positive
kinetic anchor mass. It neither proves commutator-bound saturation nor the
existence of a blowup solution or unconditional smooth continuation.

## Exact transport cancellation budget on the synchronized direct clock

Define B(t)=4422(1+C1 sqrt(E_H3(t))), the existing commutator envelope.
The normalized *cancellation slack* is Delta(t) = B(t) + T_H3(t)/E_H3(t),
where T_H3 is the signed transport derivative. The existing H3 commutator
estimate proves Delta >= 0. Exact algebra gives

    Delta(t) + (-T_H3(t)-2D(t))/E(t) = 4422 + S(t),

where S(t)=4422*C1*sqrt(E(t))-2D(t)/E(t) is the baseline-free spectral
shortfall. At times with positive actual normalized zero-margin excess q0,
its max is inactive and Delta(t)+q0(t)=4422+S(t). On the already established
common physical-clock sequence for hypothetical nonextension, positive kinetic
anchor mass, and exact direct selection, q0(sigma_n)>n and S(sigma_n)>n;
therefore 0<=Delta(sigma_n) and Delta(sigma_n)+n<4422+S(sigma_n).
Neither the size nor the asymptotic fraction of Delta is determined.

If on one terminal H3 energy-class tail the quantitative compensation bound

    B(t) - (2-epsilon) D(t)/E(t) - r(t) <= Delta(t)

holds for nonnegative epsilon and integrable r, then the exact signed PDE
transport satisfies -T_H3<=(2-epsilon)D+rE, so continuation follows.
Under hypothetical nonextension, every such bound must fail somewhere on
every terminal subtail. This is a conditional cancellation-coercivity test,
not proof that the missing estimate holds, and it establishes neither
unconditional H3 continuation nor a finite-time blowup example.

## Compact normalized transport-cancellation share

On positive actual-excess H3 energy-class times, the nonnegative commutator
cancellation slack Delta and the positive actual full-dissipation transport
excess q0 satisfy Delta+q0=4422+S, where S is the baseline-free canonical
spectral shortfall. Normalize by their positive sum: cancellation share is
Delta/(Delta+q0), and growth share is q0/(Delta+q0). Both lie in [0,1] and
sum exactly to one. Under hypothetical nonextension and at any positive-mass
kinetic anchor, an earlier physical terminal-clock sequence has q0 and S
both tending to +infinity with exact direct selection and no selected
absorption. By compactness of [0,1], one can select a cofinal subsequence on
which cancellation share tends to theta in [0,1], and the complementary
actual-growth share tends to 1-theta, while q0 and S STILL diverge along
that same subsequence. The endpoint theta=1 does not imply q0 bounded;
its fraction can vanish despite absolute divergence if the total budget
grows sufficiently fast. This is a neutral quantitative classification,
not a new cancellation estimate and not a proof of global regularity or
finite-time blowup.

## Relative cancellation and actual-growth share cluster

On the conditional synchronized H3 terminal-clock sequence, the nonnegative
commutator cancellation gap Delta and positive actual normalized excess q0
form complementary shares theta=Delta/(Delta+q0) and gamma=q0/(Delta+q0).
The previous compactness result extracts a subsequence with theta -> theta_*
in [0,1] and gamma -> 1-theta_* while q0 and the spectral shortfall both
remain divergent and exact direct selection persists. The new relative-rate
classification is exhaustive: if theta_* < 1, then Delta/q0 tends to the
finite rate theta_*/(1-theta_*). This includes theta_*=0, where Delta/q0
vanishes. If theta_*=1, then q0/Delta tends to zero (the cancellation gap
is eventually positive). In the latter case q0 still tends to infinity:
relative negligibility must not be confused with absolute boundedness.
All conclusions remain conditional on hypothetical nonextension; no
Navier--Stokes cancellation or regularity estimate is assumed or proved.

## Quantitative spectral-budget fractions along the direct terminal clock

The exact positive-actual-excess H3 budget is Delta(t)+q0(t)=4422+S(t),
where Delta is nonnegative commutator cancellation slack, q0 is the actual
normalized positive transport excess after the full two copies of viscous
dissipation, and S is the baseline-free canonical spectral shortfall.
On the previously extracted conditional direct terminal-clock subsequence,
the cancellation share converges to theta in [0,1] and the actual-growth
share converges to 1-theta; q0 and S both diverge absolutely.

If theta<1, then for every fixed eta with 0<eta<1-theta, eventually
eta*(4422+S(t_n))<q0(t_n): actual growth retains a definite fraction of
the spectral budget. If theta=1, then for every eta>0, eventually
q0(t_n)<eta*(4422+S(t_n)), even though q0(t_n)->+infinity. The ratio
conclusions are algebraic consequences of the established compact share
cluster; neither endpoint is excluded and no new PDE transport estimate,
unconditional regularity, or blowup result is asserted.

## Physical energy and slope lower bounds on the synchronized direct clock

The exact full-dissipation positive transport excess q0=max(0,(-T_H3-2D)/E)
coincides on H3 energy-class times with max(0,E'/E). For any nonnegative M,
M<q0 therefore implies M*E<E'. The nonnegative H3 dissipation also gives
S=4422*C1*sqrt(E)-2D/E <= 4422*C1*sqrt(E), so M<S forces the physical
quadratic lower bound M^2 < (4422*C1)^2 * E. In particular, conditional on
hypothetical nonextension, positive kinetic anchor mass, and the previous
synchronized direct terminal-clock sequence, both inequalities occur at the
same arbitrarily late times. They also persist on the cofinal subsequence
selected by compactness of the cancellation share: with indices k(n),

    (k(n))^2 < (4422*C1)^2 * E(sigma(k(n)))
    k(n) * E(sigma(k(n))) < E'(sigma(k(n))).

The terminal physical times converge to T, actual normalized excess and
spectral shortfall diverge, exact direct selection remains active and the
cancellation share tends to theta in [0,1]. These are indexed necessary
conditions only, not physical-time power-law blowup rates, new PDE coercive
bounds, evidence for commutator saturation, or a proof of NS regularity or
finite-time singularity. In particular k(n) has no prescribed relation to
1/(T-sigma(k(n))) beyond the explicit localization upper width.

## Indexed terminal clock-width cluster and physical-rate frontier

The direct H3 witnesses from the prior compact cancellation-share cluster
satisfy k < q0(t), k < S(t), and 0 < T-t < 1/(k+1). Define the indexed
physical terminal width w=k*(T-t), necessarily in [0,1]. Exact H3 balance
and the nonnegative dissipation imply

    w < (T-t)*E'(t)/E(t),
    w < (T-t)*4422*C1*sqrt(E(t))

at every selected witness. Compactness gives a further cofinal subsequence
on which w tends to chi in [0,1], preserving the earlier cancellation-share
limit theta, convergence of physical time to T, divergence of actual excess
and spectral shortfall, and exact direct selection. If chi>0, the two
physical-time normalized quantities above are eventually greater than
chi/2 on that selected subsequence. If chi=0, no inverse-terminal-width
bound follows from this indexed argument. In fact, for each threshold M and
every width delta>0 the direct witness can be selected within (T-delta,T),
independently of M; the width of the chosen terminal window is not fixed by
the PDE. A positive chi is a conditional property of a particular witness
selection, not a forced consequence of nonextension. No global regularity,
finite-time singularity, or universal physical-time exponent is proved.

## Arbitrarily fast terminal witness selection

The preceding H3 physical-clock indexed-width theorem extracts a witness
sequence with n<q0(t_n), n<S(t_n), and terminal localization. The witness
selection result is in fact available on every strict terminal interval.
For every positive gauge delta(n) with delta(n)->0 and n*delta(n)->0,
choose direct-selected witnesses t_n in (T-delta(n), T) with both q0(t_n)
and S(t_n) above n, and zero selected absorption. The actual normalized
full-dissipation transport excess and spectral shortfall tend to +infinity,
while t_n->T and n*(T-t_n)->0. Compactness gives a cofinal subsequence
on which the cancellation share converges to a value theta in [0,1]
without losing these properties. In particular the explicit gauge

delta(n) = 1/(n+1)^2

produces a **zero** indexed-width cluster for any hypothetical nonextension
branch with a positive-mass kinetic anchor. This is a consequence of the
freedom to choose late witnesses, not evidence of a new Navier--Stokes
physical-time growth bound. The earlier possible positive width cluster
was always conditional on witness selection. Neither the existence of a
blowup solution nor unconditional smooth continuation is established.

## Intrinsic Riccati terminal clock and freely selected fast witnesses

The repository already proves an intrinsic pointwise Riccati lower bound in
PrimeTensor/Fluid/Vorticity/Continuation/H3/Terminal/Riccati/Lower/Bound.lean:
conditional on hypothetical nonextension, every strict energy-class time t
satisfies 2 <= K*(T-t)*sqrt(E_H3(t)), with K=4422*(C1+1)>0. It follows that
4 <= K^2*(T-t)^2*E_H3(t), independent of how witnesses are chosen. In
particular a single strict-tail time with K^2*(T-t)^2*E_H3(t)<4 (or with
K*(T-t)*sqrt(E_H3(t))<2) suffices for smooth continuation, by contraposition.

The earlier fast-clock theorem permits exact direct-selected witnesses at
0<T-t_n<1/(n+1)^2, with actual normalized full-dissipation transport excess
and spectral shortfall both above n. The intrinsic Riccati bound then also
forces 4*(n+1)^4 <= K^2*E_H3(t_n). A cofinal cancellation-share cluster
retains this eventual quartic indexed energy floor and its zero indexed
width n*(T-t_n)->0, along with divergence of both excesses. The quartic
index result does not represent a new independent physical-time exponent:
it is the intrinsic inverse-square time bound evaluated in a freely chosen
quadratically narrowing window. No unconditional extension or finite-time
singular solution is claimed. The current work reuses the already existing
Riccati lower bound rather than presenting it as a newly discovered estimate.

## Exact Riccati growth defect and terminal coefficient refinement

The existing autonomous H3 Riccati bound is E'<=K*sqrt(E)*E with
K=4422*(C1+1). On every strict H3 energy-class time the exact signed
PDE balance yields the nonnegative three-channel defect identity

  K*sqrt(E) - E'/E = 4422*(sqrt(E)-1) + Delta + 2*D/E,

where Delta=B+T_H3/E is canonical commutator cancellation slack,
B=4422*(1+C1*sqrt(E)), and D is the nonnegative full H3 dissipation.
This identifies the 4422*(sqrt(E)-1) overhead introduced when bounding
the fixed baseline 4422 by 4422*sqrt(E). For any eta>0, wherever
4422<=eta*sqrt(E), the closed energy inequality improves pointwise to

  E' <= (4422*C1+eta)*sqrt(E)*E.

The already proved intrinsic Riccati floor for a hypothetical
nonextendible H3 path, 2<=K*(T-t)*sqrt(E(t)) at every energy-class
time, forces the high-energy premise for all sufficiently late times,
with the explicit terminal-width cutoff 2*eta/(K*4422). Thus, under
hypothetical nonextension, for every eta>0 there is a final energy-class
tail where the refined pointwise growth coefficient holds throughout.
This refines an upper differential inequality only; it does not yet
re-run the inverse-root Riccati comparison with the smaller coefficient,
prove a stronger intrinsic terminal floor, force cancellation, prove
smooth continuation, or construct a finite-time singularity.

## Refined intrinsic inverse-root terminal Riccati clock

Under hypothetical nonextension, for every eta>0 the previously
proved exact Riccati-defect theorem provides a final H3 energy-class
tail satisfying

    E' <= (4422*C1+eta)*sqrt(E)*E.

For F=1/sqrt(E), the corresponding derivative inequality is

    F' >= -(4422*C1+eta)/2.

The shifted inverse-root energy is monotone. Passing to the terminal
energy-divergence sequence yields, at every sufficiently late time,

    1/sqrt(E) <= ((4422*C1+eta)/2)*(T-t),
    2 <= (4422*C1+eta)*(T-t)*sqrt(E),
    4 <= (4422*C1+eta)^2*(T-t)^2*E.

The terminal cutoff may depend on eta. No fixed-time zero-tolerance
inequality is claimed. Recurrent strict violations for any fixed
eta>0 force smooth continuation by contraposition.

This improves an intrinsic necessary condition under hypothetical
nonextension; it neither proves unconditional smooth continuation
nor constructs a finite-time singularity.

## Effective Riccati defect and the leading nonlinear coercivity barrier

The earlier exact defect decomposition gives an H3 energy-class identity

  E'/E + Q = 4422 + A*sqrt(E),
  Q = Delta + 2*D/E >= 0,   A = 4422*C1 > 0.

Here Delta is the gap between the canonical commutator transport envelope
and actual signed H3 transport, D is full nonnegative H3 dissipation,
and Q is the *effective* dissipative/cancellation defect. Nonnegativity
of Q by itself does not absorb the nonlinear Riccati term A*sqrt(E).

On any strict terminal energy-class tail, the extra coercivity premise

  A*sqrt(E(t)) <= Q(t) + r(t)

with any integrable scalar remainder r yields E'(t) <= (4422+r(t))*E(t)
pointwise, so the established linear-growth continuation theorem applies.
This assumption is **not established** by the existing commutator estimate.
Conversely, a hypothetical nonextendible H3 path must, on every strict
terminal subtail and for every integrable r on that subtail, admit a time
at which Q(t)+r(t) < A*sqrt(E(t)). In particular, Q alone must fall below
A*sqrt(E) at some time in every terminal subtail. This leaves open which
of the two nonnegative channels supplies a potential analytic coercivity
bound; no unconditional regularity or singularity conclusion is claimed.

## Positive unabsorbed Riccati rate and terminal nonintegrability

With the existing exact energy identity E'/E + Q = 4422 + A sqrt(E),
where A=4422*C1 and Q=Delta+2D/E, define the nonnegative *unabsorbed*
leading Riccati rate

  U(t) = max(0, A*sqrt(E(t)) - Q(t)).

At each strict H3 energy-class time, the exact signed PDE balance gives

  U(t) = max(0, E'(t)/E(t) - 4422),
  E'(t) <= (4422+U(t))*E(t).

If U is integrable on any terminal H3 energy-class tail, 4422+U is an
integrable scalar growth majorant; the previously closed continuation
criterion yields a smooth extension. Therefore hypothetical nonextension
forces U to be nonintegrable on every strict terminal H3 energy-class
subtail. The previously proved integrable-compensation obstruction also
implies that on every such subtail U exceeds any prescribed integrable
scalar remainder somewhere; taking constant remainders shows pointwise
unboundedness of U there. The rate is a diagnostic of *unabsorbed*
nonlinear transport, not a new lower bound for cancellation or dissipation.
No unconditional smooth continuation or singular solution is asserted.

## Synchronized unabsorbed Riccati growth on the fast terminal clock

The full-dissipation actual positive transport excess is exactly
q0=max(0,E'/E) at strict H3 energy-class times, while the unabsorbed
nonlinear Riccati rate is U=max(0,E'/E-4422). Their positive-part forms give

    0 <= q0-U <= 4422.

Consequently q0 and U diverge to +infinity together on *any* sequence
eventually in the same energy-class tail; no new selection or PDE hypothesis
is needed to transfer one escape rate to the other. Under hypothetical
nonextension, every prescribed strict terminal subtail contains a
canonical direct-selected, zero-absorbed witness with both U and the
spectral shortfall exceeding any real threshold (the actual excess
threshold is shifted by 4422). The previously constructed quadratic
terminal-window sequence and its compact cancellation-share subsequence
therefore carry q0, U, and the spectral shortfall all diverging on one
physical clock. That clock still has n*(T-t_n)->0 and retains the earlier
intrinsic Riccati-derived quartic indexed-energy floor. Neither the
bounded baseline comparison nor a freely chosen narrow window provides a
new independent physical-time exponent or an analytic estimate making U
integrable. This is a neutral necessary-condition synchronization only.

## Essential temporal barrier for unabsorbed Riccati growth

On the strict H3 energy-class terminal tail, the exact unabsorbed growth
rate U = max(0,4422*C1*sqrt(E)-(Delta+2*D/E)) agrees with
max(0,E'/E-4422). Tail-local temporal continuity of E and measurability
of its derivative establish almost-everywhere strong measurability of U
for the restricted Lebesgue measure. If U is dominated almost everywhere
by any integrable real-valued remainder r, then |U|<=|r| almost everywhere;
U is integrable, and the existing continuation criterion yields a smooth
extension. Hence hypothetical nonextension forbids a.e. domination of U
by every integrable remainder on each strict terminal energy-class
subtail. In particular, for every finite M, it is impossible that
U(t)<=M almost everywhere on such a tail: the exceedance has non-null
temporal presence, not merely a possible isolated selected witness.
Equivalently, almost-everywhere compensation of the leading nonlinear
term 4422*C1*sqrt(E) by Delta+2*D/E plus an integrable remainder is
impossible on any such tail under nonextension. No quantitative measure,
time occupation fraction, new PDE coercivity, unconditional continuation,
or existence of blowup is asserted.

## High-amplitude unabsorbed Riccati superlevel tails

Write U(t)=max(0,A*sqrt(E(t))-Q(t)), where A=4422*C1 and
Q=Delta+2D/E. For every fixed real threshold M, define

    U_M(t)=max(0,U(t)-M).

The pointwise bound 0<=U<=U_M+max(0,M) shows that integrability of
U_M on any finite strict terminal H3 energy-class tail implies
integrability of U and therefore smooth continuation.

Consequently hypothetical nonextension forces U_M to be
nonintegrable on every such terminal subtail, for every fixed M.
The high-rate excess above each finite threshold must carry
infinite L1 time cost. This is stronger than pointwise or essential
unboundedness, but does not supply a quantitative occupation-time
fraction or any new PDE coercivity estimate.

## Essential simultaneous PDE-channel deficit

Write A=4422*C1, E=canonical H3 energy, Delta=nonnegative
commutator/transport cancellation gap, and D=full nonnegative H3
dissipation. The effective PDE absorption is Q=Delta+2D/E, and the
unabsorbed Riccati rate is U=max(0,A*sqrt(E)-Q).

For every fixed nonnegative M, at every physical time U>M if and only
if Q+M<A*sqrt(E). At strict H3 energy-class times, this is also equivalent
to 4422+M<E'/E. Both nonnegative PDE channels must therefore individually
fall short of A*sqrt(E) by the threshold M on any high-U time, although
this condition alone does not characterize their summed shortfall.

Because the earlier essential barrier prohibits almost-everywhere
compensation of the leading coefficient A*sqrt(E) by Q plus any integrable
remainder r on any strict terminal tail under hypothetical nonextension,
the path also cannot have the property that *at almost every time* either
Delta+r or 2D/E+r absorbs A*sqrt(E). Thus the *simultaneous failure* of
both individual channel ceilings cannot be confined to a time-null set.
Conversely, proving such almost-everywhere one-channel absorption with one
integrable scalar allowance on some tail would force smooth continuation.
Similarly, a hypothetical nonextension cannot possess any finite
a.e. ceiling for the normalized physical energy slope E'/E on any tail.

This is a repackaging of already-established PDE balance and essential
nonintegrability, not an independently closed coercivity theorem, not a
quantitative occupation-time bound, and not a proof of unconditional
continuation or existence of finite-time singularities.

## Critical cubic viscous-dissipation shortfall

The exact H3 balance splits leading normalized energy growth as

  E'/E + Delta + 2*D/E = 4422 + A*sqrt(E),  A=4422*C1.

The actual unabsorbed nonlinear Riccati rate U=max(0,A*sqrt(E)-Delta-2*D/E)
is bounded above by the dissipation-only rate

  V=max(0,A*sqrt(E)-2*D/E).

Nonnegative transport cancellation gives the sharp comparison

  U <= V <= U+Delta.

Thus V is a physical upper envelope for U. Whenever V is integrable on
one strict terminal H3 energy-class tail, continuation follows.

For M>=0, V>M holds exactly when

  2*D+M*E < A*sqrt(E)*E.

Under hypothetical nonextension V is nonintegrable on every strict
terminal subtail, and this cubic viscous floor with any fixed
linear-energy margin fails on a non-null subset of every such tail.

No independent bound D >= c*E^(3/2), unconditional continuation,
or singularity existence is established.

## Anchored top Fourier moment versus cubic dissipation deficit

The independently established spatial Fourier interpolation inequality
E3(t)^4 <= E0(t)*D3(t)^3, kinetic antitonicity, and D3<=D combine at
any strict time t later than a fixed kinetic anchor b to yield

    E3(t)^4 <= (E0(b)+1)*D(t)^3.

The exact normalized H3 energy balance and the earlier pure-dissipation
shortfall theorem show that if unabsorbed growth U(t)>M>=0, then

    2*D(t) < B_M(t),
    B_M(t) = A*sqrt(E(t))*E(t)-M*E(t), A=4422*C1.

Consequently, with no added assumptions on the PDE, every high-U time
obeys the strictly bounded Fourier moment corridor

    8*E3(t)^4 < (E0(b)+1)*B_M(t)^3.

Conversely, the reverse weak inequality at a time gives U(t)<=M.
If the reverse weak inequality is valid for every time in one strict
terminal H3 energy-class tail, the bounded U has an integrable temporal
majorant and smooth continuation follows. Under hypothetical nonextension,
arbitrarily late arbitrarily high U times satisfy the strict corridor.

The reverse moment barrier is NOT established by Fourier interpolation or
by the Navier--Stokes equations. Spatial interpolation alone supplies a
4/3 top-energy dissipation exponent; the continuation threshold has a
3/2 full-energy exponent. Their mismatch is the outstanding analytic gap.
No unconditional regularity or singularity is proved.

## High-energy degeneracy of the cubic Fourier moment corridor

The previously derived necessary condition for high unabsorbed growth was

    8 E3(t)^4 < (E0(b)+1) B_M(t)^3,
    B_M(t) = A sqrt(E(t)) E(t) - M E(t), A=4422*C1>0.

At M=0, the exact algebraic equality is

    B_0(t)^3 = A^3 sqrt(E(t)) E(t)^4.

Because 0<=E3(t)<=E(t) and E0(b)>=0, whenever

    8 < A^3 sqrt(E(t)),

the moment corridor already holds strictly, independently of dissipation,
transport cancellation or any PDE estimate. Therefore the reverse weak
moment barrier proposed as a sufficient criterion for U<=0 is *impossible*
at high H3 energy. On the hypothetical nonextension branch, the previously
proved physical full-tail divergence E(t)->+infinity as t approaches T
from below ensures that the zero-threshold corridor holds at every
sufficiently late time; its reverse fails everywhere on that late tail.

This identifies a genuine limitation of using the Fourier interpolation
E3^4<=E0 D3^3 alone to close the cubic dissipation frontier. The latter
only controls D from below at an E3^(4/3) scale, whereas the Landau
absorption threshold scales like E^(3/2). The zero-threshold moment
corridor is not an independent high-energy PDE obstruction and should
not be mistaken for one. No unconditional continuation, improved
coercivity or existence of finite-time singularity is established.

## Retained-order H3 nonlinear transport coefficient

The established orderwise transport estimates give

    |transport| <= C1*sqrt(E)*(24*E + 4398*E3).

The first two commutator blocks contribute 6E and 18E.
The third block contributes 4398E3; the zeroth-order flux
cancels exactly.

Using the closed PDE pairing and exact H3 energy balance gives

    E' + 2D <= C1*sqrt(E)*(24*E + 4398*E3),
    E'/E <= C1*sqrt(E)*(24 + 4398*E3/E).

Therefore the positive unabsorbed Riccati growth obeys

    U <= max(0, C1*sqrt(E)*(24 + 4398*E3/E) - 4422).

Because the canonical E includes a positive constant,
E3<E strictly. Thus the new coefficient is strictly below
4422*C1*sqrt(E), although the gain need not stay uniformly
positive relative to the original coefficient.

Integrability of the refined positive remainder suffices for
continuation. That integrability is not established for all
Navier--Stokes paths, and unconditional regularity is not proved.

## Signed third-order transport retention

Writing E for normalized H3 energy, D for full H3 dissipation,
T3 for the actual signed third-order nonlinear transport pairing and
h=C1*sqrt(E), the proved lower-order commutator bounds contribute at
most 6hE + 18hE = 24hE; the zeroth-order flux cancels. Therefore,

    E' + 2D <= 24hE - T3.

The signed top transport rate and positive remainder are

    S3 = 24h - (T3+2D)/E,
    W3 = max(0,S3-4422).

The existing exact unabsorbed Riccati growth U satisfies U<=W3.
Integrability of W3 on one H3 energy-class terminal tail suffices for
continuation; hypothetical nonextension forces W3 nonintegrable on
all such strict subtails. Every time U>M>=0 also satisfies

    (4422+M)E+2D < 24hE-T3.

This identifies the *signed* third-order PDE term that a genuine
cancellation/absorption estimate must control. The estimate leaves
T3 untouched; no new bound on its adverse sign, no integrability of
W3 for arbitrary paths, and no unconditional continuation or singularity
existence is asserted.

## Signed top-order transport with a viscous Young share

Write E for the canonical H3 energy, E0 for the kinetic block, E3 for
its top H3 block, D for full H3 dissipation, D3 for top viscous
dissipation, and T3 for signed third-order nonlinear transport. Set

    h = C1*sqrt(E), K = 4398*h,
    A3_eps = max(0, -T3-eps*D3).

The exact physical order-three Landau estimate and independently proved
Fourier interpolation/Young inequality yield for eps>0

    |T3| <= K*E3 <= eps*D3 + K^4*E0/eps^3,
    0 <= A3_eps <= K^4*E0/eps^3.

Retaining the exact sign of T3 and the lower-order 24hE estimate gives,
for eps>=0,

    E' + (2-eps)*D <= 24*h*E + A3_eps.

For 0<=eps<=2, the retained dissipation is nonnegative, so the actual
unabsorbed rate is bounded by

    U <= max(0, 24*h + A3_eps/E - 4422).

Time-integrability of that signed, normalized positive remainder on one
strict terminal H3 energy-class tail implies smooth continuation.
Hypothetical nonextension forces nonintegrability on every later tail.

Analytic limitation: The universal Young estimate is of order
K^4*E0 ~ E0*E^2 and, after normalization, of order E0*E. It is too
large to prove the required integrability by itself. Any continuation
advance must exploit genuine favorable orientation, cancellation,
frequency localization, or stronger PDE information about A3_eps.
This theorem does not establish such an estimate or a singular solution.

## Signed top transport with separate first- and second-order energies

The established actual first- and second-order commutator estimates are
|T1|<=6h E1 and |T2|<=18h E2, where h=C1*sqrt(E). A previous
signed-third-order estimate weakened their sum to 24h E. Retaining the
actual derivative-order energies instead yields

    E' + 2D <= h*(6 E1 + 18 E2) - T3.

After retaining a nonnegative epsilon share of top dissipation D3 and
setting A3_eps=max(0,-T3-eps D3), the exact PDE balance implies

    E' + (2-eps) D <= h*(6 E1 + 18 E2) + A3_eps.

For 0<=eps<=2, the positive part of

    (h*(6 E1 + 18 E2)+A3_eps)/E - 4422

bounds actual unabsorbed H3 growth. Integrability of that normalized
positive part on one strict energy-class terminal tail implies smooth
continuation. Conversely, hypothetical nonextension forces its
nonintegrability on every strict subtail.

More structurally, any physical time with unabsorbed growth U>M>=0 has
one of two properties:

    (4422+M) E < h*(6 E1 + 18 E2),

or

    2D < -T3.

Thus if the genuine low-order nonlinear cost stays below the indicated
threshold at such a time, the signed third-order pairing must be adverse
and exceed twice the full viscous dissipation. The argument does not
prove that either alternative can be excluded, nor integrability of
the sharper scalar remainder. No unconditional continuation or blowup
existence is established.

## Kinetic Fourier absorption of second-order H3 transport

The existing Cauchy--Schwarz estimate on Fourier radial moments and the
independent physical identifications M0=E0, M2=E2, M4=D3 imply

    E2(t)^2 <= E0(t)*D3(t).

Kinetic antitonicity and D3<=D give, for any fixed earlier kinetic anchor b,

    E2(t)^2 <= E0(b)*D(t).

A quadratic Young inequality therefore absorbs the whole second-order
commutator allowance for eps>0, h=C1*sqrt(E):

    18*h*E2 <= eps*D + (18*h)^2*E0(b)/eps.

Combining with the already-closed signed orderwise transport bound gives

    E' + (2-eps)*D <= 6*h*E1 + (18*h)^2*E0(b)/eps - T3.

With eps=1, the remainder is exactly 324*C1^2*E0(b)*E, so its normalized
contribution is constant on the kinetic-anchored tail. The independent
second-order transport obstruction has been removed at the expense of one
unit of D. Every high-U instant U>M>=0 consequently satisfies

    (4422+M-324*C1^2*E0(b))*E + D < 6*h*E1 - T3.

If the remaining first-order commutator is at most the displayed energy
threshold, then the actual signed third-order pairing must satisfy D<-T3.
Neither that first-order ceiling nor a favorable bound on T3 is proved.
In particular this is a genuine improvement of the lower-order PDE estimate,
not unconditional Navier--Stokes continuation or blowup existence.

## Absorb all lower-order H3 transport by kinetic Fourier moments

For the physical radial Fourier moment q=|xi|^2, the pointwise inequality
2q<=1+q^2 and the established Plancherel identifications imply

    2 E1(t) <= E0(t) + E2(t).

The first-order and second-order commutator allowances satisfy, with
h=C1*sqrt(E) and b an earlier kinetic anchor,

    6h E1 + 18h E2 <= 3h E0(b) + 21h E2.

The physical Fourier bound E2^2<=E0(b)*D and quadratic Young absorption
give for eps>0

    E' + (2-eps)*D
       <= 3h E0(b) + (21h)^2 E0(b)/eps - T3.

At eps=1 this becomes

    E' + D <= 3*C1*sqrt(E)*E0(b)
              + 441*C1^2*E0(b)*E - T3.

Since normalized H3 energy E>=1, sqrt(E)<=E. Both lower-order
commutator costs therefore have a bounded normalized coefficient.

The established unbounded actual unabsorbed rate under hypothetical
nonextension implies: for every M>=0 and every strict terminal subtail
(d,T), there exists t in (d,T) such that

    -T3(t) > D(t) + M*E(t).

This excludes lower-order commutators as an independent obstruction
at arbitrarily high normalized rates. It neither proves favorable
third-order cancellation nor establishes regularity or singularity
existence. The remaining frontier is signed third-order transport.

## Signed third-order transport and the top Fourier frequency corridor

The previous kinetic-Fourier reduction eliminates order-one and order-two
transport as independent high-growth obstacles and proves that hypothetical
nonextension produces arbitrarily late signed top-order witnesses

    -T3(t) > D(t) + M E(t),  M >= 0.

The established, concrete Landau commutator bound is

    |T3(t)| <= 4398 C1 sqrt(E(t)) E3(t).

Using D3 <= D gives a new necessary physical Fourier corridor

    D3(t) + M E(t) < 4398 C1 sqrt(E(t)) E3(t).

Consequently E3(t)>0 and

    D3(t)/E3(t) + M E(t)/E3(t) < 4398 C1 sqrt(E(t)).

The ratio D3/E3 is the effective q=|xi|^2 frequency of the top
radial energy moment; it must lie strictly below the square-root H3
gradient scale at all these high-adversity times. The inequality is
necessary, not an automatic contradiction.

Conversely, if on some strict terminal tail the physical top Fourier
viscous block satisfies

    4398 C1 sqrt(E(t)) E3(t) <= D3(t),

then the required signed transport witness is impossible and the path
has a smooth continuation. This is a conditional spectral-dissipation
criterion; no proof that it holds on arbitrary solutions is claimed.

## Signed third-order Fourier fourth-moment corridor

Combining the already-proved signed top-transport witness and the concrete
Landau estimate yields at each high-growth witness, for M>=0,

    D3(t) + M*E(t) < K(t)*E3(t),
    K(t) = 4398*C1*sqrt(E(t)).

The previously proved physical Cauchy--Schwarz Fourier moment estimate

    E3(t)^4 <= E0(t)*D3(t)^3

implies (because E3(t)>0 and D3(t)<K(t)*E3(t)) that

    E3(t) < E0(t)*K(t)^3 <= E0(b)*K(t)^3

for every earlier kinetic anchor b<t. Since E3<=E, the original signed
corridor also implies M<K(t). Hypothetical nonextension forces these two
strict spectral restrictions at arbitrarily late times for any M>=0.

Conversely, if E3(t)>=E0(b)*K(t)^3 at every time on one strict terminal
tail, no such witness exists and the H3 path has a smooth continuation.
This is a *conditional* continuation criterion. The upper bound
E0(b)*K(t)^3 grows like E(t)^(3/2), while E3<=E. Hence the new upper
bound is generally weak at high energy; it is not a global regularity
proof and does not construct singularities. The unresolved physical
frontier remains signed third-order transport cancellation/localization.

## Signed third-order interpolation frontier

The exact third-order nonlinear PDE pairing splits into its genuine
12-term gradient commutator block G3 and 9-term interpolation commutator
block I3, after the already-established flux cancellation and pairing
integrability have been instantiated on the H3 energy-class slice:

    T3 = G3 + I3,
    |G3| <= 24*C1*sqrt(E)*E3.

The complete lower-order kinetic-Fourier absorption proved earlier that
hypothetical nonextension forces, arbitrarily late for each M>=0,

    D + M*E < -T3.

The exact signed split therefore forces at those same times

    D + M*E < 24*C1*sqrt(E)*E3 - I3.

When D>=24*C1*sqrt(E)*E3 at such a time, this becomes

    -I3 > M*E.

In particular, if the gradient block is absorbed by viscosity throughout
one strict terminal tail, hypothetical nonextension produces arbitrarily
late times with a genuinely negative interpolation pairing of arbitrarily
large normalized size. Conversely, if the actual interpolation pairing
and full physical dissipation jointly satisfy

    24*C1*sqrt(E)*E3 <= D + I3

throughout some strict terminal tail, nonextension is impossible and
smooth continuation follows. No universal sign of I3, automatic gradient
absorption, or unconditional continuation is asserted. This isolates an
explicit PDE cancellation target rather than extending the already weak
fourth Fourier-moment envelope.

## Individual signed third-order interpolation coordinate frontier

The exact signed interpolation block I3 comprises 81 physical
coordinate pairings P(j,i,k,l). No absolute values are taken.

The finite pigeonhole theorem establishes:

    I3 < 81*B
       => exists j,i,k,l: P(j,i,k,l)<B.

At a signed top-transport witness D+M*E<-T3, one obtains

    exists j,i,k,l:
      81*P(j,i,k,l) < 24*C1*sqrt(E)*E3-D-M*E.

Hypothetical nonextension forces these deficits arbitrarily late
on every strict terminal subtail.

If the explicit additional condition

    24*C1*sqrt(E)*E3 <= D

holds throughout a strict tail, nonextension forces for every R>=0
arbitrarily late coordinate pairings satisfying

    P(j,i,k,l) < -R*E.

Consequently a tail-wide lower bound P(j,i,k,l)>=-R*E
for all coordinate pairings, together with gradient absorption,
implies smooth continuation.

Neither extra condition is established for arbitrary solutions.
No unconditional continuation or existence of singularities is claimed.

## Signed individual third-order interpolation monomial frontier

The physical third-order interpolation pairing I3 is an 81-slot sum of
signed coordinate pairings P(j,i,k,l). Every P is itself the exact sum
of nine signed spatial-energy pairings of D³u with a product of two
D²u factors: three monomial types along each of the three velocity axes.
Existing Landau analytic data supply genuine integrability of every term.
No absolute values are taken when splitting the signed pairings.

Whenever signed third-order adversity satisfies

    D + M*E < -T3,

one of these 729 actual triple-product pairings is strictly below

    (24*C1*sqrt(E)*E3 - D - M*E)/729.

Under the explicit additional gradient absorption assumption

    24*C1*sqrt(E)*E3 <= D

throughout one strict terminal tail, hypothetical nonextension forces,
for every R>=0 on every later strict subtail, an actual spatial
triple-product pairing P_mono satisfying

    P_mono < -R*E.

Conversely, if that gradient absorption hypothesis holds and all 729
physical signed monomial pairings obey P_mono >= -R*E with a fixed
R>=0 throughout the tail, smooth continuation follows.

Neither extra condition is proved universally. This is a localized
necessary-condition and conditional criterion, not unconditional NS
regularity, nor a singularity construction.

## Signed H3 interpolation monomial mixed-partial symmetry

The first two D3u*(D2u D2u) interpolation monomial families are not
independent. Preterminal spatial C3 regularity supplies commutation of the
outer partials of the differentiated velocity, while the underlying D2u
product of the first monomial at (j,i,k,l,r) is definitionally identical
to the second monomial at (j,k,i,l,r). Thus the actual signed spatial-energy
pairings satisfy the exact identity

    P_0(j,i,k,l,r) = P_1(j,k,i,l,r).

The previously established adverse interpolation monomial witness can always
be represented by type 0 or type 2 after reorienting the outer indices.
Therefore no independent type-1 witness family is required. There are only
two inequivalent monomial types (486 index slots), instead of 729 formal
slots. The previous threshold of one 729th is retained, not strengthened.

Under the additional stated terminal gradient absorption hypothesis,
hypothetical nonextension forces arbitrarily adverse normalized type-0 or
type-2 pairings. A uniform normalized lower bound on just these two
families, together with gradient absorption, suffices for continuation.
This is exact mixed-partial symmetry, not a signed cancellation or a proof
of unconditional regularity.

## Cyclic mixed-partial symmetry reduces interpolation to one monomial type

Spatial C3 regularity of each velocity component implies the exact identity
between the previously distinct signed spatial-energy pairings:

    P_2(j,i,k,l,r) = P_0(j,l,i,k,r).

The other proved identity is

    P_1(j,i,k,l,r) = P_0(j,k,i,l,r).

Both are signed equalities, based on commutation of second and third mixed
partials; neither asserts a favorable sign or a cancellation estimate.
Every signed monomial witness in the nine-term block is therefore equivalent
to an actual type-0 pairing (243 formal ordered five-axis slots rather than
729 three-type slots). The threshold 1/729 is retained, not improved.

Whenever a physical signed top-transport witness satisfies D+M*E < -T3,
there is a type-0 pairing P0 with

    P0 < (24*C1*sqrt(E)*E3 - D - M*E)/729.

With the *additional* terminal-tail assumption 24*C1*sqrt(E)*E3 <= D,
hypothetical nonextension forces a type-0 pairing P0 < -R*E on arbitrarily
late subtail slices for every R>=0. A uniform lower bound on only the type-0
family, together with that gradient absorption, implies smooth continuation.
This does not prove either additional bound for arbitrary solutions and does
not settle global regularity.

## Full signed H3 interpolation aggregate has multiplicity three

The previous files proved exact signed mixed-partial identities for the
second and third interpolation monomial types, each as a permutation
of the first.

Reindexing the complete finite derivative sums yields

    I3(t) = 3 * A0(t),
    A0(t) = sum_{j,r,i,k,l} P0(j,i,k,l,r;t).

The original signed sum contains 729 monomial occurrences. The
canonical type-0 family contains 243 ordered five-axis slots, with
exact multiplicity three. No absolute values are taken.

Thus actual third-order transport satisfies

    T3 = G3 + 3*A0,
    |G3| <= 24*C1*sqrt(E)*E3.

At every physical signed witness D+M*E < -T3:

    D+M*E < 24*C1*sqrt(E)*E3 - 3*A0.

Hypothetical nonextension requires such aggregate deficits arbitrarily
late on every strict terminal tail.

A conditional continuation criterion is

    24*C1*sqrt(E)*E3 <= D + 3*A0

throughout one strict terminal tail.

This is an exact rewriting of the previous signed-interpolation
compensation criterion. It does not prove A0=0, favorable sign,
automatic gradient absorption, or unconditional regularity.

The outstanding PDE frontier is a substantive estimate or cancellation
for the canonical signed type-0 aggregate.

## Signed first-monomial six-channel exchange decomposition

The exact interpolation identity I3=3*A0 reduces the complete
third-order interpolation commutator to one monomial family.

Group by the two velocity-component indices:

    Q(j,r)=sum_{i,k,l} P0(j,i,k,l,r).

The skew part W(j,r)=(Q(j,r)-Q(r,j))/2 cancels exactly
under the complete exchange of velocity indices:

    sum_{j,r} W(j,r)=0.

The canonical signed aggregate is precisely six channels:

    A0=Qxx+Qyy+Qzz
       +(Qxy+Qyx)+(Qxz+Qzx)+(Qyz+Qzy).

Each individual Q entry contains 27 actual triple-product pairings.

Under the separate terminal gradient-absorption condition

    24*C1*sqrt(E)*E3 <= D,

hypothetical nonextension forces arbitrarily late times where at
least one of these six channels is below -R*E for every R>=0.

Uniform normalized lower bounds on all six channels, plus gradient
absorption, imply continuation.

This exchange-skew cancellation is algebraic. No favorable sign
or automatic analytic estimate for the six surviving channels
has been established.

## Joint gradient-excess and signed six-channel obstruction

Without assuming gradient absorption, the existing nonextension deficit at
M = 27R (R >= 0) yields, on each strict terminal subtail, a time with

either G - D > 9 R E or one of the six signed symmetric first-monomial
channels below -R E. Here G = 24 C1 sqrt(E) E3 and D is physical H3
dissipation. The proof combines the exact six-channel decomposition with
a finite real inequality; it does not establish an analytic estimate for
either side of the alternative.

If all six channels have the lower bounds -R E on a strict terminal tail,
nonextension forces a gradient excess larger than 9 R E. Conversely, an
upper bound G - D <= 9 R E forces one adverse symmetric channel. Both
upper and lower bounds together imply continuation, conditionally.

## Fixed seven-source H3 terminal obstruction

The joint signed obstruction offers seven possible adverse sources: one
H3 gradient-excess term and six exchange-symmetric first-monomial velocity
channels. The finite cofinal pigeonhole theorem fixes one index in
{0,...,6} such that, under hypothetical nonextension, on every strict
terminal subtail and for every nonnegative R, a time satisfies

    9 R E(t) < S_index(t).

Here S_0 = G-D, and S_1,...,S_6 are -9 times the three diagonal signed
channel values and the three symmetric off-diagonal channel pairs.

The selected index does not depend on either the subtail or R. The proof
uses only the previous joint alternative and E(t) >= 1.

Consequently, if each of the seven indexed sources individually admits
an eventual normalized upper bound (with its own terminal starting time
and its own nonnegative coefficient), continuation follows.

This is an obstruction classification, not an unconditional PDE estimate,
regularity result, or proof of finite-time singularity.

## Fixed directed ten-source H3 obstruction

The joint H3 nonextension obstruction can be refined from six symmetric
velocity channels to nine *ordered* velocity-component channels. Write
Q(j,r) for the complete signed first-monomial sum with velocity indices
(j,r), and E, D, G for H3 energy, dissipation, and the third-order gradient
bound respectively.

The ten scalar sources are S0=G-D; S1,...,S3=-9 Qjj for diagonal axes;
and S4,...,S9=-18 Qjr for the six off-diagonal ordered axis pairs.
The factor 18 is exact: Qjr+Qrj < -R E forces at least one of Qjr or Qrj
below -(R/2) E. Thus each alternative has the common threshold 9 R E.

Under hypothetical nonextension, a *single* fixed source among these ten
exceeds 9 R E arbitrarily late on every terminal subtail for every R>=0.
Separate eventual normalized upper bounds on all ten directed sources
imply continuation. This is an algebraic reduction, not an unconditional
PDE sign estimate or regularity proof.

## Fixed directed H3 normalized terminal sequence

The cofinal ten-source obstruction has a sequential strengthening.
For a hypothetical nonextendible H3 path, a single fixed index `i`
(one gradient-excess or one of nine ordered velocity channels) admits
actual times `tau(n)` with

    T - 1/(n+1) < tau(n) < T,
    n < S_i(tau(n)) / (9 E(tau(n))).

Thus `tau(n) -> T`, the normalized signed source tends to +infinity,
and the raw signed source tends to +infinity as well, since E >= 1.
Neither a particular source index nor a PDE estimate is established.
This is a conditional necessary asymptotic statement, not a proof of
singularity or unconditional continuation.

## Directed signed H3 source Landau energy-growth bridge

The established H3 Landau/Hölder closure bounds every genuine type-0 signed
interpolation monomial by 6 C1 sqrt(E) E3. Each ordered velocity component
Q(j,r) contains 27 such terms, hence

    |Q(j,r)| <= 162 C1 sqrt(E) E3.

The largest weight among the ten directed physical obstruction sources is
18, so each source satisfies

    S_i <= 2916 C1 sqrt(E) E3 <= 2916 C1 sqrt(E) E.

The fixed directed-source nonextension sequence therefore also satisfies,
eventually, n < 324 C1 sqrt(E(tau_n)). It follows that the same times witness
E(tau_n) -> +infinity. This synchronizes the signed-source obstruction with
physical H3 energy blowup, using proved Landau estimates, but does not prove
singularity or unconditional regularity.

## Directed-source H3 top-derivative energy synchronization

Retaining the physical third-order energy E3 (rather than replacing it by E)
in the proved per-monomial Landau estimate yields the ten-channel upper bound

    S_i(t) <= 2916 C1 sqrt(E(t)) E3(t).

Hypothetical nonextension selects a fixed directed source i and actual times
τ(n) -> T with 9n E(τ(n)) < S_i(τ(n)). Since E >= 1 and E = sqrt(E)^2,
the same times satisfy, eventually,

    n sqrt(E(τ(n))) < 324 C1 E3(τ(n)).

Consequently E3(τ(n)) -> +infinity on this *same* signed-source sequence.
This is a conditional necessary obstruction, not an assertion of singularity,
an unconditional continuation theorem, or an independent PDE estimate.

## Directed H3 top-energy / square-root energy obstruction

The fixed directed-source nonextension sequence has the sharper quantitative
rate n * sqrt(E(tau(n))) < 324 C1 E3(tau(n)) for all large n. Since E >= 1,
it follows along the same selected source sequence that

    E3(tau(n)) / sqrt(E(tau(n))) -> +infinity.

Consequently a uniform terminal estimate E3(t) <= K sqrt(E(t)) on any one
strict energy-class tail, for any fixed real K, forces smooth continuation.
This is a conditional H3 continuation criterion, not a proof of that bound,
or a claim that a nonextendible Navier--Stokes path exists.

## Fixed directed-source intrinsic top-frequency cascade

The fixed signed first-monomial source index and terminal times previously
satisfy E3(tau(n))/sqrt(E(tau(n))) -> +infinity. Because E >= 1, the same
times have E3(tau(n)) -> +infinity. The established fourth Fourier moment
inequality E3^4 <= E0 D3^3, kinetic antitonicity, and the existing
characteristic-frequency coercivity theorem then force

    Lambda3(tau(n)) = sqrt(D3(tau(n)) / E3(tau(n))) -> +infinity,
    D3(tau(n)) / E3(tau(n)) -> +infinity.

Both divergences occur on the very same selected signed-source sequence,
not on an unrelated positive-derivative selection. A fixed late-time ceiling
on Lambda3 is consequently a conditional sufficient criterion for smooth
continuation. Such a ceiling is not asserted automatically: the conclusion
is a necessary condition of hypothetical nonextension and does not prove
finite-time blowup or unconditional regularity.

## Fixed directed H3 source and physical critical clocks

Hypothetical H3 nonextension produces one fixed directed signed-source index
and terminal times tau(n) -> T for which the normalized signed source and
intrinsic top frequency both diverge. On these same exact times, all three
already-established physical critical-time inequalities hold eventually:

    1 <= 3 K^2 (E0(b)+1) (T-t)^2 Lambda3(t)^6,
    1 <= A_b (T-t)^2 (D3(t)/E(t))^3,
    8 <= A_b (T-t)^2 ((-T_H3(t)-E'(t))/E(t))^3,

where A_b = 3 K^2 (E0(b)+1) (4+3 E0(b))^3. The normalized full
balance gap is the exact physical PDE quantity 2 D(t)/E(t).

If, additionally, the gradient cost 24 C1 sqrt(E) E3 is absorbed by full
viscous dissipation on one terminal tail, the fixed source index is nonzero:
it is a physical ordered first-monomial velocity channel rather than the
gradient-excess source. This absorption premise is explicit and unproved in
general. No regularity or finite-time singularity is concluded unconditionally.

## Directed H3 physical signed-source dichotomy

Hypothetical H3 nonextension fixes one of ten sources and a single sequence
approaching the terminal time. This same sequence carries the three critical
physical clocks and divergent top-order characteristic frequency.

The source itself has an exhaustive physical signed classification:

1. If its index is zero, the normalized gradient excess
   (24 C1 sqrt(E) E3 - D)/(9 E) tends to +infinity.
2. Otherwise, for one fixed ordered velocity-component pair (j,r), the
   actual negative signed first-monomial ratio -2 Q(j,r)/E tends to +infinity.

The factor two accommodates both diagonal and off-diagonal channel weights.
The ordered pair does not vary with time or threshold. No gradient absorption,
velocity sign, or contradiction is assumed. Both branches are retained as
conditional necessary alternatives, not asserted to occur.

## Fixed signed source spectral corridor

The fixed physical H3 directed-source dichotomy can be sharpened without
assuming gradient absorption. Whenever its gradient-excess source is positive,
top viscous dissipation D3 <= D and Lambda3^2 = D3/E3 give the strict
physical inequality

    Lambda3(t)^2 < 24 C1 sqrt(E(t)).

Thus hypothetical nonextension selects one fixed signed source and one
terminal sequence carrying all three critical clocks, on which either this
spectral corridor eventually holds, or a single ordered first-monomial
velocity component has -2 Q(j,r)/E -> +infinity.

A spectral lower barrier Lambda3^2 >= 24 C1 sqrt(E), combined with the
conditional lower bound -2 Q(j,r) <= K E for every ordered component on one
strict terminal tail, excludes both nonextension alternatives and forces
smooth continuation. Neither extra bound has been proved automatically.
This theorem asserts neither finite-time blowup nor unconditional regularity.

## Fixed directed H3 spectral-gap magnitude alternative

If R >= 0 and the normalized physical gradient excess exceeds R,
then E3 > 0 and top dissipation D3 <= D imply

    9 R < 24 C1 sqrt(E) - Lambda3^2.

Hypothetical nonextension therefore forces either divergence of this
spectral gap on the fixed source sequence, or divergence of one fixed
ordered negative monomial ratio -2 Q(j,r)/E.

Both alternatives retain the three physical critical clocks. Uniform
terminal ceilings for both mechanisms suffice for continuation.
Neither ceiling is asserted unconditionally.

## Fixed directed H3 physical energy clock alternative

The gradient-excess branch satisfies Lambda3^2 < 24 C1 sqrt(E), while the
existing physical top-frequency clock enforces

    1 <= 3 K^2 (E0(b)+1) (T-t)^2 Lambda3^6.

Combining these inequalities gives the strict necessary physical clock

    1 < 3 K^2 (E0(b)+1) (24 C1)^3 (T-t)^2 sqrt(E)^3.

The energy exponent is E^(3/2), corresponding to an inverse-4/3 lower rate
for E(t) on this branch. Along the same fixed signed-source sequence,
nonextension alternatively forces one fixed ordered monomial -2 Q(j,r)/E
to diverge. Both alternatives retain the three established critical clocks.
A terminal energy-clock upper bound and signed-monomial ceiling jointly imply
continuation, but neither estimate is asserted to be automatic.

## Fixed directed H3 shifted physical energy clocks

For any fixed R >= 0, a normalized gradient-excess source larger than R
forces the strict spectral inequality

    Lambda3^2 < 24 C1 sqrt(E) - 9 R.

Together with the established kinetic-anchored intrinsic frequency clock,
this gives the shifted physical-time bound

    1 < 3 K^2 (E0(b)+1) (T-t)^2 (24 C1 sqrt(E)-9 R)^3.

On the fixed gradient-source nonextension sequence, the normalized signed
source diverges. Consequently this shifted physical clock holds eventually
for every fixed nonnegative R (the eventual time can depend on R). The
neutral alternative is divergence of one fixed negative ordered monomial
ratio -2 Q(j,r)/E on the same times. All three physical critical clocks are
retained. A finite terminal-tail ceiling on one shifted clock plus ceilings
on all signed ordered ratios forces continuation. None of these extra
ceilings are claimed to follow automatically from the PDE.

## Indexed directed H3 physical gradient gap

The original fixed-ten-source witness has n < S_i(tau(n))/(9 E(tau(n)))
for every natural n, not merely asymptotic divergence. Its very same
selected times satisfy all three established terminal physical critical
clocks eventually. This yields the exhaustive strengthened classification:

* Gradient index zero: for EVERY n, the physical top-frequency gap obeys
      9 n < 24 C1 sqrt(E(tau(n))) - Lambda3(tau(n))^2.
  The moving shifted physical energy clock with shift R=n is consequently
  satisfied eventually on precisely those terminal times.
* A nonzero directed index: ONE fixed ordered velocity-component pair
  (j,r) satisfies for EVERY n,
      n < -2 Q(j,r)(tau(n))/E(tau(n)).

This stronger indexed witness has no new PDE sign or regularity assumption.
It is a necessary dichotomy for hypothetical nonextension, and neither
branch is assumed excluded.

## Indexed signed H3 full dissipative and exact balance budgets

For the original fixed ten-source indexed nonextension witness
n < S_i(tau(n))/(9 E(tau(n))), the index-zero gradient source obeys,
at every selected time,

    9 n + D(tau(n))/E(tau(n))
      < 24 C1 sqrt(E(tau(n))) E3(tau(n))/E(tau(n)).

Unlike the previous top-frequency corridor, this inequality keeps the
actual full Navier--Stokes viscous dissipation D and the exact third-order
energy fraction E3/E. On a sufficiently late part of the same sequence,
the energy/transport balance identity G = (-T_H3-E')/E = 2 D/E gives

    18 n + G(tau(n))
      < 48 C1 sqrt(E(tau(n))) E3(tau(n))/E(tau(n)).

The three previously proved critical terminal clocks remain synchronized.
Alternatively one fixed ordered velocity-component monomial satisfies
n < -2 Q(j,r)(tau(n))/E(tau(n)) for every index n.

Both are necessary branches conditional on hypothetical nonextension; no
new PDE sign, dissipation ceiling, global regularity or blowup is inferred.

## Fixed directed H3 top-energy-share critical clock

On the fixed indexed H3 gradient-source sequence, the physical full
viscous budget retains the actual third-order energy fraction E3/E:

    9 n + D/E < 24 C1 sqrt(E) E3/E.

The exact H3 PDE gap satisfies G = (-T_H3-E')/E = 2 D/E. Combining its
existing third physical terminal clock

    8 <= A_b (T-t)^2 G^3,
    A_b = 3 K^2 (E0(b)+1) (4+3 E0(b))^3

with the full gradient budget forces, eventually on the SAME sequence,

    8 < A_b (T-t)^2 (2*(24 C1 sqrt(E) E3/E - 9*n))^3.

The neutral alternative remains a single fixed ordered velocity-channel
pair (j,r) with n < -2 Q(j,r)/E for every indexed time. The established
three critical clocks and top-order energy divergence are retained.
An eventual zero-shift top-share clock ceiling and a signed-channel
ceiling imply continuation, but neither assumption is automatic.
These statements do not establish finite-time singularity or unconditional
Navier--Stokes regularity.

## Universal asymptotic top-energy share on fixed directed source

The physical H3 endpoint interpolation and kinetic-energy monotonicity give,
for every b<t<T in the admissible H3 energy-class tail,

    E(t) <= 1 + 3 E0(b) + 3 E3(t).

Under hypothetical H3 nonextension the already-selected, indexed, fixed
signed-source sequence has E3(tau(n)) -> +infinity. Consequently, for every
fixed epsilon > 0, on that very same sequence, eventually

    E3(tau(n)) <= E(tau(n)) <= (3+epsilon) E3(tau(n)),
    E3(tau(n))/E(tau(n)) >= 1/(3+epsilon).

The leading factor three is independent of the chosen kinetic anchor, unlike
the earlier (4+3 E0(b)) comparison. The original index inequality, all three
critical physical clocks, and both alternatives (gradient full-dissipation
and top-share clock; or one fixed adverse ordered velocity monomial) remain
unchanged. This is a necessary feature of hypothetical nonextension and does
not exclude either source branch or establish an NS regularity theorem.

## Sharp radial polynomial improves fixed directed H3 top share

The elementary nonnegative Fourier-frequency identity

    1+q^3-q-q^2 = (q-1)^2(q+1) >= 0

integrates to the new physical endpoint inequality

    E1(t)+E2(t) <= E0(t)+E3(t).

Together with kinetic monotonicity, this gives the anchor-dependent
pointwise energy estimate E(t) <= 1+2E0(b)+2E3(t) for b<t<T.
On the SAME previously selected fixed directed signed-source witness,
E3(tau(n)) -> infinity, hence for each fixed epsilon > 0 eventually

    E3 <= E <= (2+epsilon) E3,
    E3/E >= 1/(2+epsilon).

The universal leading coefficient is improved from 3 to 2.
The original index witness, three physical terminal clocks and the
neutral gradient-versus-fixed-ordered-monomial alternative are retained.
This does not prove limiting share one, exclude either branch, or imply
unconditional Navier--Stokes regularity.

## Fixed directed H3 top-order share converges to one

The parameterized Fourier polynomial comparison for A >= 1 and q >= 0,

    q + q^2 <= (A+A^2) + (2/A) q^3,

integrates on real H3 path slices to

    E1 + E2 <= (A+A^2) E0 + (2/A) E3.

Kinetic monotonicity supplies E0(t) <= E0(b). Under hypothetical H3
nonextension, the original fixed directed ten-source indexed sequence has
E3(tau(n)) -> infinity; for each epsilon > 0 a sufficiently large fixed A
makes 2/A arbitrarily small, while the anchored E0 cost is negligible
relative to E3. Therefore on the SAME fixed-source terminal sequence,

    E(tau(n)) <= (1+epsilon) E3(tau(n)) eventually,
    E3(tau(n)) / E(tau(n)) -> 1.

This is a genuine improvement over the fixed constants 3 and 2. The indexed
source rate, three independent physical clocks and neutral exhaustive
alternatives (gradient full-dissipation/top-share clock, or a fixed adverse
ordered velocity monomial) are all retained unchanged. It neither excludes
a branch nor proves unconditional Navier--Stokes regularity or blowup.

## Universal left-terminal H3 top-energy concentration

The fixed-source sequence theorem showed E3(tau(n))/E(tau(n)) -> 1.
A stronger, previously established result gives E3(t) -> +infinity along
THE ENTIRE left-terminal filter nhdsLT T under hypothetical nonextension.

Combine that full-tail divergence with the parameterized physical Fourier
interpolation and monotonicity of zeroth-order kinetic energy. For every
fixed epsilon > 0, throughout some terminal subinterval,

    E(t) <= (1+epsilon) E3(t),
    E1(t) + E2(t) <= epsilon E3(t).

It follows that the top-order fraction E3(t)/E(t) tends to 1 as t approaches
T from the left, without choosing any special subsequence or source index.
The result therefore holds on all the previously constructed selected
terminal witnesses (gradient-excess OR fixed adverse signed monomial).
Neither physical source branch is excluded, and no unconditional smooth
continuation, finite-time blowup, or new PDE sign estimate is claimed.

## Full left-terminal H3 viscous dissipation concentration

The exact physical dissipation-block identification gives

    D = D0+D1+D2+D3 = E1+E2+E3+D3.

The preceding full-tail theorem forces E1+E2 = o(E3) under hypothetical
nonextension. Independently the previously established full characteristic
frequency cascade forces D3/E3 -> +infinity on the ENTIRE left terminal
neighborhood. Thus for every epsilon > 0, eventually

    D <= (1+epsilon) D3,
    D0+D1+D2 <= epsilon D3,
    D3/D -> 1.

This is an exact physical full-dissipation concentration statement. It
requires no new Navier--Stokes nonlinear transport-sign bound or source
selection and does not exclude either fixed directed-source alternative.
The conclusions are conditional necessary properties of nonextension, not
an unconditional regularity or finite-time singularity result.

## Full left-terminal intrinsic H3 frequency equivalence

The full-tail top-order energy and viscous dissipation share limits imply

    E3/E -> 1,      D3/D -> 1   as t approaches T from below,

under hypothetical nonextension of an admissible H3 path. Consequently

    (D3/E3)/(D/E) = (D3/D)/(E3/E) -> 1.

Thus the full physical squared-frequency scale D/E and top-order squared
frequency D3/E3 become equivalent in RELATIVE ratio. For every epsilon>0
that quotient eventually lies strictly between 1-epsilon and 1+epsilon.
This comparison holds along the whole left terminal tail AND the original
fixed indexed directed-source witness, preserving the three critical clocks
and both exhaustive gradient/signed-monomial alternatives.

The frequencies themselves need not differ by a bounded amount; this is
only a relative ratio limit. No new transport sign, realized singularity,
or unconditional continuation is asserted.

## Full left-terminal physical H3 frequency amplitude equivalence

The established full-tail squared-frequency comparison says

    (D3/E3) / (D/E) -> 1  as t approaches T from below

under hypothetical H3 nonextension. Its square root identifies the genuine
physical square-root frequency amplitudes

    Omega3 = sqrt(D3/E3),     Omega = sqrt(D/E),
    Omega3 / Omega -> 1.

On the entire left terminal tail, E3 and D3 are eventually positive, and
Omega is strictly positive. The amplitude ratio thus has a direct physical
meaning beyond the squared-frequency formulation. For every epsilon>0,
eventually 1-epsilon < Omega3/Omega < 1+epsilon. The same limit is attached
to the preselected fixed directed ten-source obstruction witness, preserving
its index, three physical clocks and neutral gradient/ordered-monomial
alternative. This is relative convergence, not convergence of Omega3-Omega
or an exclusion of hypothetical Navier--Stokes nonextension.

## Full left-terminal H3 characteristic-length equivalence

The conditional full-tail intrinsic-frequency limits and the two established
frequency amplitudes imply both canonical physical length scales tend to zero:

    ell_top = 1/sqrt(D3/E3) -> 0,
    ell_full = 1/sqrt(D/E) -> 0,

as t increases toward T along the ENTIRE left terminal neighborhood.
Whenever E3 and D3 are strictly positive, an exact algebraic identity gives

    ell_full/ell_top = Omega_top/Omega_full,

and hence ell_full/ell_top -> 1. A strict relative corridor of arbitrary
positive tolerance eventually holds. The same two length limits and relative
scale equivalence hold on the existing fixed directed-source witness, with
its critical clocks and both gradient/ordered-signed-monomial alternatives.
This does not establish an absolute length vs T-t rate, exclude either source
branch, or claim unconditional finite-time singularity or smooth continuation.

## Full physical H3 sixth-power length rate on terminal tail

The pre-existing conditional top characteristic-length estimate gives, on
sufficiently late physical times,

    ell_top(t)^6 <= 3 K^2 (E0(b)+1) (T-t)^2.

The recently established physical full/top length equivalence implies,
for every epsilon > 0, on a possibly later strict terminal interval,

    ell_full(t)^6 <= (1+epsilon)^6 * 3 K^2 (E0(b)+1) (T-t)^2.

Thus the full length inherits the top sixth-power (T-t)^2 terminal clock,
with an arbitrarily small RELATIVE coefficient loss but not a new lower
bound. On the SAME indexed directed ten-source obstruction witness,

    (n+1)^2 * ell_full(tau(n))^6
      <= (1+epsilon)^6 * 3 K^2 (E0(b)+1)

eventually. The original source index, physical critical clocks, and neutral
gradient versus fixed adverse ordered-monomial alternative are preserved.
All results remain conditional necessary conditions of H3 nonextension;
no unconditional regularity, singularity or transport-sign theorem is claimed.

## Full physical H3 dissipation cubic terminal clock

From the conditional full-physical sixth-power characteristic-length bound,
using ell_full = sqrt(E/D) and Omega_full = sqrt(D/E), one obtains for every
fixed epsilon > 0 eventually along the ENTIRE left terminal interval,

    1 <= (1+epsilon)^6 * 3 K^2 (E0(b)+1) * (T-t)^2 * (D/E)^3.

The proof converts the already established length estimate using exact
reciprocal-length duality and Omega_full^6 = (D/E)^3. No new transport-sign
bound is introduced. On the SAME fixed directed ten-source sequence, its
indexed sixth-power length rate gives

    (n+1)^2 <= (1+epsilon)^6 * 3 K^2 (E0(b)+1) * (D/E)^3.

The original source index, three physical critical clocks and the neutral
full-gradient versus fixed adverse ordered-monomial alternatives are kept.
These are necessary constraints under hypothetical H3 nonextension only;
neither regularity nor actual finite-time blowup is established.

## Sharp full H3 cubic terminal clock threshold

The previous full-physical cubic floor is quantified for every epsilon>0:

    1 <= (1+epsilon)^6 C_b (T-t)^2 (D/E)^3,
    C_b = 3 K^2 (E0(b)+1).

A continuity argument chooses epsilon small enough for ANY q<1 to deduce,
on the COMPLETE sufficiently late left terminal neighborhood,

    q <= C_b (T-t)^2 (D/E)^3.

This is the sharp asymptotic lower threshold (liminf at least one), not
an unjustified eventual inequality with q=1. Contrapositively, if a
fixed q<1 is violated arbitrarily close to T (recurrently, on every
strict subtail), the path admits a smooth continuation. The SAME fixed
indexed directed ten-source witness inherits the universal subunit floor
without changing its index, three physical clocks, or the gradient versus
fixed ordered adverse-monomial branches. No transport sign is presumed and
no unconditional Navier--Stokes regularity or blowup is asserted.

## Full H3 cubic-rate ceiling and kinetic anchor optimization

Write R(t)=(T-t)^2 (D(t)/E(t))^3 and define the kinetic coefficient
C_b=3 K^2 (E0(b)+1). Earlier formalized results give, conditional on
hypothetical nonextension, every strict subunit q<1 as an eventual lower
bound on C_b R(t) throughout the physical left terminal tail.

The direct contrapositive is a useful continuation criterion: if some finite
upper ceiling R(t)<=B holds eventually and C_b B<1, then a smooth extension
exists. The same result holds when the upper ceiling is known only along an
arbitrarily chosen sequence approaching T from below, including the already
fixed indexed ten-source directed obstruction witness; no new witness or sign
branch is required. The proof needs no additional transport estimate.

If the canonical H3 energy data hypothesis is available, kinetic energy E0
is antitone on the strict tail, so C_c<=C_b for any later anchor b<=c<T.
The associated cubic clock at the same physical time can only decrease with
a later anchor. This monotonicity claim explicitly requires the canonical
energy data hypothesis and is not asserted without it.

These are conditional continuation criteria, not unconditional regularity
or finite-time singularity results.

## Terminal kinetic-limit optimized H3 cubic clock

An explicit additional terminal hypothesis E0(t) -> L >= 0 as t approaches T
from below gives convergence of the anchored cubic clock coefficient

    C_b = 3 K^2 (E0(b)+1) -> C_* = 3 K^2 (L+1) > 0.

The previous anchored sharp threshold under hypothetical nonextension holds
for EVERY fixed b in (a,T) and EVERY q<1. Choosing a sufficiently late but
fixed anchor and adjusting q inside the proof yields the stronger limiting
coefficient threshold, on the WHOLE physical left terminal tail,

    q <= C_* (T-t)^2 (D(t)/E(t))^3,   for each q<1 eventually.

This is a terminal liminf lower bound; it does not assert an eventual bound
with q=1, and the kinetic limit itself is explicitly assumed, not inferred.
A terminal cubic-rate ceiling R(t)<=B with C_* B<1 forces smooth extension.
The same criterion holds along any preselected left-terminal sequence. The
original fixed ten-source witness also inherits the limiting-coefficient
sharp threshold with all physical clocks and both signed-source alternatives.
The results are conditional; neither finite-time singularity existence nor
unconditional smooth continuation is established.

## Canonical kinetic monotonicity closes terminal cubic limit

If canonical H3 energy data are present on (a,T), the exact kinetic energy
identity and integration-by-parts argument prove E0(t) antitone there.
Nonnegativity E0(t)>=0 and the monotone left-limit theorem then imply

    E0(t) -> L := inf {E0(s) : a<s<T} >= 0,  as t increases to T.

This automatically discharges the extra finite-limit hypothesis of the
previous terminal-kinetic coefficient theorem. Moreover L<=E0(b) at every
strict anchor. The limiting coefficient C*=3 K^2 (L+1) is <= each C_b.
Under hypothetical nonextension, each q<1 remains an eventual lower bound
on C* (T-t)^2 (D/E)^3 throughout the full physical left terminal tail.
An eventual, or preselected-sequence, ceiling R<=B with C* B<1 implies
smooth continuation. The original fixed ten-source index and physical
critical clocks, including both neutral PDE sign alternatives, are retained.
Canonical H3 energy data are an EXPLICIT additional hypothesis; the formal
result is not unconditional Navier--Stokes regularity or singularity.

## Full physical fifth-power H3 dissipation escape

The full physical H3 energy clock is known to diverge on the entire left
terminal neighborhood under hypothetical nonextension:

    (T-t) E(t) -> +infinity.

With canonical H3 energy data, the sharp terminal kinetic-coefficient cubic
clock also has an eventual positive floor, for example

    (1/2) <= C_* (T-t)^2 (D(t)/E(t))^3,
    C_* = 3 K^2 (L+1)>0, L=inf_{a<s<T} E0(s).

The exact algebraic product of the cubic rate and the CUBE of the full
physical energy clock is (T-t)^5 D(t)^3. Its value therefore tends to
+infinity along the ENTIRE left terminal neighborhood, not just a sequence.
This is an exponent-free statement that D grows faster than the critical
(T-t)^(-5/3) dissipation scale, conditional on hypothetical nonextension.
Any eventual finite fifth-clock ceiling, including a ceiling along ONE
preselected physical terminal sequence, forces smooth continuation. The
same original fixed directed ten-source witness has fifth-clock escape
while retaining its sharp kinetic clock, three critical clocks and both
neutral gradient/ordered signed-monomial source branches. This statement
assumes canonical H3 energy data and does not prove unconditional regularity
or any realized finite-time singularity.

## Top-order fifth-power H3 dissipation escape

On hypothetical nonextension and canonical H3 energy data, the full fifth
physical dissipation clock (T-t)^5 D(t)^3 tends to +infinity throughout the
entire strict left terminal tail. The independent physical dissipation
concentration theorem guarantees D(t) <= 2 D3(t) sufficiently late. Hence

    (T-t)^5 D(t)^3 <= 8 (T-t)^5 D3(t)^3,

and the true top-order fourth-derivative clock (T-t)^5 D3(t)^3 also tends
to +infinity along the ENTIRE physical tail. Any eventual finite bound on
that top clock, including a bound along an arbitrary PRESELECTED sequence
approaching T from below, forces smooth continuation under the same
canonical analytic assumptions. The original fixed ten-source indexed
witness retains BOTH fifth-clock divergences, the terminal-kinetic sharp
cubic floor, its three critical clocks and its exhaustive gradient versus
fixed ordered signed-monomial branches. All claims remain conditional;
neither sign alternative is excluded and no singularity is constructed.

## Relative equivalence of full and top fifth-power H3 clocks

Under hypothetical H3 nonextension, the exact top/full dissipation share
D3/D tends to one along the entire physical left terminal neighborhood.
Where t<T and D>0, the ratio of the two fifth-power viscous clocks equals

    ((T-t)^5 D3(t)^3)/((T-t)^5 D(t)^3) = (D3(t)/D(t))^3.

Hence this ratio tends to one on the ENTIRE terminal tail, and the relative
lower-block defect 1-(top fifth clock)/(full fifth clock) tends to zero.
For every positive epsilon, the full/top fifth clocks satisfy eventually

    (1-epsilon) (T-t)^5 D(t)^3 < (T-t)^5 D3(t)^3
      <= (T-t)^5 D(t)^3.

This is a relative, not absolute, negligibility statement for the lower
viscous blocks. Under the additional canonical H3 analytic data needed for
fifth-clock divergence, the original fixed directed ten-source witness
retains both fifth-clock escapes, the exact ratio/defect limits, the strict
relative corridor, the terminal kinetic cubic floor, three critical clocks,
and the neutral gradient versus adverse ordered-monomial alternatives.
No PDE sign is decided and no singularity is constructed.

## Recurrent lower-order viscous share continuation

On a hypothetical nonextendible H3 path, full-tail dissipation
concentration gives D3/D -> 1. The exact physical identity

    D(t) = D0(t) + D1(t) + D2(t) + D3(t)

then implies, wherever D>0, that the complementary lower-block share

    (D0(t)+D1(t)+D2(t))/D(t) = 1-D3(t)/D(t) -> 0

on the entire left terminal neighborhood. In contrast to the fifth-power
clock divergence theorems, this conclusion DOES NOT require the additional
CanonicalH3EnergyDataOnTail assumption. A strictly positive fixed lower
viscous fraction recurring arbitrarily late on every strict subtail thus
forces smooth continuation. The same criterion holds if a positive lower
fraction persists along any preselected sequence converging to T from below.
These contrapositives assume only the logged H3 path and physical energy
class, not an extra canonical energy-data hypothesis or transport sign.

The original fixed directed ten-source witness also inherits convergence
of the lower fraction to zero, with both divergent fifth-power clocks,
relative equivalence of their values, critical physical clocks, the sharp
terminal kinetic clock and both neutral gradient/signed-monomial branches.
That JOINT witness package retains canonical energy data because its prior
fifth-clock divergence statements require that extra hypothesis. Neither
branch is excluded and no finite-time singularity is constructed.

## Top-normalized lower viscous dissipation on the full H3 terminal tail

The full-terminal dissipation concentration theorem supplies the quantitative
estimate D0+D1+D2 <= epsilon D3 eventually for each epsilon>0, under
hypothetical H3 nonextension. Since D3 tends to +infinity along that same
left-terminal tail, the genuine lower/top physical ratio obeys

    (D0(t)+D1(t)+D2(t))/D3(t) -> 0,  as t increases to T.

This is stronger as a denominator normalization than the previously proved
lower/full dissipation fraction limit. It needs the physical preterminal H3
energy class but does NOT need a separate canonical H3 energy-data hypothesis
or any additional signed transport estimate. A fixed positive lower/top
viscous ratio recurring arbitrarily late, or persisting along any already
chosen terminal sequence, forces smooth H3 continuation. The existing fixed
ten-source witness carries the new zero ratio limit together with both
fifth-power clock divergences, their relative equivalence, the sharp kinetic
cubic floor, physical critical clocks, and the unchanged neutral source
alternatives. This joint witness package retains canonical energy data only
because the earlier fifth-clock divergence theorems required those data.
No singularity or sign resolution is asserted.
