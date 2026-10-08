# Continuation contract review

Reviewed source base: `968e6cda`. This is a review of the named contracts and
routes below, not a claim that every mathematical dependency has been audited.
The accompanying `tools/audit/Contracts.lean` prints their actual Lean types
and selected transitive axiom dependencies. The path-specific restart audit passed at `968e6cda`. This revision adds the
closed BKM theorem and the terminal-tail sufficient conditions. The additional
commands await a local baseline; exact emitted axiom lists and CI results
remain separate evidence.

## What the endpoint theorem says

The public theorem in [Clock/Endpoint.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Terminal/Clock/Endpoint.lean)
retains the following inputs:

| Input | Content that matters |
|---|---|
| `hH3` | Preterminal Navier–Stokes admissibility, H³ integrability at every strict time, and continuity of the scalar H³ energy at every strict time. |
| `hClass` | An interior tail start, spatial C⁵ velocity on the tail, and a pressure witness satisfying the preterminal PDE and spatial C⁴ regularity. |
| `hPhysical` | For one fixed vorticity component, both complementary velocity components have pathwise strong spectral H³ endpoints. Each endpoint representative agrees with the corresponding velocity component at T. |
| `hCauchy` | The total raw Fourier velocity L² square defect becomes arbitrarily small for every pair of strict times sufficiently close to T. |
| `hε` | A strictly positive threshold. |

Strict-time regularity is different from a uniform terminal bound. The named
strong endpoint property is an explicit convergence assumption, not merely a
label for spatial smoothness. The Cauchy assumption quantifies over pairs of
times near T; an identity with physical L² distances only reformulates it.

The conclusion is a disjunction: an extension package exists, or there is a
terminal sequence carrying bad-cone mass, the quantitative critical alternative,
and higher-radial universal escape. The proof splits on existence of the
extension and invokes the no-extension theorem in the other case. It does not
eliminate that second case or construct a blow-up example.

The quantitative critical alternative in
[Clock/QuantitativeAlternative.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Terminal/Clock/QuantitativeAlternative.lean)
has five disjuncts, grouped into three families:

1. A sampled normalized higher-radial moment has a finite positive lower
   threshold on a subsequence, at either of the two forcing-order families.
2. H³ energy escapes to infinity along a subsequence.
3. A higher-radial witness carries critical forward-width thresholds, again
   at either forcing-order family.

The critical threshold package supplies eventual bounds for every strict
subcritical coefficient. It excludes subcritical eventual ceilings and bounds
any finite nonnegative limit from below. It does not assert convergence or an
eventual lower bound at the exact critical coefficient. These quantifiers and
the branch alternatives remain unchanged by the path and bundle refactorings.

## Extension package and actual restart

[Preterminal/Extension.lean](../../PrimeTensor/Fluid/Vorticity/Preterminal/Extension.lean)
defines `SmoothContinuationExtension` using agreement before T, terminal
vorticity balance, and terminal cascade regularity. Those fields do not explicitly
supply a later time S > T with velocity and pressure solving Navier–Stokes on
(0,S). Keep the theorem name separate from the content of these fields.

[Continuation/Restart.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/Restart.lean)
defines the stronger `H3ControlProducesRealRestart`: preterminal PDE admissibility
and terminal H³ control yield velocity, pressure, and S > T, with agreement
before T, a PDE solution on (0,S), spatial C³ regularity, and continuity of the
third spatial jet at T. The existing bridge maps this result into the extension
package. That direction does not establish the converse.

## Two existing routes to real restart

| Route | Retained premise | What it returns |
|---|---|---|
| `h3ControlProducesRealRestart_of_unitViscosityCanonicalEnergy` | `EnergyClassProducesCanonicalH3Data` | `H3ControlProducesRealRestart` |
| `h3ControlProducesRealRestart_of_unitViscosityEnergyContinuity` | `EnergyClassProducesCanonicalH3EnergyContinuity` | The same `H3ControlProducesRealRestart` |

The first premise asks every high-order energy-class tail to supply canonical
H³ integrability, local C¹ energy regularity, and the energy-estimate analytic
package. The second only asks every such tail to supply scalar energy continuity
on each compact interval [a,b] within the tail. Both are universally quantified
interfaces. Printing or invoking a theorem with one of these premises does not
prove the premise.

`energyClassProducesCanonicalH3EnergyContinuity_of_canonicalData` already proves
that full canonical data implies the weaker continuity interface. Its proof
projects local C¹ regularity to continuity. The original contract audit printed
only the stronger route; the expanded audit includes the weaker route and this
projection, avoiding an overstatement of what continuation needs.

Sources: [canonical data](../../PrimeTensor/Fluid/Vorticity/H3/Energy/Closure.lean),
[minimal continuity](../../PrimeTensor/Fluid/Vorticity/Continuation/Restart/Endpoint/Third/Energy/Continuity/Minimal.lean),
and [continuity restart closure](../../PrimeTensor/Fluid/Vorticity/Continuation/Restart/Endpoint/Third/Energy/Continuity/Tail/Control/Closure.lean).

## The path-specific restart is already closed

The further trace reaches
[H3/Restart/Direct.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Restart/Direct.lean),
which already implements the path-specific argument considered in the previous
review. There is no new restart theorem to prove here:

- `LoggedPreterminalH3PathAdmissible.canonicalH3EnergyContinuousOnTail`
  restricts `hH3.energy_continuousAt` to each compact [a,b] with a strict
  preterminal left endpoint.
- `h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_h3Path_tailControl`
  chooses a sufficiently late anchor inside the controlled tail. Its remaining
  interval is smaller than the positive restart radius, and it carries the
  path's scalar energy continuity.
- `h3PathRealRestart_of_tailControl` uses those data to produce velocity,
  pressure, and S > T with the full real-restart conclusion.
- `h3PathH3ControlProducesExtension` then projects the real restart to the
  existing extension package.

The real-restart theorem's only explicit hypotheses, apart from its field and
terminal-time parameters, are `LoggedPreterminalH3PathAdmissible u T` and
`TerminalTailH3Control u T`. It does not assume either global energy-class
continuity interface, the full canonical-data package, a high-order energy
class, or the endpoint theorem's strong-vorticity/Cauchy assumptions.

This corrects the scope of the previous follow-up: the universal interfaces
remain premises of their general-purpose routes, but are not an outstanding
obligation for this already formalized path-specific restart. The additional
contract commands print all four stages and their selected axiom dependencies.
No library source has been changed to obtain this result.

## Existing sufficient controls and the current boundary

Tracing beyond the older `Analysis/Reduced.lean` route reaches
[H3/BKM/Closure.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/BKM/Closure.lean).
`h3PathVorticityL1LinfProducesExtension_closed` proves the path-specific BKM
criterion without an extra canonical-analysis premise. The orderwise energy
identities have already been assembled. The older reduced-analysis theorem
remains a valid conditional route, but its premise must not be presented as
an outstanding requirement of the later closed BKM theorem.

| Existing route | Sufficient input beyond the admissible H³ path | Result |
|---|---|---|
| Closed BKM | `VorticityL1LinfControl u T` | Extension package |
| Tail-local BKM | Energy-class tail and an integrable common vorticity envelope on that tail | Extension package |
| Scalar energy ceiling | Interior tail start, M ≥ 1, and canonical H³ energy ≤ M at every time in [a,T) | `TerminalTailH3Control` |
| Positive logarithmic growth | Energy-class tail and integrability of `max 0 (deriv (log ∘ energy))` on (a,T) | `TerminalTailH3Control` |

`VorticityL1LinfControl` is explicitly an integrable scalar envelope bounding
all three classical vorticity components at every spatial point and strict
time. Its definition does not invoke a spatial supremum or essential supremum.
The tail-local version only needs this control on one terminal energy-class
tail. The scalar routes feed the already closed direct real restart, so their
control conclusion is enough for an actual PDE restart beyond T.

Sources: [vorticity control](../../PrimeTensor/Fluid/Vorticity/L1Linf/Control.lean),
[tail-local BKM](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Vorticity/Tail/Integrability.lean),
[energy ceiling](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Terminal/Dichotomy.lean),
and [positive logarithmic growth](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Terminal/Log/Alternative.lean).

The named global a-priori input is
`H3PathPreterminalNavierStokesForcesVorticityL1Linf` in
[Vorticity/Apriori/Frontier.lean](../../PrimeTensor/Fluid/Vorticity/Continuation/H3/Vorticity/Apriori/Frontier.lean).
It asks every admissible H³ path to supply the required vorticity control. The
file defines that proposition and proves continuation assuming it; defining the
proposition does not establish it. This audit does not prove any of the
sufficient bounds in the table for every admissible path.

## Consolidation checkpoint and next mathematical work

The engineering pass has established full source build coverage through the
root plus five standalone targets, repaired the documentation index and stale
standalone proofs, preserved historical imports during a bounded path migration,
and added two small limit bundles with unchanged legacy interfaces. CI now
runs the full audit. The jet cardinality proof uses kernel-checked arithmetic.
User-confirmed local baselines support those checkpoints; this report does not
claim an independently observed successful CI run.

The contract pass now distinguishes the already closed path restart and BKM
criterion from their retained control inputs and the stronger endpoint
assumptions. No further proof packaging is needed to state this boundary.

The next mathematical task should target an actual estimate: trace a candidate
terminal-tail vorticity envelope or positive logarithmic energy-growth majorant,
and identify exactly which existing hypotheses establish its integrability.
Use the named sufficient criteria above as the acceptance condition. Do not
introduce another equivalent control proposition as a substitute for that
estimate, or infer a terminal bound from strict-time continuity alone.

The strong endpoint and raw L² Cauchy inputs of the quantitative endpoint
alternative remain a separate line of inquiry. Its escape branches also
remain possible conclusions of that theorem; no contradiction or blow-up
existence claim follows from the audit. Further path shortening can proceed
independently when justified by navigation needs, preserving compatibility.
