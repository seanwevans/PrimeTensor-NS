# Automatic integrated signed H³ gap replenishment without terminal dissipation integrability

Base checkpoint: `ff24fb9e`, accepted cofinal integrated signed transport budget
with explicit **local compact-gap** integrability premises.

## Key new mathematical simplification

Let `E(t)=velocityH3EnergyAt u t`, `D(t)=velocityH3DissipationAt u t` and
`Tr(t)=velocityH3TransportDerivativeAt u t`. The accepted physical H³
Navier–Stokes balance is

    E'(t) + 2D(t) = -Tr(t).

Therefore, throughout every strict-time gap,

    max(0, -Tr(t)-2D(t)) = max(0, E'(t)).

This equality means that **separate local integrability of Tr and D is
unnecessary** to integrate the signed *positive* transport surplus.

The repository already proves
`h3Path_canonicalEnergyDerivative_intervalIntegrable_automatic244`:
`E'` is interval-integrable on every compact strict-time subinterval,
using the canonical continuous H³ energy, compact Landau majorant and the
one-sided derivative-integrability lemma. Crucially, the theorem does not
assume `IntervalIntegrable D volume a T`.

The real positive part satisfies

    max(0,z) = (|z|+z)/2.

The interval-integrability of `E'`, `|E'|` and their linear combination
therefore proves automatic local integrability of
`max(0,-Tr-2D)` by congruence on the interval's interior. No global or
local integrability of Tr and D separately is needed.

## Automatic exact integrated transport charge

On any compact strict-time gap `[x,y]`, with a<x<y<T, the earlier physical
integrated majorant and FTC now apply unconditionally:

    E(y)-E(x) <= integral(x,y) max(0,-Tr(s)-2D(s)) ds.

For the **same cofinal quintic source-excess windows** selected from the
no-physical-L²-terminal-trace branch, let `start_k=t(v_k)` and
`end_k=start_k+delta_k`. Let

    H_k = M(v_k)+q(v_k)/[3(3+C_L)].

For every finite m, the new cofinal theorem supplies either a true
large-Riccati-energy witness on some window k<=m, or

    sum_(k<=m) H_k delta_k + 1
      <= E(start_0)
        + sum_(k<m) integral_(end_k)^(start_(k+1))
            max(0,-Tr(s)-2D(s)) ds.

Both required local gap-integrability statements are now returned as
**proved witness properties**, rather than supplied as hypotheses.
The original windows and their endpoint drain alternatives are unchanged.

## Limits

This closes an *analytic regularity premise* of the previous theorem; it
does not bound the cumulative gap integral independently of the source
margins, exclude large Riccati-energy windows, or establish global
Navier–Stokes regularity. The next hard obstruction is precisely an upper
budget for the positive signed transport replenishment, or a PDE estimate
forcing enough energy growth to contradict other established controls.

Lean declarations:

- `h3Critical_scalar_positiveDerivative_intervalIntegrable`
- `h3Critical_physicalGap_signedPositiveTransport_intervalIntegrable_automatic`
- `h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic`
- `h3Critical_noL2Trace_cofinalQuintic_automaticIntegratedSignedGapBudget`

Compile using the repository's pinned Lean/mathlib toolchain. Static
checks do not establish Lean elaboration.

## Local elaboration correction (fix1 at `ff24fb9e`)

The `EqOn` goals for interval-integrability congruence are equalities of
function applications. Lean did not rewrite pointwise values until these
were beta-reduced to scalar equalities. The first proof now uses an explicit
`change` before the positive/negative cases; the physical transport proof
uses `congrArg (fun z : ℝ => max 0 z)` on the accepted exact signed balance.
No declarations, hypotheses, or mathematical conclusions have changed.
