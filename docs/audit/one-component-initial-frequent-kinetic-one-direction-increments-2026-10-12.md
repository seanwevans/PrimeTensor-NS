# Initial physical trace from frequent kinetic anchors and ONE scalar direction

Base commit `d63288f3`:
`derive initial trace from frequent kinetic anchors and testwise Schwartz increments`.

## Main improvement

The previous criterion required scalar weak compatibility and integrable
positive-time momentum increments for every physical Schwartz test.

This route uses a SINGLE Hilbert scalar observable:

    f(t) = ⟪old(t), u(0)⟫.

Assume a real source g integrable on (0,b), and only strictly positive
scalar increments

    f(t) - f(s) = ∫ₛᵗ g(x) dx, 0<s,t<b,

plus ONE independent right-zero matching sequence σ such that

    f(σₙ) → ‖u(0)‖².

The existing scalar increment-to-right-limit theorem proves that
f(t) → ‖u(0)‖² on the entire right filter. No initial anchored FTC
or full weak-test family is assumed.

Independently, the checkpoint's frequent near-initial kinetic samples
along an unrelated right-zero sequence τ imply the exact positive-time
kinetic ceiling. The already-audited one-direction Radon–Riesz theorem
then yields strong physical L² right continuity and right kinetic-energy
continuity.

The same assumptions give the explicit *finite-time* squared error rate

    ‖old(t)-u(0)‖² ≤ 2 |∫₀ᵗ g(x) dx|,    0<t<b.

The conclusion contains both right traces and the existence of this
single concrete scalar source g with the rate.

## Declarations

- `h3Audit_initialOneDirectionPositiveIncrements_selfPairRightTrace`
- `h3Audit_initialPhysicalCeilingAndSelfPair_rightTraces`
- `H3AuditInitialFrequentKineticOneDirectionIncrementData`
- `h3Audit_initialOneDirectionIncrements_physicalSquaredError`
- `h3Audit_initialFrequentKineticOneDirection_physicalAndKineticRightTrace`

## Critical qualification

Reducing from all Schwartz directions to one initial-data direction
is a weakening of the *number* of test obligations but not an
automatic theorem from Schwartz distributional PDE tests:
the prescribed actual u(0) is an arbitrary L² vector and may not
be Schwartz. The source g and exact positive-time scalar increments
against that vector are independent regularity inputs. Likewise the
frequent kinetic samples and self-pair matching sequence must be
justified from the initial-value formulation. No terminal physical
vorticity H³ endpoint or unconditional smoothness is established.

## Required audit ordering

After extracting the ZIP, register root import and Contracts.lean checks
idempotently, then run

    python3 proof/generate_index.py
    python3 proof/generate_index.py --check
    python3 proof/check_fragment.py --all

before any `lake build`. The generated `proof/order.txt` is committed.
The ZIP preparation environment cannot compile Lean.
