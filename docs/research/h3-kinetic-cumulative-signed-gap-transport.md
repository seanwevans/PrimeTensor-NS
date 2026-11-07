# Cumulative physical signed H³ transport on exact kinetic annular PDE clocks

**Verified base commit:** `1d073127769b2748053a7049760ab15528f1b51a`.

## Main mathematical advance

The preceding theorem proves, on each exact kinetic annular persistence window
`I_k=[t_k,t_k+δ_k]`, a genuine physical viscous floor `D_3(s)>M_k/4` and
an exact integrated signed transport budget. It does **not** force either the
signed flux to have a sign or the physical H³ energy to decrease.

The new local lemma uses the actual differentiable H³ energy and a mean-value
point on the **same** closed window. At that point the accepted physical
`h3Critical_fullDissipationFloor_signedDrainOrRiccati` theorem applies.
Consequently each original window satisfies the explicit alternative

    some s in I_k has
      M_k/4 < κ sqrt(E_3(s)) E_3(s),

    OR

      E_3(t_k+δ_k) + q_k <= E_3(t_k),

where `q_k=δ_k M_k/4` and `κ=h3PathSqrtEnergyRiccatiCoefficient`.

The entire H³ dissipation charge is not assumed to be transported into raw
Fourier L² momentum. That would be an invalid derivative loss.

## Inter-window replenishment and finite cumulative account

Between adjacent original windows there is an actual gap
`[t_k+δ_k,t_(k+1)]` because strict separation is retained. The imported
compact-time theorem `h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic`
provides, on that exact gap,

    E_3(t_(k+1)) - E_3(t_k+δ_k)
      <= integral_[t_k+δ_k,t_(k+1)] max(0,-Tr_3(s)-2D_3(s)) ds.

No global signed-flux integrability is inserted. Applying the already proved
finite drain/replenishment telescoping theorem yields, for every `m`,

    exists k <= m and s in I_k with
      M_k/4 < κ sqrt(E_3(s)) E_3(s)

    OR

    (sum_{k=0}^m q_k) + 1
      <= E_3(t_0)
           + sum_{k=0}^{m-1} integral_gap_k max(0,-Tr_3-2D_3).

The `+1` is justified by the established physical energy lower bound
`1 <= velocityH3EnergyAt`, not by a terminal H³ energy trace.

The final theorem attaches this cumulative accounting to the original
no-terminal-H³-trace kinetic-selected windows. It preserves on a **single**
existential sequence: strict cofinality, actual cutoffs and PDE-selected
widths, disjointness, global extended viscous packing, vanishing absolute
projected-source action, and uniform moving annular raw kinetic tightness.

## What remains genuinely open

This is a finite cumulative signed balance, not a contradiction and not a
Navier–Stokes continuation theorem. The positive integrated signed
replenishment surplus may remain large even though the *unweighted*
physical projected-source L¹ action and raw Fourier annular masses vanish.
The missing analytic inequality is a bound on differentiated H³ signed
transport, or a PDE mechanism excluding its replenishment, on the same
moving annuli. Such a bound cannot be obtained by merely replacing the
third-derivative Fourier weights with order-zero kinetic norms.

## Declarations

- `thirdFullPhysical_kineticWindow_riccatiOrSecantDrain244`
- `thirdFullPhysical_kineticDisjoint_cumulativeSignedGapBudget244`
- `thirdFullPhysical_noH3Trace_kineticCumulativeSignedGapObstruction244`

No new axioms or proof placeholders. Lean elaboration must be checked in the
pinned local Lean/mathlib environment; static checks are not compilation.
