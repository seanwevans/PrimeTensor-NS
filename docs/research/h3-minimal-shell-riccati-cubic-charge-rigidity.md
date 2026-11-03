# A fixed cubic cost of a low-anchor minimal-shell Riccati peak

**Baseline:** `cb719e7a` — force minimal H3 physical source peaks into anchor energy or Riccati terminal clock.

## New physical observation

The prior inverse-root comparison was ultimately reduced to the **remaining terminal time**. The stronger raw estimate obtained *before* replacing the elapsed peak time with the terminal horizon is:

    R² < 4 B E₃(t)   or   4 < (s-t) R,
    B = 4 K_Ric²+1,

at the actual Riccati witness `s` in the original physical minimal-shell window `s ∈ [t,t+δ]`. Therefore

    R² < 4 B E₃(t)   or   4 < δ R.

Because the inner frequency is literally `R=v(k)+1≥1`, the second branch implies

    2 < δ R³/2 = h3CriticalMinimalShellCubicWindowCost δ v k.

This >2 lower bound is **independent of the minimal outer cutoff, physical source envelope, terminal gap, or last-shell overshoot fraction**. It uses the original quadratic-sharp persistence window and does not enlarge it.

## Consequence for bounded certified cubic charge

Let `c_k=δ(v(k)) R_k³/2≥0`. A uniform finite partial-sum bound

    ∃ B, ∀ q, sum_{k<q} c_k ≤ B

implies `Summable c` by the existing mathlib `summable_of_sum_range_le`. Hence `c_k → 0`, in particular `c_k < 2` at all sufficiently large selected indices. The >2 alternative is then impossible, and every late Riccati-heavy window must begin with

    R_k² < 4(4 K_Ric²+1) E₃(t_k).

If instead `4(4 K_Ric²+1) E₃(t_k) ≤ R_k²` eventually, **Riccati-heavy windows themselves are eventually absent**.

The last theorem transports these conclusions onto exactly the same strictly increasing, pairwise-separated minimal Fourier cutoffs and positive kinetic carriers as the accepted source-horizon result. Its original sixth/ninth PDE alternative, positive shell witnesses, signed-gap accounting, and unbounded-cubic-charge alternative are retained.

## Logical limits

The bounded-total-cubic-charge premise does not follow unconditionally from the Navier–Stokes equations or from one arm of an exclusive sixth/ninth estimate without a separate proof. Conversely, merely excluding late Riccati peaks under bounded cubic costs does not prove a terminal L² trace: the surviving no-Riccati branch may lose energy through an unbounded sequence of windows or require unbounded signed-gap replenishment. This patch proves a **fixed local cost** and a **bounded-cost rigidity criterion**, not global smooth continuation.

## Exports

- `h3Critical_scalar_inverseRootPeak_anchorOrFixedCubicCharge`
- `h3Critical_minimalShellRiccatiWindow_anchorOrFixedCubicCharge`
- `h3CriticalMinimalShellRiccatiAnchorOrCubicChargeAt`
- `h3Critical_scalar_boundedNonnegativeCubicCosts_eventually_below_two`
- `h3Critical_minimalShell_boundedCubicCharges_force_lateRiccatiAnchors`
- `h3Critical_minimalShell_boundedCubicCharges_smallAnchor_excludes_lateRiccati`
- `h3Critical_noL2Trace_minimalShell_riccatiCubicChargeRigidity`

## Next missing estimate

One could now try to prove, using the signed energy balance and the disjoint certified cubic dissipation integrals, that repeated quadratic **anchor** energy peaks or the complementary unbounded cubic-charge branch forces a genuinely incompatible physical expenditure. That requires new control on how energy is replenished between windows; the present algebra does not imply it.
