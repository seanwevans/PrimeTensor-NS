# Signed sixth-flux: global packing from actual integrated physical surplus

**Pinned base:** `9b0693d53130ba0d7eb7e866515a70b48aa1eb33` — accepted integrated signed-surplus certified annular fork.

## Hard-math bridge

The accepted fork derives an actual third-order adverse transport time in a
strict original kinetic gap from the integral inequality

```
thirdFullKineticGapLowOrderMargin244 u eta x y
  < thirdFullKineticGapSignedSurplus244 u x y.
```

The accepted native-adverse packing theorem, separately, chooses actual
peak-carrying annuli and proves a terminal weighted packing ledger for a
supplied sequence of adverse observation times.

This patch joins the two **without supplying those times**. It defines
`ThirdFullKineticSignedLowMaxSurplusPackingActive244` using only the actual
integrated surplus, a strict relative-dissipation bound, the prescribed inner
radius cap, and exclusion of the original tenth-power residual at **every**
adverse sample in that gap. This last condition is an *explicit unresolved PDE
premise*, not a consequence of integrable full-H3 dissipation.

For every active gap, the previously proved signed-gap PDE integral comparison
produces an actual adverse time. A single classical time selection is then
fed into the already-verified native-adverse theorem. Its selected cutoff and
width remain tied to the genuine physical annular peak, exact kinetic width
and charged full-H3 gap integral.

For each active index `k` past one cofinal threshold, with energy anchor
`E0`, capped height `h>0`, and `K(E0)=1+192 sqrt(E0)*(sqrt(E0)+54E0)`,

```
h^2 / (32*K(E0)) <= (Q(k)+1)^11 * D(k).
```

The finite weighted ledger and frequency occupancy apply to the **same**
chosen `Q(k)` for every finite prefix:

```
sum_{k<m, active(k)} [h^2 / (32*K(E0)*(Q(k)+1)^11)]
  <= integral_a^T D_H3(t) dt

count_{k<m, active(k), Q(k)<=B} * h^2/(32*K(E0))
  <= (B+1)^11 * integral_a^T D_H3(t) dt.
```

The index predicate is explicitly restricted to the late tail on which the
native adverse certificate construction is valid. It is not assumed that any
gap is active, or that active events recur. The arbitrary choices for inactive
times and frequencies do not count toward the ledger.

## Remaining PDE obstruction

To turn this necessary packing condition into exclusion of a singular
scenario requires a physically proved recurrence of integrated surplus,
quantitative exclusion of the tenth-power residual and large relative gap
cost, and sufficient control on the rate of certified annular frequency
escape. Finite terminal H3 dissipation alone supplies none of these.

**Verification:** source and registration checks only; targeted Lean build is
required before commitment. No `sorry`, `admit`, or additional axiom.
