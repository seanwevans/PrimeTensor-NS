# Sharp fourth-power H³ energy cost from the critical q⁶ budget

Base commit: `e6eaf7b6` — force quadratic physical H³ energy cost under critical higher radial budget.

The previous critical-cutoff bound `(Q+1)^10 ≤ D² R^18` is valid but loses more than six powers of `R`. From the **same** physical cap `(Q+1)^8 ≤ D R^9` one obtains instead the exact root-free fourth-power comparison

    ((Q+1)^10)^4 = ((Q+1)^8)^5 ≤ (D R^9)^5 = D^5 R^45.

The `m=2` linear energy alternative is `R^20 ≤ 512 ε² (2304 E₃ S² (Q+1)^10 + 1)`. Because `Q+1≥1` and `E₃,S≥0`, bound its RHS by `512 ε² (2304 E₃ S²+1)(Q+1)^10`. Raising this inequality to the fourth power and cancelling `R^45>0` gives

    R^35 ≤ (512 ε²)^4 (2304 E₃ S²+1)^4 D^5.

The same canonical existence theorem is reconstructed using the original witnessed interval-integrable physical `q⁶` top moment upper envelope, eventual intrinsic source ceiling `C(vk)≤S`, critical outer cutoff cap, noncompressed `R^7(T-t)/4≥η`, and sufficiently small positive `ε` excluding the quadratic branch. All are **extra explicit hypotheses**; they are not consequences of the H³ dissipation assumption. The canonical first-crossing radii, source-attaining times, disjoint windows and PDE clocks are the same.

Thus fixed positive finite ε,S,D imply an at-least-order `R^(35/4)` physical H³ energy burden (in the asymptotic sense). If S or D vanishes, these premises would eventually be inconsistent with R→∞. Neither case proves unconditional regularity.

New theorems:
- `h3Path_higherBudget_criticalEighth_forces_outerTenthFourth244`
- `h3Path_higherBudget_secondMoment_linear_forces_sharpEnergyFourth244`
- `h3Path_higherBudget_secondMoment_criticalBranches_force_sharpEnergyFourth244`
- `h3Path_noL2Trace_exactAnchor_secondHigherBudget_criticalOuter_sharpEnergyFourth244`

Offline structural checks only; full Lean compilation must run with the pinned Lake toolchain.

## Local Lean correction (fix1)

The fourth-power comparison now derives `x+1 <= x+(Q+1)^10` using `linarith only [hQten]` instead of applying `add_le_add_left` in an incompatible addition order. The theorem statements and assumptions are unchanged.
