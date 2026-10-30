# A critical eighth-power outer cap forces quadratic H³ energy cost under a q⁶ spacetime budget

Base commit: `ac08999e` — derive physical energy and outer cutoff costs of higher radial PDE rates.

The earlier precise physical theorem has four alternatives on the SAME original canonical windows, if the `m=2` physical extended top-order `q^6` radial moment admits a nonnegative real-valued interval-integrable upper envelope `F`: (i) the actual projected-source norm exceeds a proposed bound `S` at an attained time, (ii) weighted terminal-time compression, (iii) a square linear-rate cost involving genuine H³ energy and `(Q+1)^10`, or (iv) an eighth-power quadratic cutoff cost.

Assume *additionally*, all explicitly: `C(v k) <= S` eventually with `S>=0`; `(N(v k)+2)^8 <= D*(v k+1)^9` eventually (`D>=0`); and `eta <= (v k+1)^7*(T-t_k)/4` eventually (`eta>0`). Choose an `epsilon` satisfying `0<epsilon<eta` and `16*epsilon^2*(36*S^2*(D+256)+1)<1`. Such sufficiently small epsilons exist for fixed finite `S,D,eta`; the formal theorem retains the chosen tolerance explicitly.

The source branch is ruled out using the *actual* attained source envelope; the terminal compression branch contradicts `epsilon<eta`. For `R>=1`, `(R+1)^8<=256*R^9`. Thus the quadratic arm would give

    R^17 <= 16 epsilon^2 [36 S^2((Q+1)^8+(R+1)^8)+1]
          <= 16 epsilon^2 [36 S^2(D+256)+1] R^9 < R^9,

contradiction. The physical linear branch remains. The critical eighth-power cap gives the root-free (deliberately non-sharp) comparison `(Q+1)^10 <= D^2 R^18`. Since the second higher radial linear energy arm contains `R^20`, canceling `R^18>0` yields the explicit physical H³ energy burden

    R_k^2 <= 512 epsilon^2 (2304 E_3(t_k) S^2 D^2 + 1).

This genuinely improves the lower energy power over earlier critical cutoff energy results, but it is **conditional** on the additional q⁶ spacetime envelope, source ceiling, cutoff cap and noncompression. Nothing here derives these hypotheses from H³ dissipation alone, proves global smoothness, or eliminates possible concentration at terminal time.

## New Lean theorems

- `h3Path_higherBudget_criticalEighth_forces_outerTenth244`
- `h3Path_higherBudget_secondMoment_linear_forces_energyQuadratic244`
- `h3Path_higherBudget_secondMoment_outerCap_excludesQuadratic244`
- `h3Path_higherBudget_secondMoment_criticalBranches_force_energy244`
- `h3Path_noL2Trace_exactAnchor_secondHigherBudget_criticalOuter_energyCost244`

Compilation with the repository's pinned Lean/Mathlib toolchain must be done locally. The package performs only source and registrar checks offline.
