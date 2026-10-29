# Canonical higher-order time budgets amplify physical PDE clock barriers

Base: `194722c1` — conditional higher radial spacetime budget and canonical clock compression.

For each m>=0, the existing full-window physical top-order Fourier moment floor
and an explicitly **additional** nonnegative interval-integrable real majorant
for that moment imply `delta_k * R_k^(2m+3) -> 0` at the same exact disjoint
canonical clocks. The exact quadratic-sharp PDE selector is

    delta_k = min((T-t_k)/4, 1, gap_k/(4*(Lambda_k+1)), sqrt(gap_k/(4*(Xi_k+1))))

with `gap_k >= R_k^3/4`. Since `R_k -> +inf`, the unit cap is eventually
incompatible with higher moment compression. For every eps>0, eventually

    R_k^(2m+3) * (T-t_k)/4 <= eps, OR
    (R_k^2)^m * R_k^6 <= 16 eps * (Lambda_k+1), OR
    ((R_k^2)^m)^2 * R_k^9 <= 16 eps^2 * (Xi_k+1).

The strengthened sixth and ninth radial powers are `2m+6` and `4m+9`.
The results hold on the same selected times and rates, without introducing a
new Fourier moment or identifying linear and quadratic PDE rates.

No upper envelope is obtained from standard H3 dissipation; that is the
explicit outstanding analytic assumption. The three branches are not excluded.
Neither a Navier-Stokes continuation theorem nor a contradiction is claimed.

Declarations:
- `h3Path_scalar_higherRadialLinearCap_forces_rate244`
- `h3Path_scalar_higherRadialQuadraticCap_forces_rate244`
- `h3Path_scalar_higherBudget_exactPDE_threeScale244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_forces_physicalPDERates244`

Local Lean compilation with pinned Lake toolchain required; packaging checks
are not a substitute for elaboration.
