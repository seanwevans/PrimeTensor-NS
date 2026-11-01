# Fivefold H³ source windows: physical anchor versus temporal excursion

**Base:** `94197332` (accepted cofinal attained source/spectral compact-window maxima).

## Why a maximum alone is not enough

The accepted cofinal theorem chooses maximizers `sSource(k), sState(k)` on the
**original** closed physical windows `[t_k, t_k+w_k]`; their locations need
not belong to the shorter calibrated dissipation windows `[t_k,t_k+delta_k]`.
The new bridge removes this uncertainty without changing any selected
witnesses or assuming a terminal-uniform temporal modulus.

The real Hilbert-space triangle inequality gives, at the *actual* source
peak `t_k`:

    ||U(sState_k)|| <= ||U(t_k)|| + ||U(sState_k)-U(t_k)||
    ||R(sSource_k)|| <= ||R(t_k)|| + ||R(sSource_k)-R(t_k)||.

Consequently the spectral branch `S_k<3+2*C_L*||U(sState_k)||` forces

    S_k<3+4*C_L*||U(t_k)|| OR
    S_k<3+4*C_L*||U(sState_k)-U(t_k)||.

The source branch `P_k²<24*||R(sSource_k)||²` forces, by the squared triangle
inequality and `(a+b)²<=2(a²+b²)`,

    P_k²<96*||R(t_k)||² OR
    P_k²<96*||R(sSource_k)-R(t_k)||².

Here `S_k=max(1,sigma(v k))+1`, `P_k=4*q(v k)`, and `C_L` is the accepted
nonnegative Leray energy coefficient. The factor `96` is the exact factor
`24 * 2 * 2` from the squared two-component split. Both differences are
actual differences of physical Hilbert-valued paths, not auxiliary ceilings.

## Exact cofinal obstruction

On the same separated cofinal fivefold peak windows and with the same exact
`A_k,B_k` formulas, certified peak dissipation floors, calibrated widths,
attained maxima, and ENNReal summed viscous cost, one of the following
holds for every k:

1. A Riccati-energy witness on the calibrated interval;
2. Original window compression `w_k <= (E(t_k)-1)/H_k`;
3. Cutoff-paid source height `H_k <= 16(E(t_k)-1)S_k^4`;
4. Spectral norm at the anchor exceeds the new threshold;
5. Spectral-state time increment exceeds the new threshold;
6. Projected momentum source at the anchor exceeds the quadratic threshold;
7. Projected-source time increment exceeds the quadratic threshold;
8. Instantaneous physical H³ dissipation pays `P_k²<8D(t_k)`;
9. The source floor itself pays `P_k²<8H_k`.

No branch is asserted to occur universally; no time-Lipschitz estimate,
positive uniform lower window width, or integrable terminal dissipation is
introduced. In particular, a temporal excursion does *not* by itself imply
concentration inside the shorter calibrated interval. Converting such an
excursion into a width constraint requires a physical time-modulus estimate.

## Lean declarations

- `h3Critical_norm_le_anchor_add_excursion`
- `h3Critical_scalar_linearMax_anchorOrExcursion`
- `h3Critical_scalar_quadraticMax_anchorOrExcursion`
- `h3Critical_attainedPhysicalPDE_anchorOrTemporalExcursion`
- `h3Critical_noL2Trace_cofinalFivefold_anchoredTemporalExcursionGate`

Five `#check` and five `#print axioms` entries are registered. Pinned local
Lean elaboration and full baseline build are required; static tests alone do
not prove elaboration success.
