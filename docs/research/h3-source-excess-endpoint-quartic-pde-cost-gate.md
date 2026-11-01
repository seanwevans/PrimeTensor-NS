# Exact physical H³ source-clock cutoff versus PDE-cost obstruction

**Base:** `780d4262`, accepted endpoint-energy quartic source-width gate.

For the original selected source windows let

    H_k = M(v k) + q(v k)/κ > 0,    κ = 3(3 + C_L),
    J_k = E(t_k)-1,
    S_k = max(1,σ(v k)) + 1 ≥ 2,
    P_k = 4*q(v k) > 0,
    K_k = A_k²*B_k,
    r_k = S_k + sqrt(K_k)/P_k.

The existing endpoint theorem gives a genuine Riccati H³ energy observation
or, on the drain branch, `J_k > 0` and

    w_k ≤ J_k/H_k OR H_k ≤ J_k * r_k⁴.

The new elementary bridge analyzes **exactly** the second alternative,
without making a separate positivity assumption on the local PDE cost B_k.
If `K ≤ S²P²`, including the case `K<0`, then

    sqrt(K) ≤ S*P,    r ≤ 2S,
    H ≤ 16 J S⁴.

If that cutoff-only inequality fails, automatically

    K > S² P² ≥ 0.

Because the radicand is now positive, the true calibrated radius satisfies

    r P = SP + sqrt(K) ≤ 2 sqrt(K),
    H P⁴ ≤ 16 J K².

This yields the exact four-way source-window alternative:

1. A true Riccati-energy witness exists on the physical window.
2. The geometric width compresses: `w_k ≤ J_k/H_k`.
3. The source height is cutoff-paid: `H_k ≤ 16 J_k S_k⁴`.
4. The physical PDE coefficient satisfies BOTH
   `S_k² P_k² < A_k²B_k` and
   `H_k P_k⁴ ≤ 16 J_k (A_k²B_k)²`.

All local parameters and separated cofinal witnesses are inherited from the
committed endpoint-energy theorem. We do **not** assert that the noncompression
or cutoff-failure conditions hold, or that `H_k δ_k` diverges. The fourth
branch is a necessary quantitative physical PDE cost, not a resolution of
the remaining terminal regularity obstruction.

The package contains four declarations:

- `h3Critical_scalar_quarticRadius_cutoffOr_positivePDEThreshold`
- `h3Critical_scalar_quarticRadius_PDEcost_after_cutoffFailure`
- `h3Critical_scalar_quarticRadius_cutoffOr_quadraticPDECost`
- `h3Critical_noL2Trace_cofinalQuintic_endpointQuarticPDECostGate`

The registrar checks each declaration's source and registers eight
`#check` / `#print axioms` entries. Local Lean elaboration is necessary.
