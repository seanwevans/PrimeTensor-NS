# Exposing genuine physical PDE factors in fivefold cofinal source windows

**Accepted base:** `fe6fac83` — source-excess quartic PDE factor escape.

## Missing transport of physical identities

The accepted `h3Critical_noL2Trace_cofinalQuintic_quarticPDEFactorEscape`
proves the scalar constraint on chosen cofinal coefficients `A k`, `B k`,
but an earlier selection theorem existentially discharged their *physical
definitions*. This is a genuine information loss: no subsequent theorem can
use those definitions without rebuilding the local choice.

The new cofinal result returns all of `i,t,w,v,C,E,A,B,δ` from the **same
fivefold-source construction**, with exact identities

```
A_k = 3 + C_L * (‖U(t_k)‖ + E_k)
B_k = 12*C_k² + 2*(D(t_k) + H_k)
H_k = M(v_k) + q(v_k) / [3(3+C_L)]
```

For **every** `s∈[t_k,t_k+w(v_k)]`, it also retains actual compact-window
ceilings `‖projectedMomentumSource(s)‖ ≤ C_k` and
`‖actualSpectralVelocity(s)‖ ≤ E_k`, with `C_k,E_k≥0`.
Thus `A_k≥3` and `B_k≥0` follow from actual physics.

The local calibrated radius remains

```
r_k = max(1,σ(v_k)) + 1 + sqrt(A_k² B_k) / [4*q(v_k)]
```

and the selected positive duration still obeys
`min(w(v_k), r_k⁻⁴) ≤ δ_k ≤ w(v_k)`.

## Final conditional alternative

The exact endpoint energy identity and previously proved square-root quartic
threshold give, on each selected physical source window, either:

1. An actual Riccati-energy witness in `[t_k,t_k+δ_k]`;
2. `w_k ≤ J_k/H_k` (geometric compression);
3. `H_k ≤ 16 J_k S_k⁴` (cutoff pays);
4. **Both** `S_k²P_k² < A_k²B_k` and
   `H_k P_k⁴ ≤ 16 J_k(A_k²B_k)²`, together with a genuine physical
   subalternative:

```
S_k < 3 + C_L*(‖U(t_k)‖ + E_k)
OR
P_k² < 12*C_k² + 2*(D(t_k) + H_k)
```

where `S_k=max(1,σ(v_k))+1`, `P_k=4q(v_k)`, and
`J_k=velocityH3EnergyAt(u,t_k)-1>0` on the endpoint-drain branch.

This preserves the exact projected-momentum-source and spectral-velocity
factors but proves no terminal uniform bound, rate divergence, or
Navier–Stokes continuation. The local source ceilings are only compact-time
witnesses and may grow without limit.

## Audit

Two declarations:
- `h3Critical_fivefoldWindow_exactPhysicalPDEFactorGate`
- `h3Critical_noL2Trace_cofinalFivefold_explicitPhysicalPDEFactorGate`

The registrar adds two checks and two axiom audits. Lean elaboration is
required in the pinned toolchain; static packaging is not a proof check.

The cofinal conclusion also retains the **original disjoint full-H³
physical dissipation costs**, in the form of the finite-sum inequality

```
Σ_{k<m} ofReal(H_k)*ofReal(δ_k)
  ≤ Σ_{k<m} ∫⁻_{(t_k,t_k+δ_k]} ofReal(D(s)) ds.
```

The proof uses the existing extended-window lower-floor lemma, with no
extra `L¹` dissipation hypothesis. The whole source-selection proof is
performed from the accepted `5*q` witness, not merely by asserting new
unrelated coefficient witnesses.

## Lean elaboration repair (fix1, base `fe6fac83`)

The local interval endpoint proof now uses `add_le_add_right hδw x`,
which produces `x + δ ≤ x + w` in the required orientation.
The unused existential component index is renamed `_i` without modifying
the witness or any theorem assumptions. Both changes are elaboration-only.

## Lean elaboration repair (fix2, base `fe6fac83`)

The source-factor branch previously simplified `|A|` and unfolded the
physical identity `A = 3 + C_L (‖U(x)‖ + E)` simultaneously. Simplification
unfolded `A` inside the absolute value before the `abs_of_nonneg` rewrite
could apply. A chained `calc` now first uses the established physical
nonnegativity `0 ≤ A` to replace `|A|` by `A`, then uses the explicit
physical identity to obtain the unsquared threshold. Neither hypotheses
nor theorem statements change.
