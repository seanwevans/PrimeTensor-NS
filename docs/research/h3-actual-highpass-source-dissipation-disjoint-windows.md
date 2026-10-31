# Disjoint common actual-source/H³-dissipation windows

Base: `ba5d5130` — persist moving highpass source and H³ dissipation on common time windows.

The previous Lean theorem produces `t(n) → T` and positive widths `δ(n)`,
with each closed interval `[t(n), t(n)+δ(n)]` strictly below `T`. At every
point of that window, the genuine projected-source Fourier square mass
outside radius `n+1` and actual high-radial H³ dissipation beyond `n+1`
both exceed `n`. Both time integrals are at least `n δ(n)`.

The repository already proves the geometric selection lemma
`h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244`.
Apply it to these exact common windows to obtain a strictly increasing
subsequence `v` with `t(v(k))+δ(v(k)) < t(v(l))` whenever `k<l`.
The selected times still converge to `T`, and *all* source and dissipation
bounds remain true at the moving radii `v(k)+1`. Finite sum monotonicity
supplies simultaneous bounds

```
Σ_{k<m} v(k) δ(v(k)) ≤ Σ_{k<m} ∫_[t(v(k)),t(v(k))+δ(v(k))] sourceMass_{v(k)+1}(s) ds
Σ_{k<m} v(k) δ(v(k)) ≤ Σ_{k<m} ∫_[t(v(k)),t(v(k))+δ(v(k))] highDiss_{v(k)+1}(s) ds
```

The `hNoTrace` premise and the explicit continuity assumption on full physical
H³ dissipation are unchanged. The theorem does not obtain a lower bound on
window widths or prove divergence of the selected cost sum, nor does it prove
that a no-trace path exists. In particular no terminal L¹ bound on full H³
dissipation is assumed: such a bound would contradict the committed no-trace
obstruction. The next substantive task remains a quantitative temporal modulus
or signed-PDE transport estimate preventing excessive window compression.

Lean declaration:
`h3Critical_noL2Trace_actualHighpassSourceDissipation_disjointWindows`.

Compile with the repository's pinned Lean toolchain; no remote Lean compilation
is claimed for this package.
