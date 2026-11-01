# Physical compact source, spectral, and viscosity thresholds from the quartic clock

**Base commit:** `111480f6`. The source witnesses and `PrimeTensor.Depth` log bridge are unchanged.

The accepted fivefold cofinal witness supplies genuine compact-window upper bounds

    ||h3PathActualProjectedMomentumSource244(s)|| <= C_k,
    ||h3AuditActualSpectralVelocityTotal(s)|| <= E_k,

for every `s ∈ [t_k,t_k+w_k]`, and exactly

    A_k = 3 + C_L*(||U(t_k)|| + E_k),
    B_k = 12*C_k² + 2*(D(t_k)+H_k),
    H_k = M(v_k) + q(v_k)/(3*(3+C_L)),
    P_k = 4*q(v_k),  S_k = max(1,σ(v_k))+1.

The original cofinal quartic PDE branch forces
`S_k < |A_k| OR P_k² < B_k`. Since `||U(t_k)||<=E_k` and `C_L>=0`,
`A_k>=0` and the first branch sharpens to

    S_k < 3 + 2*C_L*E_k.

For the B branch, a strict weighted pigeonhole argument shows

    P_k² < 24*C_k² OR P_k² < 8*D(t_k) OR P_k² < 8*H_k.

The constants arise because the three competing right-hand contributions
`12*C_k²`, `2*D(t_k)`, `2*H_k` would total at most `P_k²` if every
corresponding strict alternative failed. No positivity of `D` or `H` is
needed for this elementary implication.

The new cofinal theorem carries the **same selected windows** and keeps their
separation, exact local C/E ceilings, explicit A/B identities, quartic clock,
and finite-sum extended H³ dissipation-cost bound. Each window has a real
Riccati-energy witness or is paid by geometric compression, cutoff scale,
the spectral ceiling, projected-source ceiling, physical dissipation at the
peak, or the enhanced source floor itself.

If `8*H_k <= P_k²`, the floor branch is ruled out. It then becomes a genuine
**three-way physical factor** alternative after Riccati/compression/cutoff.
The extra floor bound is explicit; it is not inferred from `q_k>0` because
the free nonnegative `M(v_k)` can be arbitrarily large.

Lean declarations:

- `h3Critical_scalar_explicitAB_forces_physicalFourWay`
- `h3Critical_scalar_explicitAB_forces_physicalThreeWay`
- `h3Critical_noL2Trace_cofinalFivefold_physicalSourceViscousFactorGate`

Scope: necessary local physical escape alternatives; no terminal uniform
upper bounds, no divergence of cumulative charges, no resolution of the
Navier–Stokes regularity frontier. The archive is statically checked only;
Lean elaboration must be run using the pinned local environment.

## Lean elaboration repair (fix1; base `111480f6`)

The accepted explicit cofinal witness has already rewritten its PDE factor
disjunction into concrete physical definitions, whereas the scalar
`explicitAB_forces_physicalFourWay` theorem consumes an abstract
`S < |A| ∨ P² < B` disjunction. At the call site reconstruct that
abstract disjunction using the retained physical identities `hA`, `hB`
and the established nonnegativity of `A`. The subsequent scalar argument
is unchanged; no theorem declarations or hypotheses change.
