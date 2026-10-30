# Physical viscosity-inclusive H³ logarithmic radius budget

Base commit: `9e51f2cd` — transfer critical H3 logarithmic radius barrier to physical Riccati energy.

At positive exact normalized signed transport growth, g(s)=max(0,(-Transport₃(s)-2D₃(s))/E₃(s)) equals the raw quotient, and so

    g(s) + 2 D₃(s)/E₃(s) = -Transport₃(s)/E₃(s).

The already-proved complete physical PDE commutator bounds -Transport₃(s)/E₃(s) by 4422*(1+|h(s)|), where h is the **canonical C¹ gradient upper envelope**. This is a complete physical transport statement, not an inferred lower bound on the true gradient supremum.

The committed conditional all-orders canonical logarithmic-rate theorem provides, for each fixed b in (a,T) and all sufficiently late first-crossing radii R_k=v(k)+1, an intermediate strict physical time s∈(b,τ(v k)) with

    (16m+3) log R_k ≤ 8 (T-b) g(s).

Strict monotonicity of v ensures log R_k→+∞. Hence this selected g(s) is positive for all sufficiently late k. Adding the full viscous share to the preceding gradient bound at that SAME s gives the new necessary PDE constraint

    (16m+3) log R_k + 16(T-b) D₃(s)/E₃(s)
      ≤ 8(T-b)*4422*(1+|h(s)|).

Thus the positive physical dissipation ratio consumes part of the available gradient-envelope budget instead of being discarded. The higher radial q^(4+m) majorant, actual projected-source ceiling, eighth-power critical outer cap, small epsilon and noncompressed terminal clock are **unchanged explicit premises** inherited from the exact-anchor theorem. The theorem does not rule out the conditional terminal escape without a new PDE bound on h that is independently stronger than this inequality.

Lean declarations:
- `h3Path_positiveFullExcess_add_viscousShare_le_gradientEnvelope244`
- `h3Path_scalar_logRate_viscousShare_budget244`
- `h3Path_noL2Trace_exactAnchor_higherBudget_physicalViscousGradientBudget244`

Lean compilation requires the pinned repository Lake toolchain; offline checks are structural only.
