# Endpoint energy versus the calibrated quintic source clock

**Base:** `b67e50cf` (accepted physical H³ gradient-energy gap-spike theorem and root-import cleanup).

## New hard-math constraint on the *same* physical source windows

The previously accepted theorem selects actual pairwise-separated quintic-source
windows with start `t_k=t(v k)`, original geometric width `w(v k)`, calibrated
subwidth `δ_k`, and actual local PDE coefficients `A_k,B_k`. Write

    H_k = M(v k) + q(v k)/κ, κ=3(3+C_L)>0,
    r_k = max(1,σ(v k))+1+sqrt(A_k² B_k)/(4 q(v k)) > 0.

The *proved* calibration gives

    min(w(v k), 1/r_k⁴) ≤ δ_k,

and the physical endpoint alternative gives

    either there is s∈[t_k,t_k+δ_k] with
      H_k < K sqrt(E(s)) E(s),
    or E(t_k+δ_k) + H_k δ_k ≤ E(t_k).

The actual normalized energy always obeys `E(t)≥1`. Therefore **on the
non-Riccati branch** the positive source-window cost is limited by the
energy available above normalization:

    0 < H_k * min(w(v k), 1/r_k⁴)
      ≤ H_k δ_k ≤ E(t_k)-1.

In particular, `E(t_k)>1`. Applying the already accepted exact calibrated
quartic scalar compression theorem with `J=E(t_k)-1>0` gives

    w(v k) ≤ [E(t_k)-1]/H_k
    OR
    H_k/[E(t_k)-1] ≤ r_k⁴.

The radius alternative is a genuine *fourth-power physical frequency-demand*
constraint on the actual source-driven PDE parameters `σ,A,B,q`. The theorem
does not hide an upper bound for `A_k² B_k` or for `E(t_k)`.

## Quantified noncompression consequence

If an external bound `E(t_k)≤U` is available and the original window satisfies

    U-1 < H_k w(v k),

then the compression branch is impossible, forcing

    H_k ≤ (U-1) r_k⁴.

This elementary scalar lemma is formalized separately. It clarifies precisely
what would need to be proved to turn arbitrarily large source margin into
an actual cutoff/PDE-cost obstruction: control of physical H³ energy and a
non-collapsing original geometric window. Neither follows from positivity
of δ or cofinality alone.

## New Lean declarations

- `h3Critical_scalar_endpointEnergy_forces_calibratedQuarticGate`
- `h3Critical_scalar_noncompressedEnergy_forces_quarticRadius`
- `h3Critical_noL2Trace_cofinalQuintic_endpointEnergyQuarticGate`

The cofinal proof directly reuses the accepted witness, its signed endpoint
energy alternative, and the older quartic charge-compression lemma. No
terminal integrability, no new PDE axiom, and no hypothetical uniform bound
are introduced. Existing large-Riccati-energy exceptions remain explicit.

The package is subject to Lean elaboration in the pinned repository toolchain;
static verification is not a claim of successful Lean compilation.

## Lean elaboration repair (fix1, base `b67e50cf`)

The noncompressed-window scalar lemma had two elaboration failures caused
solely by multiplication order after applying `le_div_iff₀` and
`div_le_iff₀`. Explicit `calc` steps with `mul_comm` now normalize
`w * H` into `H * w`, and `R ^ 4 * (Einitial - 1)` into
`(Einitial - 1) * R ^ 4`. No theorem statement or analytic hypothesis changed.
