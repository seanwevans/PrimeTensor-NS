# Canonical physical H³ high-tail mass or projected-source impulse

Base: `c446b4de` — force canonical H3 physical temporal cliffs into high-frequency tail evacuation.

## Exact new three-arm consequence

On the *same* original canonical disjoint physical PDE windows let

- `t_k=τ(v k)`, `δ_k=δ(v k)`, `Q_k=N(v k)+1`;
- `D_k=velocityH3DissipationAt u t_k`;
- `H_k=h3PathActualHighRadialDissipation244 Q_k U₃(t_k)`;
- `K_k=‖U₃(t_k)‖`, exactly, without identifying the three-component energy with `1+K²`;
- `C_k` be the **attained** physical projected-source envelope on the original half-terminal interval;
- `V_k=(Q_k+1) sqrt(3 W(Q_k)) C_k` be the genuine low-Q gradient PDE coefficient;
- `X_k=V_k δ_k` and `Y_k=(Q_k+1)K_k`.

The existing physical high-tail evacuation theorem gives, at each actual point `s_k` where `D(s_k)<θ D_k`,

    (1-θ) D_k - [Λ_Q δ_k + Ξ_Q δ_k²] < H_k - H_Q(s_k),

with the **exact**, not surrogate, one-cutoff budget

    Λ_Q δ_k + Ξ_Q δ_k² = 6 Y_k X_k + 3 X_k².

For any real `β` one obtains the exact trichotomy

    β D_k < H_k
    OR  (1-θ-β) D_k < 12 Y_k X_k
    OR  (1-θ-β) D_k < 6 X_k².

Indeed, if the first arm fails, `H_k ≤ βD_k`, and because `H_Q(s_k)≥0`, the one-cutoff PDE budget must exceed `(1-θ-β)D_k`. At least one of its linear and quadratic terms must exceed half that amount. This uses no extra source estimate, no bound on the full future H³ state, no guessed time continuity of untruncated full dissipation, and no critical ninth/eighth width cap.

With `0<θ<1`, `0≤β`, `θ+β<1`, each arm is a genuinely positive fraction of the physical anchor dissipation. The cofinal theorem transfers the trichotomy to exactly the witnesses provided by `h3Path_noL2Trace_exactAnchor_persistentCharge_highTailEvacuation244`, preserving their clocks, source envelope, strict time separation, and spectral anchor.

**Logical frontier:** The cofinal cliff event still explicitly requires the eventual nonvanishing anchor-height charge `η≤δ_k D_k`. Neither this charge nor an upper bound on the projected-source impulse `X_k` is proven automatically. To rule out two of the arms and force large high-frequency mass, one must prove a physically sourced impulse bound. No global Navier–Stokes regularity theorem is claimed.

## Lean declarations

1. `h3PathCubicAnnulusOuterLowGradientSourceImpulse244` — exact canonical cutoff-weighted projected-source action.
2. `h3Path_scalar_sourceActionLinearOrQuadratic244` — quadratic budget splitting.
3. `h3Path_scalar_smallHighTail_cliff_forces_sourceAction244` — low tail forces source action.
4. `h3Path_scalar_cliff_highTailOrSourceAction244` — unconditional pointwise three-arm alternative given a cliff.
5. `h3Path_exactAnchorPDE_cliff_highTailOrSourceAction244` — transfer to exact physical cutoffs and coefficients.
6. `h3Path_noL2Trace_exactAnchor_persistentCharge_highTailOrSourceAction244` — transfer to the unchanged cofinal/disjoint canonical sequence.

Lean/Mathlib compilation remains unverified in the packaging environment; run the pinned full Lake build and audit in the user's repository.
