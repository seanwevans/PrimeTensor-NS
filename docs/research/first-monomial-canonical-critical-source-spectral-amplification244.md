# Canonical critical width: a physical source–spectral amplification restriction

Parent: `f5cd1130`, which proves the conditional cofinal three-way critical-regime failure under hypothetical nonextension.

This increment uses the **actual projected PDE source** and **actual original minimal Fourier annular cutoff**, rather than postulated Fourier growth rates. Define

- `R_k=v(k)+1`, `Q_k=N(v(k))+1`, `L_k=N(v(k))-v(k)`;
- `K_k`: original H³ spectral anchor coefficient on the canonical clock;
- `C_k`: attained physical projected-source maximum on the half-terminal window;
- `Λ_k=6 K_k C_k [(Q_k+1)^2 sqrt(3 W(Q_k)) + (R_k+1)^2 sqrt(3 W(R_k))]`, `W(x)=1+x²+x⁴+x⁶`.

For `0 ≤ R ≤ Q`, elementary polynomial estimates give `sqrt(3W(x)) ≤ 4(x+1)^3` and thus

    Λ(R,Q,K,C) ≤ 48 |KC| (Q+1)^5.

Under a critical outer cutoff cap `(Q+1)^8 ≤ D R^9` and an escaping linear rate `U R^6 < Λ`, raising to eighth powers yields the root-free, sharp-exponent constraint

    U^8 R^3 < (48 |KC|)^8 D^5.

The end-to-end theorem preserves all original canonical windows, cutoff indices, source maximizers and summable dissipation costs. Under hypothetical nonextension and eventual geometric noncompression and critical width cap `((N-v)+1)^8 ≤ V R^9`, **for every U≥0** there are arbitrarily late original indices with

    U^8 R^3 < (48 |K_k C_k|)^8 (256(V+1))^5.

The `+1` in the linear-rate antecedent is absorbed by asking for a coefficient `U+1` and using `R^6≥1`. No extra PDE norm bound is assumed. The nonextension hypothesis is not eliminated: the geometric-collapse and width-escape alternatives remain possible. The conclusion is an amplifier obstruction, not a proof of global regularity.

Validation: syntax/placeholder and registrar idempotence and ZIP integrity. Pinned Lean elaboration must be run locally.
