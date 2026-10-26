# Projected PDE source to finite-annulus H³ dissipation variation

Base: `c9c5fe2f` (*transfer projected PDE source modulus to finite radial H³ gradient increments*).

The earlier radial Plancherel lemma and strong physical Hilbert FTC already yield, for a physical projected-source ceiling `C` on `[s,t]`,

    Σ_{j=0}² ‖Mρ(S_j(s)-S_j(t))‖²
       ≤ 3 (ρ+1)² W(ρ) C² (t-s)²,
    W(ρ) = 1+ρ²+ρ⁴+ρ⁶.

The present proof takes a square root coordinatewise and polarizes the **bounded gradient multiplier** `Mρ` rather than the unbounded fourth-order dissipation functional. If `‖S_j(s)‖,‖S_j(t)‖ ≤ K`, then

    |D_<ρ(S(s)) - D_<ρ(S(t))|
      ≤ 6 (ρ+1)² K sqrt(3W(ρ)) C (t-s).

For finite radii `R,Q`, set

    Λ(R,Q,K,C)
       = 6 K C [ (Q+1)² sqrt(3W(Q)) + (R+1)² sqrt(3W(R)) ].

The finite-annulus dissipation `B = D_<Q - D_<R` obeys

    |B(s)-B(t)| ≤ Λ(R,Q,K,C) (t-s).

At a strict-time anchor `t`, on a right-hand interval `[t,t+δ]` where the actual source norm is at most `C` and the three spectral coordinate norms are at most `K`, if

    A < B(t) and Λ(R,Q,K,C) δ < B(t)-A,

then `B(r)>A` throughout the interval and

    δ A ≤ ∫_[t,t+δ] B(r) dr.

All radii are finite, both source and spectral envelopes may depend on the selected window, and the theorem **does not** assert a positive uniform lower bound on persistence widths or unbounded tail integrability.

The theorem package uses exact existing physical PDE derivative, Fourier cutoff, gradient-multiplier, and annular continuity interfaces. No new axiom, placeholder proof, globally bounded fourth-order operator, or terminal trace hypothesis is added. Lean compilation must be run in the user's native Lean environment.
