# Near-Young spectral heat escape with bounded lower moments

Base checkpoint `0d6d0b75`. This is an **algebraic Fourier spectral test**, not a smooth Navier–Stokes trajectory.

Take two frequency weights q=1 and q=n², with masses x=n⁹ and y=1, n≥2. The module proves explicitly that both the normalized Young gap and normalized signed heat rate are homogeneous of degree zero under this rescaling, so rescale to x=1,y=n⁻⁹, and compute m0=1+n⁻⁹, m2=1+n⁻⁵, m4=1+n⁻¹. All belong to [1,2].

The exact gap and rate are

    R(n)=n(n⁴−1)²/((n⁹+1)(n+1)) ≤ 1/n,
    B(n)=2n(n¹⁰−1)(n²−1)³(n²+1)²/((n⁹+1)²(n+1)²) ≥ n/128.

In particular, for every δ>0 and real B, the SAME algebraic spectral state has Young gap ≤δ, signed heat-production rate >B, and lower moments in [1,2]. This strengthens the previous heat-only counterexample by putting it in the near-Young regime. It does not show that any such moment tuple persists under nonlinear PDE evolution. The successful Navier–Stokes regularity approach must invoke actual PDE dynamics or stronger hypotheses than these instantaneous spectral constraints.

Note the rate is *instantaneous*: a large rate at a thin high-frequency band does not imply a comparable time-integrated concentration change. An endpoint argument must control temporal persistence, not just pointwise size.
