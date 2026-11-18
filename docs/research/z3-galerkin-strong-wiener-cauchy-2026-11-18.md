# Galerkin Fourier diagonal to strong lower-radius Wiener Cauchy convergence

**Parent:** `3656f7bf3d637201ee39d606becc85b45a257b48` (Arzelà--Ascoli Fourier diagonal, Lean verified by local user build).

## New mathematical statement

For any sequence of finite Fourier cutoffs `S_k ⊂ ℤ³`, viscosities `0 ≤ μ ≤ 1/10`, and independent finite initial states with strict initial `W_{log 2} < 100`, the previously formalized Picard/supremum construction provides strong exact Leray--Galerkin flows on the common closed time interval `I=[a,a+log(10/9)/100]`.

The Arzelà--Ascoli diagonal gives a single strictly increasing subsequence `φ` and continuous mode curves `g_n(t)` with uniform-in-time coordinate convergence at **every** lattice frequency. This module proves, as a consequence of that *constructed* convergence, the **uniform strong lower-radius Wiener Cauchy property**:

```text
For all ε > 0, there exists K such that, for k,l ≥ K and all t in I,
  sum_{n in S_{φ(k)} ∪ S_{φ(l)}}
      (3/2)^(|n|_1) * ||u_{φ(k)}(t,n) - u_{φ(l)}(t,n)|| < ε.
```

Every coefficient is zero-extended outside its own finite cutoff. Neither nested cutoffs nor cross-cutoff initial-data compatibility is assumed. Compactness selects the subsequence; it does not assert that the **original sequence** is Cauchy.

## Proof mechanism

1. Fix a finite `ℤ³` core cube of radius `N`. Its total `W_log(3/2)` weight is a *finite* nonnegative number `E_N`; choose a single per-mode tolerance `δ = ε/(2(E_N+1))`.
2. The uniform-time diagonal theorem gives one eventual index valid at *every* core mode. Thus the core difference is at most `2δ E_N ≤ ε` for any two later subsequence members and every time.
3. The analytic reserve `log(9/5)-log(3/2)` makes the remaining Fourier cost exactly `200(5/6)^N → 0`. Choose `N` so this cost is `< ε/2`; only then choose the temporal Cauchy index for the core at tolerance `ε/2`.
4. Apply the already proved two-cutoff fixed-core inequality. The Cauchy threshold is uniform in time, mode, and cutoff.
5. Repeat with **actual** finite Galerkin solutions obtained from strict analytic initial data, the genuine strong ODE, the 51000-Lipschitz property and the 9/5 ball.

## Limits of the result

This is a **strong Cauchy theorem** for finite-support coefficients. It does not yet construct the completed infinite weighted ℓ¹ Banach-space limit, establish full high-radius mass of the limit, or pass the complete Leray convolution and viscosity to an infinite-frequency Navier--Stokes equation. Those are subsequent nontrivial steps. In particular, this does not establish Clay global regularity.

## Verification

The package checker verifies structural proof markers, declarations and registration, but **does not run Lean**. The guarded run script checks the exact parent commit, archive SHA-256, proof index, targeted Lean module, full build and baseline audit before committing and pushing.
