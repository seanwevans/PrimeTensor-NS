# Full Z³ Leray source: transverse constraint and projected analytic initial data

**Base HEAD:** `59dfdbd54424ee473d21411c4b68e9faab98ba87`.

## Mathematical advance

Write \(\xi_n\in\mathbb R^3\subset\mathbb C^3\) for the integer frequency,
\(P_n\) for the complex orthogonal projection onto \((\mathbb C\xi_n)^\perp\),

\[
 B_n(u,v)=\sum_{p\in\mathbb Z^3}P_n[-i\,\langle \xi_{n-p},u_p\rangle v_{n-p}].
\]

The original exact ordered transport has the output projector **inside** every term. Thus
\(\langle\xi_n,P_n z\rangle=0\), and the identity survives every complete finite double convolution and its absolutely convergent infinite \(\ell^1\) sum. The proof uses closedness of the frequency-orthogonal subspace and the previously established high-analytic-Wiener absolute summability theorem. It does **not** discard colliding ordered pairs, even when the output mode is outside the finite input support.

Consequently, at every finite cutoff, testing the full viscous-plus-Leray Fourier vector field against \(\xi_n\) produces exactly its viscous longitudinal component, with **no nonlinear source contribution**.

The Fourier Leray projection of an arbitrary analytic initial sequence,
\(u_{0,n}^{\perp}=P_n u_{0,n}\), is componentwise divergence-free, and contraction implies

\[
\sum_n 2^{|n|_1}\|u_{0,n}^{\perp}\|\le
\sum_n2^{|n|_1}\|u_{0,n}\|<100.
\]

The previously proven prescribed-data local existence theorem therefore constructs one local Fourier flow with these projected initial coefficients, the existing \(W_{\log(9/5)}\le100\) bound, the complete \(W_{\log(5/4)}\le50,000\) nonlinear source, the exact integral evolution, and the newly proved **transverse source constraint**.

## Boundaries of the result

Transversality of the **forcing** is not yet propagation of the divergence-free constraint for the **solution**. The longitudinal velocity must be shown to satisfy a unique homogeneous heat equation, or the finite solenoidal Galerkin invariant subspace must be established and passed to the limit. Hermitian conjugate symmetry also remains to be proved to recover a real-valued physical periodic velocity. These distinctions matter before upgrading the complex Fourier flow to a physical divergence-free Navier–Stokes solution. Nothing here proves \(\mathbb R^3\) H³ continuation or global regularity.

## Verification

Run the package registration/audit scripts, direct `lake env lean` on the new module, module build, the existing repository audit and full `lake build`. The archive is prepared offline; formal Lean elaboration must be checked in the user's repository.
