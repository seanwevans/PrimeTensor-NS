# Terminal H³ escape: physical quintic/eighth radial rate channels

**Baseline:** `65b790c70751ec47e42dcff490135074eb03f70b`.

The previous endpoint theorem derives the dichotomy

\[
 (T-\tau_k)M_k<4
 \quad\text{or}\quad
 M_k^2<8(\Lambda_k+\Xi_k+1),
\]

on a single actual disjoint terminal sequence, assuming failure of an H³
terminal trace, a preterminal H³ energy class, and *finite integrated* H³
dissipation. The physical coefficients are not abstract:

\[
 \Lambda=6KC\big[(Q+1)^2\sqrt{3W_3(Q)}+(R+1)^2\sqrt{3W_3(R)}\big],
\]

\[
 \Xi=3C^2\big[(Q+1)^2 3W_3(Q)+(R+1)^2 3W_3(R)\big].
\]

The repository already establishes the genuine pointwise frequency estimates

\[
 \Lambda\le24KC\big[(Q+1)^5+(R+1)^5\big],\qquad
 \Xi\le36C^2\big[(Q+1)^8+(R+1)^8\big]
\]

for nonnegative physical amplitudes and cutoffs \(R,Q\ge1\).
The new scalar splitting step is

\[
 M^2<8(\Lambda+\Xi+1)\implies
 \bigl[M^2<16\Lambda+8\bigr]
 \ \lor\ \bigl[M^2<16\Xi+8\bigr].
\]

Thus on the *same* selected physical terminal sequence, eventually either

\[
 (T-\tau_k)M_k<4,
\]

or

\[
 M_k^2 < 384K_kC_k\big[(Q_k+1)^5+(R_k+1)^5\big]+8,
\]

or

\[
 M_k^2 < 576C_k^2\big[(Q_k+1)^8+(R_k+1)^8\big]+8.
\]

Here \(R_k=v(k)+1\) and \(Q_k=N(v(k))+1\). The theorem retains the
same disjoint windows, exact anchored widths, and summable real viscous costs.

For any *fixed* candidate source ceiling \(S\ge0\), the same selected
windows also satisfy eventually

\[
 (T-\tau_k)M_k<4\quad\lor\quad S<C_k\quad\lor\quad
 M_k^2 < 8\left(S\mathcal{L}(R_k,Q_k,K_k)
       +S^2\mathcal{Q}(R_k,Q_k)+1\right),
\]

where \(\mathcal L\) and \(\mathcal Q\) are the exact nonnegative PDE
amplification gains already proved in the repository. The statement
\(S<C_k\) concerns the *selected upper source ceiling*; it is not a
source spike, because \(C_k\) is not selected as the exact maximum.

This package is a necessary obstruction only. It does **not** prove
uniform source/gain bounds, a bound for the outer frequency, exclude
clock compression, or give Navier–Stokes continuation. The next hard step
is a minimal/exact projected-source envelope transfer and a sharpened
outer-frequency gate on the same selected windows.
