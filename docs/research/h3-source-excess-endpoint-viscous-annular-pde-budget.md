# Finite physical H³ dissipation budget for PDE-certified annular persistence

**Baseline:** `8fa3ade5` — derive physical PDE persistence widths for H³ annular endpoint spikes.

The existing positive-width annular persistence theorem constructs on each active, kinetically separated source window a new interval of explicit length

\[
\theta_k=\min\left\{\frac{d_k}{2},\frac{H_k/4}{2(\Lambda_k+1)}\right\},
\qquad H_k=R_k^2\varepsilon_k^2/8,
\]
where `d_k = t(v k) + w(v k) - p k` and `Lambda` is the **actual** physical projected-momentum annular variation coefficient, with source and state envelopes taken from the same selected window.

For the active branch, the earlier theorem gives physical dissipation at least `H_k/4` on `[p_k,p_k+theta_k]`. For inactive branches the selected width is zero. As these newly constructed intervals are contained in the original **pairwise disjoint** source windows, finite terminal physical H³ dissipation implies

\[
\sum_k\frac{\theta_k H_k}{4}\le \int_a^T D_3(t)\,dt <\infty.
\]

The charges are summable and tend to zero, hence for every `gamma>0` and sufficiently large `k` **either** the annular branch is inactive **or**

\[
\frac{d_k H_k}{8}<\gamma
\qquad\text{or}\qquad
\frac{H_k^2}{32(\Lambda_k+1)}<\gamma.
\]

These are necessary conditions; neither gives terminal continuation without further estimates on the source-window duration or the actual PDE coefficient. The four-way source/PDE/spectral gate and original cofinal observations are retained. The older, possibly overlapping endpoint intervals are **not** charged again.

## Verification

The patch contains one Lean module and an idempotent audit registrar. Run `python3 proof/generate_index.py`, `python3 proof/generate_index.py --check`, per-file Lean, the module build, then the full build and audit. Lean was not available in the patch author's container; do not treat registrar checks as Lean compilation.
