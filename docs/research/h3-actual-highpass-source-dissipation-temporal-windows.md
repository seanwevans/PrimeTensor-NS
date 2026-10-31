# Actual highpass source mass and H³ dissipation: common physical-time windows

Base: `0d753f4b` — moving-cutoff simultaneous highpass source and H³ dissipation.

The committed diagonal selects one fixed projected-momentum coordinate and actual terminal times with both moving highpass source square mass and high-radial H³ dissipation greater than `n`. This patch adds the *temporal persistence* implication.

1. The genuine projected physical momentum source is continuous on `(0,T)`. Its scalar sharp physical highpass is continuous, and the exact real Plancherel identity yields continuity of the Fourier highpass square mass at every positive time. No new source-continuity hypothesis is needed.
2. The previously proved exact spectral partition implies continuity of high-radial H³ dissipation if full physical H³ dissipation is continuous, because low-radial dissipation is already proved continuous at every nonnegative fixed cutoff. Only full-dissipation continuity remains an **explicit hypothesis**; no additional low-radial continuity premise is necessary.
3. The two strict same-time inequalities persist on the **same** positive right-hand interval `[t_n,t_n+δ_n]`, with `t_n + δ_n<T`. Both scalar integrals over that interval are at least `n·δ_n`. This is an actual common time window, not two separately chosen ones.

The theorem does **not** show that `δ_n` has a lower bound, that the windows are pairwise disjoint, or that `Σ n·δ_n` diverges. It does not contradict global smoothness; its no-strong-terminal-L²-trace premise has not been proved to arise. Further work requires quantitative control of full H³ dissipation continuity or signed nonlinear transport on the selected moving-frequency windows.

Lean declarations:
- `h3Critical_actualHighpassSourceMass_continuousOn`
- `h3Critical_twoContinuousSpikes_integratedWindow`
- `h3Critical_noL2Trace_actualHighpassSourceDissipation_integratedWindows`

Verification: registrar checks and static package inspection can be run offline. The Lean file and project baselines require the repository's pinned `lake` toolchain; no Lean compilation is asserted by this patch generator.
