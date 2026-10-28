# Canonical source-peak cubic temporal collapse

Base commit: `b36593f8`, optimized actual physical peak-persistence theorem.

Let `A_k = ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖` be the actual weighted spectral H³ SUP norm at the original canonical projected-source maxima, restricted to the cofinal disjoint persistence subsequence. Let `d_k > 0` denote those newly selected persistence widths, and `H_k >= 0` the actual physical H³ dissipation floor. The earlier theorem proves exactly

    A_k^8 = 16384 (velocityH3Energy0At u b + 1) H_k^3,
    Summable (fun k => d_k * H_k).

Hence the new zero-free polynomial clock identity

    d_k^3 A_k^8 = 16384 (E₀(b)+1) (d_k H_k)^3

forces `d_k^3 A_k^8 -> 0`. Because `A_k` diverges and `d_k` is positive, this is exactly the necessary rate `d_k = o(A_k^(-8/3))`. No fractional-power lemma is required in the Lean formalization. All canonical times and the original noncompression/sixth/ninth-eighth clock assumptions remain explicit and unchanged.

The generic quantitative per-window bound is

    d_k^3 A_k^8 <= 16384 (E₀(b)+1) B^3,

where `B` is a bound on `d_k H_k`. Any future PDE persistence lower estimate that keeps `d_k^3 A_k^8` bounded below by a fixed positive number eventually would contradict the present finite-dissipation hypothesis. Such a lower estimate is **not** proved here: spectral continuity alone only supplies arbitrary positive widths, and high-frequency H³ motion is not controlled by the existing low-frequency projected-source modulus.

Source check only; target Lean/Lake build required.
