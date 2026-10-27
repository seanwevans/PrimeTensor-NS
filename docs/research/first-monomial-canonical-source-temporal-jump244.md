# Canonical projected-source peaks: quantitative temporal-jump obstruction

Base: `da977944` — joint physical H³ and weighted spectral peaks at canonical maxima.

This module preserves the SAME physical cofinal first-crossing disjoint-window witnesses and the same predetermined source-maximizing times `s(k)` on the half-terminal windows. These maximizing times need not belong to the shorter disjoint dissipation windows anchored at `τ(v(k))`.

Write `P(t) = h3PathActualProjectedMomentumSource244 hH3 t`, `p_k=P(s(k))` and `a_k=P(τ(v(k)))`. The exact Hilbert-space triangle inequality gives `‖p_k‖ ≤ ‖a_k‖ + ‖p_k-a_k‖`. Under the existing conditional noncompression/sixth-linear-rate/ninth-eighth-width-cap regime the canonical maximum satisfies `‖p_k‖→+∞`. Thus for **every M**, eventually either `M≤‖a_k‖` or `M≤‖p_k-a_k‖`; the alternative is pointwise in k and is not a fixed branch choice.

If there exists E such that `‖p_k-a_k‖≤E` eventually, then the **anchor** source norms tend to infinity. By already proved physical Fourier H³ majorants, normalized H³ energies and actual weighted spectral-state norms simultaneously tend to infinity **at the anchor times τ(v(k))**, which are within the disjoint dissipation-charging windows. Conversely, if the anchor source norms remain bounded by E eventually, then `‖p_k-a_k‖→+∞`: the source must undergo an unbounded temporal excursion from the anchor to its half-terminal maximizer.

Neither an eventual uniform temporal source increment bound nor an eventual anchor source ceiling follows from compact-interval continuity at strictly interior times. Source norm escape at the dissipation-window anchor is therefore conditional. Even anchor energy peaks alone do not supply a positive temporal width or contradict finite integrated H³ dissipation. This module does **not** prove unconditional continuation or global Navier–Stokes regularity.
