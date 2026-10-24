# Pressure-defect L¹ mass closes old physical momentum Fubini

Baseline: `c6e10b71` — derive physical momentum distributions from old temporal L1 L2 control.

The older endpoint-independent pressure/mass analysis already proves, for each compact test φ and index i,

    M_old(r) ≤ M_projected(r) + M_pressure_defect(r),
    M_projected(r) ≤ K(E,φ),

where K(E,φ) is finite and uniform on the local canonical tail. It separately proved that the old scalar mass is measurable in elapsed time, and that temporal integrability of these masses implies joint spacetime integrability by Fubini.

This increment assumes **only** a time-integrable real profile g_(φ,i)(r) dominating the compact-tested spatial L¹ pressure-gradient difference ∂ᵢp_old − ∂ᵢp_can on the open local window. The defect need not have a global L² representative, and g need not be bounded or continuous. Integrable.mono' yields temporal integrability of M_old from K(E,φ) + g_(φ,i). The existing Fubini-to-weak-FTC result then proves the two-sided Hilbert time derivative on a straddling restart and the literal distributional momentum identity on any covered strict interval.

The old uniform pressure-defect mass bound is proved to imply this weaker L¹ criterion. A nonzero physical FTC defect forces at least one interior time to lack the new criterion.

**Open problem:** derive the integrable pressure-defect mass profile from the selected old-pressure gauge or other canonical Fourier-pressure normalization, without asserting old pressure uniqueness or decay. This is a genuinely additional PDE estimate; nothing here claims that H³ admissibility alone supplies it. Lean compilation must be checked in the user's pinned environment.
