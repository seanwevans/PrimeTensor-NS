# Canonical first-crossing PDE clock with exact anchor spectral amplitude

**Base:** `2174f9c1`. The source theorem chooses
`K = ‖h3AuditActualSpectralVelocityTotal hH3 t‖` inside its proof, before
constructing the quadratic-sharp physical annulus clock. This is the actual
spectral H³ sup norm. The exact physical energy comparison is `K² ≤ E₃(t)`;
the physical PDE rate square is at most `2304 E₃(t) C² (Q+1)^10`.

**Refinement at `b102dde4`:** The same pointwise construction now also exports
its previously proved quarter-cubic gap and minimality below the first
crossing. These extra conjuncts allow the exact coefficient to pass through
the old disjoint-window three-scale barrier without changing its mathematical
hypotheses. The proof still does not assert a terminal-uniform estimate.
