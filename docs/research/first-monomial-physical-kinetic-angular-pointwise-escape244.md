# Physical angular Gram action: cofinal pointwise speed escape

Baseline `8517aac5`: *isolate cofinal angular Gram bursts from failure of physical terminal trace*.

For the actual old physical Hilbert velocity `U(t)`, let `R(t) = U'(t)`,
`E₀(t) = ‖U(t)‖²`, `D₀(t) = -⟪U(t), R(t)⟫`, `Q(t)` the transverse source, and
`Δ(t) = E₀(t)‖R(t)‖²-D₀(t)²`.

On the positive-terminal-mass branch `L>0`, the exact angular identity gives

`f(t) := sqrt(Δ(t))/E₀(t) = ‖(sqrt E₀(t))⁻¹ • Q(t)‖ = ‖N'(t)‖`, `N(t) = U(t)/sqrt(E₀(t))`.

This module proves:

1. `f` is continuous on every strict positive-kinetic energy-class tail `(a,T)`.
2. If `f≤C` throughout `(b,T)`, then `∫_s^t f ≤ C(t-s)` whenever `b<s≤t<T`.
3. Cofinal fixed positive bursts `∫_s^t f ≥ ε>0` force `f` to exceed any given finite threshold on **every** terminal subtail: select `b' > max(b,T-ε/(max(M,0)+1))` and apply the local ceiling estimate for contradiction.
4. By contrapositive, failure of strong physical `L²` terminal convergence at positive `L` forces cofinal unboundedness of `f`, equivalently of `‖N'(t)‖`.
5. The positive-mass exact-mass physical trace / cofinal unbounded angular-speed alternative is a theorem.

The geometric obstruction is **conditional on failure of a physical L² trace**. A physical trace can exist despite unbounded angular velocity, and high-frequency H³ concentration need not imply failure of the physical L² trace. The file makes no converse or Navier–Stokes continuation claim.
