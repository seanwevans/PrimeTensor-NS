# Prescribed-gauge source/viscosity: actual late dissipation observations

Base SHA `7bf5351c722bec0efe024baa2889fd9109053300`.

## The new mathematical step

The existing prescribed-gauge no-H³-trace alternative gives physical minimal
crossing windows at height H(v(k))^8, disjoint viscous charges, an escaping
outer/gauge ratio Q(k)/H(v(k)), and four pointwise/integrated time channels.
The fourth channel is an actual terminal physical viscous action:

    H(v(k))^4 < 168 Q(k)^4 ‖F‖ (3 + C_L) ∫_[m(k),T] D_H³(r) dr,
    m(k)=(τ(v(k))+T)/2, Q(k)=N(v(k))+2.

The new scalar lemma proves that if `R < K * ∫_[m,T] D` with K≥0, m<T and
D interval-integrable, then there is a physical strict interior time
r∈(m,T) with `R < K*(T-m)*D(r)`. The proof is genuinely measure-theoretic:
if all point values were ≤ the averaged threshold, the interval integral
comparison against a constant would contradict the strict lower bound.

This yields on the exact original witnesses the alternatives:

1. `H_k^4 < 14 Q_k^4 ‖P^+_(v k) F U_T‖`;
2. an actual `r∈[τ(v k),m_k]` where
   `H_k^4 < 28 Q_k^4 ‖F‖ (m_k-τ(v k)) ‖G(r)‖`;
3. `H_k^4 < 56 Q_k^4 ‖F‖ (3+C_L) (T-m_k) (1+6E₀(b))`;
4. an actual `r∈(m_k,T)` where
   `H_k^4 < 168 Q_k^4 ‖F‖ (3+C_L) (T-m_k) D_H³(r)`.

The early source observation is attained by the existing compact source
envelope theorem. The late viscous observation comes from the new strict
integral-to-actual-time argument. Both are genuine physical trajectory times.
The source maximum is not incorrectly assumed to bound the delayed tail.

## Limitations and next hard obligation

The delayed physical dissipation integral still tends to zero along these
windows, but multiplying by the unbounded Q_k^4 need not preserve that
convergence. The new pointwise spike can be arbitrarily narrow. Nothing here
proves a terminal H³ trace, a frequency cap, or a contradiction. A future
signed-H³ transport/viscous coercivity theorem would need to bound the
radius-weighted pointwise spike (or constrain its duration), ideally through
the exact minimal-crossing PDE clock rather than an extraneous assumption.

## Verification

No axioms, sorry, admit or synthetic new data premises. Lean compilation
requires the repository-pinned Lean toolchain on the user's machine.
