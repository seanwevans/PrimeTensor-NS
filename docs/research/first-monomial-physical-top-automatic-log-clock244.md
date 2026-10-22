# Automatic integrability of the signed physical top logarithmic clock

Base checkpoint: `ffa46a63` — one-sided physical top logarithmic cubic clock.

## The previously unresolved compact-time assumption

The signed logarithmic derivative `(log D3)'` was previously an independent `IntervalIntegrable` hypothesis in the exact combined fifth-plus-phase action. Continuity of the physical cubic ratio `C=M3/D3` did not, by itself, assert that derivative integrability; a differentiable real function need not have an absolutely integrable derivative on a compact interval.

But the actual PDE gives a *one-sided* pointwise bound: `(log D3)' = C-(M5+P)/D3 <= C`, and `C` is continuous and attains a finite maximum `K` on every positive-D3 compact strict interval `[s,t]`.

Let `G(r)=K*r-log D3(r)`. The pointwise bound yields `G'(r)=K-(log D3)'(r)>=0`. The theorem `intervalIntegral.intervalIntegrable_deriv_of_nonneg` proves integrability of `G'` on the compact interval using only continuity of `G` on `[s,t]`, its interior derivative, and nonnegativity. Hence `K-G' = (log D3)'` is also interval-integrable. This argument does **not** assume smoothness of the log derivative.

## Stronger physical joint balance

The previous joint action lemma now has no signed-log/fifth/phase integrability hypotheses:

    integral_s^t (M5+P)/D3
      = integral_s^t M3/D3 - [log D3(t)-log D3(s)].

Because `M5,P>=0` and `D3>0`, this also yields the *integrated*, rather than maximal, physical cubic clock bound

    log D3(t)-log D3(s) <= integral_s^t M3/D3.

This is genuinely stronger than the compact sup clock `<= (t-s)*max(M3/D3)` and needs no signed-log integrability assumption. In particular, unbounded forward log growth along a strict tail necessitates unbounded cumulative physical third-radial Leray forcing action.

## Remaining hard analysis

The result is **local in strict preterminal time**: its upper ceiling K can diverge toward T, as can the cumulative cubic integral. It does not independently control downward logarithmic variation or yield terminal-uniform fifth/phase expenditure. A continuation theorem still requires a forcing-action estimate or a new dynamical cancellation that is uniform toward the endpoint.
