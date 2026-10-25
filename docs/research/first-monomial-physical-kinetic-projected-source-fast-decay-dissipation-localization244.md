# Fast H³ decay and moving-radial dissipation localization (244)

Base GitHub commit: `0c65b929`.

The prior fast-decay synchronization distinguished direct large normalized dissipation from high-radial **energy** mass concentration. The former does not entail the latter: tiny high-frequency energy may carry arbitrarily large dissipation.

## The missing invariant

The physical Fourier dissipation splits exactly:

\[D(t)=D_{<R}(t)+D_{\ge R}(t).\]

The precise spectral density identity is `d(ξ)=|D(ξ)|² a(ξ)`, so

\[D_{<R}\le R^2 E_{<R},\qquad D_{\ge R}\ge R^2 E_{\ge R}.\]

If high energy mass dominates at the selected cutoff,
\((R+1)E_{\ge R}>R(E_{<R}+E_{\ge R})\), hence \(D_{\ge R}>R D_{<R}\).
If instead total dissipation is exceptionally large,
\(D>(R+1)R^2 E_{H^3}\), the same inequality follows from
\(D_{<R}\le R^2 E_{H^3}\).

## Cohesive physical-time selection

Increase the requested fast-negative-slope threshold at radius R to

\[2(R+1)R^2+4422(1+C_1Q_R),\]

where \(Q_R\) is the previous kinetic-anchored high-H³-energy cutoff. The exact physical balance and two-sided commutator estimate now guarantee that *the same time* satisfies either the huge direct-dissipation bound or the high-energy radial mass dominance. Thus in either arm:

\[ D_{\ge R}(t)>R D_{<R}(t). \]

A diagonal sequence \(t_n	o T\), \(R_n=n+1\), gives

\[rac{D_{\ge R_n}(t_n)}{D(t_n)}	o 1.\]

This is conditional on the fixed cofinal fast negative H³ logarithmic energy-slope hypothesis, which in previous modules is one branch under no strong terminal kinetic L² trace and positive terminal kinetic mass. It does **not** assert high-radial H³ energy domination on the direct viscous arm, does not infer kinetic trace failure from smooth nonextension, and does not settle Navier–Stokes regularity.

## Audit

`tools/audit/register_first_monomial_physical_kinetic_projected_source_spectral_fast_decay_dissipation_localization244.py` registers the module, its 9 theorem statements, and 3 definitions in `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`. Regenerate `proof/order.txt` using `python3 proof/generate_index.py` before `--check` and full CI.
