# Fast negative H³ energy slope versus simultaneous radial/viscous dissipation

**Base checkpoint:** `c7c0e4fe` — synchronize negative canonical H3 cubic with radial dissipation.

## Exact balance and two-sided transport

At an actual strict preterminal H³ Navier–Stokes time, put

- `E(t) = velocityH3EnergyAt u t > 0`,
- `D(t) = velocityH3DissipationAt u t`,
- `F(t) = deriv (velocityH3EnergyAt u) t`,
- `W(t) = velocityH3TransportDerivativeAt u t`.

The existing actual PDE balance gives `F + 2D = -W`.
The already-closed H³ commutator estimate, with the canonical C¹ bound,
gives **both** signs of the full transport:

`|W| ≤ 4422 (1 + C₁ sqrt(E)) E`.

Hence, for every radius `R` and root threshold `Q`, if

`(2R + 4422 + 4422 C₁ Q) E < -F`,

then either `D > R E`, or `sqrt E ≥ Q`. This is pointwise algebra; the
first conclusion does *not* imply high-radial **energy** dominance by itself.

## Request calibrated to the kinetic radial bound

Freeze an admissible kinetic anchor `b`. The prior kinetic-Fourier theorem
controls the weighted low-radial H³ mass by

`K(R) E₀(b)`, where `K(R) = 1 + R² + R⁴ + R⁶`.

Take `Q_R = (R+2)(K(R) E₀(b)+2)+1`. The preceding high-energy/radial theorem
has already proved that `Q_R ≤ sqrt E(t)` implies, at the **same time**,

`(R+1) High_R(S(t)) > R SpectralSquareEnergy(S(t))`, and

`R³ E(t) < (R+2) D(t)`.

Thus very negative normalized physical energy slopes entail, at the same
time, either `D>R E`, or both moving-radial dominance and the physical
cubic dissipation clock.

## Fixed cofinal fast-slope branch

Given the **fixed** cofinal fast-slope branch already isolated by the
four-channel theorem, select the slope threshold *before* choosing a time.
The resulting single terminal sequence has `dist(t_n,T)<1/(n+1)` and
retains both the prescribed fast negative slope and the pointwise viscous
or radial alternatives. For `n≥1`, the prior cubic-clock algebra turns
either alternative into `D(t_n)/E(t_n)>n+1`. Consequently the same fixed
fast-decay sequence exhibits diverging normalized physical H³ dissipation.

This completes the synchronization of the *viscous clock* in the last
signed-energy branch. It **does not** prove the fast-decay branch must have
high-radial spectral **energy** mass: an arbitrarily small very-high-frequency
piece can carry a large fourth-derivative dissipation while contributing
little third-derivative energy. Neither hypothetical H³ nonextension nor
kinetic-trace failure is established by this theorem; these remain separate
logical premises of the preceding fixed-channel result.
