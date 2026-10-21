# Strict physical radial Fourier variance from null-frequency spheres

Base commit: `c135e0fa` — identify actual H³ Fourier Cauchy defect as radial spectral variance.

## Mathematical statement

The exact physical variance identity is

\[
E_0(E_0D_3-E_2^2)=\int_{\mathbb R^3}(E_0q(\xi)^2-E_2)^2S(\xi)\,d\xi,
\quad q(\xi)=(2\pi)^2|\xi|^2.
\]

If the first-Cauchy defect vanished and `E0>0`, existing a.e. rigidity
would force every point where `S>0` onto the set

\[
\{\xi:E_0q(\xi)^2=E_2\}.
\]

Every nonempty such set is a single Euclidean sphere: equality of the
squares of the nonnegative Fourier gradient weights forces equality of
norms. The measure-theoretic lemma
`MeasureTheory.Measure.addHaar_sphere`, specialized to the finite-dimensional
real Fourier coordinate space, establishes zero *ambient volume* of this
set. An integrable nonnegative Fourier mass density therefore has zero
integral if supported there, contradicting `E0>0`.

Hence, for every actual energy-class time with positive kinetic mass,

\[
\boxed{E_2(t)^2<E_0(t)D_3(t).}
\]

The formerly sharp abstract 27/256 Young ceiling is then strict for
positive top dissipation and positive multiplier `K`. These results are
unconditional within the existing `LoggedPreterminalH3PathAdmissible` and
`PreterminalH3EnergyClass` framework, **conditional on `E0(t)>0`**.
No *uniform quantitative* gap (in time, or relative to total mass) follows.
Arbitrarily thin Fourier annuli can make the variance arbitrarily small.

The module is deliberately limited to qualitative Fourier geometry, not
an unproved regularity theorem or a new physical continuation criterion.

## Build

Register with `tools/audit/register_first_monomial_radial_variance_strict244.py`;
regenerate `proof/generate_index.py`; run fragment checks, Lean single-file
check, focused and full Lake builds, and the baseline audit.
