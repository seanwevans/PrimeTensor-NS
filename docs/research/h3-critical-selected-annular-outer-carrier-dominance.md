# Exact physical annulus / outer-tail kinetic ledger

**Base:** `9d094a2905e2fb6bb82e28f4b63714a2a239c07c`.

The previous selected wide-aperture theorem proves that the actual physical
Young-width cost suppresses unweighted kinetic mass in the selected annulus,
conditional on strictly positive kinetic excess and nonnegative actual annular
deficit. This patch identifies the **remaining actual kinetic carrier**.

For any physical strict time `t`, ordered real radii `rho ≤ sigma`, and the
precise original sharp Fourier projector, physical Plancherel and the
measurable highpass/annulus/outer partition prove the exact identity

    M(rho,t) = N(rho,sigma,t) + M(sigma,t).

Here `M` is `thirdFullPhysicalActualSharpKineticHighMass244`, and `N` is the
already registered `thirdFullPhysicalActualSharpAnnularRawMass244`. Both are
computed on the same genuine physical velocity. The proof uses the exact
complex Fourier indicator norm identity and the real physical scalar Fourier
isometry coordinatewise; no new spectral state or regularity premise is used.

Combining the identity with the **already proved** sixth-power Young-width
bound at aperture `sigma ≥ K rho` (`K ≥ 2`) yields

    (2*K^6 - 9)*M(rho,t) ≤ 2*K^6*M(sigma,t).

For `K=2` this is the explicit bound

    119*M(rho,t) ≤ 128*M(sigma,t).

Under the existing finite-H3-dissipation cofinal hypotheses, the previously
proved aspect-escape theorem makes the outer-carrier lower bound hold
eventually for every **fixed** `K ≥ 2`. This does not assert a common index
working for all K simultaneously, a uniform positive physical kinetic mass,
or the existence of strict excess and nonnegative deficit snapshots.

**Next mathematical obstruction:** prove an actual PDE estimate incompatible
with arbitrarily large outer-tail retention *relative* to the moving inner
highpass, or show that the required selected positive deficits cannot persist.
Simple absolute L2 highpass tightness is insufficient, because both masses
can converge to zero while their ratio approaches one.
