# Low-middle-frequency gain in the integrated shell estimate

Base: 5f8c9c0c, all weighted moments derived from Schwartz data.

Let q=-(p+r), P=|p|, R=|r|, Q=|q| and A(p)=|U(p)|_2. For eps>=0,
restrict the existing shell kernel to the closed, measurable region

    Q <= eps min(P,R).

Its indicator preserves integrability. On this region Q²<=eps² PR, so

    P² R² Q³ <= eps² P³ R³ Q.

Combining this with the proved shell bound and the L2-L2-L1 integral
inequality gives

    |integral S_low| <= 2 eps² E3 M1,
    E3 = integral |p|⁶ A(p)²,
    M1 = integral |q| A(q).

The code writes E3 as integral (|p|³ A(p))². All required weighted moment
finiteness follows from the preceding Schwartz module, with no extra
analytic hypotheses. Eps=0 and zero frequencies require no division.
For a separation ratio eps=2^(-m), the coefficient is 2*2^(-2m).

## Why this improves the previous estimate

The unrestricted coarse bound involved E2 M3. The new restricted bound
uses E3 M1 and has an explicit small separation coefficient. In three
dimensions, M1 is controlled by an inhomogeneous H3 norm through weighted
Cauchy-Schwarz: the squared dual weight behaves as |q|^(-4) at infinity,
which is integrable there, and is regular at zero. This observation is
not newly formalized by this patch.

The low-middle restriction is symmetric in p and r. The patch estimates
the restricted shell contribution; it does not assert a separate physical
identity for an unsymmetrized restricted kernel.

## Remaining work

The complement includes comparable frequencies and low outer frequencies.
This patch does not bound that complement, nor does a small coefficient
by itself prove absorption against the actual viscous dissipation.
A complete argument must connect the energy quantities to the physical
normalization and control all frequency regions. No global regularity or
continuation conclusion follows from this estimate alone.

## Checks

Source index, fragment consistency and whitespace checks run before packaging.
Lean compilation and the audit remain pending on the pinned local toolchain.
No axioms or sorry declarations are introduced.
