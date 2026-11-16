#!/usr/bin/env python3
"""Independent zero-safe, full-output Galerkin consistency and Wiener audit.

Uses actual Gaussian-rational projected convolution from earlier auditors.
Heat factors and vector norms are evaluated at 100-digit Decimal precision.
Checks residual stability, finite-step telescoping, second-jet O(h^2)
consistency (including born modes), and the analytic-radius reserve.
No continuous-time ODE or PDE existence theorem is asserted here.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from random import Random

import check_h3_three_band_z3_galerkin_heat_step as heat
import check_h3_three_band_z3_galerkin_output_wiener as output
import check_h3_three_band_flux_slope as first

ZERO = heat.Z


def dec(x):
    if isinstance(x, int):
        return Decimal(x)
    if isinstance(x, Q):
        return Decimal(x.numerator) / Decimal(x.denominator)
    return Decimal(x)


def to_dec_vec(x):
    return tuple((dec(a), dec(b)) for a,b in x)


def norm_dec(x):
    return sum((a*a+b*b for a,b in x), Decimal(0)).sqrt()


def plus_dec_vec(x, y):
    return tuple((a+c,b+d) for (a,b),(c,d) in zip(x,y))


def scaled_dec_vec(c, x):
    return tuple((c*a,c*b) for a,b in x)


def minus_dec_vec(x, y):
    return plus_dec_vec(x, scaled_dec_vec(Decimal(-1),y))


def zdec():
    return tuple((Decimal(0),Decimal(0)) for _ in range(3))


def weight(n,R):
    return dec(R**output.prior.degree(n))


def state_mass(s,u,R):
    return sum((weight(n,R)*norm_dec(to_dec_vec(u.get(n,ZERO))) for n in s),Decimal(0))


def state_derivative(s,u,R):
    return sum((weight(n,R)*dec(output.prior.degree(n))*
                norm_dec(to_dec_vec(u.get(n,ZERO))) for n in s),Decimal(0))


def source_at(s,u):
    # All ordered p+q outputs, including repeated sums and output collisions.
    state={n:u.get(n,ZERO) for n in s}
    return heat.full_source(s,state)


def heat_step(s,u,nu,h,R):
    src=source_at(s,u)
    next_state={}
    debt=Decimal(0)
    for n in s:
        lam=dec(output.prior.d2(n))
        sigma=(-dec(nu)*dec(h)*lam).exp()
        un=to_dec_vec(u.get(n,ZERO))
        sn=to_dec_vec(src.get(n,ZERO))
        next_state[n]=plus_dec_vec(scaled_dec_vec(sigma,un),scaled_dec_vec(dec(h),sn))
        debt+=weight(n,R)*(1-sigma)*norm_dec(un)
    return next_state,debt


def residual(s,u,v,nu,h,R):
    step,_=heat_step(s,u,nu,h,R)
    return sum((weight(n,R)*norm_dec(minus_dec_vec(to_dec_vec(v.get(n,ZERO)),step[n]))
                for n in s),Decimal(0))


def mass_decimal(s,u,R):
    # Used when the state is the actual Decimal heat-step output.
    return sum((weight(n,R)*norm_dec(u[n]) for n in s),Decimal(0))


def test_arbitrary_path(s,states,steps,nu,R):
    tolerance=Decimal('1e-55')
    cost=Decimal(0)
    debt_sum=Decimal(0)
    W0=state_mass(s,states[0],R)
    for i,h in enumerate(steps):
        u,v=states[i:i+2]
        W=state_mass(s,u,R)
        Wnext=state_mass(s,v,R)
        D=state_derivative(s,u,R)
        step_state,debt=heat_step(s,u,nu,h,R)
        Rdef=residual(s,u,v,nu,h,R)
        assert Rdef>=0 and debt>=0
        assert Wnext<=mass_decimal(s,step_state,R)+Rdef+tolerance
        assert mass_decimal(s,step_state,R)+debt<=W+dec(h)*W*D+tolerance
        assert Wnext+debt<=W+dec(h)*W*D+Rdef+tolerance
        debt_sum+=debt
        cost+=dec(h)*W*D+Rdef
    assert state_mass(s,states[-1],R)+debt_sum<=W0+cost+tolerance


def test_second_jet_consistency():
    checked=0
    for nu in (Q(0),Q(1,10),Q(1)):
        u=first.make_initial(Q(1),Q(1))
        q=first.quadratic(u)
        u1=first.first_derivative(u,nu,q)
        q1=first.quadratic_derivative(u,u1)
        modes=set(u)|set(u1)|set(q1)
        u2={n:first.vadd(q1.get(n,first.VZERO),
                          first.vscale(-nu*first.norm2(n),u1.get(n,first.VZERO)))
             for n in modes}
        s=sorted(modes)
        R=Q(5,4)
        # From |exp(-z)-1+z| <= z^2/2 for z>=0, mode by mode.
        C=sum((weight(n,R)/2 *
               (dec(nu*nu*first.norm2(n)**2)*norm_dec(to_dec_vec(u.get(n,ZERO)))+
                norm_dec(to_dec_vec(u2.get(n,ZERO)))))
              for n in s)
        assert C>0
        for h in (Q(1,10),Q(1,20),Q(1,40),Q(1,80)):
            v={n:first.vadd(first.vadd(u.get(n,ZERO),first.vscale(h,u1.get(n,ZERO))),
                             first.vscale(h*h/2,u2.get(n,ZERO))) for n in s}
            r=residual(s,u,v,nu,h,R)
            assert r<=C*dec(h)**2+Decimal('1e-60'),(nu,h,r,C)
            assert r>=0
            checked+=1
    return checked


def test_analytic_reserve():
    rng=Random(833003)
    pool=[(a,b,c) for a in range(-3,4) for b in range(-3,4)
          for c in range(-2,3)]
    checked=0
    for n in pool:
        # Exact, not a truncated numeric search for the uniform theorem.
        m=output.prior.degree(n)
        lam=output.prior.d2(n)
        assert Q(lam)*Q(5,4)**m <= 100*Q(3,2)**m
    for size in (1,3,5,8):
        for _ in range(40):
            s=rng.sample(pool,size)
            u={n:output.prior.rnd_vec(rng) for n in s}
            src=source_at(s,u)
            alloutputs=list(src)
            targets=rng.sample(alloutputs,min(10,len(alloutputs)))
            lap=sum((dec(output.prior.d2(n))*weight(n,Q(5,4))*
                     norm_dec(to_dec_vec(src[n])) for n in targets),Decimal(0))
            WH=state_mass(s,u,Q(3,2))
            DH=state_derivative(s,u,Q(3,2))
            assert lap<=100*WH*DH+Decimal('1e-55')
            checked+=1
    return checked


def run():
    with localcontext() as ctx:
        ctx.prec=100
        rng=Random(992033)
        pool=[(a,b,c) for a in range(-2,3) for b in range(-2,3)
              for c in range(-1,2)]
        cases=0
        for size in (1,3,5,7):
            for nu in (Q(0),Q(1,10),Q(1)):
                for R in (Q(1),Q(5,4),Q(3,2)):
                    for trial in range(8):
                        s=rng.sample(pool,size)
                        states=[]
                        for i in range(4):
                            states.append({n:output.prior.rnd_vec(rng) if (i+trial)%4 else ZERO
                                           for n in s})
                        test_arbitrary_path(s,states,
                            (Q(1,100),Q(1,50),Q(1,25)),nu,R)
                        cases+=1
        jets=test_second_jet_consistency()
        reserve=test_analytic_reserve()
        # Abstract mesh: local residual C*h^2 has total <= C*hMax*sum(h).
        for C in (Q(0),Q(1,3),Q(10)):
            for steps in ((Q(1,10),),
                          (Q(1,3),Q(1,6),Q(1,12)),
                          tuple(Q(1,100) for _ in range(37))):
                assert sum(C*h*h for h in steps)<=C*max(steps)*sum(steps)
        print(f'PASS: {cases} arbitrary full-output multi-step Galerkin paths')
        print(f'PASS: {jets} exact full-PDE second-jet O(h^2) residual comparisons')
        print(f'PASS: {reserve} analytic-reserve weighted Laplacian source comparisons')
        print('PASS: arbitrary-mesh residual sum <= C*hMax*sum(h)')
        print('PASS: residual stability + telescoping heat debt at all zero/nonzero modes')
        print('NOTE: existence of a uniform O(h^2) Galerkin ODE residual remains a proof obligation')


if __name__=='__main__':
    run()
