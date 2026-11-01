#!/usr/bin/env python3
"""Rigorous local quadrature helper for actual tetrahedral facet moments.

Requires python-flint. Inputs log_d_corners MUST enclose the actual log d
at the four corners; this module does not silently substitute sampled d.
The demo uses proved origin-tangent bounds for those actual values.
All error bounds and returned intervals use Arb arithmetic.
"""
from flint import arb, ctx


def integer_power(x, n):
    # Older python-flint versions route x**n through a branch-sensitive
    # function when x contains zero. Multiplication is valid for every ball.
    result=arb(1)
    while n:
        if n & 1:
            result *= x
        n >>= 1
        if n:
            x *= x
    return result


def constants():
    pi = arb.pi()
    L = (-arb(1)/3).acos()
    d0 = L/(2*pi*pi.sqrt())
    kappa = (2*pi/3).sqrt()/(4*L)
    jac = 2*arb(2).sqrt()/3
    gaussian = 1/(2*pi*(2*pi).sqrt())
    return L, d0, kappa, jac*gaussian


def origin_tangent_log_d_box(u, v):
    """Proved but coarse interval containing log d at a real ray point."""
    _, d0, kappa, _ = constants()
    q = (u+v)/arb(3).sqrt()
    r2 = u*u+v*v-2*u*v/3
    tangent = d0.log()-kappa*q
    return (tangent-r2/16).union(tangent)


def moment_cell(log_d_corners, u0, u1, v0, v1, p=0, q=0, order=8):
    """Enclose int_cell qcoord^p zcoord^q exp(-r^2/8) d(lambda)/d.

    x = u*a + v*b, with unit a,b and a.b=-1/3.
    qcoord=(u+v)/sqrt(3), zcoord=sqrt(2/3)*(v-u).
    Corners are ordered (u0,v0),(u1,v0),(u0,v1),(u1,v1).
    p,q are nonnegative integers, q even, and u0,v0 >= 0.
    Returns lower, upper, quadrature_error_upper, interpolation_eps_upper.
    """
    u0,u1,v0,v1 = map(arb,(u0,u1,v0,v1))
    assert u0 >= 0 and v0 >= 0 and u1 > u0 and v1 > v0
    assert isinstance(p,int) and isinstance(q,int) and p>=0 and q>=0 and q%2==0
    assert isinstance(order,int) and order>=1
    g00,g10,g01,g11 = map(arb,log_d_corners)
    hu,hv = u1-u0,v1-v0
    uc,vc = (u0+u1)/2,(v0+v1)/2
    ru,rv = hu/2,hv/2
    g0 = (g00+g10+g01+g11)/4
    gu = (g10+g11-g00-g01)/(2*hu)
    gv = (g01+g11-g00-g10)/(2*hv)
    guv = (g11-g10-g01+g00)/(hu*hv)
    r20 = uc*uc+vc*vc-2*uc*vc/3
    # E = -5|x|^2/8 - bilinear_interpolant(log d), centered coordinates.
    E0 = -5*r20/8-g0
    Eu = -5*uc/4+5*vc/12-gu
    Ev = -5*vc/4+5*uc/12-gv
    Euu = -arb(5)/8
    Evv = Euu
    Euv = arb(5)/12-guv
    _,_,_,prefactor = constants()
    sqrt3 = arb(3).sqrt()
    sqrt23 = (arb(2)/3).sqrt()

    nodes = [arb.legendre_p_root(order,k,weight=True) for k in range(order)]
    quadrature = arb(0)
    for tn,tw in nodes:
        du = ru*tn
        for sn,sw in nodes:
            dv = rv*sn
            qc = (uc+vc+du+dv)/sqrt3
            zc = sqrt23*(vc-uc+dv-du)
            expo = E0+Eu*du+Ev*dv+Euu*du*du+Euv*du*dv+Evv*dv*dv
            quadrature += tw*sw*integer_power(qc,p)*integer_power(zc,q)*expo.exp()
    quadrature *= prefactor*ru*rv

    # Cauchy majorant on complex polydisc of radii twice the FULL cell widths.
    Ru,Rv = 2*hu,2*hv
    qc0=(uc+vc)/sqrt3
    zc0=sqrt23*(vc-uc)
    pmajor=(qc0.abs_upper()+(Ru+Rv)/sqrt3)**p
    qmajor=(zc0.abs_upper()+sqrt23*(Ru+Rv))**q
    emajor=(E0.upper()+Eu.abs_upper()*Ru+Ev.abs_upper()*Rv
            +Euu.abs_upper()*Ru*Ru+Euv.abs_upper()*Ru*Rv
            +Evv.abs_upper()*Rv*Rv)
    M=(prefactor*pmajor*qmajor*emajor.exp()).upper()
    # |I-Q| <= 2 area M sum_j tau_j^(2n)/(1-tau_j), tau_j=1/4.
    error=(arb(16)*hu*hv*M/(3*arb(16)**order)).upper()
    eps=((hu*hu+hv*hv)/64).upper()
    lower=((quadrature.lower()-error)*(-eps).exp()).lower()
    upper=(quadrature.upper()+error).upper()
    if lower < 0:
        lower=arb(0)
    return lower,upper,error,eps


def demo():
    ctx.prec=160
    h=arb(3)/20
    corners=[origin_tangent_log_d_box(u,v)
             for u,v in [(arb(0),arb(0)),(h,arb(0)),(arb(0),h),(h,h)]]
    L,d0,kappa,_=constants()
    print('ACTUAL TETRAHEDRAL DIAGONAL: PROVED ORIGIN-CONSTANT ENCLOSURES')
    print('L =',L)
    print('d(0) =',d0)
    print('kappa =',kappa)
    print('Actual diagonal corner logs enclosed by global tangent/curvature bounds.')
    print('Cell: 0<=u,v<=3/20. This is not a full-window certificate.')
    for p,q in [(0,0),(2,0),(0,2),(4,2)]:
        lo,hi,error,eps=moment_cell(corners,0,h,0,h,p,q,8)
        assert lo>=0 and hi>lo and error>0
        print(f'M_{p},{q}: lower={lo}; upper={hi}')
        print('  Gauss error <=',error,'; log-interpolation error <=',eps)
    _,_,error,_=moment_cell(corners,0,h,0,h,0,0,8)
    assert error < arb('1e-10')
    assert (2*h*h/64).contains(arb(9)/12800)
    print('PASS: all output endpoints and errors are Arb enclosures.')


if __name__=='__main__':
    demo()
