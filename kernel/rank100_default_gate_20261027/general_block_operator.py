"""Exact O(1)-size covariance reduction for any n>b>=2, full-rank blocks.

A row vector is represented by its own-coordinate, selected-block-sum, and
all-coordinate-sum coefficients, separately for e and f. No n-dimensional
matrix is materialized.
"""
from fractions import Fraction as F

def image(n,b,s,delta,eta,stale,C):
    lam=F(n,b)*s*s;gamma=1/(F(n,b)*s);cor=1-delta
    def add(x,y):return [a+c for a,c in zip(x,y)]
    def scale(c,x):return [c*a for a in x]
    y=[1/(1+s),F(0),F(0),s/(1+s),F(0),F(0)]
    e=[F(1),F(0),F(0),F(0),F(0),F(0)]
    f=[F(0),F(0),F(0),F(1),F(0),F(0)]
    g=add(scale(delta,y),scale(lam,e if stale else y))
    g[2]+=cor/(1+s);g[5]+=cor*s/(1+s)
    sumg=[F(0),g[0],b*g[2],F(0),g[3],b*g[5]]
    step=scale(1/(lam+2*delta),add(g,scale(-cor/(b+lam-(b-2)*delta),sumg)))
    basev=add(scale(1-s,f),scale(s,y))
    w=[add(y,scale(-eta,step)),y]
    v=[add(basev,scale(-gamma*eta,step)),basev]
    def dot(x,y,ix,iy):
        a,c,d=x;aa,cc,dd=y
        return a*aa*(ix==iy)+a*cc*(ix<b)+c*aa*(iy<b)+a*dd+d*aa+c*cc*b+(c*dd+d*cc)*b+d*dd*n
    def total(x):return x[0]+b*x[1]+n*x[2]
    ca,cb,cc,cd,ce,cf=C
    def bil(x,y,ix,iy):
        xe,xf=x[:3],x[3:];ye,yf=y[:3],y[3:]
        ex,fx,ey,fy=map(total,[xe,xf,ye,yf])
        return ca*dot(xe,ye,ix,iy)+(cb-ca)*ex*ey/n+cc*(dot(xe,yf,ix,iy)+dot(xf,ye,ix,iy))+(cd-cc)*(ex*fy+fx*ey)/n+ce*dot(xf,yf,ix,iy)+(cf-ce)*fx*fy/n
    out=[]
    for x,y0 in [(w,w),(w,v),(v,v)]:
        diag=(b*bil(x[0],y0[0],0,0)+(n-b)*bil(x[1],y0[1],b,b))/n
        off=(b*(b-1)*bil(x[0],y0[0],0,1)+b*(n-b)*(bil(x[0],y0[1],0,b)+bil(x[1],y0[0],b,0))+(n-b)*(n-b-1)*bil(x[1],y0[1],b,b+1))/(n*(n-1))
        out.extend([diag-off,diag+(n-1)*off])
    return out

