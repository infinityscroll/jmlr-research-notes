#!/usr/bin/env python3
"""Exact independent polynomial check of the pure-entry layer identity.

Gaussian rational coefficients are pairs of fractions. No Gaussian-generator
code or flow matrix assembly is used in computing these layer forms.
"""
import itertools, json, math, random
from fractions import Fraction as F
from pathlib import Path

ZERO=(F(0), F(0))
def ca(a,b): return (a[0]+b[0],a[1]+b[1])
def cm(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cs(a,s): return (a[0]*s,a[1]*s)
def cc(a): return (a[0],-a[1])
def put(out,e,v):
    w=ca(out.get(e,ZERO),v)
    if w==ZERO: out.pop(e,None)
    else: out[e]=w
def add(a,b,s=F(1)):
    out=a.copy()
    for e,v in b.items(): put(out,e,cs(v,s))
    return out
def scale(a,s): return {e:cs(v,s) for e,v in a.items() if cs(v,s)!=ZERO}
def mul(a,b):
    out={}
    for e,v in a.items():
        for f,w in b.items(): put(out,tuple(x+y for x,y in zip(e,f)),cm(v,w))
    return out
def inner(a,b):
    out=ZERO
    for e,v in a.items():
        out=ca(out,cs(cm(cc(v),b.get(e,ZERO)),math.prod(math.factorial(x) for x in e)))
    return out
def norm(a):
    z=inner(a,a);assert z[1]==0
    return z[0]
def compositions(k,d):
    if d==1:
        yield (k,);return
    for a in range(k+1):
        for t in compositions(k-a,d-1):yield (a,)+t
def contract(a,d,which):
    out={}
    for e,v in a.items():
        for i in range(d):
            j=which*d+i
            if e[i] and e[j]:
                f=list(e);f[i]-=1;f[j]-=1
                put(out,tuple(f),cs(v,e[i]*e[j]))
    return out
def ordinary_sym(a,d):
    out={}
    for e,v in a.items():put(out,e[:d]+tuple(x+y for x,y in zip(e[d:2*d],e[2*d:])),v)
    return out
def ordinary_swap(a,d):return {e[:d]+e[2*d:]+e[d:2*d]:v for e,v in a.items()}
def falling(k,l):return math.factorial(k)//math.factorial(k-l)

def layer_form(a,k,d):
    derivatives={(0,0):a}
    for l in range(1,k+1):
        for p in range(l+1):
            derivatives[p,l-p]=contract(derivatives[p-1,l-p],d,1) if p else contract(derivatives[0,l-1],d,2)
    total=F(0);records=[]
    for l in range(1,k+1):
        e=[scale(derivatives[p,l-p],F(1,falling(k,l)*math.factorial(p)*math.factorial(l-p))) for p in range(l+1)]
        cy=scale(derivatives[l,0],F(1,falling(k,l)**2))
        cz=ordinary_swap(scale(derivatives[0,l],F(1,falling(k,l)**2)),d)
        b=add(cy,cz)
        if l<k:
            s={}
            for ep in e:s=add(s,ordinary_sym(ep,d))
            factor=F(math.factorial(k)**2,math.factorial(k-l)**2)
            constant=factor*norm(s)
            delta=factor*F(math.comb(k,l)**2,2)*norm(b)
            q=constant+delta
            assert constant>=0 and delta>=0
            records.append({'l':l,'constant':str(constant),'delta':str(delta)})
        else:
            i={}
            for ep in e[1:-1]:i=add(i,ordinary_sym(ep,d))
            bs=ordinary_sym(b,d)
            q=math.factorial(k)**2*(norm(i)+F(3,2)*inner(bs,i)[0])
            completed=math.factorial(k)**2*(norm(add(i,bs,F(3,4)))-F(9,16)*norm(bs))
            assert q==completed
            records.append({'l':l,'value':str(q)})
        total+=q
    # The physical trace identity and its norm bound, independently in Fock coordinates.
    if k>=2:
        prev=add(scale(derivatives[k-1,0],F(1,falling(k,k-1)**2)),ordinary_swap(scale(derivatives[0,k-1],F(1,falling(k,k-1)**2)),d))
        assert contract(prev,d,1)==b
        assert norm(b)<=d*norm(prev)
    return total,records

def product_tensor(p,q,r):
    return {a+b+c:cm(cc(x),cm(y,z)) for a,x in p.items() for b,y in q.items() for c,z in r.items()}
def gram_per(polys):
    g=[[inner(x,y) for y in polys] for x in polys]
    ans=ZERO
    for perm in itertools.permutations(range(3)):
        v=(F(1),F(0))
        for i,j in enumerate(perm):v=cm(v,g[i][j])
        ans=ca(ans,v)
    assert ans[1]==0
    return ans[0]

def main():
    rng=random.Random(20261030);records=[]
    for k,d in [(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3),(5,2)]:
        for trial in range(3):
            polys=[{e:(F(rng.randrange(-2,3)),F(rng.randrange(-2,3))) for e in compositions(k,d)} for _ in range(3)]
            forms=[]
            for cut in range(3):
                p=polys[cut];q=polys[(cut+1)%3];r=polys[(cut+2)%3]
                forms.append(layer_form(product_tensor(p,q,r),k,d)[0])
            exact=norm(mul(mul(polys[0],polys[1]),polys[2]))-gram_per(polys)
            assert sum(forms,F(0))/3==exact,(k,d,trial,forms,exact)
            if k>=3 and d<=F(8*k*k,9):assert min(forms)>=0
            records.append({'k':k,'d':d,'trial':trial,'averaged_layer_form':str(exact),'passed':True})
    out={'passed':True,'exact_complex_product_trials':len(records),'records':records,
         'scope':'Independent exact normalization and complex phase checks; the all-k positivity theorem is analytic.'}
    Path(__file__).with_name('LITERAL_LAYER_CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'passed':True,'exact_complex_product_trials':len(records)}))

if __name__=='__main__':main()
