#!/usr/bin/env python3
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import itertools,json,math
from pathlib import Path
import numpy as np
from scipy.special import roots_laguerre,roots_legendre,roots_hermite,ndtr
from scipy.linalg import eigh,null_space

rho=-1/3; sig=math.sqrt(1-rho*rho)
Y=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=float)/2
edges=list(itertools.combinations(range(4),2))
inc=np.zeros((6,4))
for e,(i,j) in enumerate(edges): inc[e,i]=1;inc[e,j]=-1
HG,HW=roots_hermite(64)

def utility_weight(means,i,j):
    other=[k for k in range(4) if k not in (i,j)]
    tt=(means[:,i]+means[:,j])[:,None]/2+HG[None,:]
    v=ndtr(tt-means[:,other[0],None])*ndtr(tt-means[:,other[1],None])
    return np.exp(-(means[:,i]-means[:,j])**2/4)*(v@HW)/(2*math.pi)

def run(nr,nt,deg):
    sr,wr=roots_laguerre(nr);tt,wt=roots_legendre(nt)
    exps=[(i,j) for total in range(deg+1) for i in range(total+1) for j in [total-i]]
    nb=len(exps); dim=6*nb
    D=np.zeros((dim,dim));K=np.zeros_like(D);Kplus=np.zeros_like(D);M=np.zeros((4,dim));Xp=[];WW=[];PP=[]; aa=[]
    for e,(i,j) in enumerate(edges):
        other=[k for k in range(4) if k not in (i,j)]
        u=-Y[other[0]];u=u/np.linalg.norm(u);z=-Y[other[1]];z=z/np.linalg.norm(z)
        angle=math.acos(u@z);v=z-(u@z)*u;v=v/np.linalg.norm(v)
        th=(tt+1)*angle/2
        X=(np.sqrt(2*sr)[:,None,None]*(np.cos(th)[None,:,None]*u+np.sin(th)[None,:,None]*v)).reshape(-1,3)
        weight=(wr[:,None]*wt[None,:]*angle/2/(2*math.pi)**1.5).ravel()
        coord1=X@u;coord2=X@v
        pol=np.column_stack([coord1**ii*coord2**jj for ii,jj in exps])
        means=rho/sig*(X@Y.T)
        wij=utility_weight(means,i,j)
        others=sum(utility_weight(means,i,k) for k in other)
        a=-rho*math.sqrt(2)/sig*(2*wij+others)
        sl=slice(e*nb,(e+1)*nb)
        D[sl,sl]=pol.T@((weight*a)[:,None]*pol)
        M[:,sl]=inc[e,:,None]*(weight@pol)[None,:]
        Xp.append(X);WW.append(weight);PP.append(pol);aa.append(a)
    for e in range(6):
        for f in range(e,6):
            sign=inc[e]@inc[f]
            if sign==0: continue
            X=Xp[e];Z=Xp[f]
            exponent=(2*rho*(X@Z.T)-rho*rho*((X*X).sum(1)[:,None]+(Z*Z).sum(1)[None,:]))/(2*(1-rho*rho))
            kern=np.exp(exponent)/(1-rho*rho)**1.5
            block=sign*(PP[e].T@((WW[e][:,None]*kern*WW[f][None,:])@PP[f]))
            K[e*nb:(e+1)*nb,f*nb:(f+1)*nb]=block
            K[f*nb:(f+1)*nb,e*nb:(e+1)*nb]=block.T
            exponentplus=(-2*rho*(X@Z.T)-rho*rho*((X*X).sum(1)[:,None]+(Z*Z).sum(1)[None,:]))/(2*(1-rho*rho))
            blockplus=sign*(PP[e].T@((WW[e][:,None]*np.exp(exponentplus)/(1-rho*rho)**1.5*WW[f][None,:])@PP[f]))
            Kplus[e*nb:(e+1)*nb,f*nb:(f+1)*nb]=blockplus
            Kplus[f*nb:(f+1)*nb,e*nb:(e+1)*nb]=blockplus.T
    ev,vec=eigh(K,D)
    Z=null_space(M)
    ec,vc=eigh(Z.T@K@Z,Z.T@D@Z)
    evenvals=eigh(Z.T@((K+Kplus)/2)@Z,Z.T@D@Z,eigvals_only=True)
    one=np.zeros(dim)
    # exact translations, using outward normal n_ij=(Yj-Yi)/sqrt2
    trans=np.zeros((dim,3))
    for e,(i,j) in enumerate(edges): trans[e*nb,:]=(Y[j]-Y[i])/math.sqrt(2)
    translation_res=np.linalg.norm((K-3*D)@trans)/np.linalg.norm(D@trans)
    np.savez_compressed(Path(__file__).parent/f'paired_boundary_degree{deg}_nr{nr}_nt{nt}.npz',D=D,K=K,Kplus=Kplus,M=M,full_eigenvalues=ev,full_eigenvectors=vec,mass_zero_basis=Z,mass_zero_eigenvalues=ec,mass_zero_eigenvectors=vc,exponents=np.array(exps),sites=Y)
    return {'all_full_eigenvalues':ev.tolist(),'all_mass_zero_eigenvalues':ec.tolist(),'radial_nodes':nr,'angular_nodes':nt,'degree':deg,'dimension':dim,'mass_constraint_rank':int(np.linalg.matrix_rank(M)),'minimum_K_over_D':float(ev[0]),'largest_K_over_D':ev[-8:].tolist(),'mass_zero_even_channel_largest':float(evenvals[-1]),'mass_zero_minimum_K_over_D':float(ec[0]),'mass_zero_largest_K_over_D':ec[-8:].tolist(),'translation_eigenvalue3_relative_residual':float(translation_res),'single_rule_minimum_normalized_half_hessian':float(1+ev[0]),'paired_contrast_minimum_normalized_half_hessian':float(1-ec[-1])}

out=[]
for spec in [(10,14,2),(16,20,2),(24,28,2),(14,20,3),(22,28,3)]:
    r=run(*spec);out.append(r);print(json.dumps(r),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps({'status':'Non-certified floating point spectral diagnostics only','conventions':'D=rN_r, K=boundary T_-r bilinear form. Same-direction Hessian D+K; opposite-direction equal-mass Hessian D-K on M u=0.','runs':out},indent=2)+'\n')
