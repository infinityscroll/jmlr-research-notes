"""New exact coupled-cycle and overlapping-cactus checks, standard library only."""
from fractions import Fraction as F
from pathlib import Path
import itertools,json,random
HERE=Path(__file__).resolve().parent

def zeros(n,m=None):return [[F(0) for _ in range(n if m is None else m)] for _ in range(n)]
def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def tr(A):return [list(x) for x in zip(*A)]
def mul(A,B):return [[sum((a*b for a,b in zip(row,col)),F(0)) for col in zip(*B)] for row in A]
def inverse(A):
 n=len(A);B=[list(row)+unit for row,unit in zip(A,eye(n))]
 for j in range(n):
  k=next(k for k in range(j,n) if B[k][j]);B[j],B[k]=B[k],B[j]
  q=B[j][j];B[j]=[x/q for x in B[j]]
  for i in range(n):
   if i!=j:
    q=B[i][j];B[i]=[x-q*y for x,y in zip(B[i],B[j])]
 return [row[n:] for row in B]
def diag(values):
 A=zeros(len(values))
 for i,v in enumerate(values):A[i][i]=v
 return A
def blockdiag(blocks):
 n=sum(map(len,blocks));A=zeros(n);offset=0
 for block in blocks:
  for i,row in enumerate(block):
   for j,v in enumerate(row):A[offset+i][offset+j]=v
  offset+=len(block)
 return A
def cycle_T(m,a):
 T=eye(m)
 for i in range(m):T[i][(i+1)%m]=-a
 return T
def congruence(T,S):return mul(tr(T),mul(S,T))
def fmt(A):return [[str(v) for v in row] for row in A]

# Exact density of homogeneous nontrivial branch changes, lengths 3 through 12.
density=[]
for m in range(3,13):
 a=F(1,2);M=mul(tr(cycle_T(m,1/a)),inverse(tr(cycle_T(m,a))))
 assert all(v for row in M for v in row)
 expected_diag=(1-a**(m-2))/(1-a**m)
 assert all(M[i][i]==expected_diag for i in range(m))
 density.append({'length':m,'entrywise_nonzero':True,'diagonal':str(expected_diag)})

# Exhaust all 512 cross-error supports between two three-cycles. Check
# invariance of the entire support vector space, not a lucky sampled Omega.
M0=mul(tr(cycle_T(3,F(2))),inverse(tr(cycle_T(3,F(1,2)))))
M1=mul(tr(cycle_T(3,F(3))),inverse(tr(cycle_T(3,F(1,3)))))
atlas=[]
for mask in range(512):
 allowed={(i,j) for i in range(3) for j in range(3) if mask>>(3*i+j)&1}
 partial0=any(0<sum((i,j) in allowed for i in range(3))<3 for j in range(3))
 partial1=any(0<sum((i,j) in allowed for j in range(3))<3 for i in range(3))
 actual=[]
 for flips in itertools.product((0,1),repeat=2):
  A=M0 if flips[0] else eye(3);B=M1 if flips[1] else eye(3)
  preserves=all(A[r][i]*B[c][j]==0 for i,j in allowed for r in range(3) for c in range(3) if (r,c) not in allowed)
  predicted=not ((flips[0] and partial0) or (flips[1] and partial1))
  assert preserves==predicted,(mask,flips)
  if preserves:actual.append(flips)
 assert len(actual)==2**(int(not partial0)+int(not partial1))
 atlas.append({'mask':mask,'partial':[partial0,partial1],'surviving_flips':actual})

# Whole positive-definite covariance examples, including each possible branch count.
fixtures=[]
for name,allowed in [('none',set()),('single_bridge',{(0,0)}),('one_sided_full',{(i,0) for i in range(3)}),('full',set(itertools.product(range(3),repeat=2))),('matching',{(i,i) for i in range(3)})]:
 O=eye(6)
 for i,j in allowed:O[i][j+3]=O[j+3][i]=F(1,1000+37*(3*i+j))
 assert all(O[i][i]>sum(abs(O[i][j]) for j in range(6) if i!=j) for i in range(6))
 true=blockdiag([cycle_T(3,F(1,2)),cycle_T(3,F(1,3))]);Ti=inverse(true);Sigma=mul(tr(Ti),mul(O,Ti))
 survive=[]
 for flips in itertools.product((0,1),repeat=2):
  T=blockdiag([cycle_T(3,F(2) if flips[0] else F(1,2)),cycle_T(3,F(3) if flips[1] else F(1,3))]);Op=congruence(T,Sigma)
  permitted=lambda i,j: i==j or (i<3<=j and (i,j-3) in allowed) or (j<3<=i and (j,i-3) in allowed)
  if all(permitted(i,j) or Op[i][j]==0 for i in range(6) for j in range(6)):
   assert mul(tr(inverse(T)),mul(Op,inverse(T)))==Sigma
   survive.append(flips)
 predicted=2**(int(not any(0<sum((i,j) in allowed for i in range(3))<3 for j in range(3)))+int(not any(0<sum((i,j) in allowed for j in range(3))<3 for i in range(3))))
 assert len(survive)==predicted,(name,survive,predicted)
 fixtures.append({'name':name,'bidirected_cross_edges':sorted(allowed),'generic_expected_branches':predicted,'exact_surviving_flips':survive,'Sigma':fmt(Sigma)})

# Construct arbitrary coherent cycle-cacti by gluing each new cycle at one
# existing vertex. The graph, not covariance data, chooses reconstruction.
def recover_cactus(cycles,K):
 n=len(K);parents=[[] for _ in range(n)];children=[[] for _ in range(n)];membership=[[] for _ in range(n)]
 for ci,cyc in enumerate(cycles):
  for pos,v in enumerate(cyc):
   parents[v].append(cyc[pos-1]);children[v].append(cyc[(pos+1)%len(cyc)]);membership[v].append(ci)
 d=[None]*n
 for v in range(n):
  if len(membership[v])>1:
   p,q=parents[v][:2];d[v]=K[p][v]*K[q][v]/K[p][q]
 for step in range(n):
  changed=False
  for v in range(n):
   if d[v] is None and len(children[v])==1 and d[children[v][0]] is not None:
    j=children[v][0];d[v]=K[v][v]-K[v][j]**2/d[j];changed=True
  if not changed:break
 assert all(x is not None and x>0 for x in d)
 T=eye(n)
 for i in range(n):
  for j in children[i]:T[i][j]=K[i][j]/d[j]
 return T,d
rng=random.Random(20261030);cactus=[]
for case in range(24):
 cycles=[list(range(3+case%3))];n=len(cycles[0])
 for _ in range(1,2+case%4):
  anchor=rng.randrange(n);length=3+rng.randrange(3)
  cycles.append([anchor]+list(range(n,n+length-1)));n+=length-1
 T=eye(n)
 for cyc in cycles:
  for i,j in zip(cyc,cyc[1:]+cyc[:1]):T[i][j]=F(rng.choice((-1,1)),17+rng.randrange(20))
 d=[F(2+rng.randrange(5),1+rng.randrange(3)) for _ in range(n)]
 K=mul(T,mul(diag(d),tr(T)));Q=inverse(K)
 Tp,dp=recover_cactus(cycles,inverse(Q))
 assert Tp==T and dp==d
 cactus.append({'case':case,'vertices':n,'cycle_lengths':list(map(len,cycles)),'articulations':sum(sum(v in c for c in cycles)>1 for v in range(n)),'exact_recovery':True})

# Named five-vertex overlap fixture.
cycles=[[0,1,2],[0,3,4]];T=eye(5)
for cyc in cycles:
 for i,j in zip(cyc,cyc[1:]+cyc[:1]):T[i][j]=-F(1,2)
d=[F(1)]*5;K=mul(T,tr(T));Tp,dp=recover_cactus(cycles,K)
assert Tp==T and dp==d
out={'status':'PASS','method':'Exact Fraction arithmetic, no imported prior checker','branch_change_density':density,'cross_support_patterns':len(atlas),'cross_support_flip_comparisons':4*len(atlas),'support_atlas':atlas,'whole_covariance_fixtures':fixtures,'cactus_reconstructions':cactus,'overlap_fixture':{'cycles':cycles,'precision':fmt(K),'Sigma':fmt(inverse(K)),'articulation_d_ratio':str(K[2][0]*K[4][0]/K[2][4])},'scope':'Checks support the separately written uniform proofs. Finite enumeration alone does not establish generic graph identification.'}
(HERE/'EXACT_COUPLING_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','method','cross_support_patterns','cross_support_flip_comparisons']},indent=2))
print('Exact whole-covariance fixtures:',len(fixtures),'Cactus reconstructions:',len(cactus))

# Essential boundary: two length-two cycles, matched cross-error correlations.
# Reciprocal column swaps can be synchronized, despite both cycles having a
# partial outside bidirected neighbor. This is a generic symbolic mechanism.
T0=[[F(1),-F(1,2)],[-F(1,3),F(1)]]
T1=[[F(1),-F(1,4)],[-F(1,5),F(1)]]
A0=[[F(1),-F(3)],[-F(2),F(1)]]
A1=[[F(1),-F(5)],[-F(4),F(1)]]
T=blockdiag([T0,T1]);Ta=blockdiag([A0,A1]);O=eye(4)
O[0][2]=O[2][0]=F(1,10);O[1][3]=O[3][1]=F(1,7)
Ti=inverse(T);Sigma=mul(tr(Ti),mul(O,Ti));Oa=congruence(Ta,Sigma)
allowed=lambda i,j:i==j or {i,j} in [{0,2},{1,3}]
assert all(allowed(i,j) or Oa[i][j]==0 for i in range(4) for j in range(4))
assert mul(tr(inverse(Ta)),mul(Oa,inverse(Ta)))==Sigma
assert T!=Ta
boundary={'status':'PASS','vertices':4,'directed_edges':[[0,1],[1,0],[2,3],[3,2]],'bidirected_edges':[[0,2],[1,3]],'both_cycles_have_partial_outside_neighbor':True,'T':fmt(T),'T_alternative':fmt(Ta),'Omega':fmt(O),'Omega_alternative':fmt(Oa),'Sigma':fmt(Sigma),'scope':'Exact fixture of a generic simultaneous reciprocal-swap mechanism, proving length-two cycles must be excluded from the dense-change criterion.'}
(HERE/'TWO_CYCLE_LENGTH_BOUNDARY.json').write_text(json.dumps(boundary,indent=2)+'\n')
print('Length-two simultaneous-swap boundary: PASS')
