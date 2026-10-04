"""Independent transcript certificate: reconstruct integer margins from payoff columns.
Does not import production simulation code or use its phase/count/score formulas.
"""
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
from pathlib import Path
import json,gzip,time,hashlib,math
R=Path(__file__).resolve().parent
out=Path(__file__).parent
if not __debug__: raise RuntimeError('Run verification without -O or -OO')
start=time.time(); data=json.loads((R/'order3_event_result.json').read_text()); c=json.loads((R/'order3_construction.json').read_text())
scale=int(data['integer_scale']); B=[[int(F(x)*scale) for x in row] for row in c['matrix']];n=len(B)
assert all(F(x)*scale==B[i][j] for i,row in enumerate(c['matrix'])for j,x in enumerate(row))
assert all(B[i][j]==-B[j][i] for i in range(n) for j in range(n))
cols=list(map(list,zip(*B))); z=[1]+[0]*(n-1); score=cols[0][:];t=1
samples={x['event']:x for x in data['samples']}; checked=0; runs=batches=cycles=0
norm=max(abs(x)for row in B for x in row)
def sample(event):
 global checked
 if event not in samples:return
 s=samples[event]; H=max(score)
 assert int(s['t'])==t and int(s['height_scaled'])==H
 assert F(s['gap'])==F(2*H,scale*t) and F(s['normalized_gap'])==F(2*H,norm*t)
 assert score==[sum(a*b for a,b in zip(row,z))for row in B]
 checked+=1
sample(0)
minimum=10**100
with gzip.open(R/'order3_event_transcript.jsonl.gz','rt')as f:
 for event,line in enumerate(f):
  rec=json.loads(line);assert rec['event']==event
  if rec['kind']=='maximal_constant_action':
   a=rec['action'];L=int(rec['length']);assert L>0
   for j in range(n):
    if j==a:continue
    g=score[a]-score[j];last=g+(L-1)*(B[a][a]-B[j][a]);assert min(g,last)>0,(event,a,j,g,last)
    minimum=min(minimum,g,last)
   score=[s+L*x for s,x in zip(score,cols[a])];z[a]+=L;t+=L;runs+=1
   assert max(score)>score[a],(event,'run not maximal')
  else:
   assert rec['kind']=='RPS_cycle_batch'
   N=int(rec['cycles']);L=list(map(int,rec['first_lengths']));assert N>0 and min(L)>0
   actions=[1,2,3]
   d0=[sum(L[i]*cols[a][j] for i,a in enumerate(actions))for j in range(n)]
   d1=[3*sum(cols[a][j]for a in actions)for j in range(n)]
   prev=[0]*n;prev_slope=[0]*n
   for i,a in enumerate(actions):
    for endpoint in (0,1):
     # Twice each leader-minus-rival quadratic avoids half-integral coefficients.
     v0=[score[j]+prev[j]+endpoint*(L[i]-1)*cols[a][j]for j in range(n)]
     v1=[2*d0[j]-d1[j]+2*prev_slope[j]+endpoint*6*cols[a][j]for j in range(n)]
     for j in range(n):
      if j==a:continue
      aa=d1[a]-d1[j];bb=v1[a]-v1[j];cc=2*(v0[a]-v0[j])
      offsets=[0,N-1]
      if aa>0:
       r=(-bb)//(2*aa)
       offsets.extend([max(0,min(N-1,r)),max(0,min(N-1,r+1))])
      val=min((aa*r+bb)*r+cc for r in offsets)
      assert val>0,(event,a,j,endpoint,N,aa,bb,cc,val)
      minimum=min(minimum,F(val,2))
    prev=[prev[j]+L[i]*cols[a][j]for j in range(n)]
    prev_slope=[prev_slope[j]+3*cols[a][j]for j in range(n)]
   for i,a in enumerate(actions):
    inc=N*L[i]+3*N*(N-1)//2;z[a]+=inc;t+=inc
   score=[score[j]+N*d0[j]+(N*(N-1)//2)*d1[j]for j in range(n)]
   runs+=3*N;batches+=1;cycles+=N
  assert t==int(rec['t']) and t==sum(z)
  sample(event+1)
  if (event+1)%250000==0:print('verified',event+1,'events in',round(time.time()-start,2),'seconds',flush=True)
assert event+1==data['events']==2000000
assert score==list(map(int,data['final_scores_scaled'])) and z==list(map(int,data['counts'])) and t==int(data['t'])
assert runs==int(data['represented_constant_action_runs']) and batches==data['certified_base_cycle_batches'] and cycles==int(data['certified_base_cycles'])
Q=int(c['Q']);q=Q+250000
assert z==[1]+[sum(F(row[j])*(math.comb(q,j+1)-math.comb(Q,j+1))for j in range(3)) for row in c['C']]
with localcontext()as ctx:
 ctx.prec=90;cp=F(c['rate_constant_power_k']);constant=(D(cp.numerator)/D(cp.denominator))**(D(1)/3)
 ratio=(D(2*max(score))/D(scale*t))*D(t)**(D(1)/3)/constant
 report=dict(status='PASS',events=event+1,represented_runs=runs,batches=batches,cycles=cycles,samples=checked,t=str(t),minimum_scaled_integer_margin=str(minimum),ratio=str(ratio),relative_deviation=str(ratio-1),seconds=time.time()-start,checks=['every constant run decision by affine endpoint comparison','every batched cycle decision by exact quadratic integer minimum','all actions including setup and every outer action','every event count/time update','every saved sample gap and normalization','final score/count identities','phase-boundary count formula'],scope='Finite exact independently coded certificate; shares only payoff matrix, transcript word, and output data, imports no production routines',inputs={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [R/'order3_construction.json',R/'order3_event_result.json',R/'order3_event_transcript.jsonl.gz']})
(out/'full-cubic-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
