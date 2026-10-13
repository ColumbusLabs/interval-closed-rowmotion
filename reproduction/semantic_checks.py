#!/usr/bin/env python3
"""Small literal-toggle cross-checks; these computations are not universal proofs."""
import json, math, sys
if sys.flags.optimize:raise SystemExit('Run without Python optimization.')

def grid(m,n):
    points=[(i,j) for i in range(m) for j in range(n)]
    intervals=[]
    for a,x in enumerate(points):
        for c,z in enumerate(points):
            if x[0]<=z[0] and x[1]<=z[1]:
                inside=sum(1<<k for k,y in enumerate(points) if x[0]<=y[0]<=z[0] and x[1]<=y[1]<=z[1])
                intervals.append(((1<<a)|(1<<c),inside))
    def convex(mask):return all(mask&ends!=ends or mask&inside==inside for ends,inside in intervals)
    valid={mask for mask in range(1<<(m*n)) if convex(mask)}
    def sweep(mask,reverse=True):
        indices=range(m*n-1,-1,-1) if reverse else range(m*n)
        for k in indices:
            candidate=mask^(1<<k)
            if candidate in valid:mask=candidate
        return mask
    mapping={s:sweep(s) for s in valid}
    assert set(mapping.values())==valid
    assert all(sweep(mapping[s],False)==s for s in valid)
    periods={};unseen=set(valid)
    while unseen:
        first=next(iter(unseen));cycle=[];s=first
        while not cycle or s!=first:
            assert s not in cycle
            cycle.append(s);s=mapping[s]
        for s in cycle:periods[s]=len(cycle)
        unseen.difference_update(cycle)
    full_rows=sum(all(s&(((1<<n)-1)<<(i*n)) for i in range(m)) for s in valid)
    expected=math.comb(n+m-1,m)*math.comb(n+m,m)//(m+1)
    assert full_rows==expected,(m,n,full_rows,expected)
    assert math.comb(n+m-1,m)*math.comb(n+m,m)%(m+1)==0
    record={'width':m,'length':n,'states':len(valid),'row_nonempty':full_rows,'periods':sorted(set(periods.values()))}
    if m==1:
        assert len(valid)==1+n*(n+1)//2
        bad=sum(p!=n+2 for p in periods.values())
        assert bad<=(n+2)//2+2
        for s,p in periods.items():
            if s not in {0,(1<<n)-1}:assert p==n+2 or (n+2)%2==0 and p==(n+2)//2
        record['exceptional_states']=bad
    if m==3:
        baseline=sum(p==n+4 for p in periods.values());two=sum(p==2*n+10 for p in periods.values());three=sum(p==3*n+14 for p in periods.values());other=sum(p not in {n+4,2*n+10,3*n+14} for p in periods.values())
        assert baseline+two+three+other==len(valid)
        record['period_partition']={'baseline':baseline,'two':two,'three':three,'other':other}
    return record

def main():
    cases=[(1,n) for n in range(13)]+[(2,n) for n in range(7)]+[(3,n) for n in range(5)]+[(4,n) for n in range(4)]
    records=[grid(m,n) for m,n in cases]
    print(json.dumps({'status':'pass','scope':'Finite literal point-toggle checks of order-convexity, reversibility, least returns, chain counts, row-nonempty Narayana counts and width-three partition. No asymptotic inference.','cases':records},indent=2))
if __name__=='__main__':main()
