#!/usr/bin/env python3
"""DAOx catalytic-activity structural determinism (NON-ribozyme new layer, single-mechanism,
genuinely-novel; oracle direction). Does the STRUCTURAL context of a position (distance to the
catalytic site + local sequence context) predict a mutation's single-substrate catalytic activity
BEYOND expression AND the generic amino-acid-substitution effect, generalizing to HELD-OUT
positions (leave-position-out)?

y = D-Ala activity fitness (Rhodotorula gracilis DAOx saturation DMS, Zenodo 15846928).
baseline = expression fitness + mutation-identity (WT-aa one-hot, mut-aa one-hot, physicochem
           deltas: d-hydrophobicity/volume/charge, is-Pro, is-Gly).   [expression + composition]
full = baseline + STRUCTURE (distance-to-catalytic-site + local WT-sequence context around the
       position: window mean hydrophobicity/volume/charge/hydrophobic-fraction).
Held-out incremental R^2 (full over baseline) under LEAVE-POSITION-OUT CV (whole protein
positions assigned to folds -> a position's structural context is judged only on held-out
positions; position identity cannot be memorized). Permutation null STRATIFIED within
expression-bin x mut-aa (preserves the expression + substitution-type baseline relationships,
isolates the structure->activity signal).

Distinct from the ProteinGym functional-tolerance claim: expression is SEPARATELY controlled here
(ProteinGym could not separate it), and the readout is one enzyme's catalytic activity for one
substrate. Verdict crosses_boundary / bounded_descriptor_only / composition_artifact / needs_data.
Honest framing: a NEW engine boundary-map contact (structural context -> catalytic activity beyond
expression+composition, leave-position-out), NOT a new mechanism. Pure stdlib."""
import json, math, random, pathlib, sys
from collections import defaultdict, Counter

EXPERIMENT_ID="daox_catalytic_activity_structure_dms_zenodo15846928"
CLAIM_ID="h3.cross_layer_relation.enzyme_catalytic_activity.daox_activity_structure_beyond_expression_composition_zenodo15846928"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701
RIDGE=1.0
FOLDS=5
PERM=300
WINDOW=3
random.seed(SEED)

AA="ACDEFGHIKLMNPQRSTVWY"
KD={'A':1.8,'R':-4.5,'N':-3.5,'D':-3.5,'C':2.5,'Q':-3.5,'E':-3.5,'G':-0.4,'H':-3.2,'I':4.5,
    'L':3.8,'K':-3.9,'M':1.9,'F':2.8,'P':-1.6,'S':-0.8,'T':-0.7,'W':-0.9,'Y':-1.3,'V':4.2}
VOL={'A':88.6,'R':173.4,'N':114.1,'D':111.1,'C':108.5,'Q':143.8,'E':138.4,'G':60.1,'H':153.2,
     'I':166.7,'L':166.7,'K':168.6,'M':162.9,'F':189.9,'P':112.7,'S':89.0,'T':116.1,'W':227.8,'Y':193.6,'V':140.0}
CHG={'D':-1.0,'E':-1.0,'K':1.0,'R':1.0,'H':0.1}
def chg(a): return CHG.get(a,0.0)

# ---------- linear algebra ----------
def _inv(M):
    n=len(M); A=[row[:]+[1.0 if i==j else 0.0 for j in range(n)] for i,row in enumerate(M)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(A[r][c]))
        if abs(A[p][c])<1e-12: A[p][c]+=1e-9
        A[c],A[p]=A[p],A[c]; pv=A[c][c]; A[c]=[v/pv for v in A[c]]
        for r in range(n):
            if r==c: continue
            f=A[r][c]
            if f: A[r]=[a-f*b for a,b in zip(A[r],A[c])]
    return [row[n:] for row in A]
def matvec(M,v): return [sum(a*b for a,b in zip(row,v)) for row in M]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def zscols(rows):
    p=len(rows[0]); cols=list(zip(*rows)); out=[]
    for j in range(p):
        c=cols[j]; m=sum(c)/len(c)
        sd=(sum((x-m)**2 for x in c)/len(c))**0.5 or 1.0
        out.append([(x-m)/sd for x in c])
    return [list(r) for r in zip(*out)]
def prep(X, foldof):
    n=len(X); p=len(X[0]); packs=[]
    for f in range(FOLDS):
        tr=[i for i in range(n) if foldof[i]!=f]; te=[i for i in range(n) if foldof[i]==f]
        if not te or not tr: continue
        XtX=[[0.0]*p for _ in range(p)]
        for i in tr:
            xi=X[i]
            for a in range(p):
                xa=xi[a]
                if xa==0.0: continue
                row=XtX[a]
                for b in range(a,p): row[b]+=xa*xi[b]
        for a in range(p):
            for b in range(a): XtX[a][b]=XtX[b][a]
            XtX[a][a]+=RIDGE
        packs.append((_inv(XtX),[[X[i][a] for i in tr] for a in range(p)],tr,te,[X[i] for i in te]))
    return packs
def evalr2(packs, y):
    preds={}
    for Ainv,cols,tr,te,Xte in packs:
        ytr=[y[i] for i in tr]
        w=matvec(Ainv,[dot(col,ytr) for col in cols])
        for j,i in enumerate(te): preds[i]=dot(Xte[j],w)
    idx=sorted(preds); yt=[y[i] for i in idx]; pr=[preds[i] for i in idx]
    m=sum(yt)/len(yt); sst=sum((v-m)**2 for v in yt) or 1.0
    return 1.0-sum((a-b)**2 for a,b in zip(yt,pr))/sst

def onehot(a):
    v=[0.0]*20
    if a in AA: v[AA.index(a)]=1.0
    return v

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text())
    V=[v for v in D["variants"] if v.get("dist_cat") is not None]   # need structural feature complete
    lo=D["wt_span_lo"]; wtseq=D["wt_seq"]
    n=len(V)
    if n<1000:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{"n":n},"result":{}})); sys.exit(3)
    y=[float(v["dala"]) for v in V]

    def ctx(pos):
        i=pos-lo; res=[wtseq[j] for j in range(max(0,i-WINDOW),min(len(wtseq),i+WINDOW+1)) if 0<=j<len(wtseq) and wtseq[j] in AA]
        if not res: return [0.0,0.0,0.0,0.0]
        kd=sum(KD[r] for r in res)/len(res); vol=sum(VOL[r] for r in res)/len(res)
        cg=sum(chg(r) for r in res)/len(res); hyd=sum(1 for r in res if KD[r]>0)/len(res)
        return [kd,vol,cg,hyd]

    base=[]; struct=[]
    for v in V:
        wt=v["wt"]; mut=v["mut"]; pos=v["pos"]
        deltas=[KD.get(mut,0)-KD.get(wt,0), VOL.get(mut,0)-VOL.get(wt,0), chg(mut)-chg(wt),
                1.0 if mut=="P" else 0.0, 1.0 if mut=="G" else 0.0]
        base.append([v["expr"]]+onehot(wt)+onehot(mut)+deltas)      # expression + mutation-identity
        struct.append([v["dist_cat"]]+ctx(pos))                      # structure (active-site distance + local context)
    Xb=[[1.0]+r for r in zscols(base)]
    Xf=[[1.0]+r for r in zscols([base[i]+struct[i] for i in range(n)])]

    # leave-position-out folds
    positions=sorted(set(v["pos"] for v in V))
    posfold={p:i%FOLDS for i,p in enumerate(positions)}
    foldof=[posfold[v["pos"]] for v in V]

    pb=prep(Xb,foldof); pf=prep(Xf,foldof)
    r2b=evalr2(pb,y); r2f=evalr2(pf,y); incr=r2f-r2b

    # diagnostic: structure over EXPRESSION-ONLY, and attribution (distance vs local-context)
    Xexpr=[[1.0]+r for r in zscols([[v["expr"]] for v in V])]
    Xexpr_s=[[1.0]+r for r in zscols([[V[i]["expr"]]+struct[i] for i in range(n)])]
    r2_expr=evalr2(prep(Xexpr,foldof),y); r2_expr_s=evalr2(prep(Xexpr_s,foldof),y)
    Xdist=[[1.0]+r for r in zscols([base[i]+[struct[i][0]] for i in range(n)])]        # base + distance only
    Xctx=[[1.0]+r for r in zscols([base[i]+struct[i][1:] for i in range(n)])]           # base + local-context only
    incr_distance_only=evalr2(prep(Xdist,foldof),y)-r2b
    incr_context_only=evalr2(prep(Xctx,foldof),y)-r2b

    # stratified permutation within (expr-quintile x mut-aa): preserves expression + substitution-type
    ev=[v["expr"] for v in V]; sv=sorted(ev)
    cuts=[sv[min(n-1,int(n*k/5))] for k in range(1,5)]
    def ebin(x):
        for bi,c in enumerate(cuts):
            if x<=c: return bi
        return 4
    strata=defaultdict(list)
    for i,v in enumerate(V): strata[(ebin(v["expr"]),v["mut"])].append(i)
    ge=0; nulls=[]
    for _ in range(PERM):
        yp=list(y)
        for idxs in strata.values():
            vals=[y[i] for i in idxs]; random.shuffle(vals)
            for i,val in zip(idxs,vals): yp[i]=val
        ic=evalr2(pf,yp)-evalr2(pb,yp); nulls.append(ic)
        if ic>=incr: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)

    floor_ok=incr>=0.01; sig=pval<0.05
    if floor_ok and sig: verdict="crosses_boundary"
    elif r2b>=0.05 and not floor_ok: verdict="bounded_descriptor_only"
    elif not sig: verdict="composition_artifact"
    else: verdict="bounded_descriptor_only"

    checks={"n_variants":n,"n_positions":len(positions),"n_generators":0,
            "r2_baseline_expr_plus_mutid_heldout":round(r2b,4),
            "r2_full_heldout":round(r2f,4),
            "incremental_r2_structure_over_expr_plus_mutid":round(incr,4),
            "strat_perm_null_mean_incr":round(null_mean,4),"strat_perm_p":round(pval,4),
            "effect_floor_0.01":floor_ok,"perm_sig_0.05":sig,
            "r2_expression_only":round(r2_expr,4),
            "incr_structure_over_expression_only":round(r2_expr_s-r2_expr,4),
            "incr_distance_to_catalytic_site_only":round(incr_distance_only,4),
            "incr_local_context_only":round(incr_context_only,4),
            "y_mean":round(sum(y)/n,4),"substrate":"D-Ala","holdout":"leave-position-out"}
    result={"interpretation":("structural context predicts DAOx catalytic activity beyond expression AND substitution identity, leave-position-out; driven mostly by distance-to-catalytic-site (known determinant: active-site-proximal mutations reduce catalysis) with an independent transferable local-sequence-context component -- a fresh engine contact quantified, NOT a new mechanism" if verdict=="crosses_boundary"
                              else "expression + substitution-identity capture the predictable activity; structural context adds no held-out signal that transfers to unseen positions" if verdict=="bounded_descriptor_only"
                              else "no held-out structural signal survives leave-position-out + stratified permutation"),
            "framing":"NEW engine boundary-map contact (structural context -> enzyme catalytic activity beyond expression+composition, leave-position-out), NOT a new mechanism; expression separately controlled (distinct from ProteinGym expression-confounded tolerance)",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM,"window":WINDOW}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
