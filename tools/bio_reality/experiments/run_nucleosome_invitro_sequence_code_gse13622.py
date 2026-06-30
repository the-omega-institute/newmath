#!/usr/bin/env python3
"""In-vitro nucleosome sequence code (oracle direction; single-mechanism like claim 160/170):
does local DNA sequence STRUCTURE predict in-vitro reconstituted nucleosome occupancy BEYOND
low-order composition? GSM351491 (Kaplan 2009 GSE13622: purified yeast DNA + chicken histone
octamer + salt dialysis -- one physical mechanism, no perturbation arm), 300bp windows on R64.
y = mean normalized occupancy. Held-out incremental R^2 of sequence-STRUCTURE features (rotational
WW 10-11bp periodicity, poly-dA:dT clustering, entropy, palindrome) over a LOW-ORDER COMPOSITION
baseline (mononucleotide A/C/G fractions), chromosome-held-out, within GC-decile permutation null.
NEW engine boundary-map contact (classic nucleosome code quantified beyond composition), not a new
mechanism. Pure stdlib, deterministic."""
import json, math, random, pathlib, time

EXPERIMENT_ID="nucleosome_invitro_sequence_code_gse13622"
CLAIM_ID="h3.cross_layer_relation.nucleosome_positioning.invitro_occupancy_sequence_structure_beyond_composition_gse13622"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; PERM=500; FOLDS=5; RIDGE=1e-3

def features(seq):
    s=seq.upper(); n=len(s)
    if n<200: return None
    a=s.count("A")/n; c=s.count("C")/n; g=s.count("G")/n  # mononucleotide composition (low-order)
    # STRUCTURE features (beyond composition):
    homo=0;cur=0;prev=""
    for b in s:
        if b==prev: cur+=1
        else: cur=1
        prev=b
        if b in "AT": homo=max(homo,cur)
    mxat=0;cur=0
    for b in s:
        if b in "AT": cur+=1
        else: cur=0
        mxat=max(mxat,cur)
    ww=[1 if s[i] in "AT" and s[i+1] in "AT" else 0 for i in range(n-1)]
    m=sum(ww)/len(ww) if ww else 0
    def ac(lag):
        num=sum((ww[i]-m)*(ww[i+lag]-m) for i in range(len(ww)-lag)); den=sum((x-m)**2 for x in ww) or 1.0
        return num/den
    ww_period=(ac(10)+ac(11))/2   # rotational nucleosome-positioning signal
    di={}
    for i in range(n-1): di[s[i:i+2]]=di.get(s[i:i+2],0)+1
    tot=sum(di.values()) or 1; ent=-sum((cnt/tot)*math.log(cnt/tot) for cnt in di.values())
    comp={"A":"T","T":"A","G":"C","C":"G"};pal=0;K=6;step=10
    for i in range(0,n-K,step):
        k=s[i:i+K];rc="".join(comp.get(b,"N") for b in k[::-1])
        if rc in s: pal+=1
    paldens=pal/max(1,(n//step))
    return {"a":a,"c":c,"g":g,"homo":float(homo),"mxat":float(mxat),"ww_period":ww_period,"dient":ent,"paldens":paldens}

def _inv(M):
    p=len(M);A=[row[:]+[1.0 if i==j else 0.0 for j in range(p)] for i,row in enumerate(M)]
    for cc in range(p):
        piv=max(range(cc,p),key=lambda r:abs(A[r][cc]));A[cc],A[piv]=A[piv],A[cc]
        d=A[cc][cc] if abs(A[cc][cc])>1e-12 else 1e-12
        for k in range(2*p):A[cc][k]/=d
        for r in range(p):
            if r!=cc:
                f=A[r][cc]
                for k in range(2*p):A[r][k]-=f*A[cc][k]
    return [row[p:] for row in A]
def prep(X,folds):
    p=len(X[0]);out=[]
    for te in folds:
        ts=set(te);tr=[i for i in range(len(X)) if i not in ts]
        XtX=[[sum(X[i][a]*X[i][b] for i in tr)+(RIDGE if a==b else 0.0) for b in range(p)] for a in range(p)]
        out.append((_inv(XtX),tr,te))
    return out,X,p
def evalr2(pr,y):
    folds,X,p=pr;n=len(y);yb=sum(y)/n;sse=0.0;sst=0.0
    for inv,tr,te in folds:
        Xty=[sum(X[i][a]*y[i] for i in tr) for a in range(p)]
        beta=[sum(inv[a][b]*Xty[b] for b in range(p)) for a in range(p)]
        for i in te:
            pred=sum(beta[a]*X[i][a] for a in range(p));sse+=(y[i]-pred)**2;sst+=(y[i]-yb)**2
    return 1-sse/sst if sst>0 else 0.0
def zs(col):
    n=len(col);m=sum(col)/n;sd=(sum((x-m)**2 for x in col)/n)**0.5 or 1.0
    return [(x-m)/sd for x in col]
def ranks(xs):
    o=sorted(range(len(xs)),key=lambda i:xs[i]);r=[0.0]*len(xs);i=0
    while i<len(xs):
        j=i
        while j+1<len(xs) and xs[o[j+1]]==xs[o[i]]:j+=1
        for k in range(i,j+1):r[o[k]]=(i+j)/2.0+1
        i=j+1
    return r
def spearman(a,b):
    ra,rb=ranks(a),ranks(b);n=len(a);ma=sum(ra)/n;mb=sum(rb)/n
    nu=sum((ra[i]-ma)*(rb[i]-mb) for i in range(n));da=(sum((x-ma)**2 for x in ra))**.5;db=(sum((x-mb)**2 for x in rb))**.5
    return nu/(da*db) if da>0 and db>0 else 0.0

def main():
    t0=time.time();d=json.loads(DATA_PATH.read_text());W=d["windows"]
    feats=[]
    for w in W:
        f=features(w["seq"])
        if not f: continue
        f["chrom"]=w["chrom"];f["occ"]=w["occ"];f["gc"]=w["gc"];feats.append(f)
    n=len(feats);checks={"data_loaded":n>3000}
    if n<3000:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"needs_data","verdict":"needs_data","checks":checks,"result":{"n":n,"cannot_claim":d.get("cannot_claim",[])}}));return 3
    Y=[f["occ"] for f in feats]
    comp_keys=["a","c","g"]  # low-order composition baseline (T = 1-a-c-g)
    struct_keys=["homo","mxat","ww_period","dient","paldens"]  # structure beyond composition
    cols={k:zs([f[k] for f in feats]) for k in comp_keys+struct_keys}
    C=[[1.0]+[cols[k][i] for k in comp_keys] for i in range(n)]
    CX=[C[i]+[cols[k][i] for k in struct_keys] for i in range(n)]
    fold={}
    for i,f in enumerate(feats): fold.setdefault(f["chrom"]%FOLDS,[]).append(i)
    folds=[fold[k] for k in sorted(fold)]
    prC=prep(C,folds);prCX=prep(CX,folds)
    r2c=evalr2(prC,Y);r2cx=evalr2(prCX,Y);incr=r2cx-r2c
    fr={k:spearman([f[k] for f in feats],Y) for k in struct_keys}
    def dec(vals):
        order=sorted(range(n),key=lambda i:vals[i]);dd=[0]*n
        for r,i in enumerate(order):dd[i]=r*10//n
        return dd
    dg=dec([f["gc"] for f in feats]);bins={}
    for i in range(n):bins.setdefault(dg[i],[]).append(i)
    rng=random.Random(SEED);ge=0
    for _ in range(PERM):
        yp=Y[:]
        for grp in bins.values():
            vv=[Y[i] for i in grp];rng.shuffle(vv)
            for k,i in enumerate(grp):yp[i]=vv[k]
        if (evalr2(prCX,yp)-evalr2(prC,yp))>=incr: ge+=1
    p=(1+ge)/(1+PERM)
    checks.update({"occupancy_readout":True,"lowqorder_composition_baseline":True,"structure_features_beyond_composition":True,"chromosome_heldout":True,"gc_decile_perm_null":True})
    if incr>=0.01 and p<0.05: verdict="crosses_boundary"
    elif p<0.05 and incr>0: verdict="bounded_descriptor_only"
    elif incr<=0 or p>=0.05: verdict="composition_artifact"
    else: verdict="needs_data"
    checks["nucleosome_sequence_code_verdict"]=verdict
    out={"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"passed" if verdict!="needs_data" else "needs_data","verdict":verdict,"checks":checks,
         "result":{"n_windows":n,"r2_composition_baseline_heldout":round(r2c,4),"r2_plus_structure_heldout":round(r2cx,4),
                   "incremental_heldout_r2_structure":round(incr,4),"perm_p":round(p,4),"perm_B":PERM,"runtime_sec":round(time.time()-t0,1),
                   "structure_feature_spearman_with_occ":{k:round(v,3) for k,v in fr.items()},
                   "readout":"y = mean in-vitro nucleosome occupancy per 300bp window (Kaplan 2009 reconstitution); test = sequence STRUCTURE incremental R^2 over mononucleotide composition baseline",
                   "cannot_claim":d.get("cannot_claim",[])+[
                     "GC/composition alone predicts occupancy strongly (Spearman~0.81); this tests the STRUCTURE residual beyond that",
                     "in-vitro reconstitution + MNase map (Kaplan validated with MNase-free oligo); 300bp windows coarse vs single-nucleosome",
                     "classic nucleosome sequence code -- a NEW engine boundary-map contact (structure-beyond-composition), not a new mechanism; a composition_artifact verdict = occupancy is composition-only at this resolution"]}}
    print(json.dumps(out));return 0 if verdict!="needs_data" else 3

if __name__=="__main__":
    import sys;sys.exit(main())
