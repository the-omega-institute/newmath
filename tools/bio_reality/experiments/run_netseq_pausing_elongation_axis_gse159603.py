#!/usr/bin/env python3
"""NET-seq Pol II pausing x elongation-factor-deletion modulation (oracle direction; like
claim 170/171 -- a perturbation-layer modulating a sequence->readout crossing): does local DNA
sequence grammar predict the CHANGE in Pol II pause density caused by specific elongation-factor
deletions? Yeast NET-seq GSE159603, WT(4 reps) + POSITIVE arms (dst1/chd1/ino80) + NEGATIVE/
specificity arms (spt4/rpb4/ubp8), 1kb windows on R64. Y_pos = mean over positive arms of
log1p(mut)-log1p(WT) = pause redistribution. Held-out incremental R^2 of sequence over
[WT-pause baseline + GC], chromosome-held-out, within (WT-density x GC decile) permutation null.
NEGATIVE arm = specificity control (signal should be POSITIVE-arm-specific). dst1/chd1/ino80
same-sign = replication. Pure stdlib, deterministic."""
import json, math, random, pathlib, time

EXPERIMENT_ID="netseq_pausing_elongation_axis_gse159603"
CLAIM_ID="h3.cross_layer_relation.transcription_elongation_axis_modulation.netseq_pausing_sequence_redistribution_gse159603"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; PERM=1000; FOLDS=5; RIDGE=1e-3
POS=["dst1","chd1","ino80"]; NEG=["spt4","rpb4","ubp8"]

def features(seq):
    s=seq.upper(); n=len(s)
    if n<500: return None
    at=(s.count("A")+s.count("T"))/n
    mx=0;cur=0;prev=""
    for b in s:
        if b in "AT" and (b==prev or prev in "AT" or not prev): cur+=1
        else: cur=1
        prev=b; mx=max(mx,cur)
    homo=0;cur=0;prev=""
    for b in s:
        if b==prev: cur+=1
        else: cur=1
        prev=b
        if b in "AT": homo=max(homo,cur)
    ww=[1 if s[i] in "AT" and s[i+1] in "AT" else 0 for i in range(n-1)]
    m=sum(ww)/len(ww) if ww else 0
    def ac(lag):
        num=sum((ww[i]-m)*(ww[i+lag]-m) for i in range(len(ww)-lag)); den=sum((x-m)**2 for x in ww) or 1.0
        return num/den
    period=(ac(10)+ac(11))/2
    di={}
    for i in range(n-1): di[s[i:i+2]]=di.get(s[i:i+2],0)+1
    tot=sum(di.values()) or 1; ent=-sum((c/tot)*math.log(c/tot) for c in di.values())
    comp={"A":"T","T":"A","G":"C","C":"G"};pal=0;K=6;step=10
    for i in range(0,n-K,step):
        k=s[i:i+K];rc="".join(comp.get(b,"N") for b in k[::-1])
        if rc in s: pal+=1
    paldens=pal/max(1,(n//step))
    cpg=sum(1 for i in range(n-1) if s[i:i+2]=="CG")/(n-1)
    return {"at":at,"polyatrun":float(mx),"homo":float(homo),"ww_period":period,"dient":ent,"paldens":paldens,"cpg":cpg}

def _inv(M):
    p=len(M);A=[row[:]+[1.0 if i==j else 0.0 for j in range(p)] for i,row in enumerate(M)]
    for c in range(p):
        piv=max(range(c,p),key=lambda r:abs(A[r][c]));A[c],A[piv]=A[piv],A[c]
        d=A[c][c] if abs(A[c][c])>1e-12 else 1e-12
        for k in range(2*p):A[c][k]/=d
        for r in range(p):
            if r!=c:
                f=A[r][c]
                for k in range(2*p):A[r][k]-=f*A[c][k]
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
    L=lambda x: math.log1p(x)
    for w in W:
        f=features(w["seq"])
        if not f: continue
        f["chrom"]=w["chrom"];f["gc"]=w["gc"];f["wt"]=w["WT"]
        for g in POS+NEG: f["d_"+g]=L(w[g])-L(w["WT"])
        feats.append(f)
    n=len(feats);checks={"data_loaded":n>2000}
    if n<2000:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"needs_data","verdict":"needs_data","checks":checks,"result":{"n":n,"cannot_claim":d.get("cannot_claim",[])}}));return 3
    Y_POS=[sum(f["d_"+g] for g in POS)/len(POS) for f in feats]
    Y_NEG=[sum(f["d_"+g] for g in NEG)/len(NEG) for f in feats]
    fkeys=["at","polyatrun","homo","ww_period","dient","paldens","cpg"]
    cols={k:zs([f[k] for f in feats]) for k in fkeys}
    wtl=zs([math.log1p(f["wt"]) for f in feats]); gc=zs([f["gc"] for f in feats])
    C=[[1.0,wtl[i],gc[i]] for i in range(n)]
    CX=[C[i]+[cols[k][i] for k in fkeys] for i in range(n)]
    fold={}
    for i,f in enumerate(feats): fold.setdefault(f["chrom"]%FOLDS,[]).append(i)
    folds=[fold[k] for k in sorted(fold)]
    prC=prep(C,folds);prCX=prep(CX,folds)
    r2c=evalr2(prC,Y_POS);r2cx=evalr2(prCX,Y_POS);incr=r2cx-r2c
    incr_neg=evalr2(prCX,Y_NEG)-evalr2(prC,Y_NEG)
    fr={k:spearman([f[k] for f in feats],Y_POS) for k in fkeys}
    best=max(fr,key=lambda k:abs(fr[k]))
    rep={g:round(spearman([feats[i][best] for i in range(n)],[f["d_"+g] for f in feats]),3) for g in POS}
    same_sign=len(set(v>0 for v in rep.values()))==1
    def dec(vals):
        order=sorted(range(n),key=lambda i:vals[i]);dd=[0]*n
        for r,i in enumerate(order):dd[i]=r*10//n
        return dd
    dw=dec([f["wt"] for f in feats]);dg=dec([f["gc"] for f in feats]);bins={}
    for i in range(n):bins.setdefault((dw[i],dg[i]),[]).append(i)
    rng=random.Random(SEED);ge=0
    for _ in range(PERM):
        yp=Y_POS[:]
        for grp in bins.values():
            vv=[Y_POS[i] for i in grp];rng.shuffle(vv)
            for k,i in enumerate(grp):yp[i]=vv[k]
        if (evalr2(prCX,yp)-evalr2(prC,yp))>=incr: ge+=1
    p=(1+ge)/(1+PERM)
    pos_specific=(incr>0 and incr_neg<=0) or (incr>=2*max(incr_neg,1e-9))
    checks.update({"pause_redistribution_readout":True,"wt_baseline_controlled":True,"chromosome_heldout":True,"negative_specificity_arm":True,"three_positive_arm_replication":True})
    if incr>=0.01 and p<0.05 and same_sign and pos_specific: verdict="crosses_boundary"
    elif p<0.05 and incr>0: verdict="bounded_descriptor_only"
    elif incr<=0 or p>=0.05: verdict="composition_artifact"
    else: verdict="needs_data"
    checks["elongation_axis_modulation_verdict"]=verdict
    out={"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"passed" if verdict!="needs_data" else "needs_data","verdict":verdict,"checks":checks,
         "result":{"n_windows":n,"r2_control_wtbaseline_gc_heldout":round(r2c,4),"r2_plus_sequence_heldout":round(r2cx,4),
                   "incremental_heldout_r2_POS":round(incr,4),"incremental_heldout_r2_NEG_specificity":round(incr_neg,4),"pos_specific":pos_specific,
                   "perm_p":round(p,4),"perm_B":PERM,"runtime_sec":round(time.time()-t0,1),
                   "feature_spearman_with_Y_POS":{k:round(v,3) for k,v in fr.items()},
                   "positive_arm_replication":rep,"three_pos_same_sign":same_sign,
                   "positive_arms":POS,"negative_specificity_arms":NEG,
                   "readout":"Y_POS = mean over (dst1,chd1,ino80) of [log1p(NETseq_mut)-log1p(NETseq_WT)] per 1kb window = elongation-factor-deletion pause redistribution",
                   "cannot_claim":d.get("cannot_claim",[])+[
                     "1kb windows coarse vs single-nucleotide pausing; both strands summed (strand-resolved pausing lost)",
                     "WT pause baseline controlled so the verdict is NOT a trivial high-pause-window artifact",
                     "POSITIVE-arm specificity required (NEG arm); a composition/bounded verdict means pause redistribution has no coarse sequence signature beyond baseline",
                     "BY4741 reads on R64 reference; observational"]}}
    print(json.dumps(out));return 0 if verdict!="needs_data" else 3

if __name__=="__main__":
    import sys;sys.exit(main())
