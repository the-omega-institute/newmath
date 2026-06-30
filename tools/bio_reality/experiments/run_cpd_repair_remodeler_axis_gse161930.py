#!/usr/bin/env python3
"""CPD-seq UV-repair remodeler-axis modulation (oracle direction; like claim 170 -- a
perturbation-layer modulating a sequence->readout crossing): does local DNA sequence grammar
predict RSC-dependent repair PERSISTENCE? Yeast CPD-seq GSE161930, WT + RSC(rsc2/sth1) +
SWI/SNF(snf5/snf6) at 0h/2h UV, 1kb windows on R64. repair_g = log1p(CPD_0h)-log1p(CPD_2h);
Y_RSC = mean over (rsc2,sth1) of (repair_mut - repair_WT) = RSC-dependent repair-persistence change.
Held-out incremental R^2 of sequence over [0h-damage + dipyrimidine composition + GC], chromosome
held-out, within (0h-count x GC decile) permutation null. SWI/SNF arm = specificity control (the
modulation should be RSC-specific). rsc2/sth1 same-sign = replication. Pure stdlib, deterministic."""
import json, math, random, pathlib, time

EXPERIMENT_ID="cpd_repair_remodeler_axis_gse161930"
CLAIM_ID="h3.cross_layer_relation.ner_remodeler_axis_modulation.cpd_rsc_repair_persistence_sequence_gse161930"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; PERM=1000; FOLDS=5; RIDGE=1e-3

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
    def rep(w,g): return math.log1p(w[g+"_0h"])-math.log1p(w[g+"_2h"])
    for w in W:
        f=features(w["seq"])
        if not f: continue
        f["chrom"]=w["chrom"];f["wt0"]=w["WT_0h"];f["gc"]=w["gc"];f["dipy"]=w["dipy"]
        f["repWT"]=rep(w,"WT")
        for g in ["rsc2","sth1","snf5","snf6"]: f["rep_"+g]=rep(w,g)
        feats.append(f)
    n=len(feats);checks={"data_loaded":n>2000}
    if n<2000:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"needs_data","verdict":"needs_data","checks":checks,"result":{"n":n,"cannot_claim":d.get("cannot_claim",[])}}));return 3
    Y_RSC=[(((f["rep_rsc2"]-f["repWT"])+(f["rep_sth1"]-f["repWT"]))/2) for f in feats]
    Y_SWI=[(((f["rep_snf5"]-f["repWT"])+(f["rep_snf6"]-f["repWT"]))/2) for f in feats]
    Yg={g:[f["rep_"+g]-f["repWT"] for f in feats] for g in ["rsc2","sth1"]}
    fkeys=["at","polyatrun","homo","ww_period","dient","paldens","cpg"]
    cols={k:zs([f[k] for f in feats]) for k in fkeys}
    wt0=zs([math.log1p(f["wt0"]) for f in feats]); gc=zs([f["gc"] for f in feats])
    dipy={k:zs([f["dipy"][k] for f in feats]) for k in ["TT","TC","CT","CC"]}
    C=[[1.0,wt0[i],gc[i]]+[dipy[k][i] for k in ["TT","TC","CT","CC"]] for i in range(n)]
    CX=[C[i]+[cols[k][i] for k in fkeys] for i in range(n)]
    fold={}
    for i,f in enumerate(feats): fold.setdefault(f["chrom"]%FOLDS,[]).append(i)
    folds=[fold[k] for k in sorted(fold)]
    prC=prep(C,folds);prCX=prep(CX,folds)
    r2c=evalr2(prC,Y_RSC);r2cx=evalr2(prCX,Y_RSC);incr=r2cx-r2c
    incr_swi=evalr2(prCX,Y_SWI)-evalr2(prC,Y_SWI)
    fr={k:spearman([f[k] for f in feats],Y_RSC) for k in fkeys}
    best=max(fr,key=lambda k:abs(fr[k]))
    rep_rsc2=spearman([feats[i][best] for i in range(n)],Yg["rsc2"]); rep_sth1=spearman([feats[i][best] for i in range(n)],Yg["sth1"])
    same_sign=(rep_rsc2>0)==(rep_sth1>0)
    def dec(vals):
        order=sorted(range(n),key=lambda i:vals[i]);dd=[0]*n
        for r,i in enumerate(order):dd[i]=r*10//n
        return dd
    d0=dec([f["wt0"] for f in feats]);dg=dec([f["gc"] for f in feats]);bins={}
    for i in range(n):bins.setdefault((d0[i],dg[i]),[]).append(i)
    rng=random.Random(SEED);ge=0
    for _ in range(PERM):
        yp=Y_RSC[:]
        for grp in bins.values():
            vv=[Y_RSC[i] for i in grp];rng.shuffle(vv)
            for k,i in enumerate(grp):yp[i]=vv[k]
        if (evalr2(prCX,yp)-evalr2(prC,yp))>=incr: ge+=1
    p=(1+ge)/(1+PERM)
    rsc_specific = (incr>0 and incr_swi<=0) or (incr >= 2*max(incr_swi,1e-9))
    checks.update({"repair_persistence_readout":True,"zero_hour_damage_controlled":True,"dipyrimidine_composition_controlled":True,"chromosome_heldout":True,"swisnf_specificity_arm":True,"rsc_two_subunit_replication":True})
    if incr>=0.01 and p<0.05 and same_sign and rsc_specific: verdict="crosses_boundary"
    elif p<0.05 and incr>0: verdict="bounded_descriptor_only"
    elif incr<=0 or p>=0.05: verdict="composition_artifact"
    else: verdict="needs_data"
    checks["ner_axis_modulation_verdict"]=verdict
    out={"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"passed" if verdict!="needs_data" else "needs_data","verdict":verdict,"checks":checks,
         "result":{"n_windows":n,"r2_control_0h_dipy_gc_heldout":round(r2c,4),"r2_plus_sequence_heldout":round(r2cx,4),
                   "incremental_heldout_r2_RSC":round(incr,4),"incremental_heldout_r2_SWISNF_specificity":round(incr_swi,4),
                   "rsc_specific":rsc_specific,"perm_p":round(p,4),"perm_B":PERM,"runtime_sec":round(time.time()-t0,1),
                   "feature_spearman_with_Y_RSC":{k:round(v,3) for k,v in fr.items()},
                   "rsc_subunit_replication":{"rsc2":round(rep_rsc2,3),"sth1":round(rep_sth1,3),"same_sign":same_sign},
                   "readout":"Y_RSC = mean over (rsc2,sth1) of [log1p(CPD_0h)-log1p(CPD_2h)]_mutant - [...]_WT per 1kb window = RSC-dependent repair-persistence change",
                   "cannot_claim":d.get("cannot_claim",[])+[
                     "sequence features are stdlib proxies; 1kb windows coarse vs per-dipyrimidine resolution",
                     "0h damage + dipyrimidine composition controlled so the verdict is NOT a TT/TC/CT/CC lesion-formation artifact",
                     "RSC-specificity required (SWI/SNF arm); a composition/bounded verdict means RSC-dependent repair persistence has no coarse sequence signature beyond damage+composition",
                     "single replicate per condition; observational"]}}
    print(json.dumps(out));return 0 if verdict!="needs_data" else 3

if __name__=="__main__":
    import sys;sys.exit(main())
