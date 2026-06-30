#!/usr/bin/env python3
"""Spo11 meiotic-DSB axis-modulation (oracle direction; like claim 168 -- a non-textbook
RELATIONSHIP, not a known fact): does local DNA sequence grammar predict where meiotic
DSBs REDISTRIBUTE when the chromosome-axis machinery is perturbed? SK1 WT (GSE119689) vs
red1/hop1/mek1 axis mutants (GSE84859), 1kb windows on R64. Y = consensus axis-redistribution
= mean over 3 mutants of logCPM(mutant) - logCPM(WT). Held-out incremental R^2 of sequence
features over [GC + WT-level (regression-to-mean control)], chromosome-held-out folds,
within-(GC-decile x WT-decile) permutation null. 3 independent axis perturbations = replication.
Pure stdlib, deterministic."""
import json, math, random, pathlib, time

EXPERIMENT_ID="spo11_dsb_axis_modulation_gse119689"
CLAIM_ID="h3.cross_layer_relation.meiotic_axis_modulation.spo11_dsb_sequence_redistribution_gse119689"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; PERM=1000; FOLDS=5; RIDGE=1e-3; PC=1.0

def features(seq):
    s=seq.upper(); n=len(s)
    if n<500: return None
    at=(s.count("A")+s.count("T"))/n
    gc=(s.count("G")+s.count("C"))/n
    # longest poly-dA:dT run (nucleosome-disfavoring)
    mx=0; cur=0; prev=""
    for b in s:
        if b in "AT" and (b==prev or prev in "AT" or not prev): cur+=1
        else: cur=1
        prev=b; mx=max(mx,cur)
    # poly-A or poly-T homopolymer max run (stricter)
    homo=0; cur=0; prev=""
    for b in s:
        if b==prev: cur+=1
        else: cur=1
        prev=b
        if b in "AT": homo=max(homo,cur)
    # WW dinucleotide 10-11bp periodicity (bendability proxy): autocorr of WW indicator at lag 10,11
    ww=[1 if s[i] in "AT" and s[i+1] in "AT" else 0 for i in range(n-1)]
    m=sum(ww)/len(ww) if ww else 0
    def ac(lag):
        num=sum((ww[i]-m)*(ww[i+lag]-m) for i in range(len(ww)-lag))
        den=sum((x-m)**2 for x in ww) or 1.0
        return num/den
    period=(ac(10)+ac(11))/2
    # dinucleotide entropy
    di={}
    for i in range(n-1): di[s[i:i+2]]=di.get(s[i:i+2],0)+1
    tot=sum(di.values()) or 1; ent=-sum((c/tot)*math.log(c/tot) for c in di.values())
    # palindrome (reverse-complement) 6-mer self-match density
    comp={"A":"T","T":"A","G":"C","C":"G"}; pal=0; K=6; step=10
    for i in range(0,n-K,step):
        k=s[i:i+K]; rc="".join(comp.get(b,"N") for b in k[::-1])
        if rc in s: pal+=1
    paldens=pal/max(1,(n//step))
    cpg=sum(1 for i in range(n-1) if s[i:i+2]=="CG")/(n-1)
    return {"at":at,"gc":gc,"polyatrun":float(mx),"homo":float(homo),"ww_period":period,
            "dient":ent,"paldens":paldens,"cpg":cpg}

def logcpm(vals):
    tot=sum(vals) or 1.0
    return [math.log2(v/tot*1e6+PC) for v in vals]

def _inv(M):
    p=len(M); A=[row[:]+[1.0 if i==j else 0.0 for j in range(p)] for i,row in enumerate(M)]
    for c in range(p):
        piv=max(range(c,p),key=lambda r:abs(A[r][c])); A[c],A[piv]=A[piv],A[c]
        d=A[c][c] if abs(A[c][c])>1e-12 else 1e-12
        for k in range(2*p): A[c][k]/=d
        for r in range(p):
            if r!=c:
                f=A[r][c]
                for k in range(2*p): A[r][k]-=f*A[c][k]
    return [row[p:] for row in A]

def prep(X,folds):
    p=len(X[0]); out=[]
    for te in folds:
        te_set=set(te); tr=[i for i in range(len(X)) if i not in te_set]
        XtX=[[sum(X[i][a]*X[i][b] for i in tr)+(RIDGE if a==b else 0.0) for b in range(p)] for a in range(p)]
        out.append((_inv(XtX),tr,te))
    return out,X,p

def evalr2(pr,y):
    folds,X,p=pr; n=len(y); yb=sum(y)/n; sse=0.0; sst=0.0
    for inv,tr,te in folds:
        Xty=[sum(X[i][a]*y[i] for i in tr) for a in range(p)]
        beta=[sum(inv[a][b]*Xty[b] for b in range(p)) for a in range(p)]
        for i in te:
            pred=sum(beta[a]*X[i][a] for a in range(p)); sse+=(y[i]-pred)**2; sst+=(y[i]-yb)**2
    return 1-sse/sst if sst>0 else 0.0

def zs(col):
    n=len(col); m=sum(col)/n; sd=(sum((x-m)**2 for x in col)/n)**0.5 or 1.0
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
    t0=time.time(); d=json.loads(DATA_PATH.read_text()); W=d["windows"]
    feats=[]; keep=[]
    for w in W:
        f=features(w["seq"])
        if f: f["chrom"]=w["chrom"]; f["WT"]=w["WT"]; f["red1"]=w["red1"]; f["hop1"]=w["hop1"]; f["mek1"]=w["mek1"]; feats.append(f); keep.append(w)
    n=len(feats); checks={"data_loaded":n>2000}
    if n<2000:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"needs_data","verdict":"needs_data","checks":checks,"result":{"n":n,"cannot_claim":d.get("cannot_claim",[])}})); return 3
    # per-profile logCPM
    wtL=logcpm([f["WT"] for f in feats])
    mutL={g:logcpm([f[g] for f in feats]) for g in ["red1","hop1","mek1"]}
    # consensus axis-redistribution Y = mean over mutants of (logCPM_mut - logCPM_WT)
    Y=[sum(mutL[g][i]-wtL[i] for g in ["red1","hop1","mek1"])/3 for i in range(n)]
    # per-mutant redistribution (for replication check)
    Yg={g:[mutL[g][i]-wtL[i] for i in range(n)] for g in ["red1","hop1","mek1"]}
    fkeys=["at","polyatrun","homo","ww_period","dient","paldens","cpg"]
    cols={k:zs([f[k] for f in feats]) for k in fkeys}
    gc=zs([f["gc"] for f in feats]); wtl=zs(wtL)
    # control = GC + WT-level (regression-to-mean); CX = + sequence features
    C=[[1.0,gc[i],wtl[i]] for i in range(n)]
    CX=[C[i]+[cols[k][i] for k in fkeys] for i in range(n)]
    # chromosome-held-out folds
    foldmap={}
    for i,f in enumerate(feats): foldmap.setdefault(f["chrom"]%FOLDS,[]).append(i)
    folds=[foldmap[k] for k in sorted(foldmap)]
    prC=prep(C,folds); prCX=prep(CX,folds)
    r2c=evalr2(prC,Y); r2cx=evalr2(prCX,Y); incr=r2cx-r2c
    # single-feature spearman with Y (strongest), + replication: sign consistency across mutants
    fr={k:spearman([f[k] for f in feats],Y) for k in fkeys}
    rep={g:spearman([feats[i][best] for i in range(n)],Yg[g]) for g in ["red1","hop1","mek1"] for best in [max(fr,key=lambda k:abs(fr[k]))]}
    # perm null: shuffle Y within GC-decile x WT-decile bins
    def deciles(vals):
        order=sorted(range(n),key=lambda i:vals[i]); dd=[0]*n
        for r,i in enumerate(order): dd[i]=r*10//n
        return dd
    gd=deciles(wtL); cd=deciles([f["gc"] for f in feats]); bins={}
    for i in range(n): bins.setdefault((gd[i],cd[i]),[]).append(i)
    rng=random.Random(SEED); ge=0
    for _ in range(PERM):
        yp=Y[:]
        for grp in bins.values():
            vv=[Y[i] for i in grp]; rng.shuffle(vv)
            for k,i in enumerate(grp): yp[i]=vv[k]
        if (evalr2(prCX,yp)-evalr2(prC,yp))>=incr: ge+=1
    p=(1+ge)/(1+PERM)
    same_sign=all((rep[g]>0)==(rep["red1"]>0) for g in ["red1","hop1","mek1"])
    checks.update({"per_profile_logcpm":True,"consensus_redistribution_readout":True,
        "regression_to_mean_controlled":True,"chromosome_heldout":True,"gc_wt_decile_perm_null":True,
        "three_mutant_replication":True})
    if incr>=0.01 and p<0.05 and same_sign: verdict="crosses_boundary"
    elif p<0.05 and incr>0: verdict="bounded_descriptor_only"
    elif incr<=0 or p>=0.05: verdict="composition_artifact"
    else: verdict="needs_data"
    checks["axis_modulation_verdict"]=verdict
    out={"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"passed" if verdict!="needs_data" else "needs_data",
         "verdict":verdict,"checks":checks,
         "result":{"n_windows":n,"r2_control_gc_wtlevel_heldout":round(r2c,4),"r2_plus_sequence_heldout":round(r2cx,4),
                   "incremental_heldout_r2":round(incr,4),"perm_p":round(p,4),"perm_B":PERM,"runtime_sec":round(time.time()-t0,1),
                   "feature_spearman_with_redistribution":{k:round(v,3) for k,v in fr.items()},
                   "three_mutant_replication_spearman":{g:round(v,3) for g,v in rep.items()},"three_mutant_same_sign":same_sign,
                   "readout":"Y = mean over red1/hop1/mek1 of [logCPM(mutant)-logCPM(WT)] per 1kb window = consensus axis-removed DSB redistribution",
                   "cannot_claim":d.get("cannot_claim",[])+[
                     "WT raw-hitcount (GSE119689) vs mutant RPM (GSE84859) -> per-profile logCPM-normalized before differencing; residual batch possible",
                     "SK1 reads on R64/S288C reference (strain SNPs minor at 1kb-window k-mer scale)",
                     "1kb windows are coarse (sub-kb hotspot structure averaged out)",
                     "sequence features (poly-dA:dT, WW-periodicity, entropy, palindrome) are stdlib proxies; a null/bounded result means axis-redistribution has no coarse sequence signature"]}}
    print(json.dumps(out)); return 0 if verdict!="needs_data" else 3

if __name__=="__main__":
    import sys; sys.exit(main())
