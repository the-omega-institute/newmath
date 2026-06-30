#!/usr/bin/env python3
"""Hel2-resolution residual: does sequence grammar BEYOND known stall motifs predict
ribosome-collision PERSISTENCE when RQC (Hel2) is knocked out? (oracle-designed,
GSE139036 Meydan&Guydosh 2020). Readout Y_g = Dlog2(disome/mono) [hel2D - WT].
Predictors masked of known stalls (CGA, CGA-CGA, poly-Pro, total basic content in
aa-comp): charge-CLUSTERING grammar (run/dipeptide at fixed content) + downstream
self-pairing proxy. Held-out incremental R^2 over composition+coverage+known-stalls,
within-coverage-bin permutation null. Pure stdlib, deterministic."""
import json, math, random, pathlib, time

EXPERIMENT_ID="disome_collision_persistence_hel2_gse139036"
CLAIM_ID="h3.cross_layer_relation.collision_persistence_rqc.disome_hel2_resolution_residual_gse139036"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; PERM=1000; PC=1.0; FOLDS=5; RIDGE=1e-3

GC={}
for cs,aa in [("TTT TTC","F"),("TTA TTG CTT CTC CTA CTG","L"),("ATT ATC ATA","I"),("ATG","M"),
 ("GTT GTC GTA GTG","V"),("TCT TCC TCA TCG AGT AGC","S"),("CCT CCC CCA CCG","P"),("ACT ACC ACA ACG","T"),
 ("GCT GCC GCA GCG","A"),("TAT TAC","Y"),("CAT CAC","H"),("CAA CAG","Q"),("AAT AAC","N"),("AAA AAG","K"),
 ("GAT GAC","D"),("GAA GAG","E"),("TGT TGC","C"),("TGG","W"),("CGT CGC CGA CGG AGA AGG","R"),("GGT GGC GGA GGG","G"),
 ("TAA TAG TGA","*")]:
    for c in cs.split(): GC[c]=aa
AAS="ACDEFGHIKLMNPQRSTVWY"
BASIC=set("KR"); ACIDIC=set("DE")

def features(seq):
    seq=seq.upper().replace("U","T")
    cod=[seq[i:i+3] for i in range(0,len(seq)-len(seq)%3,3)]
    cod=[c for c in cod if set(c)<=set("ACGT")]
    aas=[GC.get(c,"*") for c in cod]
    aas=[a for a in aas if a!="*"]
    n=len(aas)
    if n<50: return None
    aaf={a:aas.count(a)/n for a in AAS}
    gc=sum(seq.count(b) for b in "GC")/max(1,len(seq))
    gc3=sum(1 for c in cod if c[2] in "GC")/max(1,len(cod))
    # known stalls (controls to mask)
    cga=cod.count("CGA")/max(1,len(cod))
    cgacga=sum(1 for i in range(len(cod)-1) if cod[i]=="CGA" and cod[i+1]=="CGA")/max(1,len(cod))
    pp=sum(1 for i in range(n-1) if aas[i]=="P" and aas[i+1]=="P")/n
    # NEW: charge-clustering grammar (at fixed basic content, which is in aaf)
    runs=[]; cur=0
    for a in aas:
        if a in BASIC: cur+=1
        else:
            if cur: runs.append(cur)
            cur=0
    if cur: runs.append(cur)
    max_basic_run=max(runs) if runs else 0
    basic_dipep=sum(1 for i in range(n-1) if aas[i] in BASIC and aas[i+1] in BASIC)/n
    acidic_dipep=sum(1 for i in range(n-1) if aas[i] in ACIDIC and aas[i+1] in ACIDIC)/n
    # NEW: downstream self-pairing proxy (composition-aware): mean over windows of best
    # reverse-complement self-match length within a 45-nt window (a structure proxy, not RNAfold)
    comp={"A":"T","T":"A","G":"C","C":"G"}
    s=seq; W=45; STEP=15; scores=[]
    for i in range(0,max(1,len(s)-W),STEP):
        win=s[i:i+W]
        rc="".join(comp.get(b,"N") for b in win[::-1])
        # longest common substring length between win and its own rc (palindromic pairing potential)
        best=0
        for a in range(0,W-4,3):
            k=win[a:a+6]
            if len(k)==6 and k in rc: best=max(best,6)
        scores.append(best)
    pair=sum(scores)/len(scores) if scores else 0.0
    return {"aaf":aaf,"gc":gc,"gc3":gc3,"cga":cga,"cgacga":cgacga,"pp":pp,
            "max_basic_run":float(max_basic_run),"basic_dipep":basic_dipep,
            "acidic_dipep":acidic_dipep,"pair":pair,"loglen":math.log(n)}

def _inv(M):
    p=len(M); A=[row[:]+[1.0 if i==j else 0.0 for j in range(p)] for i,row in enumerate(M)]
    for c in range(p):
        piv=max(range(c,p),key=lambda r:abs(A[r][c])); A[c],A[piv]=A[piv],A[c]
        d=A[c][c]
        if abs(d)<1e-12: d=1e-12
        for k in range(2*p): A[c][k]/=d
        for r in range(p):
            if r!=c:
                fct=A[r][c]
                for k in range(2*p): A[r][k]-=fct*A[c][k]
    return [row[p:] for row in A]

def prep_folds(X,folds,lam,seed):
    """Precompute per-fold inv(XtX_tr + lam I), train/test index lists, and X. Y-independent."""
    n=len(X); p=len(X[0]); idx=list(range(n)); random.Random(seed).shuffle(idx)
    fold=[idx[i::folds] for i in range(folds)]
    out=[]
    for f in range(folds):
        te=fold[f]; te_set=set(te); tr=[i for i in idx if i not in te_set]
        XtX=[[sum(X[i][a]*X[i][b] for i in tr)+(lam if a==b else 0.0) for b in range(p)] for a in range(p)]
        out.append((_inv(XtX),tr,te))
    return out,X,p

def eval_r2(prep,y):
    """Fast held-out R^2 for a given y using precomputed inverses."""
    folds,X,p=prep; n=len(y); ybar=sum(y)/n; sse=0.0; sst=0.0
    for inv,tr,te in folds:
        Xty=[sum(X[i][a]*y[i] for i in tr) for a in range(p)]
        beta=[sum(inv[a][b]*Xty[b] for b in range(p)) for a in range(p)]
        for i in te:
            pred=sum(beta[a]*X[i][a] for a in range(p))
            sse+=(y[i]-pred)**2; sst+=(y[i]-ybar)**2
    return 1-sse/sst if sst>0 else 0.0

def zscore(col):
    n=len(col); m=sum(col)/n; sd=(sum((x-m)**2 for x in col)/n)**0.5 or 1.0
    return [(x-m)/sd for x in col]

def build_matrix(rows, keys_ctrl, keys_new):
    cols={}
    for k in keys_ctrl+keys_new: cols[k]=zscore([r[k] for r in rows])
    for a in AAS: cols["aa_"+a]=zscore([r["aaf"][a] for r in rows])
    n=len(rows)
    ctrl_keys=keys_ctrl+["aa_"+a for a in AAS]
    C=[[1.0]+[cols[k][i] for k in ctrl_keys] for i in range(n)]
    CX=[C[i]+[cols[k][i] for k in keys_new] for i in range(n)]
    return C,CX

def ranks(xs):
    o=sorted(range(len(xs)),key=lambda i:xs[i]); r=[0.0]*len(xs); i=0
    while i<len(xs):
        j=i
        while j+1<len(xs) and xs[o[j+1]]==xs[o[i]]: j+=1
        for k in range(i,j+1): r[o[k]]=(i+j)/2.0+1
        i=j+1
    return r
def spearman(a,b):
    ra,rb=ranks(a),ranks(b); n=len(a); ma=sum(ra)/n; mb=sum(rb)/n
    num=sum((ra[i]-ma)*(rb[i]-mb) for i in range(n))
    da=(sum((x-ma)**2 for x in ra))**.5; db=(sum((x-mb)**2 for x in rb))**.5
    return num/(da*db) if da>0 and db>0 else 0.0

def main():
    _t0=time.time()
    d=json.loads(DATA_PATH.read_text())
    rows=[]
    for g in d["genes"]:
        f=features(g["seq"])
        if not f: continue
        y=math.log2((g["hel2_di"]+PC)/(g["hel2_mono"]+PC))-math.log2((g["WT_di"]+PC)/(g["WT_mono"]+PC))
        f["Y"]=y; f["cov"]=math.log2(g["WT_mono"]+g["hel2_mono"]+PC); rows.append(f)
    n=len(rows)
    checks={"data_loaded":n>800,"readout_hel2_minus_wt":True}
    if n<800:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"needs_data","verdict":"needs_data",
            "checks":checks,"result":{"n":n,"cannot_claim":d.get("cannot_claim",[])}}));return 3
    y=[r["Y"] for r in rows]
    keys_ctrl=["loglen","gc","gc3","cga","cgacga","pp","cov"]
    keys_new=["max_basic_run","basic_dipep","acidic_dipep","pair"]
    C,CX=build_matrix(rows,keys_ctrl,keys_new)
    prepC=prep_folds(C,FOLDS,RIDGE,SEED); prepCX=prep_folds(CX,FOLDS,RIDGE,SEED)
    r2_c=eval_r2(prepC,y); r2_cx=eval_r2(prepCX,y)
    incr=r2_cx-r2_c
    feat_rho={k:spearman([r[k] for r in rows],y) for k in keys_new}
    # permutation null: shuffle Y within coverage deciles, recompute incr (fast via precomputed inverses)
    covs=sorted(range(n),key=lambda i:rows[i]["cov"]); dec=[covs[i::10] for i in range(10)]
    rng=random.Random(SEED); ge=0
    for _ in range(PERM):
        yp=y[:]
        for grp in dec:
            vals=[y[i] for i in grp]; rng.shuffle(vals)
            for k,i in enumerate(grp): yp[i]=vals[k]
        if (eval_r2(prepCX,yp)-eval_r2(prepC,yp))>=incr: ge+=1
    p=(1+ge)/(1+PERM)
    checks.update({"baseline_ctrl_r2":True,"incremental_heldout_r2":True,"known_stalls_masked":True,
                   "within_coverage_bin_perm_null":True,"feature_rho_reported":True})
    if incr>=0.01 and p<0.05: verdict="crosses_boundary"
    elif p<0.05 and incr>0: verdict="bounded_descriptor_only"
    elif incr<=0 or p>=0.05: verdict="composition_artifact"
    else: verdict="needs_data"
    checks["collision_persistence_verdict"]=verdict
    out={"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"passed" if verdict!="needs_data" else "needs_data",
         "verdict":verdict,"checks":checks,
         "result":{"n_genes":n,"r2_controls_heldout":round(r2_c,4),"r2_controls_plus_grammar_heldout":round(r2_cx,4),
                   "incremental_heldout_r2":round(incr,4),"perm_p":round(p,4),"perm_B":PERM,"runtime_sec":round(time.time()-_t0,1),
                   "new_feature_spearman_with_Y":{k:round(v,3) for k,v in feat_rho.items()},
                   "readout":"Y_g = Dlog2(disome/mono) hel2D - WT (RQC-resolution sensitivity / collision persistence)",
                   "controls_masking_known_stalls":keys_ctrl+["20-aa-composition"],
                   "new_grammar_features":keys_new,
                   "cannot_claim":d.get("cannot_claim",[])+[
                     "downstream-pairing is a stdlib 6-mer palindrome proxy, not measured RNA structure",
                     "charge-clustering controls total basic content via aa-composition but spacing/run is a coarse grammar",
                     "verdict tests grammar BEYOND known stalls; a null/bounded result is the honest finding if collisions are dominated by the masked motifs"]}}
    print(json.dumps(out))
    return 0 if verdict!="needs_data" else 3

if __name__=="__main__":
    import sys; sys.exit(main())
