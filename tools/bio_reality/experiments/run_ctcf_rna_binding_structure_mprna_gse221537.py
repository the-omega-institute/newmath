#!/usr/bin/env python3
"""CTCF-RNA binding structural code (NEW MODALITY: RNA-protein binding; single-mechanism; oracle
direction). Does RNA-tile STRUCTURE (stem-pairing potential) predict CTCF fRIP enrichment beyond
composition, TRANSFERRING across held-out source RNAs (not just interpolating within an RNA)?

y = replicate-mean CPM-normalized log2(IP/Input) CTCF enrichment per 150nt RNA tile (barcodes
pooled). baseline = composition (mono A/C/G, 16 dinuc, GC, length) + tile-position. full = +
structure (reverse-complement/stem density k4/5/6, max RC-stem, trinuc entropy, homopolymer/purine
runs). Holdouts: (1) leave-one-source-RNA-out (9 RNAs) = primary + permutation (tiles from a
held-out RNA never in train -> controls overlapping-tile leakage + RNA-identity); (2) within-RNA-
centered + random 5-fold (does structure pick binding tiles WITHIN an RNA, RNA-level removed);
(3) random 5-fold (interpolation reference). Verdict crosses_boundary if structure adds >=0.01
leave-RNA-out (perm sig) AND within-RNA-centered; bounded_descriptor_only if only interpolates /
RNA-identity; composition_artifact if null. NEW-modality engine contact, not a new mechanism.
Pure stdlib."""
import json, math, random, pathlib, sys
from collections import Counter, defaultdict

EXPERIMENT_ID="ctcf_rna_binding_structure_mprna_gse221537"
CLAIM_ID="h3.cross_layer_relation.rna_protein_binding.ctcf_rna_tile_structure_beyond_composition_gse221537"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=300
random.seed(SEED)
COMP={"A":"T","T":"A","G":"C","C":"G"}
def revcomp(s): return "".join(COMP.get(c,"N") for c in reversed(s))

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
        c=cols[j]; m=sum(c)/len(c); sd=(sum((x-m)**2 for x in c)/len(c))**0.5 or 1.0
        out.append([(x-m)/sd for x in c])
    return [list(r) for r in zip(*out)]
def prep(X, foldof, folds):
    n=len(X); p=len(X[0]); packs=[]
    for f in folds:
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
        ytr=[y[i] for i in tr]; w=matvec(Ainv,[dot(col,ytr) for col in cols])
        for j,i in enumerate(te): preds[i]=dot(Xte[j],w)
    idx=sorted(preds); yt=[y[i] for i in idx]; pr=[preds[i] for i in idx]
    m=sum(yt)/len(yt); sst=sum((v-m)**2 for v in yt) or 1.0
    return 1.0-sum((a-b)**2 for a,b in zip(yt,pr))/sst
def comp_feats(s):
    L=len(s); f={c:s.count(c)/L for c in "ACGT"}
    di={a+b:0 for a in "ACGT" for b in "ACGT"}
    for i in range(L-1):
        d=s[i:i+2]
        if d in di: di[d]+=1
    tot=L-1 or 1
    return [f["A"],f["C"],f["G"],f["G"]+f["C"],L/150.0]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
def shannon_k(s,k):
    c=Counter(s[i:i+k] for i in range(len(s)-k+1)); n=sum(c.values()) or 1
    return -sum((v/n)*math.log((v/n),2) for v in c.values())
def rc_density(s,k):
    ks=set(s[i:i+k] for i in range(len(s)-k+1))
    return sum(1 for km in ks if revcomp(km) in ks)/len(ks) if ks else 0.0
def max_rc_stem(s,kmax=14):
    best=0
    for k in range(4,min(kmax,len(s)//2)+1):
        pos={}
        for i in range(len(s)-k+1): pos.setdefault(s[i:i+k],[]).append(i)
        found=False
        for km,ps in pos.items():
            rc=revcomp(km)
            if rc in pos and any(abs(pi-pj)>=k for pi in ps for pj in pos[rc]): found=True; break
        if found: best=k
        else: break
    return best
def mrun(s,al):
    b=c=0
    for ch in s:
        if ch in al: c+=1; b=max(b,c)
        else: c=0
    return b
def struct_feats(s):
    L=len(s)
    return [shannon_k(s,3),rc_density(s,4),rc_density(s,5),rc_density(s,6),max_rc_stem(s)/14.0,
            mrun(s,"A")/L,mrun(s,"T")/L,max(mrun(s,c) for c in "ACGT")/L,mrun(s,"AG")/L,mrun(s,"CT")/L]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); T=D["tiles"]; n=len(T)
    if n<300:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{"n":n},"result":{}})); sys.exit(3)
    cores=[t["core"] for t in T]; y=[float(t["y"]) for t in T]
    rnas=sorted(set(t["rna"] for t in T)); rnaidx={r:i for i,r in enumerate(rnas)}
    maxpos={r:max(t["tilenum"] for t in T if t["rna"]==r) for r in rnas}
    Cfeat=[comp_feats(cores[i])+[T[i]["tilenum"]/max(1,maxpos[T[i]["rna"]])] for i in range(n)]
    Sfeat=[struct_feats(cores[i]) for i in range(n)]
    Xc=[[1.0]+r for r in zscols(Cfeat)]; Xf=[[1.0]+r for r in zscols([Cfeat[i]+Sfeat[i] for i in range(n)])]

    # (1) leave-one-source-RNA-out
    fo_rna=[rnaidx[t["rna"]] for t in T]; rnfolds=list(range(len(rnas)))
    pc=prep(Xc,fo_rna,rnfolds); pf=prep(Xf,fo_rna,rnfolds)
    r2c=evalr2(pc,y); r2f=evalr2(pf,y); incr_rna=r2f-r2c

    # (3) random 5-fold
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS
    r2c_r=evalr2(prep(Xc,fo_rnd,list(range(FOLDS))),y); r2f_r=evalr2(prep(Xf,fo_rnd,list(range(FOLDS))),y); incr_random=r2f_r-r2c_r

    # (2) within-RNA-centered y + random 5-fold (RNA-level offset removed -> pure within-RNA structure signal)
    rmean=defaultdict(list)
    for i in range(n): rmean[T[i]["rna"]].append(y[i])
    rmu={r:sum(v)/len(v) for r,v in rmean.items()}
    yc=[y[i]-rmu[T[i]["rna"]] for i in range(n)]
    incr_within=evalr2(prep(Xf,fo_rnd,list(range(FOLDS))),yc)-evalr2(prep(Xc,fo_rnd,list(range(FOLDS))),yc)

    # permutation on primary (leave-one-RNA-out), global shuffle
    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pc,yp); nulls.append(ic)
        if ic>=incr_rna: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)

    floor=incr_rna>=0.01; sig=pval<0.05; within_ok=incr_within>=0.01
    if floor and sig and within_ok: verdict="crosses_boundary"
    elif floor and sig: verdict="bounded_descriptor_only"
    elif incr_within>=0.01 and not floor: verdict="bounded_descriptor_only"   # within-RNA only, doesn't transfer across RNAs
    else: verdict="composition_artifact"

    checks={"n_tiles":n,"n_source_rnas":len(rnas),
            "r2_composition_leave_rna_out":round(r2c,4),"r2_full_leave_rna_out":round(r2f,4),
            "incr_structure_leave_one_rna_out":round(incr_rna,4),
            "incr_structure_within_rna_centered":round(incr_within,4),
            "incr_structure_random_split":round(incr_random,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,"within_rna_signal":within_ok,
            "y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("RNA-tile structure (stem-pairing potential) predicts CTCF fRIP enrichment beyond composition and TRANSFERS across held-out source RNAs -- a transferable RNA-structure CTCF-binding code" if verdict=="crosses_boundary"
                              else "structure predicts CTCF enrichment within source RNAs but does NOT transfer to held-out RNAs (source-identity / interpolation), not a general CTCF RNA-binding code" if verdict=="bounded_descriptor_only"
                              else "no held-out structure signal beyond composition survives leave-one-RNA-out + permutation"),
            "framing":"NEW-MODALITY engine boundary-map contact (RNA-protein binding: RNA-tile structure -> CTCF fRIP enrichment beyond composition, source-RNA transfer tested), NOT a new mechanism",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
