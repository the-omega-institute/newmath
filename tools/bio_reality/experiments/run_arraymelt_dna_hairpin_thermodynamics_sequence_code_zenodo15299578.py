#!/usr/bin/env python3
"""Array Melt DNA-hairpin folding-thermodynamics sequence code (NEW MODALITY: DNA secondary-
structure thermodynamics; single-mechanism, genuinely-novel; oracle direction).

Does sequence STRUCTURE predict measured hairpin folding free energy dG_37 beyond composition,
and does it TRANSFER across held-out synthetic scaffolds AND structural-motif families (not just
interpolate within the library)? y = measured dG_37 (two-state melt fit). baseline = composition
(mono A/C/G, 16 dinuc, GC, length). full = + structure (reverse-complement/stem density k4/5/6,
max RC-stem, trinuc entropy, homopolymer/purine/pyrimidine runs).

Three holdouts (the oracle's design): (1) leave-scaffold-out (72 scaffolds -> folds) = primary +
permutation; (2) leave-Series-out (8 structural-motif families each held out) = strictest transfer;
(3) random 5-fold = library-interpolation comparison. Plus a NUPACK diagnostic (does structure add
beyond the nearest-neighbor model). Verdict: crosses_boundary if structure adds >=0.01 held-out
incr under leave-scaffold-out (perm sig) AND leave-Series-out (transfers across families);
bounded_descriptor_only if it only interpolates (random high, leave-family collapses);
composition_artifact if null. Honest framing: a fresh NEW-MODALITY engine contact (transferable
DNA folding code beyond composition), NOT a new mechanism. Pure stdlib."""
import json, math, random, pathlib, sys
from collections import Counter, defaultdict

EXPERIMENT_ID="arraymelt_dna_hairpin_thermodynamics_sequence_code_zenodo15299578"
CLAIM_ID="h3.cross_layer_relation.dna_secondary_structure_thermodynamics.arraymelt_hairpin_dg37_sequence_structure_beyond_composition_zenodo15299578"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701
RIDGE=1.0
FOLDS=5
PERM=200
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
        c=cols[j]; m=sum(c)/len(c)
        sd=(sum((x-m)**2 for x in c)/len(c))**0.5 or 1.0
        out.append([(x-m)/sd for x in c])
    return [list(r) for r in zip(*out)]
def prep(X, foldof, nf):
    n=len(X); p=len(X[0]); packs=[]
    for f in range(nf):
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

def composition_feats(s):
    L=len(s); f={c:s.count(c)/L for c in "ACGT"}
    di={a+b:0 for a in "ACGT" for b in "ACGT"}
    for i in range(L-1):
        d=s[i:i+2]
        if d in di: di[d]+=1
    tot=L-1 or 1
    return [f["A"],f["C"],f["G"], f["G"]+f["C"], L/20.0]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
def shannon_k(s,k):
    c=Counter(s[i:i+k] for i in range(len(s)-k+1)); n=sum(c.values()) or 1
    return -sum((v/n)*math.log((v/n),2) for v in c.values())
def rc_density(s,k):
    ks=set(s[i:i+k] for i in range(len(s)-k+1))
    return sum(1 for km in ks if revcomp(km) in ks)/len(ks) if ks else 0.0
def max_rc_stem(s,kmax=10):
    best=0
    for k in range(3,min(kmax,len(s)//2)+1):
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
def structure_feats(s):
    L=len(s)
    return [shannon_k(s,3), rc_density(s,4), rc_density(s,5), rc_density(s,6),
            max_rc_stem(s)/10.0, mrun(s,"A")/L, mrun(s,"T")/L,
            max(mrun(s,c) for c in "ACGT")/L, mrun(s,"AG")/L, mrun(s,"CT")/L]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text())
    V=D["variants"]; n=len(V)
    if n<2000:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{"n":n},"result":{}})); sys.exit(3)
    # dG_37 is dominated by the constant SCAFFOLD stem; composition of the variable RefSeq cannot
    # predict a held-out scaffold's baseline (leave-scaffold-out composition R^2 goes negative). The
    # SOUND baseline is composition + the NUPACK nearest-neighbor thermodynamic model (which accounts
    # for scaffold + Watson-Crick pairing). Primary test = does generic sequence STRUCTURE add beyond it?
    seqs=[v["seq"] for v in V]; y=[float(v["dg37"]) for v in V]
    if not all(v.get("nupack") is not None for v in V):
        V=[v for v in V if v.get("nupack") is not None]; n=len(V)
        seqs=[v["seq"] for v in V]; y=[float(v["dg37"]) for v in V]
    Cfeat=[composition_feats(s) for s in seqs]; Sfeat=[structure_feats(s) for s in seqs]
    NN=[[V[i]["nupack"]] for i in range(n)]
    Xcomp=[[1.0]+r for r in zscols(Cfeat)]                                   # composition only (diagnostic)
    Xb=[[1.0]+r for r in zscols([Cfeat[i]+NN[i] for i in range(n)])]         # SOUND baseline: composition + NUPACK
    Xf=[[1.0]+r for r in zscols([Cfeat[i]+NN[i]+Sfeat[i] for i in range(n)])]# + structure

    scaffs=sorted(set(v["scaffold"] for v in V)); sfold={s:i%FOLDS for i,s in enumerate(scaffs)}
    fo_scaf=[sfold[v["scaffold"]] for v in V]
    series=sorted(set(v["series"] for v in V)); yfold={s:i for i,s in enumerate(series)}
    fo_ser=[yfold[v["series"]] for v in V]; nser=len(series)
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS

    pc=prep(Xb,fo_scaf,FOLDS); pf=prep(Xf,fo_scaf,FOLDS)
    r2_comp_only=evalr2(prep(Xcomp,fo_scaf,FOLDS),y)
    r2b=evalr2(pc,y); r2f=evalr2(pf,y); incr_scaf=r2f-r2b                    # structure over composition+NUPACK, leave-scaffold-out
    incr_series=evalr2(prep(Xf,fo_ser,nser),y)-evalr2(prep(Xb,fo_ser,nser),y)
    incr_random=evalr2(prep(Xf,fo_rnd,FOLDS),y)-evalr2(prep(Xb,fo_rnd,FOLDS),y)

    # permutation on the PRIMARY (structure over composition+NUPACK, leave-scaffold-out)
    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pc,yp); nulls.append(ic)
        if ic>=incr_scaf: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)

    floor=incr_scaf>=0.01; sig=pval<0.05; transfers=incr_series>=0.01
    if floor and sig and transfers: verdict="crosses_boundary"
    elif floor and sig: verdict="bounded_descriptor_only"          # meaningful + sig but family-specific (no transfer)
    else: verdict="composition_artifact"                           # below effect floor: no meaningful structure signal beyond composition+NN

    checks={"n_variants":n,"n_scaffolds":len(scaffs),"n_series":nser,
            "r2_composition_only_leave_scaffold_out":round(r2_comp_only,4),
            "r2_baseline_composition_plus_nupack":round(r2b,4),
            "r2_full_composition_nupack_structure":round(r2f,4),
            "incr_structure_over_comp_nupack_leave_scaffold_out":round(incr_scaf,4),
            "incr_structure_leave_series_out":round(incr_series,4),
            "incr_structure_random_split":round(incr_random,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,"transfers_leave_family":transfers,
            "nupack_alone_pearson_note":"NUPACK NN-model is the physical baseline; composition alone leave-scaffold-out R^2 is negative (scaffold-offset unpredictable from variable RefSeq composition)",
            "dg37_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("sequence STRUCTURE predicts DNA-hairpin dG_37 beyond composition + the nearest-neighbor model, transferring leave-scaffold-out AND leave-family -- a transferable folding-code residual the NN model misses" if verdict=="crosses_boundary"
                              else "structure adds beyond composition+NN within/across scaffolds but does not transfer across held-out structural-motif families (family-specific)" if (verdict=="bounded_descriptor_only" and floor and sig)
                              else "generic alignment-free sequence-structure descriptors add no significant held-out signal beyond composition + the nearest-neighbor thermodynamic model: DNA-hairpin folding free energy is captured by composition + NN, with no residual for crude structure features"),
            "framing":"NEW-MODALITY engine boundary-map contact (DNA secondary-structure thermodynamics; sequence structure vs composition + nearest-neighbor model), NOT a new mechanism",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
