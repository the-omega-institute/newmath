#!/usr/bin/env python3
"""N-zip 3'UTR-zipcode neurite/soma localization code (6th MODALITY: RNA subcellular localization;
single-mechanism, genuinely-novel; oracle direction). Does higher-order sequence (trinucleotide
motifs + structure) predict neurite/soma reporter-RNA localization beyond mono+dinuc composition,
TRANSFERRING across held-out source genes (leave-one-gene-out)?

y = DESeq2 log2ratio(neurite/soma) WT per 3'UTR tile (N-zip MPRA, mouse cortical neurons).
baseline = composition (mono A/C/G, 16 dinuc, GC, length, tile-offset). full = + trinucleotide
(64) + structure (RC/stem density k4/5, max RC-stem, trinuc entropy, max-AU-run, homopolymer).
Held-out incremental R^2 under LEAVE-ONE-GENE-OUT (gene-grouped 5-fold; a source gene's overlapping
tiles never straddle train/test) + permutation. Verdict crosses_boundary if higher-order sequence
adds >=0.01 held-out (perm sig) -> a transferable localization code beyond composition;
bounded_descriptor_only if composition (AU-richness) explains it; composition_artifact if null.
NEW-modality engine contact (RNA localization), not a new mechanism. Pure stdlib.

Distinct from the Fazal-2019 whole-gene APEX-seq mRNA-localization claim (correlational, ER/nucleus,
signal-peptide-confounded, bounded): N-zip CAUSALLY isolates the per-tile neurite/soma cis-element."""
import json, math, random, pathlib, sys
from collections import Counter, defaultdict

EXPERIMENT_ID="nzip_3utr_zipcode_localization_emtab10902"
CLAIM_ID="h3.cross_layer_relation.rna_subcellular_localization.nzip_3utr_zipcode_sequence_beyond_composition_emtab10902"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=300
random.seed(SEED)
COMP={"A":"T","T":"A","G":"C","C":"G"}
def revcomp(s): return "".join(COMP.get(c,"N") for c in reversed(s))
BASES="ACGT"; TRI=[a+b+c for a in BASES for b in BASES for c in BASES]

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
        ytr=[y[i] for i in tr]; w=matvec(Ainv,[dot(col,ytr) for col in cols])
        for j,i in enumerate(te): preds[i]=dot(Xte[j],w)
    idx=sorted(preds); yt=[y[i] for i in idx]; pr=[preds[i] for i in idx]
    m=sum(yt)/len(yt); sst=sum((v-m)**2 for v in yt) or 1.0
    return 1.0-sum((a-b)**2 for a,b in zip(yt,pr))/sst

def comp_feats(s,offset,utrlen):
    L=len(s); f={c:s.count(c)/L for c in "ACGT"}
    di={a+b:0 for a in "ACGT" for b in "ACGT"}
    for i in range(L-1):
        d=s[i:i+2]
        if d in di: di[d]+=1
    tot=L-1 or 1
    pos=(offset/utrlen) if (offset is not None and utrlen) else 0.0
    return [f["A"],f["C"],f["G"],f["G"]+f["C"],L/100.0,pos]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
def tri_feats(s):
    c=Counter(s[i:i+3] for i in range(len(s)-2)); tot=len(s)-2 or 1
    return [c.get(t,0)/tot for t in TRI]
def shannon_k(s,k):
    c=Counter(s[i:i+k] for i in range(len(s)-k+1)); n=sum(c.values()) or 1
    return -sum((v/n)*math.log((v/n),2) for v in c.values())
def rc_density(s,k):
    ks=set(s[i:i+k] for i in range(len(s)-k+1))
    return sum(1 for km in ks if revcomp(km) in ks)/len(ks) if ks else 0.0
def max_rc_stem(s,kmax=12):
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
def au_run(s):
    b=c=0
    for ch in s:
        if ch in "AT": c+=1; b=max(b,c)
        else: c=0
    return b
def struct_feats(s):
    L=len(s)
    return [shannon_k(s,3),rc_density(s,4),rc_density(s,5),max_rc_stem(s)/12.0,
            au_run(s)/L,max(mrun(s,c) for c in "ACGT")/L,mrun(s,"AG")/L]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); T=D["tiles"]; n=len(T)
    if n<500:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{"n":n},"result":{}})); sys.exit(3)
    seqs=[t["seq"] for t in T]; y=[float(t["y"]) for t in T]
    Cfeat=[comp_feats(seqs[i],T[i].get("offset"),T[i].get("utr_len")) for i in range(n)]
    Hfeat=[tri_feats(seqs[i])+struct_feats(seqs[i]) for i in range(n)]
    Xc=[[1.0]+r for r in zscols(Cfeat)]; Xf=[[1.0]+r for r in zscols([Cfeat[i]+Hfeat[i] for i in range(n)])]
    genes=sorted(set(t["gene_id"] for t in T)); gfold={g:i%FOLDS for i,g in enumerate(genes)}
    fo=[gfold[t["gene_id"]] for t in T]
    pc=prep(Xc,fo); pf=prep(Xf,fo)
    r2c=evalr2(pc,y); r2f=evalr2(pf,y); incr=r2f-r2c
    # random-split diagnostic (interpolation vs gene-transfer)
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS
    incr_random=evalr2(prep(Xf,fo_rnd),y)-evalr2(prep(Xc,fo_rnd),y)

    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pc,yp); nulls.append(ic)
        if ic>=incr: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)

    floor=incr>=0.01; sig=pval<0.05
    if floor and sig: verdict="crosses_boundary"
    elif incr_random>=0.01 and not floor: verdict="bounded_descriptor_only"
    else: verdict="composition_artifact"

    checks={"n_tiles":n,"n_source_genes":len(genes),
            "r2_composition_leave_gene_out":round(r2c,4),"r2_full_leave_gene_out":round(r2f,4),
            "incr_higherorder_seq_leave_gene_out":round(incr,4),
            "incr_higherorder_seq_random_split":round(incr_random,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,"y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("higher-order sequence (trinucleotide motifs + structure) predicts neurite/soma mRNA localization beyond mono+dinuc composition, transferring across held-out source genes -- a transferable 3'UTR localization code" if verdict=="crosses_boundary"
                              else "low-order composition (AU-richness) captures the predictable localization; higher-order sequence adds signal only within-gene (interpolation), not across held-out genes" if verdict=="bounded_descriptor_only"
                              else "no held-out higher-order-sequence signal beyond composition survives leave-one-gene-out + permutation"),
            "framing":"NEW-modality engine boundary-map contact (RNA subcellular localization: 3'UTR-tile higher-order sequence -> neurite/soma localization beyond composition, gene-transfer tested), NOT a new mechanism; CAUSAL per-tile MPRA, distinct from the correlational whole-gene Fazal-2019 claim",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
