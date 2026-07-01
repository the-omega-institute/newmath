#!/usr/bin/env python3
"""CHiTA twister-ribozyme self-cleavage sequence-code (single-mechanism, genuinely-novel).

Question: does the RNA sequence of a natural twister ribozyme predict its QUANTITATIVE
in-vitro self-cleavage activity (fraction-cleaved), beyond base composition (mono+dinuc),
when near-identical genomic families are held out whole (no family leakage)?

Design (single mechanism, no perturbation arm):
  y = replicate-mean fraction-cleaved (QC Keep set, 3-rep agreement), variable twister core.
  baseline C = composition: length, GC, mononucleotide(A,C,G), dinucleotide(16) fractions.
  full   = C + structure-beyond-composition: trinuc entropy, reverse-complement(stem) density
           at k=4/5/6, max RC-stem length, max homopolymer/purine/pyrimidine runs.
  Held-out incremental R^2 (full over C) under FAMILY-CLUSTER holdout CV (k-mer Jaccard
  single-linkage; whole clusters assigned to folds -> a near-duplicate can never straddle
  train/test). Permutation null permutes y globally and re-runs the same clustered CV.

Verdict: crosses_boundary if incr held-out R^2 >= 0.01 AND perm p < 0.05 (structure adds
genuine sequence-code signal beyond composition under leakage control); bounded_descriptor_only
if composition already explains it / incr tiny; composition_artifact if baseline itself is the
whole story and structure null; needs_data if join/coverage insufficient. Honest framing: a
NEW ENGINE boundary-map contact (sequence-structure -> ribozyme activity quantified beyond
composition), NOT a new mechanism. Pure stdlib."""
import json, math, random, pathlib, sys, zlib

EXPERIMENT_ID="twister_ribozyme_selfcleavage_sequence_code_chita"
CLAIM_ID="h3.cross_layer_relation.ribozyme_self_cleavage.twister_activity_sequence_structure_beyond_composition_chita"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701
RIDGE=1.0           # z-scored features (XtX feature-diagonal ~ n); stabilizes dinuc collinearity
FOLDS=5
PERM=600
KMER_FAM=10         # k for family-clustering k-mer set (10-mers separate distinct twisters; conserved catalytic core is short)
JACCARD=0.6         # single-linkage family threshold: merge near-duplicate genomic families, keep distinct twisters apart
random.seed(SEED)

COMP={"A":"T","T":"A","G":"C","C":"G"}
def revcomp(s): return "".join(COMP.get(c,"N") for c in reversed(s))

# ---------- linear algebra (pure stdlib) ----------
def _inv(M):
    n=len(M); A=[row[:]+[1.0 if i==j else 0.0 for j in range(n)] for i,row in enumerate(M)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(A[r][c]))
        if abs(A[p][c])<1e-12: A[p][c]+=1e-9
        A[c],A[p]=A[p],A[c]
        pv=A[c][c]
        A[c]=[v/pv for v in A[c]]
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
    """Precompute per-fold inv(Xtr^T Xtr + lambda I) and train/test row indices (Y-independent)."""
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
            for b in range(a):
                XtX[a][b]=XtX[b][a]
            XtX[a][a]+=RIDGE
        packs.append((_inv(XtX), tr, te))
    return packs

def evalr2(packs, X, y):
    """Pooled held-out R^2 across folds via precomputed inverses."""
    p=len(X[0]); preds={};
    for Ainv,tr,te in packs:
        Xty=[0.0]*p
        for i in tr:
            yi=y[i]; xi=X[i]
            for a in range(p): Xty[a]+=xi[a]*yi
        w=matvec(Ainv,Xty)
        for i in te: preds[i]=dot(X[i],w)
    idx=sorted(preds); yt=[y[i] for i in idx]; pr=[preds[i] for i in idx]
    m=sum(yt)/len(yt); sst=sum((v-m)**2 for v in yt) or 1.0
    ssr=sum((a-b)**2 for a,b in zip(yt,pr))
    return 1.0-ssr/sst

# ---------- features ----------
def kmer_set(s,k):
    return frozenset(s[i:i+k] for i in range(len(s)-k+1))

def composition_feats(s):
    L=len(s); f={c:s.count(c)/L for c in "ACGT"}
    gc=f["G"]+f["C"]
    di={}
    tot=L-1 or 1
    for a in "ACGT":
        for b in "ACGT": di[a+b]=0
    for i in range(L-1):
        d=s[i:i+2]
        if d in di: di[d]+=1
    dv=[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
    return [L/100.0, gc, f["A"], f["C"], f["G"]]+dv   # 5 + 16 = 21

def shannon_k(s,k):
    from collections import Counter
    c=Counter(s[i:i+k] for i in range(len(s)-k+1))
    n=sum(c.values()) or 1
    return -sum((v/n)*math.log((v/n),2) for v in c.values())

def rc_density(s,k):
    """fraction of k-mers whose reverse-complement also appears in the sequence (stem potential)."""
    ks=set(s[i:i+k] for i in range(len(s)-k+1))
    if not ks: return 0.0
    hit=sum(1 for km in ks if revcomp(km) in ks)
    return hit/len(ks)

def max_rc_stem(s,kmax=14):
    """longest k such that some k-mer's reverse-complement occurs at a non-overlapping position."""
    best=0
    for k in range(4,min(kmax,len(s)//2)+1):
        pos={}
        for i in range(len(s)-k+1): pos.setdefault(s[i:i+k],[]).append(i)
        found=False
        for km,ps in pos.items():
            rc=revcomp(km)
            if rc in pos:
                for pi in ps:
                    for pj in pos[rc]:
                        if abs(pi-pj)>=k: found=True; break
                    if found: break
            if found: break
        if found: best=k
        else: break
    return best

def max_run(s,alphabet):
    best=cur=0
    for c in s:
        if c in alphabet: cur+=1; best=max(best,cur)
        else: cur=0
    return best

def structure_feats(s):
    L=len(s)
    return [shannon_k(s,3),
            rc_density(s,4), rc_density(s,5), rc_density(s,6),
            max_rc_stem(s)/14.0,
            max_run(s,"A")/L, max_run(s,"T")/L,
            max(max_run(s,c) for c in "ACGT")/L,    # max homopolymer
            max_run(s,"AG")/L, max_run(s,"CT")/L]   # purine / pyrimidine runs

# ---------- family clustering (LSH-blocked union-find, deterministic) ----------
def minhash(kset, nh):
    out=[]
    for h in range(nh):
        mn=1<<32
        salt=str(h).encode()
        for km in kset:
            v=zlib.crc32(salt+km.encode())&0xffffffff
            if v<mn: mn=v
        out.append(mn)
    return out

def family_clusters(cores):
    n=len(cores)
    ksets=[kmer_set(c,KMER_FAM) for c in cores]
    NH=16; BANDS=8; PERBAND=NH//BANDS
    sigs=[minhash(ks,NH) if ks else [0]*NH for ks in ksets]
    parent=list(range(n))
    def find(x):
        while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
        return x
    def union(a,b):
        ra,rb=find(a),find(b)
        if ra!=rb: parent[max(ra,rb)]=min(ra,rb)
    # LSH banding -> candidate buckets
    buckets={}
    for i in range(n):
        for band in range(BANDS):
            key=(band,)+tuple(sigs[i][band*PERBAND:(band+1)*PERBAND])
            buckets.setdefault(key,[]).append(i)
    for key,members in buckets.items():
        if len(members)<2: continue
        for a_i in range(len(members)):
            i=members[a_i]; ki=ksets[i]
            if not ki: continue
            for b_i in range(a_i+1,len(members)):
                j=members[b_i]; kj=ksets[j]
                if not kj: continue
                if find(i)==find(j): continue
                inter=len(ki & kj); uni=len(ki|kj)
                if uni and inter/uni>=JACCARD: union(i,j)
    roots={}
    for i in range(n): roots.setdefault(find(i),len(roots))
    return [roots[find(i)] for i in range(n)]

# ---------- main ----------
def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing data file %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text())
    rz=D["ribozymes"]
    cores=[r["core"] for r in rz]; y=[float(r["frac"]) for r in rz]
    n=len(rz)
    if n<300:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{"n":n},"result":{"reason":"too few ribozymes"}})); sys.exit(3)

    clusters=family_clusters(cores)
    ncl=len(set(clusters))
    from collections import Counter
    csz=Counter(clusters); big=max(csz.values())
    foldof=[clusters[i]%FOLDS for i in range(n)]

    Cfeat=[composition_feats(s) for s in cores]
    Sfeat=[structure_feats(s) for s in cores]
    # intercept (1.0) prepended AFTER z-scoring features -- never standardize the constant column
    Xc=[[1.0]+r for r in zscols(Cfeat)]
    Xf=[[1.0]+r for r in zscols([c+s for c,s in zip(Cfeat,Sfeat)])]

    pc=prep(Xc,foldof); pf=prep(Xf,foldof)
    r2c=evalr2(pc,Xc,y); r2f=evalr2(pf,Xf,y)
    incr=r2f-r2c

    # bare correlation sanity: best single structure feature (rc_density k6) vs y
    from statistics import mean
    s6=[Sfeat[i][3] for i in range(n)]
    def spear(a,b):
        ra={v:i for i,v in enumerate(sorted(range(len(a)),key=lambda k:a[k]))}
        rb={v:i for i,v in enumerate(sorted(range(len(b)),key=lambda k:b[k]))}
        ar=[ra[i] for i in range(len(a))]; br=[rb[i] for i in range(len(b))]
        ma=mean(ar); mb=mean(br)
        num=sum((x-ma)*(yy-mb) for x,yy in zip(ar,br))
        den=(sum((x-ma)**2 for x in ar)*sum((yy-mb)**2 for yy in br))**0.5 or 1.0
        return num/den

    # permutation null: permute y, recompute incremental under same clustered CV
    ge=0; nulls=[]
    yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx)
        yp=[y[i] for i in yidx]
        ic=evalr2(pf,Xf,yp)-evalr2(pc,Xc,yp)
        nulls.append(ic)
        if ic>=incr: ge+=1
    pval=(ge+1)/(PERM+1)
    null_mean=sum(nulls)/len(nulls)

    floor=incr>=0.01
    sig=pval<0.05
    if floor and sig: verdict="crosses_boundary"
    elif r2c>=0.05 and not floor: verdict="bounded_descriptor_only"   # composition explains it, structure adds nothing
    elif not sig: verdict="composition_artifact"
    else: verdict="bounded_descriptor_only"

    checks={
        "n_ribozymes":n,"n_family_clusters":ncl,"largest_cluster":big,
        "r2_composition_heldout":round(r2c,4),
        "r2_full_heldout":round(r2f,4),
        "incremental_r2_structure_over_composition":round(incr,4),
        "perm_null_mean_incr":round(null_mean,4),
        "perm_p":round(pval,4),
        "effect_floor_0.01":floor,"perm_sig_0.05":sig,
        "spearman_rcdensity6_vs_activity":round(spear(s6,y),4),
        "y_mean":round(sum(y)/n,4),
    }
    result={
        "interpretation":("twister self-cleavage activity carries sequence-STRUCTURE signal beyond mono+dinuc composition, family-leakage-controlled" if verdict=="crosses_boundary"
                          else "composition (mono+dinuc) already captures the predictable activity; higher-order structure adds no held-out signal" if verdict=="bounded_descriptor_only"
                          else "no held-out sequence signal survives family-cluster holdout"),
        "framing":"NEW ENGINE boundary-map contact (sequence-structure -> ribozyme self-cleavage activity, quantified beyond composition under family-leakage control), NOT a new mechanism",
        "data":D.get("source",""),
        "FOLDS":FOLDS,"PERM":PERM,"family_jaccard":JACCARD,"family_k":KMER_FAM,
    }
    out={"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result}
    print(json.dumps(out,indent=1))
    sys.exit(0)

if __name__=="__main__":
    main()
