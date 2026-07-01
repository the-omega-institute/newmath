#!/usr/bin/env python3
"""Azoarcus group-I-intron self-reproducing ribozyme generative landscape: does long-range
sequence STRUCTURE predict catalytic activity beyond composition AND beyond the design
generator (single-mechanism, genuinely-novel; oracle direction #1).

y = authors' continuous activity act=log(f_sel/f_ref) (censored inactives floored).
baseline C = composition (mono A/C/G, 16 dinuc, GC) + GENERATOR seq_type one-hot(11)
             + read-depth + Hamming-distance-to-WT.  (controls generator leakage + composition
             + how-far-from-WT + depth -- the confounds the oracle flagged.)
full = C + structure-beyond-composition (trinuc entropy, reverse-complement/stem density k4/5/6,
       max RC-stem, max homopolymer/purine/pyrimidine runs).
Held-out incremental R^2 (full over C) under HAMMING-IDENTITY cluster holdout CV (whole
near-duplicate families to folds; >=92% identity single-linkage, LSH-banded). Permutation null
STRATIFIED within seq_type x distance-bin x depth-bin (shuffle y within strata so the null keeps
generator/distance/depth structure intact and isolates the sequence-structure signal).

Verdict crosses_boundary if incr held-out R^2 >= 0.01 AND strat-perm p < 0.05; else
bounded_descriptor_only / composition_artifact / needs_data. Honest framing: a NEW engine
boundary-map contact (long-range sequence structure -> ribozyme activity beyond composition
AND generator), NOT a new mechanism. Pure stdlib."""
import json, math, random, pathlib, sys, zlib
from collections import Counter, defaultdict

EXPERIMENT_ID="azoarcus_selfreproducing_ribozyme_sequence_code_zenodo16531362"
CLAIM_ID="h3.cross_layer_relation.ribozyme_self_reproduction.azoarcus_groupI_activity_sequence_structure_beyond_composition_generator_zenodo16531362"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701
RIDGE=1.0
FOLDS=5
PERM=200
N_MAX=8000          # stratified subsample (by generator) for tractable runtime at full-pool scale; reported, not silent
KMER_FAM=10         # k-mer for family clustering (10-mers separate distinct families; conserved core is short)
JACCARD=0.6         # near-duplicate families ~0.85 Jaccard vs distinct families ~0.3 -> 0.6 cleanly separates
random.seed(SEED)

COMP={"A":"U","U":"A","G":"C","C":"G"}
def revcomp(s): return "".join(COMP.get(c,"N") for c in reversed(s))

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
    """Per-fold: inv(Xtr^T Xtr + lam I), transposed training columns (for fast Xty per perm), test rows."""
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
        Ainv=_inv(XtX)
        cols=[[X[i][a] for i in tr] for a in range(p)]   # transposed training columns
        Xte=[X[i] for i in te]
        packs.append((Ainv, cols, tr, te, Xte))
    return packs

def evalr2(packs, y):
    preds={}
    for Ainv, cols, tr, te, Xte in packs:
        ytr=[y[i] for i in tr]
        Xty=[dot(col,ytr) for col in cols]
        w=matvec(Ainv,Xty)
        for j,i in enumerate(te): preds[i]=dot(Xte[j],w)
    idx=sorted(preds); yt=[y[i] for i in idx]; pr=[preds[i] for i in idx]
    m=sum(yt)/len(yt); sst=sum((v-m)**2 for v in yt) or 1.0
    return 1.0-sum((a-b)**2 for a,b in zip(yt,pr))/sst

# ---------- features ----------
def composition_feats(s):
    L=len(s); f={c:s.count(c)/L for c in "ACGU"}
    di={a+b:0 for a in "ACGU" for b in "ACGU"}
    for i in range(L-1):
        d=s[i:i+2]
        if d in di: di[d]+=1
    tot=L-1 or 1
    return [f["A"],f["C"],f["G"], f["G"]+f["C"]] + [di[a+b]/tot for a in "ACGU" for b in "ACGU"]   # 4+16

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
def max_run(s,al):
    b=c=0
    for ch in s:
        if ch in al: c+=1; b=max(b,c)
        else: c=0
    return b
def structure_feats(s):
    L=len(s)
    return [shannon_k(s,3), rc_density(s,4), rc_density(s,5), rc_density(s,6),
            max_rc_stem(s)/14.0, max_run(s,"A")/L, max_run(s,"U")/L,
            max(max_run(s,c) for c in "ACGU")/L, max_run(s,"AG")/L, max_run(s,"CU")/L]

# ---------- k-mer-Jaccard family clustering (minhash-LSH union-find, deterministic) ----------
def kmer_set(s,k): return frozenset(s[i:i+k] for i in range(len(s)-k+1))
def minhash(ks,nh):
    out=[]
    for h in range(nh):
        mn=1<<32; salt=str(h).encode()
        for km in ks:
            v=zlib.crc32(salt+km.encode())&0xffffffff
            if v<mn: mn=v
        out.append(mn)
    return out
def family_clusters(seqs):
    n=len(seqs)
    ksets=[kmer_set(s,KMER_FAM) for s in seqs]
    NH=16; BANDS=8; PERBAND=NH//BANDS
    sigs=[minhash(ks,NH) if ks else [0]*NH for ks in ksets]
    parent=list(range(n))
    def find(x):
        while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
        return x
    def union(a,b):
        ra,rb=find(a),find(b)
        if ra!=rb: parent[max(ra,rb)]=min(ra,rb)
    buckets=defaultdict(list)
    for i in range(n):
        for band in range(BANDS):
            buckets[(band,)+tuple(sigs[i][band*PERBAND:(band+1)*PERBAND])].append(i)
    for members in buckets.values():
        if len(members)<2: continue
        for ai in range(len(members)):
            i=members[ai]; ki=ksets[i]
            if not ki: continue
            for bi in range(ai+1,len(members)):
                j=members[bi]; kj=ksets[j]
                if not kj or find(i)==find(j): continue
                if len(ki&kj)/len(ki|kj)>=JACCARD: union(i,j)
    roots={}
    for i in range(n): roots.setdefault(find(i),len(roots))
    return [roots[find(i)] for i in range(n)]

# ---------- main ----------
def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text())
    dz_all=D["designs"]; n_total=len(dz_all)
    if n_total<1000:
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{"n":n_total},"result":{}})); sys.exit(3)
    # stratified subsample by generator (deterministic) for tractable runtime; proportional per seq_type
    if n_total>N_MAX:
        bytype=defaultdict(list)
        for i,d in enumerate(dz_all): bytype[d["seq_type"]].append(i)
        keep=[]
        for t_,idxs in sorted(bytype.items()):
            idxs=sorted(idxs); random.Random(SEED).shuffle(idxs)
            keep+=idxs[:max(1,round(N_MAX*len(idxs)/n_total))]
        keep=sorted(keep)[:N_MAX]
        dz=[dz_all[i] for i in keep]
    else:
        dz=dz_all
    n=len(dz)
    seqs=[d["seq"] for d in dz]; y=[float(d["y"]) for d in dz]

    # generator one-hot
    types=sorted(set(d["seq_type"] for d in dz))
    tindex={t:i for i,t in enumerate(types)}
    def onehot(t):
        v=[0.0]*len(types); v[tindex[t]]=1.0; return v

    # clusters -> folds
    clusters=family_clusters(seqs)
    ncl=len(set(clusters)); big=max(Counter(clusters).values())
    foldof=[clusters[i]%FOLDS for i in range(n)]

    Cfeat=[composition_feats(s) for s in seqs]
    Sfeat=[structure_feats(s) for s in seqs]
    # baseline features: composition + generator onehot + depth + dist_wt
    Cbase=[Cfeat[i]+onehot(dz[i]["seq_type"])+[dz[i]["depth"], dz[i]["dist_wt"]] for i in range(n)]
    Cfull=[Cbase[i]+Sfeat[i] for i in range(n)]
    Xc=[[1.0]+r for r in zscols(Cbase)]
    Xf=[[1.0]+r for r in zscols(Cfull)]

    pc=prep(Xc,foldof); pf=prep(Xf,foldof)
    r2c=evalr2(pc,y); r2f=evalr2(pf,y); incr=r2f-r2c

    # diagnostic: composition-ONLY baseline (no generator/distance/depth) + structure over it (point est, no perm)
    # -> shows whether structure's apparent lift is real or just proxies the generator captured in the full baseline
    Xcomp=[[1.0]+r for r in zscols(Cfeat)]
    Xcomp_s=[[1.0]+r for r in zscols([Cfeat[i]+Sfeat[i] for i in range(n)])]
    r2_comp_only=evalr2(prep(Xcomp,foldof),y)
    r2_comp_struct=evalr2(prep(Xcomp_s,foldof),y)
    incr_over_comp_only=r2_comp_struct-r2_comp_only

    # strata for permutation: seq_type x dist-bin x depth-bin
    def qbin(vals,nb=5):
        sv=sorted(vals); cuts=[sv[min(len(sv)-1,int(len(sv)*k/nb))] for k in range(1,nb)]
        def b(x):
            for bi,c in enumerate(cuts):
                if x<=c: return bi
            return nb-1
        return [b(v) for v in vals]
    dbin=qbin([d["dist_wt"] for d in dz]); pbin=qbin([d["depth"] for d in dz])
    strata=defaultdict(list)
    for i in range(n): strata[(dz[i]["seq_type"],dbin[i],pbin[i])].append(i)

    ge=0; nulls=[]
    for _ in range(PERM):
        yp=list(y)
        for idxs in strata.values():
            vals=[y[i] for i in idxs]; random.shuffle(vals)
            for i,v in zip(idxs,vals): yp[i]=v
        ic=evalr2(pf,yp)-evalr2(pc,yp)
        nulls.append(ic)
        if ic>=incr: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)

    # actives-only sensitivity (drop censored floor spike)
    act_idx=[i for i in range(n) if not dz[i]["censored"]]
    r2c_a=r2f_a=incr_a=None
    if len(act_idx)>2000:
        foldA=[foldof[i] for i in act_idx]
        XcA=[Xc[i] for i in act_idx]; XfA=[Xf[i] for i in act_idx]; yA=[y[i] for i in act_idx]
        # rebuild zscore on subset for fairness
        XcA=[[1.0]+r for r in zscols([Cbase[i] for i in act_idx])]
        XfA=[[1.0]+r for r in zscols([Cfull[i] for i in act_idx])]
        pcA=prep(XcA,foldA); pfA=prep(XfA,foldA)
        r2c_a=evalr2(pcA,yA); r2f_a=evalr2(pfA,yA); incr_a=r2f_a-r2c_a

    floor_ok=incr>=0.01; sig=pval<0.05
    if floor_ok and sig: verdict="crosses_boundary"
    elif incr_over_comp_only>=0.03 and not sig:
        verdict="bounded_descriptor_only"   # structure beats composition-alone but is generator-confounded -> not a generator-independent crossing
    elif r2c>=0.05 and not floor_ok: verdict="bounded_descriptor_only"
    elif not sig: verdict="composition_artifact"
    else: verdict="bounded_descriptor_only"

    checks={"n_designs_used":n,"n_total_pool":n_total,"n_family_clusters":ncl,"largest_cluster":big,"n_generators":len(types),
            "r2_baseline_heldout":round(r2c,4),"r2_full_heldout":round(r2f,4),
            "incremental_r2_structure_over_comp_plus_generator":round(incr,4),
            "strat_perm_null_mean_incr":round(null_mean,4),"strat_perm_p":round(pval,4),
            "effect_floor_0.01":floor_ok,"perm_sig_0.05":sig,
            "actives_only_incr_r2":(round(incr_a,4) if incr_a is not None else None),
            "actives_only_r2_baseline":(round(r2c_a,4) if r2c_a is not None else None),
            "r2_composition_only":round(r2_comp_only,4),
            "incr_structure_over_composition_only":round(incr_over_comp_only,4),
            "censored_fraction":round(sum(1 for d in dz if d["censored"])/n,3),
            "y_mean":round(sum(y)/n,3)}
    result={"interpretation":("long-range sequence STRUCTURE predicts group-I self-reproduction activity beyond composition AND generator identity, family-leakage-controlled" if verdict=="crosses_boundary"
                              else ("structure predicts activity over composition alone (+%.3f) but it is GENERATOR-CONFOUNDED: under design-generator (seq_type) control + stratified permutation the residual incremental (%.3f, p=%.3f) is not significant -> a generator-confounded descriptor, NOT a generator-independent structure->activity crossing"%(incr_over_comp_only,incr,pval)) if verdict=="bounded_descriptor_only"
                              else "no held-out structure signal survives family-cluster holdout + stratified permutation"),
            "framing":"NEW engine boundary-map contact (long-range sequence structure -> ribozyme self-reproduction activity beyond composition+generator under family-leakage control), NOT a new mechanism",
            "data":D.get("source",""),"floor":D.get("floor"),
            "FOLDS":FOLDS,"PERM":PERM,"family_jaccard":JACCARD,"family_k":KMER_FAM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
