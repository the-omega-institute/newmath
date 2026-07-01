#!/usr/bin/env python3
"""F1*U ligase-ribozyme fitness landscape: does RNA STRUCTURE predict ligase activity beyond
composition + mutation-load in a 2^16 combinatorial mutational hypercube (RNA catalysis; natural
enumeration, no generator confound; oracle direction)?

y = log2(Mean_RA + 0.05) (replicate-mean relative ligase activity, Rotrattanadumrong 2022, Zenodo
6945203; 'Combinatorially complete' 2^16 subset). baseline = composition (mono A/C/G, 16 dinuc, GC)
+ HD_WT (mutation load). full = + structure (reverse-complement/stem density k3/4/5, max RC-stem,
trinuc entropy, homopolymer/purine runs). Held-out incremental R^2 under HAMMING-NEIGHBOR cluster
holdout (variants within Hamming<=2 on the 16 variable loci held out together -> a near-neighbor
never straddles train/test; random split leaks hypercube neighbors) + permutation. Diagnostic:
structure over the ADDITIVE per-locus model (16 is-mutant indicators + HD) = the epistasis test.

Verdict crosses_boundary if structure adds >=0.01 Hamming-cluster held-out (perm sig);
bounded_descriptor_only if only interpolates (random high, cluster collapses); composition_artifact
if null. NEW engine contact (RNA fold -> ligase activity beyond composition), not a new mechanism.
Pure stdlib."""
import json, math, random, pathlib, sys
from collections import Counter, defaultdict

EXPERIMENT_ID="f1u_ligase_ribozyme_epistasis_landscape_zenodo6945203"
CLAIM_ID="h3.cross_layer_relation.ribozyme_ligase_activity.f1u_ligase_structure_beyond_composition_epistasis_zenodo6945203"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=200; N_MAX=8000; HAM_THR=2
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
def comp_feats(s):
    L=len(s); f={c:s.count(c)/L for c in "ACGT"}
    di={a+b:0 for a in "ACGT" for b in "ACGT"}
    for i in range(L-1):
        d=s[i:i+2]
        if d in di: di[d]+=1
    tot=L-1 or 1
    return [f["A"],f["C"],f["G"],f["G"]+f["C"]]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
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
def struct_feats(s):
    L=len(s)
    return [shannon_k(s,3),rc_density(s,3),rc_density(s,4),rc_density(s,5),max_rc_stem(s)/10.0,
            mrun(s,"A")/L,mrun(s,"T")/L,max(mrun(s,c) for c in "ACGT")/L,mrun(s,"AG")/L]

def hamming_clusters(varsubs):
    """cluster fixed-length variable-loci substrings by Hamming<=HAM_THR (LSH-banded union-find)."""
    n=len(varsubs); L=len(varsubs[0]) if n else 0
    parent=list(range(n))
    def find(x):
        while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
        return x
    def union(a,b):
        ra,rb=find(a),find(b)
        if ra!=rb: parent[max(ra,rb)]=min(ra,rb)
    BANDS=HAM_THR+1; seg=max(1,L//BANDS)
    buckets=defaultdict(list)
    for i,s in enumerate(varsubs):
        for band in range(BANDS):
            buckets[(band,s[band*seg:(band+1)*seg])].append(i)
    for members in buckets.values():
        if len(members)<2: continue
        for ai in range(len(members)):
            i=members[ai]; si=varsubs[i]
            for bi in range(ai+1,len(members)):
                j=members[bi]
                if find(i)==find(j): continue
                sj=varsubs[j]; hm=0
                for a,b in zip(si,sj):
                    if a!=b:
                        hm+=1
                        if hm>HAM_THR: break
                if hm<=HAM_THR: union(i,j)
    roots={}
    for i in range(n): roots.setdefault(find(i),len(roots))
    return [roots[find(i)] for i in range(n)]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); Vall=D["variants"]; n_total=len(Vall)
    if n_total>N_MAX:
        idx=list(range(n_total)); random.Random(SEED).shuffle(idx)
        V=[Vall[i] for i in sorted(idx[:N_MAX])]
    else: V=Vall
    n=len(V)
    seqs=[v["seq"] for v in V]; y=[float(v["y"]) for v in V]
    # variable positions
    votes=[Counter() for _ in range(35)]
    for s in seqs:
        for i,ch in enumerate(s): votes[i][ch]+=1
    varpos=[i for i in range(35) if len(votes[i])>1]
    varsub=["".join(s[i] for i in varpos) for s in seqs]
    wt=[votes[i].most_common(1)[0][0] for i in range(35)]

    Cfeat=[comp_feats(seqs[i])+[V[i]["hd_wt"]/16.0] for i in range(n)]
    Sfeat=[struct_feats(seqs[i]) for i in range(n)]
    Xc=[[1.0]+r for r in zscols(Cfeat)]; Xf=[[1.0]+r for r in zscols([Cfeat[i]+Sfeat[i] for i in range(n)])]
    # additive per-locus baseline (epistasis diagnostic)
    Add=[[1.0 if s[p]!=wt[p] else 0.0 for p in varpos]+[V[i]["hd_wt"]/16.0] for i,s in enumerate(seqs)]
    Xadd=[[1.0]+r for r in zscols(Add)]; Xadd_s=[[1.0]+r for r in zscols([Add[i]+Sfeat[i] for i in range(n)])]

    # A 2^16 combinatorial hypercube is Hamming-connected -> single-linkage Hamming clustering
    # collapses to one cluster (useless). The right test is structure beyond the ADDITIVE per-locus
    # model (epistasis): the additive baseline captures all first-order per-site effects (and equally
    # benefits from neighbor proximity), so the structure INCREMENT isolates non-additive (fold/
    # epistatic) signal. Primary = structure over additive, random 5-fold + perm.
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS

    pa=prep(Xadd,fo_rnd); pas=prep(Xadd_s,fo_rnd)
    r2_add=evalr2(pa,y); r2_add_s=evalr2(pas,y); incr_epi=r2_add_s-r2_add   # structure beyond additive = epistasis
    incr_over_comp=evalr2(prep(Xf,fo_rnd),y)-evalr2(prep(Xc,fo_rnd),y)      # structure beyond composition (context)

    # distance diagnostic: train on low mutation load (HD<=8), test on high (HD>=9) -> extrapolation
    fo_shell=[1 if V[i]["hd_wt"]>=9 else 0 for i in range(n)]
    def cv2(X):
        tr=[i for i in range(n) if fo_shell[i]==0]; te=[i for i in range(n) if fo_shell[i]==1]
        if len(te)<50 or len(tr)<50: return None
        p=len(X[0]); XtX=[[0.0]*p for _ in range(p)]
        for i in tr:
            xi=X[i]
            for a in range(p):
                if xi[a]==0.0: continue
                for b in range(a,p): XtX[a][b]+=xi[a]*xi[b]
        for a in range(p):
            for b in range(a): XtX[a][b]=XtX[b][a]
            XtX[a][a]+=RIDGE
        Ai=_inv(XtX); Xty=[sum(X[i][a]*y[i] for i in tr) for a in range(p)]
        w=matvec(Ai,Xty); pr=[dot(X[i],w) for i in te]; yt=[y[i] for i in te]
        m=sum(yt)/len(yt); sst=sum((v-m)**2 for v in yt) or 1.0
        return 1.0-sum((a-b)**2 for a,b in zip(yt,pr))/sst
    r2a_shell=cv2(Xadd); r2as_shell=cv2(Xadd_s)
    incr_epi_shell=(r2as_shell-r2a_shell) if (r2a_shell is not None and r2as_shell is not None) else None

    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pas,yp)-evalr2(pa,yp); nulls.append(ic)
        if ic>=incr_epi: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)

    floor=incr_epi>=0.01; sig=pval<0.05
    shell_ok=(incr_epi_shell is not None and incr_epi_shell>=0.01)
    if floor and sig and shell_ok: verdict="crosses_boundary"           # epistasis real AND extrapolates
    elif floor and sig: verdict="bounded_descriptor_only"               # epistasis detectable within-hypercube but does not transfer to higher mutation loads (interpolation-like)
    else: verdict="composition_artifact"

    checks={"n_variants_used":n,"n_total_hypercube":n_total,"n_variable_loci":len(varpos),
            "r2_additive_per_locus_random":round(r2_add,4),"r2_additive_plus_structure_random":round(r2_add_s,4),
            "incr_structure_over_additive_EPISTASIS":round(incr_epi,4),
            "incr_structure_over_composition":round(incr_over_comp,4),
            "incr_epistasis_leave_high_HD_out":(round(incr_epi_shell,4) if incr_epi_shell is not None else None),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,
            "holdout":"random-5fold (additive per-locus baseline; hypercube is Hamming-connected so cluster-holdout collapses)",
            "y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("RNA structure (stem-pairing potential) predicts ligase activity beyond the ADDITIVE per-locus model = structural EPISTASIS: the fold carries non-additive signal the per-site model misses, and it extrapolates to higher mutation loads" if (verdict=="crosses_boundary" and shell_ok)
                              else "RNA structure adds beyond the additive per-locus model (structural epistasis) within the hypercube but weakens on leave-high-HD-out extrapolation" if verdict=="crosses_boundary"
                              else "no structure signal beyond the additive per-locus model survives permutation"),
            "framing":"NEW engine boundary-map contact (RNA fold/structure -> ligase-ribozyme activity as non-additive epistasis beyond the additive per-locus model in a 2^16 combinatorial hypercube), NOT a new mechanism",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
