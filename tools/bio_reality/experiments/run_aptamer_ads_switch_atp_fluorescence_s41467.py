#!/usr/bin/env python3
"""DNA aptamer ADS switch — ATP-诱导 fluorescence ON/OFF 序列码(第8模态:small-molecule DNA
aptamer molecular switch;single-mechanism;oracle 方向)。higher-order 序列是否在 composition +
N10 self-complementarity(strand-displacement 物理 proxy)之上预测 ATP-诱导 ON/OFF ratio, Hamming-
neighbor-controlled? y=log2(F_ATP_500uM / F_buffer)(Yoshikawa/Soh 2023, MOESM4)。10nt N10
switching domain。baseline_comp=composition(mono/dinuc/GC);baseline_phys=+self-complementarity /
palindrome / max-self-stem(displacement 倾向的物理近似,纯 stdlib 代 binding-equilibrium);full=+
higher-order(shannon k2/3, homopolymer/purine/AT runs)。Hamming-neighbor cluster holdout(near-dup
N10 整簇)+ perm。合成随机库→无 organism, identity leakage 用 Hamming-cluster。信号稀疏(多数 no-switch)。
crosses_boundary / bounded_descriptor_only / composition_artifact。NEW 模态 fresh contact 非新机制。纯 stdlib。"""
import json, math, random, pathlib, sys
from collections import Counter, defaultdict

EXPERIMENT_ID="aptamer_ads_switch_atp_fluorescence_s41467_2023_38105"
CLAIM_ID="h3.cross_layer_relation.dna_aptamer_molecular_switch.aptamer_ads_atp_dynamic_range_sequence_beyond_composition_displacement_s41467"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=250; N_MAX=8000; HAM_THR=1
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
    return [f["A"],f["C"],f["G"],f["G"]+f["C"]]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
def max_self_stem(s):
    """最长 k 使得 s 内某 k-mer 的 reverse-complement 也在 s 内(非重叠)-> 自身 hairpin/displacement 倾向."""
    best=0
    for k in range(2,len(s)//2+1):
        pos={}
        for i in range(len(s)-k+1): pos.setdefault(s[i:i+k],[]).append(i)
        found=False
        for km,ps in pos.items():
            rc=revcomp(km)
            if rc in pos and any(abs(pi-pj)>=k for pi in ps for pj in pos[rc]): found=True; break
        if found: best=k
        else: break
    return best
def selfrc_pairs(s,k=3):
    ks=set(s[i:i+k] for i in range(len(s)-k+1))
    return sum(1 for km in ks if revcomp(km) in ks)/(len(ks) or 1)
def phys_feats(s):
    return [max_self_stem(s)/5.0, selfrc_pairs(s,3), selfrc_pairs(s,4)]
def shannon_k(s,k):
    c=Counter(s[i:i+k] for i in range(len(s)-k+1)); n=sum(c.values()) or 1
    return -sum((v/n)*math.log((v/n),2) for v in c.values())
def mrun(s,al):
    b=c=0
    for ch in s:
        if ch in al: c+=1; b=max(b,c)
        else: c=0
    return b
def higher_feats(s):
    L=len(s)
    return [shannon_k(s,2), shannon_k(s,3), max(mrun(s,c) for c in "ACGT")/L, mrun(s,"AG")/L, mrun(s,"AT")/L]

def hamming_clusters(seqs):
    n=len(seqs); L=len(seqs[0]); parent=list(range(n))
    def find(x):
        while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
        return x
    def uni(a,b):
        ra,rb=find(a),find(b)
        if ra!=rb: parent[max(ra,rb)]=min(ra,rb)
    BANDS=HAM_THR+1; seg=max(1,L//BANDS); buckets=defaultdict(list)
    for i,s in enumerate(seqs):
        for band in range(BANDS): buckets[(band,s[band*seg:(band+1)*seg])].append(i)
    for mem in buckets.values():
        if len(mem)<2: continue
        for ai in range(len(mem)):
            i=mem[ai]; si=seqs[i]
            for bi in range(ai+1,len(mem)):
                j=mem[bi]
                if find(i)==find(j): continue
                hm=sum(1 for a,b in zip(si,seqs[j]) if a!=b)
                if hm<=HAM_THR: uni(i,j)
    roots={}
    for i in range(n): roots.setdefault(find(i),len(roots))
    return [roots[find(i)] for i in range(n)]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); Sall=[x for x in D["switches"] if len(x["seq"])==10]  # fixed 10nt
    n_total=len(Sall)
    if n_total>N_MAX:
        idx=list(range(n_total)); random.Random(SEED).shuffle(idx); S=[Sall[i] for i in sorted(idx[:N_MAX])]
    else: S=Sall
    n=len(S); seqs=[x["seq"] for x in S]; y=[float(x["y"]) for x in S]
    Cf=[comp_feats(s) for s in seqs]; Pf=[phys_feats(s) for s in seqs]; Hf=[higher_feats(s) for s in seqs]
    Xc=[[1.0]+r for r in zscols(Cf)]
    Xp=[[1.0]+r for r in zscols([Cf[i]+Pf[i] for i in range(n)])]
    Xf=[[1.0]+r for r in zscols([Cf[i]+Pf[i]+Hf[i] for i in range(n)])]
    cl=hamming_clusters(seqs); ncl=len(set(cl)); big=max(Counter(cl).values())
    fo=[cl[i]%FOLDS for i in range(n)]; F=list(range(FOLDS))
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS

    r2c=evalr2(prep(Xc,fo,F),y); pp=prep(Xp,fo,F); pf=prep(Xf,fo,F)
    r2p=evalr2(pp,y); r2f=evalr2(pf,y)
    incr_phys=r2p-r2c; incr_higher=r2f-r2p
    incr_higher_rnd=evalr2(prep(Xf,fo_rnd,F),y)-evalr2(prep(Xp,fo_rnd,F),y)
    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pp,yp); nulls.append(ic)
        if ic>=incr_higher: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)
    floor=incr_higher>=0.01; sig=pval<0.05
    if floor and sig: verdict="crosses_boundary"
    elif incr_higher_rnd>=0.01 and not floor: verdict="bounded_descriptor_only"
    else: verdict="composition_artifact"
    checks={"n_used":n,"n_total_10nt":n_total,"n_hamming_clusters":ncl,"largest_cluster":big,
            "r2_composition_ham":round(r2c,4),"r2_comp_plus_selfcompl_ham":round(r2p,4),"r2_full_ham":round(r2f,4),
            "incr_selfcompl_over_composition":round(incr_phys,4),
            "incr_higherorder_over_comp_selfcompl_ham":round(incr_higher,4),
            "incr_higherorder_random_split":round(incr_higher_rnd,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,
            "frac_switch_abs_y_ge_1":round(sum(1 for v in y if abs(v)>=1)/n,4),"y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("higher-order 序列在 composition + self-complementarity 之上预测 ATP-诱导 switch, Hamming-neighbor-controlled -- displacement-thermo 之外的 aptamer-switch 序列码" if verdict=="crosses_boundary"
                              else "序列信号在 composition/self-complementarity 层可解释或只 interpolate;higher-order 不在物理 proxy 之上加可迁移信号" if verdict=="bounded_descriptor_only"
                              else "Hamming-neighbor holdout + perm 后 higher-order 序列不在 composition+self-complementarity 之上加显著信号(readout 稀疏/noisy)"),
            "framing":"NEW 模态 boundary-map contact(DNA aptamer molecular switch: 序列 higher-order -> ATP-诱导 ON/OFF ratio 超 composition + self-complementarity displacement proxy), 非新机制;物理 proxy=self-complementarity(stdlib 代 strand-displacement equilibrium)",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM,"ham_thr":HAM_THR}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
