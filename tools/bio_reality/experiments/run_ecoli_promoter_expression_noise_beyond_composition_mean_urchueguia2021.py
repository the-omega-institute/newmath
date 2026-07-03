#!/usr/bin/env python3
"""E. coli promoter expression NOISE 序列码(第15模态 / 全新 readout 类型 = 二阶矩;single readout;
pivot 候选, 预测 adds)。higher-order 序列结构是否在 composition + mean 表达之上预测 expression noise,
identity+gene-controlled? y=noise(Urchueguia 2021; natural promoter 96-1738nt)。baseline_comp=
composition(mono/dinuc/GC/len)+ fl_mean_log(mean 控制);full=+generic structure(shannon k2/k3、
RC/回文密度、max-RC-stem、homopolymer/purine/AT run、CpG、poly-A/T tract)。k-mer identity-cluster
holdout + leave-gene-out(regulon)迁移 + random 对照 + perm。**PRE-REGISTERED 预测:adds(中)**。
crosses_boundary / bounded_descriptor_only / composition_artifact。NEW readout 类型 fresh contact。纯 stdlib。"""
import json, math, random, pathlib, sys, zlib
from collections import Counter, defaultdict

EXPERIMENT_ID="ecoli_promoter_expression_noise_beyond_composition_mean_urchueguia2021"
CLAIM_ID="h3.cross_layer_relation.expression_noise.ecoli_promoter_sequence_noise_beyond_composition_mean_urchueguia2021"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=300; KMER=12; JAC=0.5
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
            fx=A[r][c]
            if fx: A[r]=[a-fx*b for a,b in zip(A[r],A[c])]
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
    return [f["A"],f["C"],f["G"],f["G"]+f["C"],math.log(L)]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
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
def cpg_oe(s):
    L=len(s); cg=sum(1 for i in range(L-1) if s[i:i+2]=="CG")
    pc=s.count("C")/L; pg=s.count("G")/L; exp=pc*pg*(L-1)
    return (cg/exp) if exp>0 else 0.0
def higher_feats(s):
    L=len(s)
    return [shannon_k(s,2),shannon_k(s,3),rc_density(s,4),rc_density(s,5),max_rc_stem(s)/14.0,
            max(mrun(s,c) for c in "ACGT")/L,mrun(s,"A")/L,mrun(s,"T")/L,mrun(s,"AT")/L,cpg_oe(s)]

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
def clusters(seqs):
    n=len(seqs); ksets=[kmer_set(s,KMER) for s in seqs]; NH=16;BANDS=8;PB=2
    sigs=[minhash(k,NH) if k else [0]*NH for k in ksets]; par=list(range(n))
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    def uni(a,b):
        ra,rb=find(a),find(b)
        if ra!=rb: par[max(ra,rb)]=min(ra,rb)
    bk=defaultdict(list)
    for i in range(n):
        for band in range(BANDS): bk[(band,)+tuple(sigs[i][band*PB:(band+1)*PB])].append(i)
    for mem in bk.values():
        if len(mem)<2: continue
        for ai in range(len(mem)):
            i=mem[ai]; ki=ksets[i]
            for bi in range(ai+1,len(mem)):
                j=mem[bi]; kj=ksets[j]
                if find(i)==find(j): continue
                if len(ki&kj)/len(ki|kj)>=JAC: uni(i,j)
    roots={}
    for i in range(n): roots.setdefault(find(i),len(roots))
    return [roots[find(i)] for i in range(n)]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing"}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); E=D["elements"]; n=len(E)
    seqs=[x["seq"] for x in E]; y=[float(x["y"]) for x in E]; mean=[float(x["mean"]) for x in E]; genes=[x["gene"] for x in E]
    Cf=[comp_feats(s) for s in seqs]; Hf=[higher_feats(s) for s in seqs]
    # baseline = composition + mean 控制列
    base=[Cf[i]+[mean[i]] for i in range(n)]
    Xc=[[1.0]+r for r in zscols(base)]
    Xf=[[1.0]+r for r in zscols([base[i]+Hf[i] for i in range(n)])]
    cl=clusters(seqs); ncl=len(set(cl)); big=max(Counter(cl).values())
    fo=[cl[i]%FOLDS for i in range(n)]; F=list(range(FOLDS))
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS
    ug=sorted(set(genes)); gmap={g:i for i,g in enumerate(ug)}; fo_g=[gmap[g]%FOLDS for g in genes]
    # mean-only baseline(看 composition 在 mean 之上加多少)
    Xm=[[1.0,mean[i]] for i in range(n)]
    r2m=evalr2(prep(Xm,fo,F),y)
    pc=prep(Xc,fo,F); pf=prep(Xf,fo,F)
    r2c=evalr2(pc,y); r2f=evalr2(pf,y)
    incr_comp=r2c-r2m; incr_structure=r2f-r2c
    incr_structure_rnd=evalr2(prep(Xf,fo_rnd,F),y)-evalr2(prep(Xc,fo_rnd,F),y)
    incr_structure_gene=evalr2(prep(Xf,fo_g,F),y)-evalr2(prep(Xc,fo_g,F),y)
    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pc,yp); nulls.append(ic)
        if ic>=incr_structure: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)
    floor=incr_structure>=0.01; sig=pval<0.05; transfers=incr_structure_gene>=0.01
    if floor and sig and transfers: verdict="crosses_boundary"
    elif floor and sig: verdict="bounded_descriptor_only"
    else: verdict="composition_artifact"
    matched=(verdict in ("crosses_boundary","bounded_descriptor_only"))  # 预测 adds
    checks={"n_used":n,"n_identity_clusters":ncl,"largest_cluster":big,"n_genes":len(ug),
            "r2_mean_only":round(r2m,4),"r2_comp_plus_mean":round(r2c,4),"r2_full":round(r2f,4),
            "incr_composition_over_mean":round(incr_comp,4),
            "incr_structure_over_comp_mean_clusterfold":round(incr_structure,4),
            "incr_structure_leave_gene_out":round(incr_structure_gene,4),
            "incr_structure_random_split":round(incr_structure_rnd,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,"transfers_leave_gene":transfers,
            "pre_registered_prediction":"adds","matches_pre_registered_prediction":matched,
            "y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("higher-order 序列结构在 composition + mean 之上预测 expression noise, identity+gene 迁移 -- mean 之外真实的 noise 序列码" if verdict=="crosses_boundary"
                              else "higher-order 结构在 identity-cluster 上超 composition+mean 且显著, 但不跨 gene 迁移(regulon 特异)" if verdict=="bounded_descriptor_only"
                              else "identity-cluster + perm 后 higher-order 结构不在 composition + mean 之上加显著信号 -- noise 由 composition+mean 主导"),
            "framing":"NEW readout 类型 = expression noise(分布二阶矩), NEW 模态 E. coli promoter noise; 非新机制; PRE-REGISTERED 预测=adds; mean 严格控制(noise~mean 强相关)",
            "prereg":"oracle 预测 adds 中概率(noise 有 mean-independent 轴, TFBS architecture/spacing 与 noise 耦合)",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
