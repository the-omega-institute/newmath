#!/usr/bin/env python3
"""Cas9 template-free repair-to-WT 序列码(第12模态:CRISPR editing repair outcome;single-mechanism;
oracle 第12弧 completeness-axis 检验候选 B1, 精炼规则预测 ADDS = partial model)。generic higher-order
序列结构是否在 composition + inDelphi 部分完备机制模型(r²≈0.40)之上预测 repair-to-WT 分数,
identity+gene-controlled? y=mESC repair to wt(Shen 2018; 55nt Cas9 context)。baseline_comp=composition;
baseline_phys=+inDelphi(predicted repair_to_wt + MH-deletion 变体 + frameshift, IN-TABLE);full=+generic
structure(shannon k2/k3、RC/回文密度、max-RC-stem、max 直接重复(MH proxy)、homopolymer/purine/AT run、
CpG O/E)。k-mer identity-cluster holdout + leave-gene-out 迁移 + random-split 对照 + perm。
**PRE-REGISTERED 预测:ADDS(partial model 有残余空间)**。crosses_boundary / bounded_descriptor_only /
composition_artifact。NEW 模态 fresh contact 非新机制。纯 stdlib。"""
import json, math, random, pathlib, sys, zlib
from collections import Counter, defaultdict

EXPERIMENT_ID="indelphi_crispr_repair_to_wt_structure_beyond_model_shen2018"
CLAIM_ID="h3.cross_layer_relation.crispr_repair_outcome.template_free_repair_to_wt_sequence_beyond_composition_indelphi_shen2018"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=300; KMER=8; JAC=0.5
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
    return [f["A"],f["C"],f["G"],f["G"]+f["C"]]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
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
def max_direct_repeat(s,kmax=14):
    """最长 k 使某 k-mer 在 s 内出现 >=2 次(非重叠)-> microhomology/直接重复 proxy(generic)."""
    best=0
    for k in range(3,min(kmax,len(s)//2)+1):
        pos={}
        for i in range(len(s)-k+1): pos.setdefault(s[i:i+k],[]).append(i)
        if any(len(ps)>=2 and (max(ps)-min(ps))>=k for ps in pos.values()): best=k
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
    return [shannon_k(s,2), shannon_k(s,3), rc_density(s,4), rc_density(s,5), max_rc_stem(s)/14.0,
            max_direct_repeat(s)/14.0, max(mrun(s,c) for c in "ACGT")/L, mrun(s,"AG")/L, mrun(s,"AT")/L, cpg_oe(s)]

PHYS_KEYS=['pred_wt','pred_wt_mh','pred_fs']
def phys_feats(E):
    med={}
    for k in PHYS_KEYS:
        vals=[e.get(k) for e in E if e.get(k) is not None]; med[k]=sorted(vals)[len(vals)//2] if vals else 0.0
    return [[ (e.get(k) if e.get(k) is not None else med[k]) for k in PHYS_KEYS] for e in E]

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
            if not ki: continue
            for bi in range(ai+1,len(mem)):
                j=mem[bi]; kj=ksets[j]
                if not kj or find(i)==find(j): continue
                if len(ki&kj)/len(ki|kj)>=JAC: uni(i,j)
    roots={}
    for i in range(n): roots.setdefault(find(i),len(roots))
    return [roots[find(i)] for i in range(n)]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); E=D["elements"]; n=len(E)
    seqs=[x["seq"] for x in E]; y=[float(x["y"]) for x in E]; genes=[x.get("gene","") for x in E]
    Cf=[comp_feats(s) for s in seqs]; Pf=phys_feats(E); Hf=[higher_feats(s) for s in seqs]
    Xc=[[1.0]+r for r in zscols(Cf)]
    Xp=[[1.0]+r for r in zscols([Cf[i]+Pf[i] for i in range(n)])]
    Xf=[[1.0]+r for r in zscols([Cf[i]+Pf[i]+Hf[i] for i in range(n)])]
    cl=clusters(seqs); ncl=len(set(cl)); big=max(Counter(cl).values())
    fo=[cl[i]%FOLDS for i in range(n)]; F=list(range(FOLDS))
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS
    ug=sorted(set(genes)); gmap={g:i for i,g in enumerate(ug)}; fo_g=[gmap[g]%FOLDS for g in genes]

    r2c=evalr2(prep(Xc,fo,F),y); pp=prep(Xp,fo,F); pf=prep(Xf,fo,F)
    r2p=evalr2(pp,y); r2f=evalr2(pf,y)
    incr_phys=r2p-r2c; incr_structure=r2f-r2p
    incr_structure_rnd=evalr2(prep(Xf,fo_rnd,F),y)-evalr2(prep(Xp,fo_rnd,F),y)
    incr_structure_gene=evalr2(prep(Xf,fo_g,F),y)-evalr2(prep(Xp,fo_g,F),y)
    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pp,yp); nulls.append(ic)
        if ic>=incr_structure: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)
    floor=incr_structure>=0.01; sig=pval<0.05; transfers=incr_structure_gene>=0.01
    if floor and sig and transfers: verdict="crosses_boundary"
    elif floor and sig: verdict="bounded_descriptor_only"
    else: verdict="composition_artifact"
    matched = (verdict in ("crosses_boundary","bounded_descriptor_only"))  # 预测 ADDS
    checks={"n_used":n,"n_identity_clusters":ncl,"largest_cluster":big,"n_genes":len(ug),
            "r2_composition_ident":round(r2c,4),"r2_comp_plus_indelphi_ident":round(r2p,4),"r2_full_ident":round(r2f,4),
            "incr_indelphi_over_composition":round(incr_phys,4),
            "incr_structure_over_comp_indelphi_ident":round(incr_structure,4),
            "incr_structure_leave_gene_out":round(incr_structure_gene,4),
            "incr_structure_random_split":round(incr_structure_rnd,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,"transfers_leave_gene":transfers,
            "pre_registered_prediction":"adds (bounded_descriptor_only or crosses_boundary)",
            "matches_pre_registered_prediction":matched,"y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("generic higher-order 结构在 composition + inDelphi 之上预测 repair-to-WT, identity+gene 迁移 -- inDelphi scalar 漏掉的 microhomology/结构 residual" if verdict=="crosses_boundary"
                              else "generic higher-order 结构在 identity-cluster 上超 composition+inDelphi 且显著, 但不跨 gene 迁移(基因特异)" if verdict=="bounded_descriptor_only"
                              else "identity-cluster holdout + perm 后 generic 结构不在 composition+inDelphi 之上加显著信号(inDelphi 已吃掉可及 microhomology 信号)"),
            "framing":"NEW 模态 boundary-map contact(Cas9 template-free repair OUTCOME: 序列 -> repair-to-WT 超 composition + inDelphi 部分完备机制模型), 非新机制; oracle 第12弧 completeness-axis 检验候选 B1, PRE-REGISTERED 预测=ADDS(partial model r²≈0.40 有残余); 对比 RBS-185 refuted / CRX-184 crosses",
            "prereg":"oracle 按精炼(completeness)规则预测 ADDS(inDelphi 对 repair-to-wt scalar 只 r≈0.64/r²≈0.40 partial → 有残余空间)",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
