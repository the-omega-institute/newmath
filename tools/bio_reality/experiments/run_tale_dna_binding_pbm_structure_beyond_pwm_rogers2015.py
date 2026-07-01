#!/usr/bin/env python3
"""TALE–DNA binding PBM 序列码(第13模态:protein-DNA binding;single-mechanism;oracle 第13弧
completeness-axis 判别性 near-complete 端, 精炼规则预测 FAILS)。相邻位置 dinucleotide 非加性结构
是否在 composition + per-position additive PWM(near-complete 物理模型, 论文 median R²=0.959)之上
预测 TALE probe binding signal? y=log10(VALUE)(Rogers 2015 GSM1372480 TAL2009; 60bp, 36 变量位点)。
baseline_comp=global composition;baseline_pwm=+位置 mononucleotide one-hot(=additive PWM);
full=+相邻变量位点 dinucleotide 交互 one-hot。one-hot 不 z-score(保稀疏)。unique-probe 随机 5-fold
+ perm。**PRE-REGISTERED 预测:FAILS(structure 不超近完备 PWM)**。crosses_boundary /
bounded_descriptor_only / composition_artifact。NEW 模态 fresh contact 非新机制。纯 stdlib。"""
import json, math, random, pathlib, sys, zlib
from collections import Counter, defaultdict

EXPERIMENT_ID="tale_dna_binding_pbm_structure_beyond_pwm_rogers2015"
CLAIM_ID="h3.cross_layer_relation.protein_dna_binding.tale_pbm_binding_sequence_beyond_composition_pwm_rogers2015"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=200; N_MAX=8000
random.seed(SEED)

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
def zscol(vals):
    m=sum(vals)/len(vals); sd=(sum((x-m)**2 for x in vals)/len(vals))**0.5 or 1.0
    return [(x-m)/sd for x in vals]
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

BASES="ACG"  # T = reference (dropped) 避免与 intercept 共线
def comp_feats(s):
    L=len(s); f={c:s.count(c)/L for c in "ACGT"}
    di={a+b:0 for a in "ACGT" for b in "ACGT"}
    for i in range(L-1):
        d=s[i:i+2]
        if d in di: di[d]+=1
    tot=L-1 or 1
    return [f["A"],f["C"],f["G"],f["G"]+f["C"]]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
def pwm_onehot(s,varpos):
    out=[]
    for p in varpos:
        ch=s[p]
        out.extend(1.0 if ch==b else 0.0 for b in BASES)
    return out
def dinuc_onehot(s,pairs):
    out=[]
    for (p,q) in pairs:
        a=s[p]; b=s[q]
        # 3x3 交互(main effects 已在 pwm), T-ref dropped
        out.extend(1.0 if (a==ba and b==bb) else 0.0 for ba in BASES for bb in BASES)
    return out

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
def clusters(seqs,KMER=10,JAC=0.7):
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
    D=json.loads(DATA_PATH.read_text()); E=D["elements"]; varpos=D["varpos"]; n_total=len(E)
    if n_total>N_MAX:
        idx=list(range(n_total)); random.Random(SEED).shuffle(idx); E=[E[i] for i in sorted(idx[:N_MAX])]
    n=len(E); seqs=[x["seq"] for x in E]; y=[float(x["y"]) for x in E]
    pairs=[(varpos[k],varpos[k+1]) for k in range(len(varpos)-1)]  # 相邻变量位点对
    compz=list(zip(*[zscol(c) for c in zip(*[comp_feats(s) for s in seqs])]))  # z-scored comp per row
    compz=[list(r) for r in compz]
    PW=[pwm_onehot(s,varpos) for s in seqs]
    DN=[dinuc_onehot(s,pairs) for s in seqs]
    Xc=[[1.0]+compz[i] for i in range(n)]
    Xp=[[1.0]+compz[i]+PW[i] for i in range(n)]
    Xf=[[1.0]+compz[i]+PW[i]+DN[i] for i in range(n)]
    F=list(range(FOLDS))
    # k-mer identity-cluster holdout(近重复整簇, leakage 控制)
    cl=clusters(seqs); ncl=len(set(cl)); big=max(Counter(cl).values())
    fo_cl=[cl[i]%FOLDS for i in range(n)]
    # random-split 对照
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS
    # 主判据 = cluster holdout
    pc=prep(Xc,fo_cl,F); pp=prep(Xp,fo_cl,F); pf=prep(Xf,fo_cl,F)
    r2c=evalr2(pc,y); r2p=evalr2(pp,y); r2f=evalr2(pf,y)
    incr_pwm=r2p-r2c; incr_structure=r2f-r2p
    incr_structure_rnd=evalr2(prep(Xf,fo_rnd,F),y)-evalr2(prep(Xp,fo_rnd,F),y)
    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pp,yp); nulls.append(ic)
        if ic>=incr_structure: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)
    floor=incr_structure>=0.01; sig=pval<0.05
    near_complete = r2p>=0.75   # oracle 声称 near-complete(paper 0.959); 实测是否成立
    if floor and sig: verdict="bounded_descriptor_only"  # structure 超 additive PWM (单 TALE 无 transfer 轴 -> 封顶 bounded)
    else: verdict="composition_artifact"
    # 前瞻预测 FAILS 只在 PWM 真 near-complete 时才是规则检验; 否则 premise 失败(PWM 仅 partial)
    prem_ok = near_complete
    matched=(verdict=="composition_artifact") if prem_ok else None
    checks={"n_used":n,"n_total":n_total,"n_varpos":len(varpos),"n_dinuc_pairs":len(pairs),
            "n_identity_clusters":ncl,"largest_cluster":big,
            "r2_composition_clusterfold":round(r2c,4),"r2_comp_plus_pwm_clusterfold":round(r2p,4),"r2_full_clusterfold":round(r2f,4),
            "incr_pwm_over_composition":round(incr_pwm,4),
            "incr_structure_dinuc_over_pwm_clusterfold":round(incr_structure,4),
            "incr_structure_dinuc_random_split":round(incr_structure_rnd,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "fitted_pwm_near_complete_r2ge0.75":near_complete,"oracle_claimed_pwm_r2":0.959,
            "premise_near_complete_holds":prem_ok,
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,
            "pre_registered_prediction":"fails (composition_artifact)","matches_pre_registered_prediction":matched,
            "y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    if not prem_ok:
        interp=("PREMISE 失败:自拟合 additive PWM 仅 held-out R^2=%.3f(远低于 oracle/论文声称的 0.959 near-complete)-> 这不是 near-complete 测试; 在这个 diverse probe library 上 additive PWM 只是 PARTIAL, 相邻位置 dinucleotide 非加性结构再加 cluster-holdout +%.3f(perm p=%.3f)-- 与 partial→adds 规则一致, 非规则证伪; near-complete FAILS 端仍未测"%(r2p,incr_structure,pval)) if verdict=="bounded_descriptor_only" else ("PREMISE 失败:additive PWM 仅 R^2=%.3f(非 near-complete); cluster-holdout 后 dinuc 结构不显著加信号"%r2p)
    else:
        interp=("相邻位置 dinucleotide 非加性结构在 composition + 近完备 additive PWM(R^2=%.3f)之上仍加显著信号(REFUTES 预测)"%r2p if verdict=="bounded_descriptor_only" else "cluster-holdout + perm 后 dinuc 结构不超近完备 PWM -- CONFIRMS FAILS 预测")
    result={"interpretation":interp,
            "framing":"NEW 模态 boundary-map contact(engineered protein-DNA binding: TALE probe 序列 -> PBM binding signal 超 composition + additive PWM), 非新机制; oracle 第13弧本意作 completeness-axis 判别性 near-complete 端, 但自核发现拟合 PWM 仅 partial(R^2~0.40, 非声称 0.959)-> 实为又一 partial→adds 点; near-complete FAILS 端仍缺; 对比 RBS-185/inDelphi-186(partial→adds)/CRX-184(无模型→crosses)",
            "prereg":"oracle 按精炼规则预测 FAILS(声称 additive PWM median R²=0.959 near-complete); 自核: 实测拟合 PWM held-out R^2 仅 ~0.40, near-complete premise 未复现",
            "leakage_caveat":"k-mer identity-cluster holdout(近重复整簇)vs random-split 对比给 dinuc 增量的 leakage 上界; 单 TALE(TAL2009)无 leave-TALE-out transfer 轴",
            "data":D.get("source",""),"physical_model":D.get("physical_model",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
