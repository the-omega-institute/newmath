# BEDC-Zeta 三元闭合塔

本文记录一个条件性证明纲领。核心形式是：解析延拓给出可见投影，但可见投影要成为 BEDC 合法零点，还必须由闭合三元系统生成。闭合三元系统由三条线组成：

$$
\mathsf P=\text{prime-register / packet source},
\qquad
\mathsf U=\text{unit boundary / Lee--Yang stability},
\qquad
\mathsf T=\text{phase time / recursive tower}.
$$

三元闭合关系写作

$$
\mathcal C(\mathsf P,\mathsf U,\mathsf T)=0.
$$

合法隐藏层只允许单位相位和 prime-register 纤维：

$$
\mathbb T,
\qquad
\prod_{p\in S}\mathbb Z_p.
$$

非平凡实正尺度

$$
\mathbb R_{>0}
$$

不是合法闭合 gauge。因此，若一个零点证书塔的极限读数为

$$
s=\frac12+r+i\gamma,
\qquad
r\ne0,
$$

则其局部通道包含径向因子 $e^{-rh}$。条件路线的目标是证明这类径向因子不能由合法闭合塔吸收。

## 本体三性质

三元闭合的三个读数为：

$$
\mathsf P=\text{source distinction, prime ledger, packet choice},
$$

$$
\mathsf U=\text{unit boundary, mirror symmetry, legal gauge},
$$

$$
\mathsf T=\text{time generation, routing, recursive tower}.
$$

闭合缺陷记为

$$
\Omega=\mathcal C(\mathsf P,\mathsf U,\mathsf T),
$$

缺陷能量记为

$$
\mathcal E=|\Omega|^2.
$$

能量不是原始本体性质，而是三元闭合失败后的二阶读数。

## Prime Ledger 与 Ontic Hamiltonian

令

$$
\mathcal L_{\mathbb P}:=\bigoplus_{p\in\mathbb P}\mathbb Z e_p.
$$

正整数

$$
n=\prod_p p^{v_p(n)}
$$

对应 prime ledger

$$
\nu(n)=\sum_p v_p(n)e_p.
$$

中心化 zeta 通道为

$$
n^{1/2-s}
=
\exp(-r\log n)\exp(-i\gamma\log n),
\qquad
s=\frac12+r+i\gamma.
$$

在 $\ell^2(\mathbb N_{\ge1})$ 上定义

$$
H_{\mathrm{ont}}|n\rangle=(\log n)|n\rangle.
$$

于是

$$
\log n=\sum_p v_p(n)\log p,
\qquad
H_{\mathrm{ont}}=\sum_p(\log p)N_p,
$$

并且相位流

$$
U(\gamma)=e^{-i\gamma H_{\mathrm{ont}}}
$$

是酉流。

**定理：素数频率唯一性。** 若有限多个有理数 $q_p$ 满足

$$
\sum_p q_p\log p=0,
$$

则所有 $q_p=0$。

**证明。** 清分母得到整数关系 $\sum_p a_p\log p=0$。指数化得到

$$
\prod_p p^{a_p}=1.
$$

由素数唯一分解，所有 $a_p=0$，故所有 $q_p=0$。

## 局部通道与法向缺陷

令 $a\in A_n$ 为 active 节点，带有高度 $h_a>0$。定义

$$
U_a(s):=e^{-(s-1/2)h_a}.
$$

若

$$
s=\frac12+r+i\gamma,
$$

则

$$
U_a(s)=e^{-rh_a}e^{-i\gamma h_a}.
$$

定义法向缺陷

$$
d_a(s):=\log |U_a(s)|=-rh_a.
$$

对有限 packet $A_n$，定义

$$
\Omega_n(s):=(d_a(s))_{a\in A_n},
$$

以及

$$
\mathcal E_n(s):=|\Omega_n(s)|^2
=
\sum_{a\in A_n}d_a(s)^2.
$$

于是

$$
\mathcal E_n(s)
=
r^2\sum_{a\in A_n}h_a^2.
$$

因此，如果

$$
W_n:=\sum_{a\in A_n}h_a^2\to\infty,
$$

则任何 $r\ne0$ 都使 $\mathcal E_n(s)$ 在 refinement tower 中无界。

## Solenoid 合法隐藏层

对素数集合 $S$，定义

$$
\mathbb Z[S^{-1}]
=
\left\{
\frac ab\in\mathbb Q:
b\text{ 的素因子全部属于 }S
\right\},
$$

并令

$$
\Sigma_S:=\widehat{\mathbb Z[S^{-1}]}.
$$

其相位读数满足短正合列

$$
0\to
\prod_{p\in S}\mathbb Z_p
\to
\Sigma_S
\to
\mathbb T
\to0.
$$

**定理：紧群没有非平凡实正尺度角色。** 若 $G$ 是紧群，且

$$
\rho:G\to\mathbb R_{>0}
$$

是连续群同态，则 $\rho\equiv1$。

**证明。** $\rho(G)$ 是 $\mathbb R_{>0}$ 的紧子群。取对数后，$\log\rho(G)$ 是 $(\mathbb R,+)$ 的紧子群。加法实线的紧子群只有 $\{0\}$，所以 $\rho(G)=\{1\}$。

因此，离线因子 $e^{-rh_a}$ 不能被 solenoid 的紧相位层或 $p$-进纤维吸收。

## 宇称与缺陷能量

定义 zeta 宇称反射

$$
J(s)=1-\overline{s}.
$$

若

$$
s=\frac12+r+i\gamma,
$$

则

$$
J(s)=\frac12-r+i\gamma.
$$

由 $d_a(s)=-rh_a$ 可得

$$
d_a(Js)=-d_a(s),
$$

而能量为偶量：

$$
\mathcal E_n(Js)=\mathcal E_n(s).
$$

这说明法向缺陷有符号，能量只读出其平方规模。

## Eta 折线与 Half-Split 读数

令

$$
\eta(s)=\sum_{n\ge1}(-1)^{n-1}n^{-s},
$$

并定义

$$
v_N(s)=(-1)^{N-1}N^{-s},
\qquad
P_N(s)=\sum_{n\le N}v_n(s),
\qquad
R_N(s)=\sum_{n>N}v_n(s).
$$

若 $\eta(s)=0$，定义第 $N$ 段的切分坐标 $\theta_N(s)$ 为

$$
P_{N-1}(s)+\theta_N(s)v_N(s)=0.
$$

由 $P_N=-R_N$ 得

$$
\theta_N(s)=1+\frac{R_N(s)}{v_N(s)}.
$$

又由 $R_N=v_{N+1}+R_{N+1}$ 得递归式

$$
\theta_N(s)
=
1-\left(\frac{N}{N+1}\right)^s\theta_{N+1}(s).
$$

Euler-Boole 展开给出

$$
\theta_N(s)
=
\frac12+\frac{s}{4N}+O_s(N^{-2}).
$$

因此，对

$$
s=\frac12+r+i\gamma
$$

定义

$$
\Delta_N(s)
:=
4N\left(\Re\theta_N(s)-\frac12\right)-\frac12,
\qquad
\Phi_N(s):=4N\Im\theta_N(s),
$$

则

$$
\Delta_N(s)=r+O_s(N^{-1}),
\qquad
\Phi_N(s)=\gamma+O_s(N^{-1}).
$$

half-split 坐标由有限折线读出法向尺度与相位时间；它不是边界稳定性的证明。

## Golden 分辨率与弱捕获

令

$$
\varphi=\frac{1+\sqrt5}{2},
\qquad
\varepsilon_m=\varphi^{-m},
\qquad
N_m=F_{Lm},
$$

其中 $L$ 是固定放大因子。对零点 $\rho$，定义黄金零点盒

$$
D_m=\{s:|s-\rho|\le\varphi^{-m}\}.
$$

定义黄金 eta packet

$$
P_m(s)=\sum_{n=1}^{N_m}(-1)^{n-1}n^{-s},
\qquad
R_m(s)=\eta(s)-P_m(s).
$$

**定理：Golden weak ActiveCapture。** 设 $\rho$ 是 $\eta$ 的 $q$ 阶零点，并且在某邻域内 $\Re(s)\ge\sigma_0>0$。若 $L\sigma_0>q$，则对充分细的 $m$，

$$
|R_m(s)|<|P_m(s)|
\qquad
s\in\partial D_m.
$$

因此 $P_m$ 与 $\eta$ 在 $D_m$ 内有相同零点数。

**证明。** 局部写作

$$
\eta(s)=(s-\rho)^qg(s),
\qquad
g(\rho)\ne0.
$$

取邻域使 $|g(s)|\ge c>0$。在 $\partial D_m$ 上，

$$
|\eta(s)|\ge c\varphi^{-qm}.
$$

一致收敛与交错尾项估计给出

$$
|R_m(s)|\le C N_m^{-\sigma_0}\le C'\varphi^{-L\sigma_0m}.
$$

由 $L\sigma_0>q$，对充分细的 $m$ 有

$$
|R_m(s)|<\frac12|\eta(s)|.
$$

因为 $P_m=\eta-R_m$，于是 $|R_m(s)|<|P_m(s)|$。Rouche 定理给出同零点数。

该结论给出弱证书塔：它捕获零点岛，但不提供单位边界稳定性。

## Lee-Yang Stable Packet

设 packet 主项可写成

$$
F(s)=P((u_a(s))_{a\in A}),
\qquad
u_a(s)=e^{-(s-1/2)h_a}.
$$

称 packet 是 Lee-Yang stable，若

$$
P(u)\ne0
\quad\text{当所有 } |u_a|<1,
$$

且

$$
P(u)\ne0
\quad\text{当所有 } |u_a|>1.
$$

**定理：stable packet 捕获推出固定半线读数。** 若一个 completed zero $\rho$ 被 Lee-Yang stable packet 捕获，则 $\Re(\rho)=1/2$。

**证明。** 写

$$
\rho=\frac12+r+i\gamma.
$$

若 $r>0$，则每个 active 坐标满足

$$
|u_a(\rho)|=e^{-rh_a}<1.
$$

在足够小的零点盒内仍处于内域，Lee-Yang stable packet 无零。但捕获与 Rouche 等价要求主项在该零点岛中有相同零点数，矛盾。若 $r<0$，则所有 active 坐标处于外域，同理矛盾。故 $r=0$。

## Golden Stable Capture Bridge

称 $\rho$ 满足 GoldenStableCaptureBridge，若存在黄金弱捕获 packet $P_m$ 与 Lee-Yang stable packet $Q_m$，使：

1. $P_m$ Rouche 捕获 $\rho$；
2. $Q_m$ Lee-Yang stable；
3. $P_m$ 与 $Q_m$ 在零点岛边界上有相同绕数：

$$
\operatorname{wind}(P_m(\partial D_m),0)
=
\operatorname{wind}(Q_m(\partial D_m),0).
$$

由绕数相同，$Q_m$ 捕获同一零点岛；由 Lee-Yang stability，零点岛不能位于 $r\ne0$。因此 GoldenStableCaptureBridge 推出固定半线读数。

## Zeckendorf-Godel Stable Packet Target

令

$$
X_m=\{z\in\{0,1\}^m:z_kz_{k+1}=0\}.
$$

定义 Zeckendorf-Godel 素数码

$$
g(z)=\prod_{k=1}^m p_k^{z_k},
$$

以及

$$
u_k(s)=p_k^{1/2-s}.
$$

定义 path packet

$$
Q_m(s)
=
\sum_{z\in X_m}
\prod_{k=1}^m u_k(s)^{z_k}.
$$

这是路径图的多变量独立集多项式，满足 Fibonacci 型递归

$$
I_m=I_{m-1}+u_mI_{m-2}.
$$

它是 Lee-Yang bridge 的自然候选。需要证明的是：该 Zeckendorf-Godel packet 或其 Joukowsky pullback 版本满足内外域无零，并且与黄金 eta packet 具有同一零点岛绕数。

## 主条件定理

定义 source row

$$
\mathsf{ZetaGoldenLeeYangBridge}
$$

为以下断言：每个 accepted non-trivial completed zeta zero 的黄金 weak packet 都能与一个 Zeckendorf-Godel Lee-Yang stable packet 建立同零岛绕数桥，并且桥接过程不引入 $\mathbb R_{>0}$ 实尺度 anomaly。

**定理。**

$$
\mathsf{ZetaGoldenLeeYangBridge}
\Longrightarrow
\text{all accepted non-trivial completed zeta zeros have }\Re(s)=1/2.
$$

**证明。** 任取 accepted non-trivial completed zeta zero $\rho$。Golden weak ActiveCapture 给出黄金弱 packet。$\mathsf{ZetaGoldenLeeYangBridge}$ 给出同零岛 Lee-Yang stable packet。由 stable packet 捕获定理，$\Re(\rho)=1/2$。

因此，条件路线的承重点是：

$$
\operatorname{wind}(Q_m(\partial D_m),0)
=
\operatorname{wind}(P_m(\partial D_m),0),
$$

并且该绕数桥必须保持 Zeckendorf ledger、phase ledger、tail ledger、radial purity 与 tower refinement compatibility。
