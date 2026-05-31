# PDF 构建重构说明（多 PDF 拆分方向）

> 本文档只**说明方向与约束**,不实施,也尚未进 codex-refactor-loop。它是后续 design-consensus / 人工决策的输入。

## 1. 问题

单一 `papers/bedc/main.tex` 体积持续膨胀,其中绝大部分是**机械派生内容**(NameCert 构造的饱和实例),核心理论被淹没。后果:

- 编译需要把 TeX 内存参数顶到极限(`Makefile` 里 `pool_size=300000000 max_strings=12000000 hash_extra=4000000 …`),仍随增长逼近上限。
- 单一 PDF 已无人类可读性 —— 没人会线性读一份这么大的文档。
- 因此 `make`(双趟 pdflatex)当前的**主要价值实际是语法检查**(`\input` 解析、math-mode、未定义宏、`\autoref` 解析、marker uniqueness),而不是产出可读文档。

## 2. 现状数据(实测,作为约束基线)

| 指标 | 值 |
|---|---|
| `main.tex` 的 `\input{parts/...}` 总数 | 976 |
| 其中 `parts/concrete_instances/` | **956(98%)** |
| 非机械(core / proof / vision / governance …) | 20 |
| `parts/` 总体积 | ~82 MB |
| 其中 `parts/concrete_instances/` | **77 MB(94%)** |
| 非机械内容合计 | ~5 MB(visions 3.1M / core 236K / ground_compiler 852K / …) |
| 全 paper `\autoref` 总数 | 106,905 |
| 出现在 concrete_instances 内部的 `\autoref` | 104,232 |
| concrete_instances `\label` 定义数 | 37,216 |

**跨引用耦合(决定可拆性的关键)**:

| 引用方向 | 数量 | 占比 |
|---|---|---|
| concrete ↔ concrete(机械内部互引) | 102,219 | 占 concrete 内 autoref 的 **98.1%** |
| concrete → core(机械引用核心理论) | 2,013 | 1.9% |
| core → concrete(核心引用机械实例) | 98 | 极小 |

结论:**机械派生层在引用上近乎自闭合**(98% 引用落在自身)。这使得"核心理论一份 + 机械派生分组多份"的拆分在技术上高度可行 —— 拆分主要要解决的是 1.9% 出向引用 + 98 条入向引用的跨 PDF 解析,以及机械层内部的**主题分组不切断密集互引**。

## 3. 核心张力(不可妥协的约束)

1. **语法检查覆盖必须保持**:所有 `.tex` 仍要在某处被 pdflatex 编译,否则失去"编译即语法门"的价值。拆分不能让任何子文件脱离编译覆盖。
2. **最小化自动化管线影响**:
   - `lean4/scripts/critical_path.py` 走 **`main.tex` 的 `\input{}` 闭包**做全树扫描(theorem 环境、`\leanchecked` drift、critical path)。多 root 会破坏"单一 main.tex 闭包"假设。
   - `bedc_ci.py audit`(paper↔Lean drift)、`scripts/check_marker_uniqueness.py`(`\leanchecked` 唯一性)、`Makefile` precheck(`check_math_env.sh` / check L / check M)依赖现有 parts 布局。
   - hub + subdir 布局、`\closureat` / closurestatus 协议不变。
3. **跨 PDF `\autoref`**:`\autoref` 默认只在单文档内解析。拆成多 PDF 后,跨 PDF 引用(2,013 条 concrete→core + 98 条 core→concrete + 任何跨主题 concrete↔concrete)会变成 `?? on page ??`,除非引入外部引用机制。

## 4. 方向(用户直觉 + 技术细化)

**主 PDF(可读)= 非机械核心理论**:frontmatter + core + proof_* + hardening + visions + philosophy + governance + ground_compiler / self_compilation 等。约 ~5 MB,人类可线性阅读,是"论文"本体。

**派生 PDF(分类组合)= 机械 NameCert 构造**:把 956 个 concrete_instances 按主题/引用社区分成 N 份(例:metric/completion 一组、subgroup/algebra 一组、computation/halting 一组、…)。每份是某一主题的饱和实例册,需要时单独编译/查阅。

## 5. 拆分的真正难点

1. **机械层主题分组 = 引用图社区划分**。102,219 条 concrete↔concrete 引用构成一张密集图;按主题切 PDF 时,**必须最小化跨主题引用边**(否则这些边变成跨 PDF `\autoref`)。这是一个 community-detection / graph-partition 问题,不是简单按文件名前缀切。需要先从 `\label`/`\autoref` 抽出引用图再分区。
2. **跨 PDF 引用机制**。标准解法是 `xr` / `xr-hyper` 宏包:一个文档 `\externaldocument` 另一个文档的 `.aux`,即可 `\ref`/`\autoref` 解析到外部 label(超链接需 `xr-hyper` + 一致的 `hyperref` 锚点)。方向:
   - 派生 PDF `\externaldocument{main}` → 解析 2,013 条 concrete→core。
   - 主 PDF `\externaldocument{<各派生>}` → 解析 98 条 core→concrete(或对这 98 条降级为纯文本/不加链接)。
   - 派生 PDF 之间若有残留跨主题边,互相 `\externaldocument`。
   - 代价:`xr` 需要被引文档**先编译出 `.aux`**,引入编译顺序依赖(先 main 再 derived,或多趟收敛)。

## 6. 关键设计选择:把"语法门"与"可读产物"解耦

这是最小化管线影响的杠杆。两条路线(留给决策):

- **选项 A —— monolith 留作语法门,split 作 additive 可读视图**。保留现有 `main.tex` 全量 `-draftmode` 编译作为 CI **语法检查门**(管线 / critical_path.py / bedc_ci.py **零改动**);**新增**可读的 split PDF target(主 + 派生)作为人类阅读产物。
  - 优点:管线零风险,纯增量。
  - 缺点:不解决 monolith 编译本身的内存/时长增长痛点(语法门照样吃 300MB pool)。
- **选项 B —— 用"逐 root 编译 sweep"替代 monolith 作语法门**。语法覆盖 = 各 root PDF 编译之并集(每个 root 更小、更快、更省内存);管线需教会"多 root 闭包"(critical_path.py 接受 root 列表,marker uniqueness 跨 root 聚合)。
  - 优点:真正缓解内存/时长增长。
  - 缺点:动管线,风险更高;需 critical_path.py / bedc_ci.py / precheck 适配多 root。
- **混合**:短期选 A(零风险拿到可读产物),中期评估 B(若 monolith 语法门逼近 TeX 内存硬上限再切)。

## 7. 对自动化管线的影响清单(设计时逐条回答)

- `critical_path.py`:`main.tex` 闭包 → 是否改为 root 列表闭包?选项 A 下不变。
- `bedc_ci.py audit` / `\leanchecked` drift:label/marker 现在跨多 PDF;唯一性与存在性检查需在**全 root 并集**上做,而非单 PDF。
- `check_marker_uniqueness.py`:跨 root 聚合,防同一 `\leanchecked` 在主 + 派生重复。
- `\closureat` / closurestatus / `\origin`:不变(内容协议与 PDF 划分正交)。
- rollup / deploy(dossier HTML 等下游):产物从 1 个 PDF 变 N 个,部署/索引需相应分类。
- precheck(check L math-mode / check M 死 `\input`):按 root 各跑或全树跑,覆盖不能漏。

## 8. 开放决策问题(留给 design-consensus / 人工)

1. 选 A(monolith 语法门 + additive split)还是 B(多 root sweep 替代 monolith)还是混合?
2. 派生 PDF 怎么分主题:按现有 slug / 目录,还是按引用图社区自动划分(最小化跨 PDF 边)?分几份?
3. 跨 PDF 引用:`xr-hyper` 全量解析,还是对核心↔派生的少量引用(98 + 2,013)降级为非链接文本以避免编译顺序依赖?
4. critical_path.py / bedc_ci.py 是否改为多 root 感知?还是靠选项 A 维持 main.tex 单闭包?
5. 下游 deploy / dossier HTML 如何消费 N 个 PDF?

## 9. 边界(本文档不做的)

- 不改任何 `.tex` 内容、不动 closurestatus / NameCert 协议。
- 不实施拆分、不改 Makefile、不改管线脚本。
- 未进 codex-refactor-loop;是否实施、怎么实施由后续决策。
