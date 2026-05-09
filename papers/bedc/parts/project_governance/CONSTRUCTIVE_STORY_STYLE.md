# CONSTRUCTIVE_STORY_STYLE

## 目标

本文件规定 `\constructivestory{...}` 字段的写作规范, 供 codex pipeline 在后续 R-rounds 中逐章填写。

`\constructivestory` 是 `closurestatus` 块顶端的必填字段 (空 arg 通过 CI 但不渲染), 用一段 3-4 句的自然语言告诉读者: 这个 namecert 命名的概念, 是怎么从 `BHist.Empty` / `b0` / `b1` 这些原件、加上前面章节已经垒好的概念, 一层层递归构造出来的。整个 BEDC 的核心主张是"什么都不引入, 一切都从 Empty + 标记 + 递归生成"; 这个字段就是把这条主张, 在每一章具体兑现给读者看。

## 1. 双语布局

- **EN** 写在论文 `\constructivestory{<EN>}` 里, 单参数, 由 PDF 渲染。
- **ZH** 写在 `docs/dossier/data_source/glossary.json` 对应 region key 下的可选子字段 `constructive_story_zh`, dossier UI 双语模式下显示。
- EN 与 ZH 是同一段叙事的两种语言版本, 不是互译的硬翻; 两边都按各自语言的自然节奏写。

## 2. 篇幅与基调

- 3 至 4 句; 不要 1 句过短 (没把递归讲出来), 也不要 5 句以上 (会喧宾夺主、和 `\scopeclosed` `\notclaimed` 重叠)。
- 自然语言为主, 数学符号 (`$\emp$`, `$\Eone(\emp)$` 等) 在能 *简化* 叙述时引入, 不强求出现。
- 叙述视角是"作者带读者走一遍构造", 不是 "定理陈述列表"; 避免硬编号、避免堆 lemma 名。

## 3. 结构骨架 (3 句版)

1. **追溯起点 + 走构造**: 从哪几个 prior 层 (`Empty` / `b0` / `b1` / 上一章已命名的概念) 出发, 怎么叠出新模式 —— **要走具体动作**, 不是只列依赖名字
2. **命名动作**: 本章的 NameCert 给那个已经存在的模式起了什么名 (用 `$\<Name>Up$` 形式登记)
3. **没新东西**: 强调"不引入新原件, 只是给一个本来就在的读法起名"

第 3 句可与第 2 句合并; 必要时可加第 4 句澄清范围 (例如"完整 X 理论不在本闭合层级内"), 但能放进 `\notclaimed` 的就不要重复进 story。

## 3a. 关键原则: 展示传统数学隐藏的细节

每一段 story 的 **第 1 句**最重要的不是说"X 是什么", 而是说"X 怎么垒出来的"。传统数学习惯把构造过程缩成一行结果 ("a rational is an equivalence class of pairs"), 把 *如何* 隐藏起来。BEDC 没有这层抽象遮挡 —— 一切都是从 `Empty` / `b0` / `b1` / `Eone` 一层层叠出来的, 所以 story 必须把那些被传统数学省掉的步骤明写出来:

- ❌ "A rational is a pair of integers modulo equivalence."
- ✓ "A rational is a numerator history paired with a non-empty denominator history, both kept fully visible — no quotient, no equivalence class. Two pairs that traditional math would identify, such as $(2, 4)$ and $(1, 2)$, are not collapsed; instead the classifier knows when two pairs name the same rational, and $\hsame$ transports that recognition without ever forming the equivalence class."

- ❌ "Addition is associative, commutative, with identity 0."
- ✓ "Take a unary history of depth $n$ ... and lay another of depth $m$ on top of it: $m$ more b1-marks above the existing apex. The continuation that produced it is exactly the sum $n+m$."

- ❌ "Complex multiplication satisfies $i^2 = -1$."
- ✓ "Multiplication is given by the explicit formula $(a,b)(c,d) = (ac-bd,\,ad+bc)$, so $i^2 = -1$ is not a postulate but a consequence of squaring $(0,1)$ through that formula."

读者读完这一句应该能 *动手复现* 那个构造的第一步, 不只是知道一个名字。

## 4. 词汇政策

**EN**:
- 描述概念时用**标准数学专名**: "natural number" / "Boolean" / "category" / "field" / "module" / ...
- 而**不是** BEDC 内部名字: 不要写 "$\NatUp$ is a unary history's depth" 当主词; 那是 register 句的事
- 内部名字只在第 2 句的 register 形式中出现: "The chapter registers this reading under the name $\<Name>Up$" / "本章把这一读法命名为 `<Name>Up`"
- BEDC 内部 token 如 `BHist`, `Cont`, `hsame`, `b0`, `b1` 在叙述中可直接用, 它们是构造层的真名而非 namecert 别名

**ZH**:
- 全中文叙述, 不要中英混杂式音译 ("emp", "E1-extension" 这种半拉子写法只在受限的 glossary `desc` 里用; story 字段写"空历史"、"b1 扩展"、"b1 标记叠加")
- 保留作为标识符的 BEDC 名字 (`NatUp`, `CategoryUp`, `BHist`, `Cont`, `hsame`) 不译, 是程序中的真名
- 中文里的标准数学术语用中文 ("自然数"、"布尔值"、"范畴"、"域"、"模"); 外来术语用通用学术译名

**反 jargon 清单 (避免 BEDC 内部行话当主词)**:

下面这些词组在 BEDC 内部是技术术语, 但读者一眼看不出含义。在 story 里**避免直接用**, 改用具体动作描述:

| 避免 | 改写思路 |
|---|---|
| "ledgered pair" / "账本配对" | 写"一对历史并排展示"/"两条历史保持在视野中" |
| "carrier and classifier surface" / "承载与分类器表面" | 写具体的承载 (e.g. "rational history") 和具体的分类 (e.g. "tells when two pairs name the same rational") |
| "visible to its classifier" / "对分类器可见" | 写"由分类器追踪"/"被分类器认得" |
| "ledger discipline" / "账本纪律" | 直接说做了什么动作 |
| "transport discipline" / "输运纪律" | 写"hsame 把识别送过去" |
| "X is read as Y" / "X 读作 Y" 反复出现 | 至少有一句换成具体动作 ("stack one b1 above empty, then another, ...") |
| 罗列 prior 层名字而不说怎么用 | 必须写"取 X, 做动作 D, 得到 Y" |

## 5. 数学符号政策

**EN**:
- 行内数学用 `$...$`
- BEDC 宏 (`$\emp$`, `$\Eone$`, `$\NatUp$` 等) 直接用; 它们在 preamble 里都已定义好
- 下划线在 LaTeX 参数里仍按 `\_` 转义规则处理 (`$\NatUnaryStrictPrefix\_one\_step$`)

**ZH** (写进 glossary JSON, 当前 dossier 不接 MathJax):
- 不要用 `$...$` (会显示成原始 LaTeX)
- 用 unicode 或词汇替代: 写"空历史"而非 `$\emp$`; 写"b1 扩展"或"在...上叠一个 b1 标记"而非 `$\Eone(h)$`
- 程序标识符 (`NatUp`, `Cont` 等) 直接行内出现, 用 ASCII

## 6. 示例

### NatUp

> **EN.** Start with $\emp$, the empty history. Each $\Eone$-extension stacks one b1-mark above its predecessor, generating the unary spine $\emp,\,\Eone(\emp),\,\Eone(\Eone(\emp)),\,\ldots$\ A natural number is exactly the length of such a chain, read directly off the recursion that built it. The chapter registers this reading under the name $\NatUp$; no primitive enters beyond the empty history and the act of marking.

> **ZH.** 从空历史出发. 在它之上叠一个 b1 标记, 再叠一个, 再叠一个 —— 就得到一条由 b1 标记不断累加而成的链: 空, 一个 b1, 两个 b1, 如此往下. 一个自然数, 就是这条链的长度, 直接从生成它的那次递归中读出. 本章把这一读法命名为 NatUp; 除了空历史与"叠加标记"这一动作之外, 不引入任何新原件.

### BoolUp

> **EN.** Two histories suffice: the empty history, and the history obtained by placing one b1-mark above it. Whether or not that single b1 sits above the empty root is the only distinction made — and a Boolean, in BEDC, is exactly the choice between these two endpoints. The chapter registers this two-endpoint distinction under the name $\BoolUp$, drawing the mark and history classifiers from the kernel layer; full Boolean algebra (operations, eliminators, decidable predicates) is deliberately left out at this closure level.

> **ZH.** 两条历史就够了: 空历史本身, 以及在空历史上叠了一个 b1 标记的历史. 这一个 b1 是否位于空根之上, 就是唯一被作出的区分 —— 而 BEDC 中的布尔值, 恰恰就是在这两个端点之间作选择. 本章把这一两端点区分命名为 BoolUp, 所用的标记分类器与历史分类器都来自内核层; 完整的布尔代数 (运算、消去子、可判定谓词) 在此闭合层级有意暂不纳入.

### CategoryUp

> **EN.** Take histories as objects and the continuation relation $\Cont$ between histories as morphisms. Composing two morphisms means chaining two continuations head-to-tail; the identity at each object is the reflexivity of $\hsame$ on that history. A category, in this reading, is already lying in the kernel's history-and-continuation surface, with no functor library imported. The chapter registers this reading under the name $\CategoryUp$; the category laws are checked inside BEDC's own apparatus, and nothing is posited beyond what mark-stacking and same-relations already gave.

> **ZH.** 把历史当作对象, 把历史之间的延拓关系 Cont 当作态射. 两个态射的复合, 就是把两段延拓首尾相接; 每个对象处的单位, 就是历史等同关系 hsame 在该历史上的自反性. 在这种读法下, 一个范畴本来就摆在内核的"历史 + 延拓"表面上, 不需要引入任何外部函子库. 本章把这一读法命名为 CategoryUp; 范畴公理在 BEDC 自有装置中得到验证, 在标记叠加与同一关系之外没有引入任何新东西.

### 更多已写好的 exemplar

后续填写时直接对照 paper 中已有的 story (按递归底层顺序排列), 这些都已经按本规范写好, 是最权威参照:

| Region | Paper file (含 `\constructivestory{...}`) |
|---|---|
| `nat` | `parts/concrete_instances/04_nat_namecert_construction.tex` |
| `add` | `parts/concrete_instances/05_add_namecert_construction.tex` |
| `bool` | `parts/concrete_instances/07_bool_namecert_construction.tex` |
| `option` | `parts/concrete_instances/option/02_tagged_option_namecert.tex` |
| `prod` | `parts/concrete_instances/prod/09_componentwise_certificate_transfer.tex` |
| `sum` | `parts/concrete_instances/sum/ledger_and_semantic_certificate.tex` |
| `list` | `parts/concrete_instances/list/11_public_reverse_append_antimorphism.tex` |
| `int` | `parts/concrete_instances/int/06_int_history_certificate.tex` |
| `rat` | `parts/concrete_instances/12_rat_namecert_construction.tex` |
| `realalgorder` | `parts/concrete_instances/real/13_real_alg_order_interface.tex` |
| `complex` | `parts/concrete_instances/14_complex_namecert_construction.tex` |

ZH 对照在 `docs/dossier/data_source/glossary.json` 各 region key 下的 `constructive_story_zh` 字段。

## 7. 反模式 (避免)

- ❌ "$\NatUp$ is the natural numbers." —— 把 BEDC 名字当主词, 又没讲构造
- ❌ "We define $\NatUp$ as the unary spine generated by..." —— 这是定义陈述, 不是 story; 那种话已经在章节正文里了
- ❌ "See Definition 2.3, Lemma 4.1, and Theorem 5.7." —— 不要把 story 当目录用
- ❌ 写一整段重复 `\scopeclosed{}` 或 `\notclaimed{}` 已经说过的话 —— story 是回到构造起点, 不是复述边界
- ❌ ZH 写 "$\emp$ 加一个 b1 后变成 $\Eone(\emp)$" —— 在 dossier 里会显示成原始 LaTeX, 该写"空历史上叠一个 b1 标记"
- ❌ EN 写 "Empty plus a b1 mark gives Eone(emp)" —— PDF 里裸文本而非 LaTeX 不好看, 该用 `$\Eone(\emp)$`

## 8. 给 codex 的任务说明

每一轮 R-round 中 codex 的工作:

1. 找到一个 `\constructivestory{}` 为空的 closurestatus block。
2. 读这一章的:
   - `\chapter{...}` 标题以确定主题
   - intro 段 (`\section` 之前的段落) 以确定本章在做什么
   - `\theoryclosure{}` 与 `\formalstatus{}` 以确定闭合层级
   - `\scopeclosed{}` (本章闭合的范围) 与 `\notclaimed{}` (明确不在桌上的内容)
   - 本章引用的 `\autoref{ch:...}` 与 `\autoref{def:...}` 找出 prior 层
   - 章节里的几条核心 `\leanchecked{}` / `\leandef{}` target 名字以确定本章构造的具体对象
3. 按本规范第 3 节的 3-句骨架, 用第 6 节的示例为标尺, 写一段 3-4 句的 EN 内容填进 `\constructivestory{...}`。
4. 同步在 `docs/dossier/data_source/glossary.json` 对应 region key 下加 `constructive_story_zh` 字段 (如果该 key 不在 glossary 中, 跳过 ZH —— 不在本规范的强制范围内)。
5. 跑本地验证:
   - `python3 lean4/scripts/bedc_ci.py audit` 通过
   - `cd papers/bedc && make check` 通过
   - `python3 tools/build_dossier_status.py` 通过
6. 单 commit 提交; 一轮可以处理 1-3 章, 不要一次塞太多以免与并行 worker 冲突。

## 9. 优先填写顺序建议

按"递归底层 → 高一阶 → 应用层"的顺序填, 让早写的 story 给后写的提供 prior 引用基础:

1. 内核 / 一阶: `nat`, `add`, `bool`, `option`, `prod`, `sum`, `list`
2. 数论: `int`, `rat`, `real`, `complex`, `prime`
3. 代数基础: `monoid`, `group`, `abgroup`, `ring`, `commring`, `field`
4. 代数继续: `module`, `vecspace`, `linearmap`, `matrix`, `polynomial`
5. 序与拓扑: `preorder`, `poset`, `metric`, `compact`, `continuous`
6. 范畴: `category`, `functor`, `nattrans`
7. 分析: `complexlimit`, `complexdiff`, `holomorphic`, `complexseries`, `contour`
8. 高阶 / capstone: 其余

NatUp 已有示范 story (见 `parts/concrete_instances/04_nat_namecert_construction.tex`)。
