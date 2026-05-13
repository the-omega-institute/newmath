# Cook block 到 glider cluster 对照

## 概述

Cook 2004 的 Rule 110 普适性证明把循环标签系统作为中间层, 再把循环
标签系统的 tape 与 appendant list 编进 Rule 110 的周期 ether 初态。物理
层使用 12 种 block, 记作 `A` 到 `L`; 每个 block 是可沿 zig-zag seam 拼接
的 bit tile, 对应 Cook 2004 构造中的某个 glider cluster、间隔或初始 seam
锚点。

Cook 2009 的 concrete view 把这个装配过程显式写成可执行的 block 串规
则: central tape region 从 `C` 开始, right periodic region 由 appendant
list 转成 `H/I/J/K/L` 串, left periodic region 由 `A/B` ossifier 串给出。
本文档只记录 block 到 glider cluster 的语义映射和相邻间距约束; bit-level
mask 仍以 `rule110/ignores/concrete-view-rule110-arxiv-0906.3248.pdf`
中的 Figure 1-2 为准。

## 引用口径

本页的行号引用来自对本地 PDF 或 arXiv source 的文本抽取:

- Cook 2004: `rule110/ignores/cook-2004-universality.pdf`, 对应
  `pdftotext -layout` 文本行号。
- Cook 2009 concrete view: `rule110/ignores/concrete-view-rule110-arxiv-0906.3248.pdf`,
  对应 arXiv `0906.3248` source 中 `Cork.tex` 的 `nl -ba` 行号。

## glider 三类原色

- `A4`: Martinez `A` 的四连捆束, 即四个紧密 packed `A` glider。Cook
  2004 Figure 4 说明 `A^n` 记号表示紧密 packed 的 `n` 个 `A`
  glider, line 603-605; Figure 6 给出 `A4` 与 `Ebar` 的六种相撞相位,
  line 699-732; Cook 2004 line 1152 处把 ossifier 描述为四个 `A4`。
- `Ebar` (`Ē`): Martinez `Ē`, 是 moving data、leaders、invisibles 的基础。
  Cook 2004 line 1075-1079 说明 `Ebar` 与 `C2` 交叉适合表示 moving data
  穿过 tape data; line 1121-1129 说明 leader 由八个 E-family glider
  组成, 并产生 invisible `Ebar`。
- `C2` (`C₂`): Martinez `C₂`, 静止 tape data 的基础。Cook 2004 line 1075-1079
  将 `C2` 用作 tape data; line 1252-1253 给出 tape data `Y/N` 的四个
  `C2` 间距编码。

## 12-block 对照表

| Block | 角色 | 组分 | 周期 | 出处 |
| --- | --- | --- | --- | --- |
| `A` | left periodic region 中的 pure ether spacer | `0` 个 glider; 给相邻 `B` 中的 `A4` 提供 ether 间隔 | 3 lines | Cook 2009 `Cork.tex` line 549-552, 579-583, 708-713 |
| `B` | ossifier 的 `A4` carrier | `1` 个 `A4` = `4` 个 `A` glider | 3 lines | Cook 2009 line 551-552, 708-713; Cook 2004 line 1152 |
| `C` | central region 的初始 `t=0` seam anchor | 初始 `"V"` seam; 不作为重复 glider payload | `t=0` anchor, 非周期 tile | Cook 2009 line 555-556, 624-648 |
| `D` | moving data 相邻元素之间的 glue | seam glue block; 与两侧 `Ebar` seam 对齐 | 30 lines | Cook 2009 line 557-558, 715-718 |
| `E` | moving data `N` | `4` 个 `Ebar` 表示一个 moving-data 字符, central gap 取 `N` 类 | 30 lines | Cook 2009 line 561-562, 715-718; Cook 2004 line 1149-1156 |
| `F` | moving data `Y` | `4` 个 `Ebar` 表示一个 moving-data 字符, central gap 取 `Y` 类 | 30 lines | Cook 2009 line 565-566, 715-718; Cook 2004 line 1149-1156 |
| `G` | prepared leader | prepared leader E-family cluster; 与 Figure 12 的八个 E-family leader 对齐 | 30 lines | Cook 2009 line 569-570, 733-741; Cook 2004 line 1091-1123 |
| `H` | primary component | primary component cluster; 被 acceptor 接受时产出 `2` 个 moving-data `Ebar`, 被 rejector 删除 | 30 lines | Cook 2009 line 590-591, 720-731; Cook 2009 line 1699-1709 |
| `I` | standard component, narrow spacing | standard component cluster; `II` 编码一个 table-data `Y` | 30 lines | Cook 2009 line 594-595, 726-731 |
| `J` | standard component, wide spacing | standard component cluster; 与前一个 `I` 组成 `IJ` 编码一个 table-data `N` | 30 lines | Cook 2009 line 598-599, 726-731 |
| `K` | raw leader | raw leader E-family cluster; 经 acceptor/rejector preparation 后成为 prepared leader | 30 lines | Cook 2009 line 602-603, 733-741; Cook 2009 line 1996-2006 |
| `L` | raw short leader, 空 appendant | raw short leader cluster; 用于没有 component 的 empty appendant | 30 lines | Cook 2009 line 606-607, 733-741; Cook 2009 line 2000-2010 |

说明: Cook 2009 line 619-620 指出每个 zig-zag seam 中间都有一个向右的
`Ebar`, 因此相邻 block 总是在 `Ebar` seam 处拼接。表中的“组分”描述
cluster payload; seam `Ebar` 的归属按 Cook 2009 line 720-724 的规则处理:
右 seam `Ebar` 属于当前 cluster, 左 seam `Ebar` 是前一个 cluster 的最后
一个 `Ebar`。

## 装配规则

Cook 2009 Section 1.4 给出从循环标签系统到 Rule 110 初态的三段 block
串规则。

Central region 从 block `C` 的 `t=0` row 开始:

- tape symbol `Y` 映射为 `FD`;
- tape symbol `N` 映射为 `ED`;
- 最后一个 `D` 改成 `G`;
- 前面贴 `C`;
- 例: `NNYN` 映射为 `CEDEDFDEG`。

出处: Cook 2009 `Cork.tex` line 624-648。

Right periodic region 对每个 appendant 做局部替换:

- symbol `Y` 映射为 `II`;
- symbol `N` 映射为 `IJ`;
- 每个非空 appendant 的首个 `I` 改为 `KH`;
- 空 appendant 映射为 `L`;
- 全部 appendant 转完后, 第一个 appendant 的初始 `K` 移到整个周期串末尾;
- 例: `{YN, NYYN, empty, empty}` 映射为 `HIIJKHJIIIIIJLLK`。

出处: Cook 2009 `Cork.tex` line 650-665。

Left periodic region 是 ossifier 周期串:

```text
[A]^v B [A]^13 B [A]^11 B [A]^12 B
```

其中

```text
v = 76 * Ys + 80 * Ns + 60 * nonempty + 43 * empty
```

`Ys` 和 `Ns` 分别是所有 appendant 中 `Y` 与 `N` 的总数, `nonempty` 与
`empty` 分别是非空与空 appendant 数。left bit sequence 从 block `C`
的 `t=0` row 向左拼接, 先过 `B`, 再过 12 个 `A`, 以此类推; 该 block
序列走三遍后进入周期。

出处: Cook 2009 `Cork.tex` line 667-693。

## 间距约束

Cook 2004 Section 4.2-4.4 使用两种相对距离: 对 `A4`/`Ebar` 的 diagonal
`up` 距离按 `mod 6` 读, 对 `C2`/`Ebar` 的 vertical over 距离按 `mod 4`
读。下列 `⌢k` 记作对应相对距离为 `k`。

Tape data 的物理编码:

- Tape data `Y`: `C2 18 C2 18 C2 14 C2`;
- Tape data `N`: `C2 18 C2 10 C2 14 C2`;
- 这两个编码的差异是中间 `C2` gap: `Y` 为 18, `N` 为 10。

出处: Cook 2004 line 1252-1257; Cook 2009 `Cork.tex` line 56-58。

Middle crossing 约束:

- `Ebar` 到它穿过的第一个 `C2`: `⌢3`;
- 相邻 `C2` 到 `C2`: `⌢2`;
- 相邻 `C2` 的绝对最小间距: `C2 6 C2`;
- 多个 `C2` 与多个 `Ebar` 交叉时, `C2` 间距与 `Ebar` 间距保持不变。

出处: Cook 2004 line 805-831, 845-848, 1188-1210; Cook 2009 line 1341-1370。

Left ossification 约束:

- invisible `Ebar` -> invisible `Ebar`: `⌢1`;
- invisible `Ebar` -> moving-data `Ebar`: `⌢0`;
- moving-data `Ebar` -> moving-data `Ebar`: `⌢4`;
- moving-data `Ebar` -> invisible `Ebar`: `⌢5`;
- moving data `N` 相对 `Y` 的 central `Ebar` spacing 大 `8A`;
- 最后一个 moving-data `Ebar` 不能与后续 invisible 过近。

出处: Cook 2004 line 1266-1280; Cook 2009 line 1862-1888, 2133-2141。

Right component/leader 约束:

- primary component 的第一个 `Ebar` 在 leader 之后: `⌢2`;
- standard component 的第一个 `Ebar` 在 previous component 之后: `⌢2`;
- component 在 over-distance 方向上放在 previous component/leader 的 `⌢0`
  位置, 以保证 emitted `Ebar` 能以 `⌢3` 穿过 tape data;
- raw regular leader 放在 previous component 的 `⌢0` 位置;
- raw short leader 相对 raw regular leader 在 through-`E^n` 量法下高 `⌢+3`。

出处: Cook 2004 line 1317-1343; Cook 2009 `Cork.tex` line 1996-2010。

`A4` 与 `Ebar` 的 collision 相位:

- `A4` 与 `Ebar` collision 由 diagonal `up` distance 决定, 按 `mod 6`
  读;
- construction 使用 `Ebar` 在 `A4` 后 `⌢5` 的 short reaction 做
  ossification, 其产物 `C2` 与创建它的 `Ebar` 为 `⌢0`;
- `Ebar` 在 `A4` 后 `⌢0` 时穿过 `A4`;
- 连续 `A4` 若都要被同一个 invisible `Ebar` 穿过, 相邻 `A4` 为 `⌢5`。

出处: Cook 2004 line 699-732, 887-913, 989-1008; Cook 2009 line 1519-1554。
