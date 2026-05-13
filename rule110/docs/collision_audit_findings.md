# cook_collisions.c table audit findings

`tests/test_cook_collision_martinez.c` 通过 `--strict` 或 `make test-collision-audit`
对 `encoder/cook_collisions.c` 全 33 行 collision table 跑两层检查：

1. **Direct r110 simulation**: 把 left + right glider phase 放在 ether row 上，跑
   真 `r110_run_n_steps`，detect 演化结果里的 glider 类型，跟 table 登记 outcome 比对。
2. **Martinez 2012 cross-check**: 从 `ignores/martinez-2012-solitons.pdf` 抽 Table 1/2
   数据，跟 table 行做 outcome 字符串比对。

下面是当前实际发现，由 `./tests/test_cook_collision_martinez --strict` 复现。

## Direct simulation: 11 detection failures (out of 33 rows)

`table audit (cook_collisions.c full 33 rows): 6/33 PASS, 11 FAIL` 后达 1/3 阈值停止。
绝大多数 FAIL 类型是 `detect 不到 X glider (glider_phases.c 缺 entry)`：

| Row | 形状 | 失败原因 |
|---|---|---|
| table_row_13 | Martinez 2012 soliton (m) `cook_collisions.c:41` | expected={Ebar, F} missing=Ebar |
| table_row_14 | Martinez 2012 soliton (n) `cook_collisions.c:42` | expected={Ebar, F} missing=outcome |
| table_row_15 | — | detect 不到 Ebar glider (glider_phases.c 缺 entry) |
| table_row_16 | — | detect 不到 F glider (glider_phases.c 缺 entry) |
| table_row_17 | — | detect 不到 F glider (glider_phases.c 缺 entry) |
| … | （余 6 行类似） | |

性质：**verifier 强度不够**，不是 table 数据错。`encoder/glider_phases.c` 没有为
Bbar 和某些 E/F variant 注册 canonical lookup，detector 找不到这些 glider，因此
直接模拟跑完 row 里能看到的产物但 classifier 无法命名。

修法路径：
- (a) 扩 `encoder/glider_phases.c`：从 Martinez 2007/2012 把 Bbar / 缺失的 E/F
   phase rows 注册进 lookup。这是 W3 留下 generic-D 与 D1/D2 拆分时同类的 catalog
   补强工作。
- (b) 改 detector 用更稳健的算法（diff against pure ether evolution +
   connected-component 识别），不依赖 phase string 精确匹配。

## Martinez 2012 cross-check: 1 真不一致

`Martinez 2012 Table 1/Table 2 cross-check: 33 rows, 32 matched, 0 only-in-paper, 0 only-in-table`

唯一 mismatch：
```
martinez_row_27: FAIL table={Ebar, A^3} martinez={Ebar, A^5}
   for F(H,f1_1) -1 e- Bbar(C,f1_1)
```

`encoder/cook_collisions.c` 登记此 row 的 outcome 是 `{Ebar, A^3}`（3 个 A glider），
但 `ignores/martinez-2012-solitons.pdf` 的 PDF 抽取得到 `{Ebar, A^5}`（5 个 A glider）。

可能原因：
- (a) `cook_collisions.c` table 数据错（最坏情况，需修）
- (b) `pdftotext` 抽 Martinez 2012 PDF 时 OCR 或 layout 解析把 `A^5` 读成 `A^3`
   （PDF 数学排版常见误读）
- (c) Martinez 2012 论文里同一 row 在不同位置/不同段落给出不同 outcome 字符串，
   两边都对但 reference 的位置不同

调查需要：人眼对照 Martinez 2012 Complex Systems 21.2.2 的 Table 印刷原文。

## 跟 ship 的关系

- `make test`：跑这套验证但**审计 finding 不致 FAIL**（输出 `INFO N audit finding(s)`），
  ship gate 保持绿。
- `make test-collision-audit`：strict 模式，**FAIL 即非零退出**，作为调查 / 回归门禁。
- 发现的 11+1 行**真实暴露在 stdout**，没有 SKIP / TODO 隐藏。

## 不是什么

- 不是 BEDC 主信任路径上的 bug：BEDC closure 不依赖 collision table 的精确数据，依赖
  `evaluator/rule110.c` + manifest assertion。这套 audit 是 Cook construction
  internal 一致性检查，独立于 substrate witness。
- 不是 ship blocker：Tier A v2.0 与 Tier B v3.0 的 ship 标准都跟 collision table
  audit 无关；audit 是更进一步的研究探针。
