# Rule 110 dossier figures

这些 SVG 由零依赖 C 工具 `rule110/tools/visualize_rule110.c` 生成，并随
dossier 源文件保存，方便 Quarto 部署环境直接渲染。

## 图像

- `ether_evolution.svg`：14-cell ether pattern `11111000100110` 重复到
  140 cells，并演化 70 个 Rule 110 step。
- `glider_zoo.svg`：A、B、C1、Ebar、F、G 六种 phase-0 glider 放在 ether
  背景上，每个 panel 演化三个 fundamental period。
- `collision_example.svg`：Martinez 2012 audit 覆盖的
  `A(f1_1) -4e- Ebar(A,f1_1) -> {Ebar, A}` collision，使用 audit 中同一
  phase spacing。
- `cook_packet_structure.svg`：用 `cook_encode_phase_exact` 编码
  two-production、two-tape-bit Cook packet，标出 initial row 的三个结构区，
  并演化 2048 steps。
- `scale_frontier.svg`：`scale_2p_16t_16384` frontier case，经 majority
  downsample 后显示 16384-step space-time diagram。

## 生成命令

从仓库根目录运行：

```bash
cd rule110
make visualizations
```

该 target 会把全部图像写入 `docs/dossier/figures/rule110/`。
