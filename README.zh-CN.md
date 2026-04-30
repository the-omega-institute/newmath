# newmath — BEDC Active Theory Repository

`newmath` 是 Binary Emission Discovery Calculus（BEDC）的 active theory 仓库, 同时维护 Lean 4 形式化与 LaTeX 论文主线。

本仓库默认 mathlib-free。形式化工作从 first principles 起步, 不以 Mathlib 作为证明底座。

## 仓库结构

- `papers/bedc/` — BEDC 的 LaTeX 论文
- `lean4/` — Lean 4 形式化
- `tools/` — 辅助脚本与审计工具（如存在）

## 构建

```bash
cd lean4 && lake build
cd papers/bedc && make
```

## 最新构建 PDF

每次合并到 `dev` 都会刷新 `dev-latest` 滚动 prerelease。该资源每次 push 都会被覆盖（不保留历史版本），下面的 URL 永远指向最新 `dev` 构建：

```
https://github.com/the-omega-institute/newmath/releases/download/dev-latest/bedc_dev-latest.pdf
```

带 `v*` tag 的正式 release 单独发布, 保持不可变.

## 当前状态

v0.1 是 BEDC v1.5.5 稿件的镜像迁移阶段。后续计划中的 v0.2 与 v0.3 将继续处理主题归一化与迁移后清理。

## 许可证

GPOL

## 参考

English version: [README.md](README.md)
