# BEDC

BEDC (`Binary Emission Discovery Calculus`) 是 `newmath` 仓库中的论文镜像目录。当前 `papers/bedc/` 保持 Phase 1 的近乎逐字迁移：`main.tex`、`parts/`、`frontmatter/` 与 `appendices/` 基本沿用来源稿，只做 `xelatex` 兼容修补和少量路径调整。

## 构建

在本目录运行：

```sh
make
```

生成物为 `main.pdf`。本阶段不再使用来源项目里的 `build.sh`。

## 字体要求

- macOS：默认使用 `PingFang SC` 作为中文字体，通常系统已自带。
- Linux：建议安装 `fonts-noto-cjk`，并将 `preamble.tex` 中的 CJK 字体名调整为本机可用的 `Noto Sans CJK SC` 或等价名称后再构建。
- 西文字体固定为 `Latin Modern Roman`、`Latin Modern Sans`、`Latin Modern Mono`。

## 与 Lean 的关系

附录 [`appendices/lean_scaffold.tex`](./appendices/lean_scaffold.tex) 现在通过 `\lstinputlisting` 直接展示仓库中的 `../../lean4/BEDC/BaseReflection.lean`。这样论文中的实现脚手架说明会跟随 Lane A 产出的 Lean 4 文件，而不再引用 `.source/lean/` 下的旧快照。
