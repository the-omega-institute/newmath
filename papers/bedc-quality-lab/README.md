# BEDC Model Quality Lab

本目录是 BEDC Model Quality Lab 的最小实验环境。实验闭环使用 Gaussian-OU toy world、一个 tiny encoder、线性可辨识指标和证据 envelope，生成可审阅的质量报告。

Python 侧只拥有 lab-local 的 `QualityEvidenceEnvelope` 证据边界。`bedc_refs` 只保存不透明指针，例如章节路径、label 或 Lean 目标名；这里不复制 BEDC rule 正文，也不定义 NameCert、closurestatus、origin 或 ledger 的 BEDC 语义。

## 运行

```bash
make check
python3 scripts/run_canonical_reports.py --help
```

`make run-example` 会调用 `scripts/run_gaussian_ou_lejepa.py`，写出：

- `reports/example_envelope.json`
- `reports/quality_report.md`

`make check` 是本目录的一键验证入口：先运行 lab-local pytest，再通过
`scripts/run_canonical_reports.py` 生成 `reports/canonical/` 下的 canonical 报告和
`reports/canonical/index.json`。

## 依赖

测试主体只需要 `numpy` 和 `pytest`。`torch` 是可选依赖；如果当前环境没有安装，smoke experiment 测试会跳过，其他测试仍应通过。

## 证据边界

Envelope 记录一次实验的来源、模式、分类器、稳定性设置、指标、ledger gaps、debt items、artifact 指针和 BEDC 指针。报告只投影 envelope 中已有值，不重新计算实验指标。
