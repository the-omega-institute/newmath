# PR #269 review-gate r1 fix report

## applied

- CLI 注册/可达性测试: 在 `lean4/scripts/test_closurestatus_audit.py` 中覆盖 `bedc_ci.parser().parse_args(["discovery-audit", "--json"])`, 断言 `args.func is cmd_discovery_audit` 且 `--json` 生效。
- candidate-scope gate 测试: 覆盖 human-origin、`seedClosure`、缺 `theory_closure`、parser-errored 四类合成 block, 断言 `_discovery_candidate_blocks` 返回空, 且 `discovery_audit_payload` 的候选数和三类 gap 输出均为 0/空列表。
- `kind_unknown` 分支测试: 覆盖非空 `\closureledger` 但无识别 kind 关键字的 block, 断言 `ledger_gaps` 中输出一条 `kind_unknown` 并保留 evidence。

## rejected-as-false-positive

- quality reviewer 建议拆分 `discovery_audit_payload()` 三段 loop。该建议为 advisory comment, 非 blocking；本轮 scope 是补 reject 证据要求的有效测试覆盖。拆生产 helper 会扩大实现 scope, 且 host 规则要求不为文件内注释、叙事说明或非阻断质量建议扩 scope, 所以本轮不改 `lean4/scripts/bedc_ci.py`。
- quality reviewer 自己也指出 in-source Refactor Old/New comments 与本仓库 AGENTS/CLAUDE 规则冲突；本轮未添加文件内注释或 docstring 叙事。

## blocked

- 无。

## verify

- `python3 -m unittest lean4/scripts/test_closurestatus_audit.py` exit 0.
- `python3 lean4/scripts/bedc_ci.py discovery-audit --json` exit 0.
- `python3 lean4/scripts/bedc_ci.py --help` exit 0, help 中包含 `discovery-audit`.
- `python3 lean4/scripts/bedc_ci.py audit` exit 0.

## changed files

- `lean4/scripts/test_closurestatus_audit.py`
- `FIX_REPORT.md`
