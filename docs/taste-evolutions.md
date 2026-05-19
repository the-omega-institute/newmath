# Taste 演化日志

本文件记录 `tools/taste_curator.py` daemon 每次成功的规则演化 (rule evolution).

每个 section 是一次演化, 按时间从早到晚追加. 内容固定 4 段: 变更原因 / 意义 / 实施情况 / 元数据.

## 工作方式

Daemon 每 cycle 扫描 codex-auto-dev 最近 commit, 按品味/质量维度 (carrier 同构 bucket /
origin lineage / autoref entropy / boilerplate score) 检测违规, 累积到 cluster 后派 codex
修改 P/R 自动化管线的规则文件 (papers/bedc/scripts/prompts/*, lean4/scripts/prompts/*,
lean4/scripts/bedc_ci.py, phase gate scripts), 让未来 P/R round 不再产生同类 garbage.

已经存在的违规章节不直接编辑 — P/R orchestrator 后续自然 touch 这些文件时, post-merge
audit gate 拒绝 → codex_resolve_post_rebase_audit 调 codex 顺手修复. 自我消化.

---

(以下 section 由 daemon 在每次成功 rule evolution 后追加.)
