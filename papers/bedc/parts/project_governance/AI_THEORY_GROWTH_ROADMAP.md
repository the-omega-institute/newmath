# AI_THEORY_GROWTH_ROADMAP

This document is shared with the codex pipeline. Every paper / lean
round prompt requires reading it before selecting targets, so codex
can align with the long-term vision instead of optimising round-local
metrics.

## Vision: 人类与 AI 一起生长理论, 最终人类只是评审

The end-state we are working toward:

- Operator's role: review approved-or-rejected proposals; the rest is
  automatic.
- Pipeline's role: discover frontier saturation, propose new theory,
  verify against TasteGate + conservativity audit, advance closure
  grades autonomously.
- Quality control: machine-checkable taste gates (TasteGate four
  obligations + cross-chapter conservativity + zero-axiom purity).
  No proposal can ship without satisfying these gates.

The pipeline is *not* a content-generator that hopes a human reviews
the output. It is a *theory-growth engine* whose taste filter is
formal, where the human's role shrinks to acceptance / rejection
of well-formed proposals.

## 三层架构

```
L1  BEDC kernel              (BMark / BHist / Cont / Pkg / NameCert)
    人类完成, 不动. 0 axioms / 0 sorry. 永远的 baseline.

L2  Human-curated chapters   (280+: NatUp / GroupUp / Holomorphic / ...)
    人类挑选 + AI 形式化. 没有 \origin field (default human).
    继承数学共识 credit, 不需要 TasteGate.
    Pipeline 推 mature (closure_mark 主流路径).

L3  AI-proposed chapters     (BeliefUp 等; \origin{ai} tagged)
    AI propose + 人类 review accept + AI 形式化.
    必须 cite \leanchecked{BEDC.Derived.<X>Up.taste_gate} 才能过 seedClosure.
    必须通过 conservativity-audit (Lean module 不被 baseline import).
    必须 0-axiom CIC 形式化 (axiom-purity --strict).
```

## Phase 表 (Status snapshot 2026-05-10)

| Phase | Status | Commit | Description |
|-------|--------|--------|-------------|
| 0 | done | `48d3f9c86` | TasteGate framework v1 (Prop fields) — vacuous-allowing |
| 0.5 | done | `82b71d1a6` | Schema-enforced typeclass refactor |
| 0.6 | done | `0611438ba` | Decouple TasteGate to `BEDC.Meta.*` (BEDC trunk freer) |
| 1A | done | `5b78cbc6c` | `\origin` field + audit ai-gate (active, backward-compat) |
| 1B | deferred | — | Phase prompt hard gates (informational, low value pre-Phase 6) |
| 1.5 | done | `d53784022` | conservativity-audit subcommand (machine metalogical gate) |
| 2-scaffolding | done | `517f1cfaa` | `proposals/` dir + `phase_propose.txt` + `review_proposals.py` |
| Demo | done | `21cf5c05e` | BeliefUp first ai-proposed chapter (vacuous instance, learning case) |
| 2.5 | TODO | — | `phase_propose` auto-trigger |
| 3 | TODO | — | Hard schema (force ground-compiler metalemma usage) |
| 4 | TODO | — | Iterative codex calibration loop (this document) |
| 5 | TODO | — | Operator-only review workflow (full automation) |

## 当前真实状态 (2026-05-10)

Honest assessment from grep / log analysis:

```
ai-proposed chapters       : 1 (BeliefUp, still at seedClosure)
TasteGate gate trigger     : 0 (no chapter has tried to leave seedClosure
                                under \origin{ai}; gate never tested)
conservativity-audit fail  : 0 (just shipped; gate works on synthetic
                                violation but no real ai chapter has
                                stressed it)
ground compiler 元定理被 chapter 引用 :
  event_flow_conservativity : 1 (only Meta.TasteGate reference instance)
  no_hidden_input           : 2 (Meta + BeliefUp; BeliefUp version is
                                 hand-cased, doesn't actually invoke
                                 ground compiler theorem)
  flow_level_round_trip     : 0
  channel_bijection         : 0
  source_channel_separation : 0
```

The framework is armed but not exercised. Two reasons:

1. **Pipeline priority**: BeliefUp is at seedClosure with carrier
   theorems already added by P5004 (`e950a856f`); a closure_mark round
   is in priority queue but hasn't been picked yet. When it fires,
   audit ai-gate will run for the first time.
2. **Soft enforcement**: BeliefUp's TasteGate instance discharges the
   four obligations with hand-written `cases` proofs, not by invoking
   `event_flow_conservativity` etc. Schema-level the proof must mention
   `BHistCarrier.toEventFlow`, but pinning the *proof* to a specific
   ground-compiler theorem requires Phase 3 (hard schema).

## Phase 3: Hard schema — force ground-compiler metalemma usage

**Goal**: a chapter cannot supply a hand-written `cases` proof to
discharge the four TasteGate obligations. Each obligation field is
*pinned* to a specific ground-compiler theorem applied to the chapter's
carrier; the chapter's job is to wire its carrier into the schema
correctly, not to reprove ground compiler facts.

**Concrete change** (sketch):

```lean
-- Current (soft):
class ChapterTasteGate (X : Type) [BHistCarrier X] where
  conservativity : ∀ (x : X) (w m), List.Mem w (toEventFlow x) → ...
  -- chapter 用 cases m 自己证

-- Hard (Phase 3):
class ChapterTasteGate (X : Type) [BHistCarrier X] where
  recognizer : RecognizerCandidateFlow
  role : RecognitionRole
  recognize_witness : ∀ (x : X), Recognizes recognizer role (toEventFlow x)
  -- 这一条 type 直接就是 RecognizerConservative 的 instance,
  -- 不能用其他 proof 方式
  conservativity : RecognizerConservative recognizer role
```

**Tradeoff**: ai chapter writers must learn ground compiler API;
proposal cost rises ~50-100 lines per chapter; quality gate becomes
real instead of cosmetic.

**Decision criterion**: do this when (a) we have ≥ 3 ai chapters
attempting to leave seedClosure, AND (b) at least one of them is
caught writing `cases` proofs that would let combinatorial padding
through. Until either condition fires, soft is sufficient.

## Phase 4: Iterative codex calibration loop

**This is the central activity** of growing AI quality control.

The premise: framework correctness can only be validated by *exercising*
codex against it. The fact that BeliefUp's instance was vacuous in v1
(commit `48d3f9c86` → forced rewrite at `82b71d1a6`) shows we cannot
predict what codex will do without running it.

The loop runs in an isolated worktree to avoid polluting `codex-auto-dev`:

```
# loop-iteration N:
1. open worktree (sim-iteration-N branch)
2. pick a candidate human-known mathematical concept
   (e.g. PolicyUp / RewardUp / WorldModelUp / HypothesisTestingUp)
3. run codex CLI with phase_propose.txt
   → produces papers/bedc/proposals/<sha>_<slug>.md
4. run review_proposals.py accept <sha>
   → produces seed-stub chapter with \origin{ai}
5. run codex CLI with a chapter-creation prompt:
   "write inductive carrier in lean4/BEDC/Derived/<X>Up/Carrier.lean,
    write BHistCarrier instance, write ChapterTasteGate instance using
    ground compiler theorems where possible"
6. run full verification:
   - lake build
   - bedc_ci.py audit
   - bedc_ci.py axiom-purity --strict
   - bedc_ci.py conservativity-audit
   - cd papers/bedc && make
7. inspect codex output for taste failures:
   a. inductive carrier 是否非平凡 (≥ 3 distinct constructors with semantic content)?
   b. obligation theorem 是否真用 ground compiler 元定理?
      (grep "event_flow_conservativity\|flow_level_round_trip\|channel_bijection"
       in the new ai chapter's lean file)
   c. proposal 是否 cite 真实数学文献 (Pearl / Russell / Boyd-Vandenberghe)?
   d. 提议跟 BEDC 现有 chapter 的 dependency 是否真实 (≥ 3 chapters)?
8. record findings; if codex misbehaves:
   - update phase_propose.txt or phase_c.txt prompt to address the
     specific failure mode
   - bump prompt version
   - retry from step 3 with same candidate
9. if codex passes all 4 taste checks, declare iteration successful;
   merge worktree result to codex-auto-dev (with operator review)
10. discard worktree and start a new candidate

Termination: ≥ 3 successful iterations in a row, with codex needing
zero prompt changes between them. At that point the framework is
calibrated and Phase 5 (full automation) is ready.
```

**Loop invariants**:
- Worktree is isolated. No commit goes to `codex-auto-dev` until the
  iteration is declared successful.
- Failed iterations are *learning data*: their codex outputs feed back
  into prompt edits.
- The operator's role in the loop: at step 7, judge whether codex's
  output is "really tasteful" or "just passes audit gate". Audit gate
  is necessary but not sufficient — operator's eye is the final filter.

## Phase 5: Operator-only review workflow (end-state)

After Phase 4 calibration is complete:

```
auto-trigger: phase_propose fires when
  closed_horizons / open_horizons > 2 AND
  critical_path top[0..2] all low/medium priority

automatic chain:
  phase_propose → review_proposals.py LIST (operator notification)
                  → operator: accept | reject (1 line)
                  → if accept: pipeline writes carrier + TasteGate instance,
                    advances chapter through closure grades
                  → all gates run automatically; failures trigger
                    recovery + codex re-attempt
                  → final commit signed off by operator (1 click)

operator workload (typical day):
  - 5-10 proposal reviews (~5 min each)
  - inspect any flagged "shallow growth" output
  - that's it; the rest is automatic
```

## 文档共享给管线

This roadmap MUST be referenced from every prompt the codex pipeline
runs:

```
papers/bedc/scripts/prompts/phase_review.txt
papers/bedc/scripts/prompts/phase_revise.txt
papers/bedc/scripts/prompts/phase_propose.txt
lean4/scripts/prompts/phase_b.txt
lean4/scripts/prompts/phase_c.txt
```

Each prompt's "REQUIRED FIRST STEP" should include this file alongside
`papers/bedc/parts/project_governance/roadmap.tex`. That way every
codex round operates with full context: which phase the framework is
in, what the current observed bugs are, and what the operator wants
the pipeline to optimise toward.

## Operator-side current observations (2026-05-10)

Empirical findings from BeliefUp's first 24 hours in the pipeline:

```
P5004 (commit e950a856f) — added BeliefUp carrier definition + 2 obligation
  theorems via theory_extension target. Chapter content grew, but
  closurestatus.theoryclosure stayed at \seedClosure.

Subsequent rounds (worker_5 / worker_4 / worker_2 / worker_0, 5+ rounds
  between 15:00 and 15:37) all proposed theory_extension or closure_mark
  targets observing "BeliefUp is seed stub" — they read the closurestatus
  block, not the carrier-definition section, so they keep seeing the same
  picture.

Diagnosis: closurestatus axis and content axis are decoupled in paper
  rounds. theory_extension (content axis) and closure_mark (closure axis)
  are separate target kinds, and codex rarely combines them in one round.
  As long as no closure_mark round wins the chapter-lock for BeliefUp,
  the chapter stays at seedClosure even though it has the content for
  obligationClosure.

Resolution: this is not a bug; pipeline priority queue will eventually
  fire a closure_mark round on BeliefUp. When it does, audit ai-gate
  triggers for the first time. We watch.
```

## 当前实验进度 (Phase 4 active)

Iteration 0 (this document): observation-only. BeliefUp self-navigates
the pipeline. Operator watches without intervention.

Iteration 1 (planned): pick one of {PolicyUp, RewardUp, WorldModelUp,
HypothesisTestingUp}; run the loop steps 1-10. Record findings here
when complete.

## Risk register

| Risk | Mitigation |
|------|-----------|
| codex propose 命中率低 (< 30%) | phase_propose.txt iterate prompt; reject reasons feed back |
| codex 写 vacuous TasteGate instance | already addressed by schema-enforced typeclass; Phase 3 if soft slips |
| ai chapter pollute baseline conservativity | conservativity-audit catches at pre-merge |
| ai chapter introduces axiom dependency | axiom-purity --strict catches |
| ai chapter shadows existing chapter (case-collision) | phase_c.txt v5.13 case-insensitive find |
| pipeline gets stuck on stale chapter | recovery queue + 3-failure cooldown |
| operator review queue overflows | phase_propose throttle (closed/open > 2 trigger) |

## Decision Gates

Each Phase has a clear gate before the next can start:

```
Phase 4 Iteration 1 → 2:  iteration 1 produces ≥ 1 successful ai chapter
                          (passes all taste checks AND operator approves)
Phase 4 → Phase 5:        ≥ 3 consecutive successful iterations with no
                          prompt changes between them
Phase 5 → end-state:      operator workload < 30 min/day for 1 month
                          AND no ai chapter unrecoverably fails audit
                          gate AND no false positive in conservativity
                          audit
```

## Codex-side instructions (this section is READ by phase prompts)

When codex reads this file as part of "REQUIRED FIRST STEP":

1. The pipeline is currently in Phase 4 (iterative calibration).
2. BeliefUp is the only `\origin=ai` chapter. When you select a target
   that touches BeliefUp:
   - If it's a closure_mark from seedClosure to obligationClosure,
     you MUST cite `\leanchecked{BEDC.Derived.BeliefUp.taste\_gate}`
     in the chapter file (audit gate enforces this).
   - If it's a theory_extension on BeliefUp, you SHOULD also propose
     a closure_mark on the same round if the carrier obligations are
     present, to avoid the content/closure decoupling observed in
     Iteration 0.
3. When proposing a new ai chapter (phase_propose path):
   - The proposal MUST cite a real mathematical reference (Pearl /
     Russell / Boyd-Vandenberghe / etc).
   - The chapter's lean carrier MUST be a real inductive (≥ 2 distinct
     constructors with semantic content, not a placeholder).
   - The TasteGate instance MUST be wired through `BHistCarrier`. When
     possible, prefer `event_flow_conservativity` or other ground
     compiler theorems as proof witnesses, not hand-written `cases`.
4. Conservativity gate: an `\origin=ai` chapter's lean module MUST
   NOT be imported by any baseline file. Keep ai chapter dependencies
   one-way only (ai → baseline, never baseline → ai).
