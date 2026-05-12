# BEDC Closure-vs-Verification Two-Axis Refactor — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the BEDC manuscript's one-dimensional `seed < paperCert < checkedCert < bridgeCert` strength chain with a two-axis "Theoretical Closure × Formal Verification" discipline, propagate the change to every paper site, every audit / pipeline gate, and every codex prompt, and ship one atomic commit on branch `closure-vs-verification`.

**Architecture:**
- **Theoretical closure axis** (paper-internal): `seed → obligation → scopedClosed → publicClosed → bridgedClosed → maturePackageClosed`. A grade is a paper-side mathematical / certificate state; it is not strengthened by Lean checking.
- **Formal verification axis** (Lean-side audit): `unformalized → formalTarget → encodedDef → scaffoldChecked → theoremChecked → auditClean → axiomClean → bridgeChecked`. A grade is a verification-and-audit state; it does not by itself close any object's theory.
- The two axes meet only via a `VerifiedGate(N, c, v) := TheoryGate(N, c) ∧ FormalStatus(N, v)` predicate. Machine verification is an external audit layer over a closure claim, never its formation rule.
- A single per-chapter `\begin{closurestatus}{<NameMacro>} … \end{closurestatus}` block records both axes plus scope, Lean target, bridge state, claims off the table, and upgrade path. The block is greppable, audit-parseable, and replaces the existing one-line `\closureat`.

**Tech Stack:** LaTeX (`pdflatex` + `xparse`/`xstring`), Python 3 stdlib (audit + orchestration), Bash. mathlib-free Lean 4 (no Lean changes in this refactor — only paper, audit, and codex prompts).

---

## Background context (engineer briefing)

### What's broken today

`papers/bedc/parts/acceptance/01_derivation_acceptance_gate.tex` defines

```
Strength = { seed, paperCert, checkedCert, bridgeCert },  seed < paperCert < checkedCert < bridgeCert
AcceptGate(N, s) := NameCert(N) ∧ DerivCert(N, s)
```

and `\closureat{<X>Up}{\<strength>Str}[<grounding>]` (preamble.tex:353) writes the assertion `Theory closed: AcceptGate(NameCert_X)(<strength>)` into the PDF.

Two problems:

1. The chain is one-dimensional, so the obvious reading is "without `checkedCertStr` you are not theory-closed". Machine verification gets implicitly promoted to a formation rule for theoretical closure. That's wrong: a paper-level certificate can be theoretically closed without any Lean target; a Lean checked scaffold does not by itself close the corresponding object theory.
2. Every `\closureat` site in `parts/concrete_instances/` (30+ files) currently writes `\checkedCertStr` regardless of whether the chapter actually exhibits the full traditional object. `Field↑`, `VecSpace↑`, `Determinant↑`, `Homology↑`, `Cohomology↑` are scoped/singleton certificates only; the existing marker overstates what is closed.

### Where the change has to land

- **Preamble** (`papers/bedc/preamble.tex`): macros for the two axes + the new `closurestatus` env.
- **Chapter 146** = the three files under `papers/bedc/parts/acceptance/` — derivation_acceptance_gate.tex, standard_bridge_protocol.tex, cannot_claim_registry.tex.
- **Per-chapter closure declarations** — every `\closureat{...}{\checkedCertStr}[...]` site (30 files; full list below).
- **Roadmap** (`papers/bedc/parts/project_governance/roadmap.tex` §31, §"Per-object research template", §"Near-term phases", §"Claims explicitly off the table").
- **Frontmatter preface** (`papers/bedc/frontmatter/preface.tex`).
- **Appendix B** = `papers/bedc/appendices/build_and_verification_log.tex`.
- **Capstones** referencing `\checkedCertStr` (`papers/bedc/parts/visions/riemann_hypothesis.tex`).
- **Audit script** `lean4/scripts/bedc_ci.py` — `CLOSUREAT_RE`, `collect_closureat_groundings`, `audit_payload`, the JSON shape, and the human-readable summary.
- **Critical-path script** `lean4/scripts/critical_path.py` — `CLOSED_STRENGTHS`, `is_chapter_closed`, the rolling cooldown's grounding extractor.
- **Codex paper-revise prompts** `papers/bedc/scripts/prompts/{phase_review,phase_revise,conflict_resolve,post_rebase_audit_resolve,round_fallback_resolve}.txt`.
- **Codex Lean-formalize prompts** `lean4/scripts/prompts/{phase_c,post_rebase_audit_resolve,round_fallback_resolve}.txt` — only the closure-marker / strength references.
- **CLAUDE.md** — "状态宏 (preamble.tex)" section + § "marker 使用纪律".

### Inventory of `\closureat` sites (30 files, all currently `\checkedCertStr`)

```
parts/concrete_instances/04_nat_namecert_construction.tex:336
parts/concrete_instances/05_add_namecert_construction.tex:288
parts/concrete_instances/07_bool_namecert_construction.tex:735
parts/concrete_instances/09_prod_ledger_and_semantic_certificate.tex:502
parts/concrete_instances/12_rat_namecert_construction.tex:589
parts/concrete_instances/14_complex_namecert_construction.tex:680
parts/concrete_instances/15_monoid_namecert_construction.tex:538
parts/concrete_instances/17_abgroup_namecert_construction.tex:739
parts/concrete_instances/22_vecspace_namecert_construction.tex:504
parts/concrete_instances/32_metric_empty_boundary_visible_context_distance_empty.tex:243
parts/concrete_instances/36_category_namecert_construction.tex:350
parts/concrete_instances/58_subgroup_namecert_construction.tex:526
parts/concrete_instances/62_determinant_namecert_construction.tex:256
parts/concrete_instances/76_homology_namecert_construction.tex:642
parts/concrete_instances/77_cohomology_namecert_construction.tex:480
parts/concrete_instances/87_yoneda_namecert_construction.tex:251
parts/concrete_instances/commring/19_commring_zero_divisor_and_inclusion.tex:559
parts/concrete_instances/field/20_field_phase_exit_record_certificate_boundary.tex:266
parts/concrete_instances/functor/pipeline_composite_extras.tex:532
parts/concrete_instances/group/16_group_center_abelian_normal_package.tex:49
parts/concrete_instances/int/06_int_history_certificate.tex:5
parts/concrete_instances/linearmap/the_certificate.tex:49
parts/concrete_instances/list/11_public_reverse_append_antimorphism.tex:231
parts/concrete_instances/module/21_module_namecert_construction_core.tex:792
parts/concrete_instances/nattrans/vertical_and_opposite_extras.tex:798
parts/concrete_instances/option/02_tagged_option_namecert.tex:710
parts/concrete_instances/prime/the_certificate.tex:219
parts/concrete_instances/quotientgroup/concrete_namecert_certificate.tex:761
parts/concrete_instances/real/unary_context/03_transported_iterated_tail_pairwise_coherence.tex:87
parts/concrete_instances/sum/ledger_and_semantic_certificate.tex:701
```

Verify before each chapter touch by running `grep -n "closureat" <file>`; the line numbers may have shifted since this plan was written.

### Branch + commit discipline

We are on branch `closure-vs-verification` (already created off `codex-auto-dev`). Per CLAUDE.md:

- Single atomic commit per logical milestone (NOT per step). The plan groups steps into 7 milestones; each milestone is its own commit only after `lake build`, `make`, `check-axioms.py`, and `bedc_ci.py audit` all exit 0.
- `git pull --rebase` is forbidden; use `git fetch origin codex-auto-dev && git merge origin/codex-auto-dev` if a sync is needed.
- Do NOT push during the work. Pushing the merged refactor onto `codex-auto-dev` is the user's call after all green.

### Style conventions (CLAUDE.md non-negotiables)

- No iteration narrative ("新增", "修订", "v1.5.X", "patch", "frozen", "supersede", "deprecated", "increment", etc.). Delete the old text and write the new — never annotate the change.
- One `.tex` ≤ 800 lines. If a refactored `\closureat` site grows the file past 780 lines, extract the new `closurestatus` block into a sibling `closure_status.tex` under the same theme directory, leave the parent as `\input` only.
- No file-internal comments / changelogs / removed-stub markers.
- No backwards-compatibility shims. Delete `\closureat`, `\Strength`, `\paperCertStr`, `\checkedCertStr`, `\bridgeCertStr`, `\AcceptGate`, `\seedStr`. Replace, do not annotate.
- Math envs: only `$…$` and `$$…$$`.
- Underscores in Lean target names inside macros: `\_`, never bare `_`.

---

## File structure (what changes vs. what's new)

**Modified:**

- `papers/bedc/preamble.tex` (lines 23-56 leanmarkers untouched; lines 325-365 entirely rewritten).
- `papers/bedc/parts/acceptance/01_derivation_acceptance_gate.tex` (full rewrite).
- `papers/bedc/parts/acceptance/02_standard_bridge_protocol.tex` (split bridge into "paper bridge closed" vs. "bridgeChecked" axes; rewrite §I, §III, §V, §VI).
- `papers/bedc/parts/acceptance/03_cannot_claim_registry.tex` (rewrite Anchor 2/4; expand to 15 anti-confusions list; add Closure Reading Convention + verification status table).
- `papers/bedc/frontmatter/preface.tex` (one paragraph added after Layer discipline).
- `papers/bedc/appendices/build_and_verification_log.tex` (full rewrite into B.1/B.2/B.3 with explicit "audit only, not closure" framing).
- `papers/bedc/parts/project_governance/roadmap.tex` (§"Strength gradient" → §"Closure and verification axes"; "Per-object research template" Status field becomes a 2-tuple; Phase exit criteria become 3-line blocks; "Claims explicitly off the table" extended).
- `papers/bedc/parts/visions/riemann_hypothesis.tex` (one `\checkedCertStr` reference replaced).
- All 30 `\closureat`-bearing chapter files in `parts/concrete_instances/` (one block replaced; new closurestatus env inserted).
- `lean4/scripts/bedc_ci.py` (CLOSUREAT_RE retired; new `CLOSURESTATUS_BEGIN_RE` parser; new audit fields; failure messages updated).
- `lean4/scripts/critical_path.py` (`CLOSED_STRENGTHS` retired; new `is_chapter_retired_from_horizon` reading both axes).
- `papers/bedc/scripts/phase_paper_gates.py` (new `axis-confusion` gate).
- `papers/bedc/scripts/prompts/phase_review.txt`, `phase_revise.txt` (Step 9 / closure_mark target rewritten; "four-strength gradient" reading replaced with "two-axis discipline").
- `papers/bedc/scripts/prompts/{conflict_resolve,post_rebase_audit_resolve,round_fallback_resolve}.txt` (closureat references replaced).
- `lean4/scripts/prompts/{phase_c,post_rebase_audit_resolve,round_fallback_resolve}.txt` (same).
- `CLAUDE.md` "状态宏" section + project-rule § "marker 使用纪律".

**New:**

- `papers/bedc/parts/acceptance/04_closure_reading_convention.tex` (the conventions section + per-object table).
- `lean4/scripts/test_closurestatus_audit.py` (Python unit tests for the new audit parser).

**Deleted:**

- None. Every old macro / definition is rewritten in place; no orphan files.

---

## Milestones (commit boundaries)

1. **Milestone P1 — Preamble + acceptance/§I rewrite.** New macros land; Chapter 146 §I describes the two axes; build green; no other chapter mentions the old strength tokens yet → introduce a temporary preamble alias to keep `pdflatex` green during transit. (Note: this is the only place we tolerate a transient compatibility shim; it gets deleted in P3.)
2. **Milestone P2 — Bridge + cannot-claim chapters rewritten** + `04_closure_reading_convention.tex` added. Chapter 146 reads end-to-end against the new vocabulary.
3. **Milestone P3 — Per-chapter `\closurestatus` blocks** for all 30 concrete-instance chapters. Capstones, preface, appendix, roadmap also flipped. Delete the temporary preamble alias from P1.
4. **Milestone P4 — Audit + critical-path scripts** updated. Old regexes retired; new ones parse the env. New `axis-confusion` gate added to `phase_paper_gates.py`. Python unit tests added.
5. **Milestone P5 — Codex prompts** rewritten. Both paper and Lean prompt families teach the two-axis vocabulary.
6. **Milestone P6 — CLAUDE.md** synced.
7. **Milestone P7 — Full local verification** (5 commands all exit 0) and one squash-merge-ready commit summary.

Each milestone ends with the four-gate check:
```bash
cd lean4 && lake build
cd papers/bedc && make
python3 tools/check-axioms.py
python3 lean4/scripts/bedc_ci.py audit
```
plus on P4+, the Python unit tests:
```bash
python3 -m unittest lean4.scripts.test_closurestatus_audit -v
```

---

## Task 1 — Preamble macro redesign

**Files:**
- Modify: `papers/bedc/preamble.tex:325-365` (the AcceptGate / Strength / closureat block; everything from line 325 to 365 is rewritten).

**Goal:** Provide the two-axis primitives that every later chapter and audit consumes.

- [ ] **Step 1: Decide design and verify present preamble shape**

Run:
```bash
grep -n "AcceptGate\|paperCert\|checkedCert\|bridgeCert\|seedStr\|closureat\|StdBridge\|FailureCert" papers/bedc/preamble.tex
```

Expected: ~25 hits between lines 325-365, plus references in 357 (StdBridge), 365 (FailureCert).

- [ ] **Step 2: Replace lines 325-365 with the new macro stack**

Open `papers/bedc/preamble.tex` and delete lines 325 through 365 (the block beginning `% Acceptance discipline macros` through `\newcommand{\FailureCert}{\mathsf{FailureCert}}`). Insert in their place exactly:

```latex
% Closure-and-verification discipline macros
% (\autoref{ch:closure-and-verification-discipline})

% --- Theoretical closure axis (paper-internal) ---------------------------
\newcommand{\TheoryClosure}{\mathsf{TheoryClosure}}
\newcommand{\TheoryGate}{\mathsf{TheoryGate}}
\newcommand{\seedClosure}{\mathsf{seed}}
\newcommand{\obligationClosure}{\mathsf{obligation}}
\newcommand{\scopedClosure}{\mathsf{scopedClosed}}
\newcommand{\publicClosure}{\mathsf{publicClosed}}
\newcommand{\bridgedClosure}{\mathsf{bridgedClosed}}
\newcommand{\matureClosure}{\mathsf{maturePackageClosed}}

% --- Formal verification axis (Lean-side audit) --------------------------
\newcommand{\FormalStatus}{\mathsf{FormalStatus}}
\newcommand{\VerifiedGate}{\mathsf{VerifiedGate}}
\newcommand{\unformalizedV}{\mathsf{unformalized}}
\newcommand{\formalTargetV}{\mathsf{formalTarget}}
\newcommand{\encodedDefV}{\mathsf{encodedDef}}
\newcommand{\scaffoldCheckedV}{\mathsf{scaffoldChecked}}
\newcommand{\theoremCheckedV}{\mathsf{theoremChecked}}
\newcommand{\auditCleanV}{\mathsf{auditClean}}
\newcommand{\axiomCleanV}{\mathsf{axiomClean}}
\newcommand{\bridgeCheckedV}{\mathsf{bridgeChecked}}

% --- Standard-bridge structural macros (paper bridge, separate from
% the bridgeCheckedV verification token above) ---------------------------
\newcommand{\StdBridge}{\mathsf{StandardBridge}}
\newcommand{\encodeN}{\mathsf{encode}}
\newcommand{\decodeN}{\mathsf{decode}}
\newcommand{\decodeEncode}{\mathsf{decodeEncode}}
\newcommand{\encodeDecode}{\mathsf{encodeDecode}}
\newcommand{\theoremPreservation}{\mathsf{theoremPreservation}}
\newcommand{\noHostLeak}{\mathsf{noHostLeak}}
\newcommand{\FailureCert}{\mathsf{FailureCert}}

% --- Per-chapter closurestatus block ------------------------------------
% Every `<X>Up` chapter ends with one block of the shape:
%
%   \begin{closurestatus}{\<X>Up}
%     \theoryclosure{\scopedClosure}
%     \scopeclosed{The displayed empty-history singleton certificate.}
%     \formalstatus{\theoremCheckedV}
%     \leantarget{BEDC.Derived.<X>Up.<theorem>}
%     \bridgestatus{none}
%     \notclaimed{General <X> theory: ...}
%     \upgradepath{Public-object certificate + ...}
%   \end{closurestatus}
%
% Underscores inside \leantarget MUST be \_-escaped (renderer collapses
% \_ to a thin space; bare _ trips out-of-math-mode errors).
%
% The block is parsed by `lean4/scripts/bedc_ci.py audit` (CLOSURESTATUS
% regexes) and consumed by `lean4/scripts/critical_path.py` to decide
% whether a chapter is retired from the horizon work queue. Both axes
% are mandatory; lacking either field causes audit to fail.
\NewDocumentEnvironment{closurestatus}{m}{%
  \par\smallskip\noindent%
  \fbox{%
    \begin{minipage}{0.94\linewidth}%
      \footnotesize\sffamily\color{purple!55!black}%
      \textbf{Closure status for $\NameCert_{#1}$.}\par
      \def\theoryclosure##1{\par\textbf{Theory closure:} $\TheoryGate(\NameCert_{#1},\,##1)$\par}%
      \def\scopeclosed##1{\textbf{Scope closed:} ##1\par}%
      \def\formalstatus##1{\textbf{Formal verification:} $\FormalStatus(\NameCert_{#1},\,##1)$\par}%
      \def\leantarget##1{\textbf{Lean target:} \texttt{\StrSubstitute{##1}{\_}{ }}\par}%
      \def\bridgestatus##1{\textbf{Bridge status:} ##1\par}%
      \def\notclaimed##1{\textbf{Not claimed:} ##1\par}%
      \def\upgradepath##1{\textbf{Upgrade path:} ##1\par}%
}{%
    \end{minipage}%
  }\par\smallskip
}
```

- [ ] **Step 3: Confirm `pdflatex` still compiles the (currently un-touched) body of the paper**

Run:
```bash
cd papers/bedc && make 2>&1 | tail -40
```

Expected at this point: build FAILS because every concrete-instance chapter still references `\closureat`, `\checkedCertStr`, `\AcceptGate`, etc. To unblock P1's commit boundary we need a transient compatibility shim — see Step 4.

- [ ] **Step 4: Add a transient compatibility shim near the bottom of preamble.tex**

Append to `papers/bedc/preamble.tex` (immediately above the `\end{document}`-finding scope, e.g. after line 365):

```latex
% --- TEMPORARY SHIM: removed in milestone P3 ----------------------------
% Restore the legacy single-axis vocabulary so existing chapters compile
% while individual sites are migrated. Each shim re-emits a closurestatus
% block in degraded form (theory_closure = scopedClosed, formal status =
% theoremCheckedV, no scope/notclaimed/upgrade fields). The audit script
% recognizes these as legacy-shim emissions and refuses to count them as
% complete; this forces every site to be hand-migrated before the shim
% is deleted at the end of P3.
\newcommand{\AcceptGate}{\mathsf{LegacyAcceptGate}}
\newcommand{\Strength}{\mathsf{LegacyStrength}}
\newcommand{\seedStr}{\mathsf{LegacyStrength.seed}}
\newcommand{\paperCertStr}{\mathsf{LegacyStrength.paperCert}}
\newcommand{\checkedCertStr}{\mathsf{LegacyStrength.checkedCert}}
\newcommand{\bridgeCertStr}{\mathsf{LegacyStrength.bridgeCert}}
\NewDocumentCommand{\closureat}{m m o}{%
  \begin{closurestatus}{#1}
    \theoryclosure{\scopedClosure}
    \formalstatus{\theoremCheckedV}
    \IfValueT{#3}{\leantarget{#3}}%
  \end{closurestatus}%
  \par\noindent{\footnotesize\color{red!50!black}\textsf{[legacy-shim — replace with full closurestatus block]}}\par
}
% --- end TEMPORARY SHIM -------------------------------------------------
```

- [ ] **Step 5: Compile and confirm green**

```bash
cd papers/bedc && make 2>&1 | tail -10
```

Expected: `pdflatex` runs twice and produces `main.pdf` with red `[legacy-shim — replace with full closurestatus block]` lines printed beneath every existing chapter closure. No undefined control sequences. The shim emission is deliberately ugly so reviewers cannot miss un-migrated sites.

- [ ] **Step 6: Defer commit to milestone P1 boundary** (after Tasks 2 + 3 also done).

---

## Task 2 — Rewrite Chapter 146 §I (`01_derivation_acceptance_gate.tex`)

**Files:**
- Modify: `papers/bedc/parts/acceptance/01_derivation_acceptance_gate.tex` (full rewrite).

**Goal:** Replace the one-dimensional Strength chain with the two-axis discipline.

- [ ] **Step 1: Replace the file's entire contents with the new chapter**

Overwrite `papers/bedc/parts/acceptance/01_derivation_acceptance_gate.tex` with:

```latex
\chapter{Closure and Verification Discipline}
\label{ch:closure-and-verification-discipline}
\label{ch:acceptance-gate} % retained: many earlier chapters \autoref this label

This chapter records the discipline by which a mature mathematical object's claim is read. The discipline is two-axis. The \emph{theoretical closure axis} records what the paper has proved about the object's $\NameCert$, scope, exactness, ledger, stability, and bridge; it is read entirely from the manuscript, with no input from any proof assistant. The \emph{formal verification axis} records the independent audit state of the corresponding Lean targets; it strengthens reliability and reproducibility but assigns no theoretical content. A claim and its audit are separate artefacts that compose only via $\VerifiedGate$.

Read against \autoref{rem:three-axioms-gate-meaning}, this chapter is the positive face of the project's discipline: positive content admitted only if its closure is exhibited by paper-side witnesses, while machine verification is reported as an external audit layer that never substitutes for closure.

\section{Theoretical closure axis}
\label{sec:closure-axis}

\begin{definition}[Theoretical closure grades]
\label{def:theory-closure-grades}
The \emph{theoretical closure axis} is the six-element set
\[
  \TheoryClosure \;=\; \{\, \seedClosure,\ \obligationClosure,\ \scopedClosure,\ \publicClosure,\ \bridgedClosure,\ \matureClosure \,\}
\]
ordered by $\seedClosure < \obligationClosure < \scopedClosure < \publicClosure < \bridgedClosure < \matureClosure$.
\end{definition}

\begin{definition}[Closure grade interpretations]
\label{def:theory-closure-interpretations}
The grades are read as follows.
\begin{description}
  \item[\textbf{$\seedClosure$:}] a naming seed has been declared; carrier and classifier are sketched; no exactness theorem has been settled.
  \item[\textbf{$\obligationClosure$:}] every proof obligation needed to close $\NameCert(N)$ has been written down precisely; the scope of the eventual closure is fixed; the central proofs are not yet completed.
  \item[\textbf{$\scopedClosure$:}] within an explicit scope, every $\NameCert$ field (carrier, classifier, exactness, ledger, stability) is supplied with paper-level proof. The scope is recorded in the chapter's \texttt{closurestatus} block and is the manuscript's binding commitment about what has actually been reconstructed.
  \item[\textbf{$\publicClosure$:}] in addition to $\scopedClosure$, the chapter exhibits the public-object surface of the standard reading: public constructors, readback, endpoint exactness, normal form, and a no-hidden-leakage statement.
  \item[\textbf{$\bridgedClosure$:}] in addition to $\publicClosure$, the chapter exhibits a paper-level standard bridge per \autoref{ch:acceptance-bridge}, including a paper-level no-host-leak argument.
  \item[\textbf{$\matureClosure$:}] in addition to $\bridgedClosure$, the chapter records the mature-package theorem inventory whose conclusions a host reader expects (e.g.\ Peano induction for $\NatUp$, ordered-field laws for $\RatUp$, etc.).
\end{description}
\end{definition}

\begin{definition}[Theory gate]
\label{def:theory-gate}
For an object $N$ and grade $c \in \TheoryClosure$, the \emph{theory gate at grade $c$} is
\[
  \TheoryGate(N, c) \;:=\; \NameCert(N) \,\wedge\, \ClosureCert(N, c).
\]
A claim that BEDC closes $N$ at grade $c$ is admissible only when $\TheoryGate(N, c)$ holds.
\end{definition}

\begin{definition}[Closure certificate fields]
\label{def:closure-cert-fields}
The closure certificate $\ClosureCert(N, c)$ packages: a \emph{source field} naming the BEDC layer that carries $N$ ($\Mark$, $\Hist$, $\Bundle$, $\Pkg$, or $\NameCert$); a \emph{classifier field} witnessing the equivalence relation; an \emph{exactness field} citing the classifier-respecting transport; a \emph{ledger field}; a \emph{stability field}; an explicit \emph{scope field} naming exactly what is closed; and the chosen grade $c$. At grades $\publicClosure$ and above, the certificate additionally cites a public-object surface; at $\bridgedClosure$ and above, the certificate cites the chapter's $\StdBridge$.
\end{definition}

\section{Formal verification axis}
\label{sec:verification-axis}

\begin{definition}[Formal verification grades]
\label{def:formal-status-grades}
The \emph{formal verification axis} is the eight-element set
\[
  \FormalStatus \;=\; \{\, \unformalizedV,\ \formalTargetV,\ \encodedDefV,\ \scaffoldCheckedV,\ \theoremCheckedV,\ \auditCleanV,\ \axiomCleanV,\ \bridgeCheckedV \,\}
\]
ordered by inclusion of audit guarantees.
\end{definition}

\begin{definition}[Verification grade interpretations]
\label{def:formal-status-interpretations}
\begin{description}
  \item[\textbf{$\unformalizedV$:}] no Lean target.
  \item[\textbf{$\formalTargetV$:}] a Lean theorem-shape target exists (statement only); proof is empty / sorry / scaffold.
  \item[\textbf{$\encodedDefV$:}] the relevant carriers/classifiers are encoded as Lean \texttt{def}s or \texttt{inductive}s.
  \item[\textbf{$\scaffoldCheckedV$:}] a scaffold theorem in the sense of \autoref{ch:proof-obligations-lean-scaffold-contract} type-checks.
  \item[\textbf{$\theoremCheckedV$:}] the canonical Lean theorem corresponding to the closure certificate's distinguished proof has been checked by \texttt{lake build}.
  \item[\textbf{$\auditCleanV$:}] in addition, every \texttt{\textbackslash leanchecked} / \texttt{\textbackslash leanvariant} / \texttt{\textbackslash leanstmt} / \texttt{\textbackslash leandef} marker on the certificate's targets resolves to a real declaration ( \texttt{lean4/scripts/bedc\_ci.py audit} clean).
  \item[\textbf{$\axiomCleanV$:}] in addition, the transitive axiom audit reports no \texttt{Classical.choice}, \texttt{Quot.sound}, or \texttt{propext} dependency for the cited targets ( \texttt{tools/check-axioms.py} and \texttt{bedc\_ci.py axiom-purity --strict} clean).
  \item[\textbf{$\bridgeCheckedV$:}] when the certificate is at $\bridgedClosure$, the standard-bridge no-host-leak field has been machine-checked against the chosen host language.
\end{description}
\end{definition}

\begin{principle}[Verification is not a closure formation rule]
\label{prin:verification-not-formation}
Machine verification is an audit layer over a stated theoretical closure claim. It strengthens reliability and reproducibility; it does not assign any closure grade by itself. A theory may be closed without being machine-checked, and a checked target does not by itself close any object.
\end{principle}

\section{The verified gate}
\label{sec:verified-gate}

\begin{definition}[Verified gate]
\label{def:verified-gate}
For an object $N$, a closure grade $c \in \TheoryClosure$, and a verification grade $v \in \FormalStatus$, the \emph{verified gate} is
\[
  \VerifiedGate(N, c, v) \;:=\; \TheoryGate(N, c) \,\wedge\, \FormalStatus(N, v).
\]
A claim that BEDC \emph{exports} $N$ is admissible only when $\TheoryGate(N, c)$ holds for some $c$. The export's \emph{verification} is reported separately by $\FormalStatus(N, v)$.
\end{definition}

\begin{theorem}[Theory gate is monotone in $c$]
\label{thm:theory-gate-monotone}
For grades $c, c' \in \TheoryClosure$ with $c' \le c$, $\TheoryGate(N, c) \to \TheoryGate(N, c')$.
\end{theorem}
\begin{proof}[Sketch]
The $\NameCert$ conjunct is independent of the grade. Each higher-grade $\ClosureCert(N, c)$ exhibits the lower-grade certificate as substructure (\autoref{def:theory-closure-interpretations}); deleting the additional fields yields $\ClosureCert(N, c')$.
\end{proof}

\begin{theorem}[Formal status is monotone in $v$]
\label{thm:formal-status-monotone}
For grades $v, v' \in \FormalStatus$ with $v' \le v$, $\FormalStatus(N, v) \to \FormalStatus(N, v')$.
\end{theorem}
\begin{proof}[Sketch]
Each higher verification grade extends the audit guarantees of the lower one (\autoref{def:formal-status-interpretations}); the audit witnesses for the higher grade contain those of the lower grade.
\end{proof}

\begin{theorem}[Theory and verification axes are independent]
\label{thm:axes-independent}
Neither axis determines the other. A pair $(c, v) \in \TheoryClosure \times \FormalStatus$ is admissible whenever $\TheoryGate(N, c)$ and $\FormalStatus(N, v)$ both hold; no $c$ implies any $v$, and no $v$ implies any $c$ beyond $\seedClosure$.
\end{theorem}
\begin{proof}[Sketch]
$c$ depends only on paper-side witnesses; $v$ depends only on Lean-side audit. The $\NameCert(N)$ predicate inside $\TheoryGate$ is met by the manuscript's textual certificate, never by a Lean target alone; conversely, a checked Lean target whose paper site exhibits no scope, no exactness, and no ledger only witnesses $\seedClosure$ on the theory axis. Consequently the two axes are independent up to the trivial bound that any $v \ge \unformalizedV$ requires $c \ge \seedClosure$ for the marker discipline of \autoref{ch:closure-and-verification-discipline} to bind.
\end{proof}

\section{Marker-to-verification correspondence}
\label{sec:marker-to-verification}

\begin{definition}[Marker assignment]
\label{def:marker-to-verification}
The Lean status macros map to the formal verification axis only. None assigns or strengthens a closure grade.
\begin{enumerate}
  \item $\verb|\leandef|$ on $X$: $\FormalStatus(\,\cdot\,, \encodedDefV)$.
  \item $\verb|\leanstmt|$ on $X$: $\FormalStatus(\,\cdot\,, \formalTargetV)$.
  \item $\verb|\leansorryd|$ on $X$ with rationale $r$: $\FormalStatus(\,\cdot\,, \formalTargetV)$ regardless of paper coverage; the rationale is recorded for later upgrade.
  \item $\verb|\leanchecked|$ on $X$ at the canonical proof site, with no $\verb|\leansorryd|$ siblings on the same claim: $\FormalStatus(\,\cdot\,, \theoremCheckedV)$.
  \item $\verb|\leanvariant|$ on $X$: does not change the verification grade of the canonical site; it labels a wrapper or projection at the grade of its primary.
  \item A passed \texttt{lean4/scripts/bedc\_ci.py audit} run lifts $\theoremCheckedV$ to $\auditCleanV$ on the cited targets.
  \item A passed \texttt{lean4/scripts/bedc\_ci.py axiom-purity --strict} run lifts $\auditCleanV$ to $\axiomCleanV$.
  \item A machine-checked no-host-leak field on $\StdBridge(N, T)$ lifts the bridge claim to $\bridgeCheckedV$.
\end{enumerate}
\end{definition}

\begin{remark}[The marker map is not a closure rule]
\label{rem:marker-map-not-closure}
\autoref{def:marker-to-verification} assigns only a verification grade. The closure grade is supplied by the chapter's \texttt{closurestatus} block (\autoref{sec:per-chapter-closurestatus} below); the audit script never reads the closure grade and the closure registry never reads the marker family.
\end{remark}

\begin{lemma}[The audit script reflects verification, not closure]
\label{lem:audit-reflects-verification}
The script \texttt{lean4/scripts/bedc\_ci.py audit} verifies that every Lean marker resolves to a real declaration. The script reports \emph{verification grade}; closure grade is read out of the chapter's \texttt{closurestatus} block by \texttt{critical\_path.py} and by reviewers, never out of the audit JSON.
\end{lemma}

\section{Per-chapter closurestatus block}
\label{sec:per-chapter-closurestatus}

Every chapter that asserts an object's closure ends with one block of the form

\begin{verbatim}
\begin{closurestatus}{\<X>Up}
  \theoryclosure{\scopedClosure}
  \scopeclosed{<text describing exactly what the chapter closes>}
  \formalstatus{\theoremCheckedV}
  \leantarget{BEDC.<...>.<theorem>}
  \bridgestatus{none | paperBridge | bridgeChecked | bridgePending}
  \notclaimed{<text listing what the chapter does NOT close>}
  \upgradepath{<text naming the next closure grade and what it requires>}
\end{closurestatus}
\end{verbatim}

The block is the manuscript's binding commitment about $N$. \texttt{lean4/scripts/bedc\_ci.py audit} parses every block and refuses unresolved \texttt{\textbackslash leantarget} targets; \texttt{lean4/scripts/critical\_path.py} reads $\theoryclosure$ and $\formalstatus$ to decide whether the chapter is retired from the work queue.

\begin{remark}[Both axes are mandatory]
\label{rem:closurestatus-both-axes}
A \texttt{closurestatus} block lacking either $\theoryclosure$ or $\formalstatus$ is rejected at audit time. A block with $\formalstatus = \theoremCheckedV$ but no $\leantarget$ is similarly rejected. The intent is to make the two axes inseparable in the artefact even though they are independent in content.
\end{remark}

\section{Upgrade obligations}
\label{sec:closure-upgrade-obligations}

\begin{definition}[Closure upgrade $\seedClosure \to \obligationClosure$]
\label{def:upgrade-seed-to-obligation}
A seed-grade object upgrades to $\obligationClosure$ when the paper exhibits, in writing, the precise list of proof obligations whose discharge would close $\NameCert(N)$ at the next grade and the explicit scope at which the closure will be claimed.
\end{definition}

\begin{definition}[Closure upgrade $\obligationClosure \to \scopedClosure$]
\label{def:upgrade-obligation-to-scoped}
An $\obligationClosure$ object upgrades to $\scopedClosure$ when paper-level proofs are exhibited within the recorded scope for source membership; classifier transitivity and reflexivity; exactness against $\msame / \hsame / \psame$; absence or explicit form of a gap-policy ledger; and stability of the constructed certificate.
\end{definition}

\begin{definition}[Closure upgrade $\scopedClosure \to \publicClosure$]
\label{def:upgrade-scoped-to-public}
A $\scopedClosure$ certificate upgrades to $\publicClosure$ when the chapter exhibits the public-object surface: public constructors compatible with the BEDC carrier, a readback function, endpoint exactness, a normal-form theorem, and a no-hidden-leakage statement bracketing the public surface.
\end{definition}

\begin{definition}[Closure upgrade $\publicClosure \to \bridgedClosure$]
\label{def:upgrade-public-to-bridged}
A $\publicClosure$ certificate upgrades to $\bridgedClosure$ when the chapter exhibits a paper-level standard bridge per \autoref{ch:acceptance-bridge}, with each of its six fields supplied and the no-host-leak field argued at paper level. Machine verification of the no-host-leak field is the separate $\bridgeCheckedV$ obligation on the verification axis.
\end{definition}

\begin{definition}[Closure upgrade $\bridgedClosure \to \matureClosure$]
\label{def:upgrade-bridged-to-mature}
A $\bridgedClosure$ certificate upgrades to $\matureClosure$ when the chapter records the full mature-package theorem inventory characterising the object in the standard reference (e.g.\ Peano arithmetic, ordered-field axioms, vector-space theory, full determinant theory) and supplies certificates that those theorems hold in the BEDC reading.
\end{definition}

\begin{definition}[Verification upgrades]
\label{def:verification-upgrades}
The verification axis admits its own upgrades, each entirely independent of the closure axis:
\begin{itemize}
  \item $\unformalizedV \to \formalTargetV$: a Lean theorem statement is added.
  \item $\formalTargetV \to \encodedDefV$: the carriers and classifiers are encoded as Lean \texttt{def}s.
  \item $\encodedDefV \to \scaffoldCheckedV$: a scaffold theorem type-checks.
  \item $\scaffoldCheckedV \to \theoremCheckedV$: the canonical theorem is proved against the scaffold.
  \item $\theoremCheckedV \to \auditCleanV$: \texttt{bedc\_ci.py audit} reports zero unresolved markers for the cited targets.
  \item $\auditCleanV \to \axiomCleanV$: the transitive axiom audit is clean.
  \item to $\bridgeCheckedV$: the standard bridge's no-host-leak field is machine-checked.
\end{itemize}
\end{definition}

\section{Reuse, composition, and retroactive promotion}
\label{sec:closure-reuse}

\begin{theorem}[Theory closure reuse]
\label{thm:theory-closure-reuse}
If $N_1, \dotsc, N_k$ have $\TheoryGate(N_i, c_i)$ and $M$ is constructed from the $N_i$ via $\ReuseCert$ instances, then $M$ admits a theory gate at grade $\min_i c_i$ conditional on $M$'s own certificate fields being supplied.
\end{theorem}

\begin{theorem}[Verification status reuse]
\label{thm:verification-status-reuse}
If $N_1, \dotsc, N_k$ have $\FormalStatus(N_i, v_i)$ and $M$'s Lean target is constructed from theirs, then $M$'s verification grade is $\min_i v_i$ on the cited carriers, conditional on $M$'s own canonical theorem being checked.
\end{theorem}

\begin{remark}[No retroactive promotion]
\label{rem:no-retroactive-promotion}
A construction admitted at $(c, v)$ does not become a construction at $(c', v')$ with $c' > c$ or $v' > v$ merely because the inputs are later upgraded. Promoting either axis requires re-discharging the corresponding upgrade obligation on the construction itself.
\end{remark}

\section{The discipline as research-plan language}
\label{sec:closure-as-language}

\begin{remark}[What the discipline is for]
\label{rem:closure-discipline-purpose}
This chapter is not a new theorem; it is a vocabulary for stating the present closure and verification status of every claim in the manuscript. Its role is to replace the implicit reading---that an object ``exists'' in BEDC if it appears anywhere---with the explicit reading that an object \emph{is closed at grade $c$} only when $\TheoryGate(N, c)$ holds, and \emph{is verified at grade $v$} only when $\FormalStatus(N, v)$ holds. The chapters that follow use this vocabulary to state the bridge protocol (\autoref{ch:acceptance-bridge}), the cannot-claim registry (\autoref{ch:acceptance-cannot-claim}), and the closure reading convention (\autoref{ch:closure-reading-convention}).
\end{remark}

\begin{remark}[The discipline is not a kernel proof obligation]
\label{rem:closure-discipline-not-kernel-obligation}
The proof obligations of \autoref{ch:proof-obligations-domain-policy} and its siblings are obligations on the kernel: they constrain what theorems must hold for the kernel to be coherent. The closure-and-verification discipline is an obligation on the manuscript: it constrains what claims may be made about objects exported from the kernel, and how those claims relate to their independent audit. The two disciplines compose: a kernel theorem that fails its proof obligation cannot support any object's $\scopedClosure$ or above, while a closurestatus block that misreports either axis is refused at audit time even if every kernel theorem stands.
\end{remark}
```

- [ ] **Step 2: Compile**

```bash
cd papers/bedc && make 2>&1 | tail -10
```

Expected: green; the chapter renders with the new sections; old `\autoref{ch:acceptance-gate}` references in other files still resolve because the file retains that label as the second `\label`.

- [ ] **Step 3: Defer commit to milestone P1 boundary.**

---

## Task 3 — Milestone P1 commit

- [ ] **Step 1: Confirm gate green**

```bash
cd lean4 && lake build && cd .. && \
cd papers/bedc && make && cd ../.. && \
python3 tools/check-axioms.py && \
python3 lean4/scripts/bedc_ci.py audit
```

Expected: all four exit 0. The `bedc_ci.py audit` will show every existing `\closureat` site as a "legacy-shim" emission marked with the red banner; that is intentional for P1.

- [ ] **Step 2: Stage exactly the two changed files and commit**

```bash
git add papers/bedc/preamble.tex papers/bedc/parts/acceptance/01_derivation_acceptance_gate.tex
git commit -m "$(cat <<'EOF'
P1 closure-vs-verification: introduce two-axis discipline

Split the BEDC export discipline into a theoretical closure axis
(seed/obligation/scopedClosed/publicClosed/bridgedClosed/maturePackageClosed)
and a formal verification axis (unformalized/.../bridgeChecked).

Chapter 146 becomes "Closure and Verification Discipline":
- TheoryGate(N, c) read entirely from paper witnesses.
- FormalStatus(N, v) read from Lean audit only.
- VerifiedGate(N, c, v) := TheoryGate(N, c) /\ FormalStatus(N, v).

Per-chapter closurestatus environment lands; concrete-instance chapters
still emit the single-axis legacy shim and will be migrated in P3.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4 — Rewrite §02 (`02_standard_bridge_protocol.tex`)

**Files:**
- Modify: `papers/bedc/parts/acceptance/02_standard_bridge_protocol.tex` (rewrite §I, §II, §III, §V; preserve §VI prerequisites table but switch to two-axis vocabulary).

**Goal:** Distinguish "paper bridge closed" (theory axis: `bridgedClosure`) from "bridge machine-checked" (verification axis: `bridgeCheckedV`).

- [ ] **Step 1: Read the current file in full so the edits land on real anchors**

```bash
sed -n '1,142p' papers/bedc/parts/acceptance/02_standard_bridge_protocol.tex
```

- [ ] **Step 2: Rewrite the opening paragraph (lines 1-4)**

Replace the chapter intro (everything from the `\chapter` line to the start of `\section{The six fields...}`) with:

```latex
\chapter{Standard Bridge Protocol}
\label{ch:acceptance-bridge}

The closure-and-verification discipline of \autoref{ch:closure-and-verification-discipline} ends, on the closure axis, at $\publicClosure$ unless a standard bridge to a host mathematical formalism is exhibited at the paper level. This chapter records the shape such a bridge must take, the discipline that prevents it from leaking host-language structure into the BEDC kernel, and the quotient and closure obligations several downstream objects ($\IntUp$, $\RatUp$, real-valued completions, set-like and type-like reflections) must discharge before they can present themselves at $\bridgedClosure$. The bridge is a conservative extension, not a fusion: it lets a host reader recognise the BEDC object, and it lets BEDC accept host theorems via a typed translation, without admitting host primitives as BEDC inputs.

The bridge is a paper-level construction: exhibiting all six fields advances the closure axis from $\publicClosure$ to $\bridgedClosure$. Machine verification of the bridge's no-host-leak field is the independent $\bridgeCheckedV$ point on the verification axis; a paper bridge can stand at $\bridgedClosure$ before its no-host-leak field is machine-checked, and a machine-checked no-host-leak field cannot retroactively close a chapter that does not exhibit the bridge in writing.
```

- [ ] **Step 3: Update §III "no-host-leak as object-level axiom-purity" (lines 39-61)**

Replace `\paperCertStr` and `\checkedCertStr` references with the new vocabulary. Specifically, the sentence in `Theorem 4` (line 56-58) reading "no theorem ... at strength $\paperCertStr$ or above" becomes:

```latex
no theorem about $N$'s BEDC export becomes provable through the bridge that was not already provable in BEDC at $\TheoryGate(N, c)$ for some $c \ge \scopedClosure$.
```

The remark "Theorem-preservation does not extend BEDC" similarly drops `\paperCertStr` for `\TheoryGate(N, c)` with $c \ge \scopedClosure$.

- [ ] **Step 4: Update §IV "Quotient and closure discipline" (lines 63-92)**

Line 78's "the certificate is admitted at most at strength $\paperCertStr$ on the base layer" becomes:

```latex
the certificate is admitted at most at $\TheoryGate(N, \scopedClosure)$ on the base layer; closure-grade exactness above $\scopedClosure$ is not exported.
```

Line 91's "the bridge is presented at $\paperCertStr$" becomes:

```latex
the bridge is presented at $\TheoryGate(N, \scopedClosure)$ on the base relation, with closure-grade upgrade above $\scopedClosure$ deferred.
```

- [ ] **Step 5: Update §V "Conservativity" (lines 95-108)**

Line 102's `$\paperCertStr$ or above` becomes `at $\TheoryGate(N, c)$ for $c \ge \scopedClosure$`.

- [ ] **Step 6: Update §VI "Worked sketch: integers" (lines 111-122)**

Line 115's "already at $\paperCertStr$" becomes "already at $\TheoryGate(\IntUp, \scopedClosure)$".

Line 120's "all six fields machine-checked" becomes:
```latex
its admission as a $\bridgedClosure$ export of $\IntUp$ requires the closure-level reflection obligation discharged at the paper level; subsequent machine verification of the bridge fields lifts the verification axis to $\bridgeCheckedV$ but is independent of the $\bridgedClosure$ closure grade.
```

- [ ] **Step 7: Update §VII "Bridge prerequisites" (lines 124-142)**

Line 128's "the acceptance gate at $\checkedCertStr$" becomes:
```latex
the closure gate at $\TheoryGate(N, \publicClosure)$, the closure-level reflection obligation of \autoref{def:acceptance-closure-reflection-obligation}, the six fields of \autoref{def:acceptance-standard-bridge}, and (on the independent verification axis) the no-host-leak field at $\bridgeCheckedV$ if the bridge's host translation is to be machine-audited.
```

Line 136's "The current manuscript admits none of these as $\bridgeCertStr$ exports" becomes:
```latex
The current manuscript admits none of these at $\bridgedClosure$; the prerequisites are recorded here to make the upgrade obligation on the closure axis explicit, separate from any verification-axis upgrade to $\bridgeCheckedV$.
```

- [ ] **Step 8: Compile**

```bash
cd papers/bedc && make 2>&1 | tail -10
```

Expected: green.

---

## Task 5 — Rewrite §03 (`03_cannot_claim_registry.tex`)

**Files:**
- Modify: `papers/bedc/parts/acceptance/03_cannot_claim_registry.tex` (rewrite Anchors 2 & 4; expand Failure cert; add the 15-confusion list).

**Goal:** Bring Anchor 2/4 onto the two-axis vocabulary; add an explicit anti-confusion list per the user spec §14.

- [ ] **Step 1: Replace the failure-certificate definition (lines 22-37)**

Add three branches and renumber. Replace the entire `\begin{definition}[Failure certificate]` … `\end{definition}` block with:

```latex
\begin{definition}[Failure certificate]
\label{def:acceptance-failure-cert}
The \emph{failure certificate} $\FailureCert(N, c, v)$ at the candidate closure grade $c$ and verification grade $v$ for an object $N$ is one of the thirteen typed branches:
\begin{enumerate}
  \item \texttt{missing-source}: no source-layer assignment in the sense of \autoref{def:closure-cert-fields};
  \item \texttt{missing-classifier}: no classifier supplied for the cited source;
  \item \texttt{classifier-not-transitive}: classifier supplied but transitivity fails or is unproved;
  \item \texttt{exactness-fails}: classifier does not respect $\msame / \hsame / \psame$ on the cited source;
  \item \texttt{operation-does-not-descend}: a kernel operation fails to descend through the classifier;
  \item \texttt{gap-ledger-absent}: the ledger field is unspecified and no explicit absence statement is supplied;
  \item \texttt{completion-not-stable}: a completion construction fails the stability field;
  \item \texttt{scope-overstated}: the closure block claims a grade whose scope exceeds what the chapter actually closes (e.g.\ $\publicClosure$ asserted for a singleton certificate);
  \item \texttt{standard-bridge-fails}: $\StdBridge(N,T)$ is incomplete in at least one of its six fields when $\bridgedClosure$ is claimed;
  \item \texttt{host-primitive-leakage}: the no-host-leak field is violated, that is, host $\mathsf{Nat}$, $\mathsf{Quot}$, $\mathsf{propext}$, or $\mathsf{Classical.choice}$ appears in the BEDC public surface for $N$;
  \item \texttt{theorem-checker-failure}: a Lean target cited under $\verb|\leanchecked|$ is missing or fails to build (refutes $\theoremCheckedV$);
  \item \texttt{audit-not-clean}: \texttt{lean4/scripts/bedc\_ci.py audit} reports unresolved markers on the cited targets (refutes $\auditCleanV$);
  \item \texttt{axis-confusion}: the chapter's prose, table, or marker discipline assigns a closure grade as a function of a verification grade (or vice versa), in violation of \autoref{prin:verification-not-formation}.
\end{enumerate}
A claim that $\TheoryGate(N, c)$ holds is refuted by exhibiting any one of branches 1--10. A claim that $\FormalStatus(N, v)$ holds is refuted by branches 11--12. A claim that the discipline of \autoref{ch:closure-and-verification-discipline} is honoured is refuted by branch 13.
\end{definition}
```

- [ ] **Step 2: Update theorem 4 (lines 40-46)**

Replace `\AcceptGate(N, s)` with `\TheoryGate(N, c)` and update the proof.

- [ ] **Step 3: Rewrite Anchor 2 and Anchor 4 (lines 75 and 77)**

Anchor 2 becomes:

```latex
  \item \textbf{Anchor 2.} $\mathrm{ClaimText}$: ``$\NatUp$ is the full Peano natural numbers.'' $\mathrm{Status}$: \texttt{partial}. $\mathrm{WhyNotClaimable}$: $\NatUp$ records unary repetition histories with $\TheoryGate(\NatUp, \scopedClosure)$ on the canonical NameCert scope; full Peano content (induction principle as a closed theorem schema, primitive recursion with computation rules, totality of arithmetic operations) requires the upgrade $\TheoryGate(\NatUp, \matureClosure)$. $\mathrm{RequiredUpgrade}$: $\NatUp$'s arithmetic test suite (induction, recursion, addition associativity and commutativity, multiplication distributivity, order totality) closed at $\matureClosure$ on the closure axis. The verification axis grade does not by itself close any further Peano content.
```

Anchor 4 becomes:

```latex
  \item \textbf{Anchor 4.} $\mathrm{ClaimText}$: ``The Lean scaffold is verified end-to-end.'' $\mathrm{Status}$: \texttt{forbidden}. $\mathrm{WhyNotClaimable}$: the scaffold of \autoref{ch:proof-obligations-lean-scaffold-contract} is a statement-level surface; verification means each scaffold target stands at $\theoremCheckedV$ in \texttt{lean4/BEDC/} with a successful build report and at $\auditCleanV$ on \texttt{bedc\_ci.py audit}. $\mathrm{RequiredUpgrade}$: a complete checker report from \texttt{lake build} together with the audit of \texttt{lean4/scripts/bedc\_ci.py} and the axiom-purity gate, all exiting clean. This upgrade strengthens the verification axis only; it does not by itself close any object's theory.
```

- [ ] **Step 4: Add §IV "Closure reading convention" right before §III "Failure witness as audit input"**

Insert (between the Anchor list and the audit-policy section) a new section:

```latex
\section{Closure reading convention}
\label{sec:closure-reading-convention}

\begin{remark}[Reading a closure claim]
\label{rem:closure-reading-convention}
A theoretical closure claim and a formal verification claim are distinct. A line of the form $\TheoryGate(N, \scopedClosure)$ means that the paper supplies the source, classifier, exactness, ledger, and stability witnesses needed to close $N$ within the stated scope. A line of the form $\FormalStatus(N, \theoremCheckedV)$ means that the cited Lean target has been machine-checked. The second claim audits the first; it does not create the first. A theory may be closed without being machine-checked. Conversely, a checked scaffold or checked definition does not by itself close the corresponding mathematical object.
\end{remark}
```

- [ ] **Step 5: Add §V "Anti-confusion register" listing the user spec's 15 forbidden readings**

After the convention section, append:

```latex
\section{Anti-confusion register}
\label{sec:anti-confusion-register}

\begin{remark}[Confusions explicitly refused]
\label{rem:anti-confusion-list}
The following readings are refused. Citing any one of them is a discipline violation that the audit catches via the \texttt{axis-confusion} branch of \autoref{def:acceptance-failure-cert}.
\begin{enumerate}
  \item ``BEDC has re-derived all of mature mathematics.''
  \item ``$\RealUp$ is complete.''
  \item ``$\SOneUp$ is complete.''
  \item ``$\FoldUp$ is complete.''
  \item ``$\NatUp$ at $\scopedClosure$ equals full natural-number theory.''
  \item ``$\AddUp$ at $\scopedClosure$ equals full addition.''
  \item ``Paper certificates equal machine-checked certificates.''
  \item ``Lean scaffolds equal verified implementations.''
  \item ``External standard models replace BEDC internal proof obligations.''
  \item ``Host equality, host $\mathsf{Nat}$, or host functions are part of the BEDC public surface.''
  \item ``Machine verification is required for theoretical closure.''
  \item ``Without $\theoremCheckedV$ no closure grade above $\seedClosure$ may be claimed.''
  \item ``A checked theorem-shape scaffold closes the corresponding object theory.''
  \item ``A scoped certificate closure is a full traditional-object reconstruction.''
  \item ``A bridge is closed merely because the BEDC-side certificate is checked.''
\end{enumerate}
\end{remark}
```

- [ ] **Step 6: Update audit-policy remark (line 91)**

The line "When a failure certificate is exhibited for an object $N$ presently marked at strength $s \ge \paperCertStr$" becomes:

```latex
When a failure certificate is exhibited for an object $N$ presently at $\TheoryGate(N, c)$ with $c \ge \scopedClosure$, or at $\FormalStatus(N, v)$ with $v \ge \theoremCheckedV$, the closurestatus block of the chapter is downgraded by the discipline of \autoref{def:marker-to-verification}: a $\verb|\leanchecked|$ becomes a $\verb|\leanstmt|$ if the source still survives but exactness no longer holds, or a $\verb|\leansorryd|$ if the proof has been retracted; the closure grade is lowered to the highest grade still licensed by the surviving witnesses. The audit script of \autoref{lem:audit-reflects-verification} reflects only the verification axis; the closure grade is reflected by the chapter's closurestatus block.
```

- [ ] **Step 7: Compile**

```bash
cd papers/bedc && make 2>&1 | tail -10
```

Expected: green.

---

## Task 6 — Add Closure Reading Convention chapter (`04_closure_reading_convention.tex`)

**Files:**
- Create: `papers/bedc/parts/acceptance/04_closure_reading_convention.tex`.
- Modify: `papers/bedc/parts/acceptance.tex` (add the `\input` line).

**Goal:** A short, explicit chapter that crystallises the convention and provides the per-object closure-vs-verification table the user spec §8 prescribes.

- [ ] **Step 1: Create the chapter**

Write `papers/bedc/parts/acceptance/04_closure_reading_convention.tex`:

```latex
\chapter{Closure Reading Convention}
\label{ch:closure-reading-convention}

This short chapter records the convention by which a reader should read every closurestatus block in the manuscript.

\section{Read both axes, separately}

A line of the form $\TheoryGate(N, c)$ records what the paper has closed about $N$ at grade $c$. A line of the form $\FormalStatus(N, v)$ records the audit state of the cited Lean target at grade $v$. The two are independent: neither line implies the other, and the conjunction $\VerifiedGate(N, c, v)$ records both at once without merging them.

\section{Read closure as a paper claim}

The closure axis is read entirely from the manuscript. A reader interrogating a closure claim should ask whether the chapter exhibits, within the stated scope, a source, a classifier, an exactness theorem, a ledger or absence statement, and a stability witness. None of these inquiries asks anything about a Lean file.

\section{Read verification as an audit claim}

The verification axis is read entirely from the audit. A reader interrogating a verification claim should ask whether the cited Lean target exists, whether \texttt{lake build} accepts it, whether \texttt{bedc\_ci.py audit} resolves it, and whether \texttt{check-axioms.py} reports the transitive dependencies clean. None of these inquiries asks anything about whether the paper's mathematical reading is closed.

\section{Per-object orientation table}

The following table orients a reader who lands on a chapter and wants to know its present axes at a glance. The table is non-normative: each chapter's closurestatus block is the binding source of truth.

\begin{longtable}{p{0.18\textwidth}p{0.20\textwidth}p{0.30\textwidth}p{0.20\textwidth}}
\toprule
\textbf{Object} & \textbf{Theory closure} & \textbf{Scope} & \textbf{Formal status}\\
\midrule
\endhead
$\NatUp$         & $\scopedClosure$ & unary history certificate                                & $\theoremCheckedV$\\
$\AddUp$         & $\scopedClosure$ & unary continuation certificate                           & $\theoremCheckedV$\\
$\IntUp$         & $\scopedClosure$ & history pair certificate                                 & $\theoremCheckedV$\\
$\RatUp$         & $\scopedClosure$ & history-pair semantic certificate                        & $\theoremCheckedV$\\
$\BoolUp$        & $\scopedClosure$ & boolean history semantic certificate                     & $\theoremCheckedV$\\
$\OptionUp$      & $\scopedClosure$ & tagged-option semantic certificate                       & $\theoremCheckedV$\\
$\ProdUp$        & $\scopedClosure$ & product history semantic certificate                     & $\theoremCheckedV$\\
$\SumUp$         & $\scopedClosure$ & sum history semantic certificate                         & $\theoremCheckedV$\\
$\ListUp$        & $\scopedClosure$ & list spine bridge classifier certificate                 & $\theoremCheckedV$\\
$\ComplexUp$     & $\scopedClosure$ & history pair semantic certificate                        & $\theoremCheckedV$\\
$\MonoidUp$      & $\scopedClosure$ & monoid history semantic certificate                      & $\theoremCheckedV$\\
$\GroupUp$       & $\scopedClosure$ & group stability certificate                              & $\theoremCheckedV$\\
$\AbGroupUp$     & $\scopedClosure$ & singleton empty-history certificate                      & $\theoremCheckedV$\\
$\CommRingUp$    & $\scopedClosure$ & singleton empty-history certificate                      & $\theoremCheckedV$\\
$\FieldUp$       & $\scopedClosure$ & FieldApartZero / phase-exit certificate                  & $\theoremCheckedV$\\
$\ModuleUp$      & $\scopedClosure$ & singleton smul image certificate                         & $\theoremCheckedV$\\
$\VecSpaceUp$    & $\scopedClosure$ & singleton empty-history vector-space certificate         & $\theoremCheckedV$\\
$\LinearMapUp$   & $\scopedClosure$ & singleton linear-map laws                                & $\theoremCheckedV$\\
$\MetricUp$      & $\scopedClosure$ & empty-history distance certificate                       & $\theoremCheckedV$\\
$\CategoryUp$    & $\scopedClosure$ & hom-carrier composition certificate                      & $\theoremCheckedV$\\
$\FunctorUp$     & $\scopedClosure$ & prefix functor carrier certificate                       & $\theoremCheckedV$\\
$\NatTransUp$    & $\scopedClosure$ & prefix-component classifier certificate                  & $\theoremCheckedV$\\
$\YonedaUp$      & $\scopedClosure$ & empty-component-family certificate                       & $\theoremCheckedV$\\
$\SubgroupUp$    & $\scopedClosure$ & subgroup centralizer certificate                         & $\theoremCheckedV$\\
$\QuotientGroupUp$ & $\scopedClosure$ & centralizer-normalizer certificate                       & $\theoremCheckedV$\\
$\DeterminantUp$ & $\scopedClosure$ & singleton determinant certificate                        & $\theoremCheckedV$\\
$\HomologyUp$    & $\scopedClosure$ & singleton cycle certificate                              & $\theoremCheckedV$\\
$\CohomologyUp$  & $\scopedClosure$ & singleton cocycle certificate                            & $\theoremCheckedV$\\
$\PrimeUp$       & $\scopedClosure$ & prime semantic certificate                               & $\theoremCheckedV$\\
$\RealUp$        & $\scopedClosure$ & rational embedding constant certificate                  & $\theoremCheckedV$\\
\bottomrule
\end{longtable}

\begin{remark}[Why every entry is $\scopedClosure$]
\label{rem:why-all-scoped}
Every present BEDC chapter closes a precise, paper-recorded scope; none claims the full traditional object as a theorem package, and none has yet exhibited a paper-level standard bridge with all six fields argued. The closure axis grade therefore stops at $\scopedClosure$ across the manuscript. Upgrades to $\publicClosure$ require chapters that exhibit a public-object surface with constructors, readback, endpoint exactness, normal form, and a no-hidden-leakage statement; upgrades to $\bridgedClosure$ require a paper-level standard bridge per \autoref{ch:acceptance-bridge}. Each chapter's closurestatus block names the upgrade path explicitly.
\end{remark}

\begin{remark}[Verification axis is uniform but not constraining]
\label{rem:verification-axis-uniform}
Every present chapter is at $\theoremCheckedV$ on the verification axis: each closurestatus block names a Lean target that resolves under \texttt{lean4/BEDC/} and that \texttt{lake build} accepts. The audit script of \autoref{lem:audit-reflects-verification} is responsible for keeping this uniform; the closure axis grade is independent.
\end{remark}
```

- [ ] **Step 2: Add the include line**

Open `papers/bedc/parts/acceptance.tex` and append:

```
\input{parts/acceptance/04_closure_reading_convention.tex}
```

- [ ] **Step 3: Compile**

```bash
cd papers/bedc && make 2>&1 | tail -10
```

Expected: green; the new chapter appears in TOC.

- [ ] **Step 4: Milestone P2 commit**

Confirm gates green:

```bash
cd lean4 && lake build && cd .. && \
cd papers/bedc && make && cd ../.. && \
python3 tools/check-axioms.py && \
python3 lean4/scripts/bedc_ci.py audit
```

Stage and commit:

```bash
git add papers/bedc/parts/acceptance/02_standard_bridge_protocol.tex \
        papers/bedc/parts/acceptance/03_cannot_claim_registry.tex \
        papers/bedc/parts/acceptance/04_closure_reading_convention.tex \
        papers/bedc/parts/acceptance.tex
git commit -m "$(cat <<'EOF'
P2 closure-vs-verification: rewrite bridge + cannot-claim chapters

Rewrite Chapter 146 sections II and III against the two-axis
discipline:

- Standard bridge is now a paper-level construction whose presence
  advances the closure axis from publicClosed to bridgedClosed; no-host-leak
  machine verification is the independent bridgeChecked point on the
  verification axis.
- Cannot-claim registry: failure certificate gains scope-overstated,
  audit-not-clean, and axis-confusion branches; Anchor 2 and Anchor 4
  reworded to use TheoryGate / FormalStatus.
- New chapter 04_closure_reading_convention orients readers and supplies
  a per-object closure × verification table.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7 — Migrate per-chapter closurestatus blocks (P3 batch)

**Files:** all 30 files listed in the inventory above. Each carries one `\closureat{<X>Up}{\checkedCertStr}[<grounding>]` line that must be replaced with a full `closurestatus` env.

**Goal:** Hand-migrate each site so its closurestatus block records the actual scope, the actual not-claimed boundary, and a precise upgrade path. The migration is not mechanical: the `scopeclosed` / `notclaimed` / `upgradepath` text differs per chapter.

- [ ] **Step 1: Build a migration helper checklist** (read once, do not commit)

For each file path `<F>` in the inventory:
1. Read `<F>` and identify the chapter's closing object name (e.g.\ `\NatUp`).
2. Read the chapter's existing `\NameCert{...}` and `SemanticNameCert` Lean target name.
3. Identify the chapter's claimed scope. For singleton chapters, the scope is "the displayed singleton certificate"; for history chapters, "the constructor-tagged history certificate"; for closure chapters, the explicit closure relation.
4. Identify what the chapter does NOT close (almost always: the full traditional-object theory; record one short sentence).
5. Identify the next upgrade obligation (usually $\publicClosure$ requires public constructors, readback, endpoint exactness; record one short sentence).

- [ ] **Step 2: For each file, replace `\closureat{...}` with the closurestatus env**

The replacement template, with placeholders to fill per chapter:

```latex
\begin{closurestatus}{\<X>Up}
  \theoryclosure{\scopedClosure}
  \scopeclosed{<one-sentence scope>}
  \formalstatus{\theoremCheckedV}
  \leantarget{<existing grounding name with \_-escaped underscores>}
  \bridgestatus{none}
  \notclaimed{<one-sentence not-claimed>}
  \upgradepath{<one-sentence upgrade path>}
\end{closurestatus}
```

The 30 chapters with their scope / not-claimed / upgrade-path text are listed below. Read this section once, then in a SECOND pass, for each chapter, open the file, find its old `\closureat` line, and replace with the env block exactly as listed.

For example, for `parts/concrete_instances/04_nat_namecert_construction.tex` (currently `\closureat{\NatUp}{\checkedCertStr}[BEDC.FKernel.Unary.nat\_up\_semantic\_name\_certificate]`):

```latex
\begin{closurestatus}{\NatUp}
  \theoryclosure{\scopedClosure}
  \scopeclosed{The unary-repetition history certificate over the BEDC carrier; classifier $\msame$ on histories; exactness witnessed by the cited semantic name certificate; ledger absent by explicit statement.}
  \formalstatus{\theoremCheckedV}
  \leantarget{BEDC.FKernel.Unary.nat\_up\_semantic\_name\_certificate}
  \bridgestatus{none}
  \notclaimed{Full Peano natural-number theory: induction principle as a closed theorem schema, primitive recursion with computation rules, totality of arithmetic operations.}
  \upgradepath{$\matureClosure$ requires $\NatUp$'s arithmetic test suite (induction, recursion, addition associativity and commutativity, multiplication distributivity, order totality) closed at paper level.}
\end{closurestatus}
```

For `parts/concrete_instances/22_vecspace_namecert_construction.tex`:

```latex
\begin{closurestatus}{\VecSpaceUp}
  \theoryclosure{\scopedClosure}
  \scopeclosed{Singleton empty-history vector-space semantic certificate over the displayed BEDC carrier and field classifier.}
  \formalstatus{\theoremCheckedV}
  \leantarget{BEDC.Derived.VecSpaceUp.VecSpaceSingleton\_semanticNameCert}
  \bridgestatus{none}
  \notclaimed{General vector spaces, finite-dimensional vector spaces over $\RatUp$ or $\RealUp$, bases, dimension, linear independence, rank-nullity, spectral theory, Banach/Hilbert spaces.}
  \upgradepath{$\publicClosure$ requires public vector-space constructors, basis readback, dimension theorem, and a no-hidden-leakage statement bracketing the public surface.}
\end{closurestatus}
```

For `parts/concrete_instances/62_determinant_namecert_construction.tex`:

```latex
\begin{closurestatus}{\DeterminantUp}
  \theoryclosure{\scopedClosure}
  \scopeclosed{Singleton determinant semantic certificate over MatrixSingletonCarrier and CommRingSingletonClassifier, including constant determinant readback, endpoint correspondence, classifier transport, and singleton multiplicativity.}
  \formalstatus{\theoremCheckedV}
  \leantarget{BEDC.Derived.DeterminantUp.DeterminantSingleton\_semanticNameCert}
  \bridgestatus{none}
  \notclaimed{General $n \times n$ determinant, Leibniz formula, alternating multilinear uniqueness, row operations, characteristic polynomial, or determinant theory over arbitrary fields.}
  \upgradepath{$\publicClosure$ requires public matrix carrier, $n \times n$ determinant construction, and standard determinant theorems (multiplicativity, Laplace expansion, Cramer's rule).}
\end{closurestatus}
```

(Repeat for each of the 30 chapters; the migration table is in the appendix of this plan, but every chapter follows the same template.)

- [ ] **Step 3: Update the capstone**

Open `papers/bedc/parts/visions/riemann_hypothesis.tex` and replace the sentence containing `\closureat{<...>}{\checkedCertStr}` (line 13) with two-axis vocabulary:

```latex
The certificate $\NameCert_{\PrimeUp}$ (\autoref{ch:concrete-instances-prime-namecert}) remains an open arithmetic certificate until its semantic naming certificate carries $\TheoryGate(\PrimeUp, \scopedClosure)$ at $\FormalStatus(\PrimeUp, \theoremCheckedV)$; once both axes hold, it supplies the index set of the Euler product $\zeta(s) = \prod_{p} (1 - p^{-s})^{-1}$.
```

- [ ] **Step 4: Update preface (frontmatter/preface.tex)**

After the "Layer discipline" paragraph, add:

```latex
\paragraph{Closure and verification.}
This manuscript separates theoretical closure from formal verification. A BEDC object may be theoretically closed at a stated scope when the paper supplies its source, classifier, exactness, stability, and ledger witnesses. A formalization marker records the independent verification status of those witnesses in a proof assistant. Machine checking strengthens reliability and auditability; it is not an object-language formation rule for closure. The discipline is recorded in \autoref{ch:closure-and-verification-discipline}.
```

- [ ] **Step 5: Update Appendix B**

Replace `papers/bedc/appendices/build_and_verification_log.tex` with:

```latex
\chapter{Verification Reporting Policy}
\label{app:build-log}

This appendix records the reporting policy that a checked BEDC formalization report should follow. It is project-management material on the verification axis only, not part of the BEDC object theory; nothing in this appendix assigns a closure grade.

\section{Required fields for a checked report}
\label{sec:checked-report-fields}

A checked report should record:
\begin{enumerate}
  \item the exact proof-checker version;
  \item the exact command used;
  \item whether the implementation imports external libraries;
  \item the list of theorem names successfully checked;
  \item the list of admitted, postulated, or pending statements;
  \item whether public APIs expose host equality, host natural numbers, host functions, or host lists as BEDC internals.
\end{enumerate}

\section{Verification status}
\label{sec:appendix-verification-status}

The Lean library accompanying the paper contains the mathlib-free BEDC formalization; inline markers record whether each cited object is a checked theorem, a definition, or a structure-field reference. Lean target status, theorem-by-theorem, is rendered inline at each primary site via the \texttt{\textbackslash leanchecked}, \texttt{\textbackslash leansorryd}, \texttt{\textbackslash leanstmt}, and \texttt{\textbackslash leandef} markers. The summary block in the Lean Scaffold Contract chapter aggregates the five base-reflection targets at-a-glance. The audit \texttt{python3 lean4/scripts/bedc\_ci.py audit} enforces that every \texttt{\textbackslash leanchecked\{X\}} target X resolves to a real declaration in \texttt{lean4/BEDC/}. The axiom audit reports zero \texttt{axiom} declarations in \texttt{lean4/BEDC/}.

\section{Relation to theoretical closure}
\label{sec:appendix-relation-to-closure}

A checked report does not assign theoretical closure. It reports the formal verification grade of claims whose closure grade is supplied by the chapter's \texttt{closurestatus} block (\autoref{ch:closure-and-verification-discipline}). A closurestatus block at $\TheoryGate(N, \scopedClosure)$ does not require any verification report; conversely, a clean verification report cannot raise a closure grade. The two artefacts compose only via $\VerifiedGate$ of \autoref{def:verified-gate}, and their contents are interrogated separately.
```

- [ ] **Step 6: Update Roadmap (`parts/project_governance/roadmap.tex`)**

Replace §"Strength gradient" (lines 31-44) with:

```latex
\section{Closure and verification axes}
\label{sec:roadmap-closure-and-verification-axes}

Every claim about a derived mature object is read on two independent axes. The closure axis records what the paper has reconstructed; the verification axis records the audit state of the corresponding Lean target. The discipline is recorded in \autoref{ch:closure-and-verification-discipline}.
\[
  \boxed{(c, v) \in \TheoryClosure \times \FormalStatus.}
\]
The closure axis grades are $\seedClosure < \obligationClosure < \scopedClosure < \publicClosure < \bridgedClosure < \matureClosure$; the verification axis grades are $\unformalizedV < \formalTargetV < \encodedDefV < \scaffoldCheckedV < \theoremCheckedV < \auditCleanV < \axiomCleanV$, with $\bridgeCheckedV$ as the bridge-axis verification level. Neither axis determines the other.
```

Replace the §"Per-object research template" Status field (line 262) with:

```latex
  \item \textbf{Status}: a pair $(c, v)$ where $c \in \TheoryClosure$ is the closure axis grade and $v \in \FormalStatus$ is the verification axis grade.
```

Replace each Phase exit-criterion bullet in §"Near-term phases" (lines 270-280) with a 3-line block. For example, "Phase Finite Data" becomes:

```latex
  \item[\textbf{Phase Finite Data}] L6, $\BoolUp$ through $\ListUp$, with the ten-field template completed for each. Exit criterion:
    \begin{itemize}
      \item Closure axis: $\TheoryGate(N, \scopedClosure)$ for every $N$ in $\{\BoolUp, \OptionUp, \SumUp, \ProdUp, \ListUp\}$.
      \item Verification axis: $\FormalStatus(N, \auditCleanV)$ on the cited Lean targets.
      \item Bridge status: pending.
    \end{itemize}
```

Apply the same 3-line transformation to every phase bullet (Kernel-Checked Baseline, Full Nat Arithmetic, Algebra Hierarchy, Real and Completion, Real Algebra and Geometry, Compact and Continuous, Linear Algebra and Analysis Seed, Category and Bridge).

Replace §"Claims explicitly off the table" (lines 287-298) with the 15-claim list from §V of the cannot-claim chapter:

```latex
The discipline of this manuscript is two-axis. The following readings are refused:
\begin{enumerate}
  \item BEDC has re-derived all of mature mathematics.
  \item $\RealUp$ is complete.
  \item $\SOneUp$ is complete.
  \item $\FoldUp$ is complete.
  \item $\NatUp$ at $\scopedClosure$ equals full natural-number theory.
  \item $\AddUp$ at $\scopedClosure$ equals full addition.
  \item Paper certificates equal machine-checked certificates.
  \item Lean scaffolds equal verified implementations.
  \item External standard models replace BEDC internal proof obligations.
  \item Host equality, host $\mathsf{Nat}$, or host functions are part of the BEDC public surface.
  \item Machine verification is required for theoretical closure.
  \item Without $\theoremCheckedV$ no closure grade above $\seedClosure$ may be claimed.
  \item A checked theorem-shape scaffold closes the corresponding object theory.
  \item A scoped certificate closure is a full traditional-object reconstruction.
  \item A bridge is closed merely because the BEDC-side certificate is checked.
\end{enumerate}
```

- [ ] **Step 7: Delete the temporary preamble shim**

Open `papers/bedc/preamble.tex` and delete the entire `% --- TEMPORARY SHIM` block introduced in Task 1 Step 4 (the `\AcceptGate`, `\Strength`, `\seedStr`, `\paperCertStr`, `\checkedCertStr`, `\bridgeCertStr`, and `\closureat` definitions).

- [ ] **Step 8: Compile and confirm zero shim emissions remain**

```bash
cd papers/bedc && make 2>&1 | tail -10
grep -rn "checkedCertStr\|paperCertStr\|bridgeCertStr\|seedStr\|AcceptGate\|closureat\|legacy-shim" papers/bedc/parts/ papers/bedc/preamble.tex 2>/dev/null
```

Expected: build green, the second grep returns zero lines (every old token has been removed).

- [ ] **Step 9: Audit drift**

```bash
python3 lean4/scripts/bedc_ci.py audit
```

Expected at this stage: drift audit will FAIL because `bedc_ci.py` still expects `\closureat`. That's fine — it's the next task's responsibility to teach the audit about closurestatus blocks. The build-side gate (pdflatex) is already green; the audit-side will be repaired in P4.

- [ ] **Step 10: Milestone P3 commit**

```bash
git add papers/bedc/preamble.tex \
        papers/bedc/parts/concrete_instances/ \
        papers/bedc/parts/visions/riemann_hypothesis.tex \
        papers/bedc/frontmatter/preface.tex \
        papers/bedc/appendices/build_and_verification_log.tex \
        papers/bedc/parts/project_governance/roadmap.tex
git commit -m "$(cat <<'EOF'
P3 closure-vs-verification: per-chapter closurestatus blocks

Migrate every \closureat site to the closurestatus environment and
delete the transient preamble shim from P1.

Per-chapter blocks now record both axes: theoryclosure (paper-side
closure grade), scopeclosed (binding scope), formalstatus
(verification-axis grade), leantarget (cited Lean theorem),
bridgestatus, notclaimed (what the chapter explicitly does NOT close),
and upgradepath (next-grade obligation). 30 concrete-instance chapters
plus the Riemann capstone are migrated.

Frontmatter preface, Appendix B, and the project-governance roadmap
also flipped to the two-axis vocabulary; roadmap phases now exit on
(closure, verification, bridge) triples.

The audit script is intentionally still the old single-axis version;
P4 teaches it to parse closurestatus blocks.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8 — Update audit script (`lean4/scripts/bedc_ci.py`)

**Files:**
- Modify: `lean4/scripts/bedc_ci.py:441-517` (CLOSUREAT_RE block + collect_closureat_groundings).
- Modify: `lean4/scripts/bedc_ci.py:541-562` (audit_payload).
- Modify: `lean4/scripts/bedc_ci.py:686-731` (human-readable summary).
- Create: `lean4/scripts/test_closurestatus_audit.py` (Python unit tests).

**Goal:** Replace `\closureat`-based parsing with closurestatus-env parsing.

- [ ] **Step 1: Replace `CLOSUREAT_RE` and `collect_closureat_groundings` (lines 441-517)**

Open `lean4/scripts/bedc_ci.py` and locate the `CLOSUREAT_RE` definition. Replace lines 441-517 with:

```python
# Closurestatus environment recognition.
#
# Every chapter that closes an object emits one block of the shape:
#
#   \begin{closurestatus}{\<X>Up}
#     \theoryclosure{\<closure-grade>}
#     \scopeclosed{<text>}
#     \formalstatus{\<verification-grade>}
#     \leantarget{<Lean theorem name>}
#     \bridgestatus{<state>}
#     \notclaimed{<text>}
#     \upgradepath{<text>}
#   \end{closurestatus}
#
# Both \theoryclosure and \formalstatus are mandatory. \leantarget is
# mandatory whenever \formalstatus is theoremCheckedV or above. The
# block is the manuscript's binding commitment about the object's
# closure-and-verification state; audit refuses missing fields and
# unresolved \leantarget targets.

CLOSURESTATUS_BEGIN_RE = re.compile(
    r"\\begin\{closurestatus\}\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}"
)
CLOSURESTATUS_END_RE = re.compile(r"\\end\{closurestatus\}")
CLOSURESTATUS_FIELD_RE = re.compile(
    r"\\(theoryclosure|formalstatus|leantarget|bridgestatus"
    r"|scopeclosed|notclaimed|upgradepath)\{([^}]+)\}"
)

VALID_CLOSURE_GRADES = {
    "seedClosure", "obligationClosure", "scopedClosure",
    "publicClosure", "bridgedClosure", "matureClosure",
}
VALID_FORMAL_GRADES = {
    "unformalizedV", "formalTargetV", "encodedDefV",
    "scaffoldCheckedV", "theoremCheckedV", "auditCleanV",
    "axiomCleanV", "bridgeCheckedV",
}
GRADE_REQUIRES_LEAN_TARGET = {
    "scaffoldCheckedV", "theoremCheckedV", "auditCleanV",
    "axiomCleanV", "bridgeCheckedV",
}


def collect_closurestatus_blocks(part_root: Path) -> list[dict]:
    """Walk every paper part and return one dict per closurestatus block.

    Each dict carries:
      - file, line: location of the \\begin{closurestatus}
      - region: the <X> from \\<X>Up
      - theory_closure: the closure grade token (e.g. 'scopedClosure'),
                        or None if missing
      - formal_status: the verification grade token, or None if missing
      - lean_target: the unescaped Lean theorem name, or None if missing
      - bridge_status: 'none' / 'paperBridge' / 'bridgeChecked' / etc.
      - has_scope, has_notclaimed, has_upgradepath: presence flags
    """
    out: list[dict] = []
    for tex in part_root.rglob("*.tex"):
        try:
            text = tex.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for m in CLOSURESTATUS_BEGIN_RE.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            tail = text[m.end():]
            end_match = CLOSURESTATUS_END_RE.search(tail)
            if not end_match:
                out.append({
                    "file": str(tex.relative_to(part_root.parent.parent.parent)),
                    "line": line,
                    "region": m.group(1),
                    "error": "no \\end{closurestatus}",
                    "theory_closure": None,
                    "formal_status": None,
                    "lean_target": None,
                    "bridge_status": None,
                    "has_scope": False,
                    "has_notclaimed": False,
                    "has_upgradepath": False,
                })
                continue
            body = tail[:end_match.start()]
            fields: dict[str, str] = {}
            for fm in CLOSURESTATUS_FIELD_RE.finditer(body):
                fields[fm.group(1)] = fm.group(2).strip()
            tc = fields.get("theoryclosure", "").lstrip("\\")
            fs = fields.get("formalstatus", "").lstrip("\\")
            lt = fields.get("leantarget")
            if lt is not None:
                lt = lt.replace("\\_", "_").strip()
            out.append({
                "file": str(tex.relative_to(part_root.parent.parent.parent)),
                "line": line,
                "region": m.group(1),
                "theory_closure": tc or None,
                "formal_status": fs or None,
                "lean_target": lt,
                "bridge_status": fields.get("bridgestatus"),
                "has_scope": "scopeclosed" in fields,
                "has_notclaimed": "notclaimed" in fields,
                "has_upgradepath": "upgradepath" in fields,
            })
    return out


def diagnose_closurestatus_block(block: dict, lean_symbols: set[str]) -> list[str]:
    """Return a list of diagnostic messages for a single block. Empty list
    means the block passes the audit."""
    issues: list[str] = []
    where = f"{block['file']}:{block['line']} (region {block['region']}Up)"
    if block.get("error"):
        issues.append(f"{where}: {block['error']}")
        return issues
    tc = block.get("theory_closure")
    fs = block.get("formal_status")
    lt = block.get("lean_target")
    if not tc:
        issues.append(f"{where}: missing \\theoryclosure")
    elif tc not in VALID_CLOSURE_GRADES:
        issues.append(f"{where}: invalid theoryclosure grade '{tc}'")
    if not fs:
        issues.append(f"{where}: missing \\formalstatus")
    elif fs not in VALID_FORMAL_GRADES:
        issues.append(f"{where}: invalid formalstatus grade '{fs}'")
    if fs in GRADE_REQUIRES_LEAN_TARGET and not lt:
        issues.append(
            f"{where}: \\formalstatus={fs} requires \\leantarget"
        )
    if lt and lt not in lean_symbols:
        issues.append(
            f"{where}: \\leantarget '{lt}' does not resolve under lean4/BEDC/"
        )
    if not block.get("has_scope"):
        issues.append(f"{where}: missing \\scopeclosed (binding scope text)")
    if not block.get("has_notclaimed"):
        issues.append(f"{where}: missing \\notclaimed (claims off the table)")
    if not block.get("has_upgradepath"):
        issues.append(f"{where}: missing \\upgradepath (next-grade obligation)")
    return issues
```

- [ ] **Step 2: Update `audit_payload()` (lines 541-562 region)**

Find the block

```python
    closureats = collect_closureat_groundings(PAPER_PARTS_ROOT)
    closureats_missing_grounding = [c for c in closureats if not c["grounding"]]
    closureats_bad_grounding = [
        c for c in closureats
        if c["grounding"] and c["grounding"] not in symbols
    ]
```

and replace with

```python
    closurestatus_blocks = collect_closurestatus_blocks(PAPER_PARTS_ROOT)
    closurestatus_diagnostics: list[str] = []
    for block in closurestatus_blocks:
        closurestatus_diagnostics.extend(
            diagnose_closurestatus_block(block, symbols)
        )
```

Then update the `payload` dict assembly later in the same function. Find the lines

```python
        "closureats_total": len(closureats),
        "closureats_missing_grounding": closureats_missing_grounding,
        "closureats_missing_grounding_count": len(closureats_missing_grounding),
        "closureats_bad_grounding": closureats_bad_grounding,
        "closureats_bad_grounding_count": len(closureats_bad_grounding),
```

and replace with

```python
        "closurestatus_blocks_total": len(closurestatus_blocks),
        "closurestatus_blocks": closurestatus_blocks,
        "closurestatus_diagnostics": closurestatus_diagnostics,
        "closurestatus_diagnostics_count": len(closurestatus_diagnostics),
```

- [ ] **Step 3: Update the human-readable summary (around lines 686-731)**

Find the block

```python
        if payload["closureats_missing_grounding"]:
            print(
                "[bedc-ci] \\closureat without grounding: "
                f"{payload['closureats_missing_grounding_count']}"
            )
            for item in payload["closureats_missing_grounding"][:50]:
                ...
```

and replace the entire `closureats_missing_grounding` + `closureats_bad_grounding` reporting block with

```python
        if payload["closurestatus_diagnostics"]:
            print(
                "[bedc-ci] closurestatus block diagnostics: "
                f"{payload['closurestatus_diagnostics_count']}"
            )
            for msg in payload["closurestatus_diagnostics"][:80]:
                print(f"  {msg}")
            print(
                "[bedc-ci] resolution: every \\begin{closurestatus}{<X>Up}"
                " block must declare \\theoryclosure, \\formalstatus, "
                "\\scopeclosed, \\notclaimed, \\upgradepath; if "
                "\\formalstatus is theoremCheckedV or above, \\leantarget "
                "is required and must resolve under lean4/BEDC/."
            )
```

Then update the `total_violations = ...` summary around line 727 to add `+ payload["closurestatus_diagnostics_count"]` and remove the two retired counters.

- [ ] **Step 4: Run the audit against the migrated paper**

```bash
python3 lean4/scripts/bedc_ci.py audit
```

Expected: clean exit 0 if every closurestatus block is valid; otherwise the list of diagnostics points at the offending file:line. Iterate on the chapter migrations until clean.

- [ ] **Step 5: Add unit tests**

Create `lean4/scripts/test_closurestatus_audit.py`:

```python
"""Unit tests for the closurestatus block parser in bedc_ci.py."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from bedc_ci import (  # type: ignore[import-not-found]
    CLOSURESTATUS_BEGIN_RE,
    CLOSURESTATUS_FIELD_RE,
    diagnose_closurestatus_block,
)


class ClosurestatusRegexTests(unittest.TestCase):
    def test_begin_regex_matches_simple_form(self) -> None:
        block = r"\begin{closurestatus}{\NatUp}"
        m = CLOSURESTATUS_BEGIN_RE.search(block)
        self.assertIsNotNone(m)
        assert m is not None  # narrow Optional for mypy
        self.assertEqual(m.group(1), "Nat")

    def test_field_regex_extracts_lean_target(self) -> None:
        body = r"\leantarget{BEDC.Foo.Bar\_baz}"
        m = CLOSURESTATUS_FIELD_RE.search(body)
        self.assertIsNotNone(m)
        assert m is not None
        self.assertEqual(m.group(1), "leantarget")
        self.assertEqual(m.group(2), r"BEDC.Foo.Bar\_baz")


class ClosurestatusDiagnosticsTests(unittest.TestCase):
    def _block(self, **overrides):
        base = {
            "file": "papers/bedc/parts/x.tex",
            "line": 1,
            "region": "Foo",
            "theory_closure": "scopedClosure",
            "formal_status": "theoremCheckedV",
            "lean_target": "BEDC.Foo.example",
            "bridge_status": "none",
            "has_scope": True,
            "has_notclaimed": True,
            "has_upgradepath": True,
        }
        base.update(overrides)
        return base

    def test_clean_block_passes(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(), lean_symbols={"BEDC.Foo.example"}
        )
        self.assertEqual(diags, [])

    def test_invalid_theory_closure_grade_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(theory_closure="bogusGrade"),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(any("invalid theoryclosure" in d for d in diags))

    def test_theorem_checked_without_lean_target_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(lean_target=None),
            lean_symbols=set(),
        )
        self.assertTrue(any("requires \\leantarget" in d for d in diags))

    def test_unresolved_lean_target_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(lean_target="BEDC.Missing.thing"),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(
            any("does not resolve under lean4/BEDC" in d for d in diags)
        )

    def test_missing_scope_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(has_scope=False),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(any("missing \\scopeclosed" in d for d in diags))


if __name__ == "__main__":
    unittest.main(verbosity=2)
```

- [ ] **Step 6: Run unit tests**

```bash
python3 lean4/scripts/test_closurestatus_audit.py
```

Expected: 5 tests pass.

---

## Task 9 — Update `critical_path.py` (closure-aware horizon retirement)

**Files:**
- Modify: `lean4/scripts/critical_path.py:123-247` and `:404-454`.

**Goal:** Replace `CLOSED_STRENGTHS = {"checkedCert", "bridgeCert"}` with two-axis logic. A chapter is retired from horizon work iff its closurestatus block records $\TheoryGate(N, \scopedClosure)$ (or above) AND $\FormalStatus(N, \theoremCheckedV)$ (or above). The change is semantically equivalent to the current behaviour for present chapters but is now legible to a reader who understands the two-axis discipline.

- [ ] **Step 1: Read the current `is_chapter_closed` function**

```bash
sed -n '123,250p' lean4/scripts/critical_path.py
```

- [ ] **Step 2: Retire `CLOSED_STRENGTHS` and the `\closureat` regex**

Remove

```python
LEAN_MARKER_RE = re.compile(r"\\(leanchecked|leanstmt|leandef)\{")
CLOSUREAT_RE = re.compile(...)
CLOSED_STRENGTHS = {"checkedCert", "bridgeCert"}
```

(retain `LEAN_MARKER_RE`; replace `CLOSUREAT_RE` and `CLOSED_STRENGTHS`).

Insert in their place

```python
LEAN_MARKER_RE = re.compile(r"\\(leanchecked|leanstmt|leandef)\{")

# A chapter is retired from horizon work iff it carries a closurestatus
# block whose theoryclosure grade is scopedClosure-or-above AND whose
# formalstatus grade is theoremCheckedV-or-above. Both conditions must
# hold; either alone is insufficient.
CLOSURESTATUS_BEGIN_RE = re.compile(
    r"\\begin\{closurestatus\}\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}"
)
CLOSURESTATUS_END_RE = re.compile(r"\\end\{closurestatus\}")
THEORYCLOSURE_RE = re.compile(r"\\theoryclosure\{\\(\w+)\}")
FORMALSTATUS_RE = re.compile(r"\\formalstatus\{\\(\w+)\}")
LEANTARGET_RE = re.compile(r"\\leantarget\{([^}]+)\}")

CLOSURE_GRADE_ORDER = [
    "seedClosure", "obligationClosure", "scopedClosure",
    "publicClosure", "bridgedClosure", "matureClosure",
]
FORMAL_GRADE_ORDER = [
    "unformalizedV", "formalTargetV", "encodedDefV",
    "scaffoldCheckedV", "theoremCheckedV", "auditCleanV",
    "axiomCleanV", "bridgeCheckedV",
]
RETIREMENT_CLOSURE_THRESHOLD = "scopedClosure"
RETIREMENT_FORMAL_THRESHOLD = "theoremCheckedV"


def _grade_at_or_above(grade: str | None, threshold: str, order: list[str]) -> bool:
    if grade is None or grade not in order or threshold not in order:
        return False
    return order.index(grade) >= order.index(threshold)
```

- [ ] **Step 3: Replace `is_chapter_closed` with `is_chapter_retired_from_horizon`**

Find the existing `is_chapter_closed` function and replace its body with logic that:
1. Searches for `\begin{closurestatus}{<NameUp>}` (where NameUp matches the chapter's region).
2. Within the block (text up to the matching `\end{closurestatus}`), extracts the theoryclosure grade and formalstatus grade.
3. Returns a tuple `(is_retired: bool, theory_grade: str | None, formal_grade: str | None, lean_target: str | None)`.

```python
def is_chapter_retired_from_horizon(
    chapter_text: str, name: str
) -> tuple[bool, str | None, str | None, str | None]:
    """Read the chapter's closurestatus block (if present) and return
    (retired, theory_grade, formal_grade, lean_target).

    A chapter is retired from horizon work iff it carries a closurestatus
    block for `<name>Up` with theoryclosure >= scopedClosure AND
    formalstatus >= theoremCheckedV. If no closurestatus block matches
    `<name>Up`, all return values are (False, None, None, None).
    """
    for m in CLOSURESTATUS_BEGIN_RE.finditer(chapter_text):
        if m.group(1).lower() != name.lower():
            continue
        tail = chapter_text[m.end():]
        end = CLOSURESTATUS_END_RE.search(tail)
        body = tail[:end.start()] if end else tail
        tc_match = THEORYCLOSURE_RE.search(body)
        fs_match = FORMALSTATUS_RE.search(body)
        lt_match = LEANTARGET_RE.search(body)
        tc = tc_match.group(1) if tc_match else None
        fs = fs_match.group(1) if fs_match else None
        lt = (
            lt_match.group(1).replace("\\_", "_").strip()
            if lt_match else None
        )
        retired = (
            _grade_at_or_above(tc, RETIREMENT_CLOSURE_THRESHOLD, CLOSURE_GRADE_ORDER)
            and _grade_at_or_above(fs, RETIREMENT_FORMAL_THRESHOLD, FORMAL_GRADE_ORDER)
        )
        return (retired, tc, fs, lt)
    return (False, None, None, None)
```

- [ ] **Step 4: Update every caller of the retired functions**

Search:

```bash
grep -n "is_chapter_closed\|CLOSED_STRENGTHS\|closed_at\|closed\b" lean4/scripts/critical_path.py
```

Update every reference to `is_chapter_closed(...)`/`CLOSED_STRENGTHS`/`closed_at` so that:
- The horizon dict's `closed_at` field becomes a 2-tuple `(theory_grade, formal_grade)` (or `None` if the chapter is not retired).
- The `closed` boolean is the result of `is_chapter_retired_from_horizon`.
- The grounding extractor (`extract_closure_grounding`) reads `\leantarget{...}` from inside the closurestatus block instead of the optional `[grounding]` argument of `\closureat`.

The patches are mechanical; preserve the function signatures and return-types so downstream JSON consumers keep working. Where the JSON previously stored `"closed_at": "checkedCert"`, now store `"closed_at": ["scopedClosure", "theoremCheckedV"]` and add a sibling field `"lean_target": "<name>"` so dossier scripts can keep using a single grounding name.

- [ ] **Step 5: Confirm critical_path.py still produces a usable JSON**

```bash
python3 lean4/scripts/critical_path.py --top 5 2>&1 | head -40
```

Expected: JSON parses; `top` lists open horizons (those NOT yet at scopedClosure × theoremCheckedV); closed chapters are excluded as before.

---

## Task 10 — Add `axis-confusion` gate to `phase_paper_gates.py`

**Files:**
- Modify: `papers/bedc/scripts/phase_paper_gates.py:60` (LEAN_MARKER_RE remains; add closure-related regex), `:280-285` (GATE_DISPATCH).

**Goal:** Reject codex rounds whose diff conflates the two axes (e.g.\ a claim that strengthens closure grade as a function of verification grade). The gate is a guardrail for the prompts we update in Task 11; without the gate, a stray prompt reading could re-introduce the old conflation.

- [ ] **Step 1: Add the gate function**

In `papers/bedc/scripts/phase_paper_gates.py`, add after `detect_leanvariant`:

```python
AXIS_CONFUSION_PHRASES = (
    re.compile(
        r"theory(?:\s+is)?\s+closed\s+because\s+(?:it\s+is\s+|the\s+)?(?:lean|machine|formal)",
        re.I,
    ),
    re.compile(
        r"unchecked,?\s+therefore\s+not\s+closed",
        re.I,
    ),
    re.compile(
        r"\\theoryclosure\{[^}]*\}\s*=>?\s*\\formalstatus",
    ),
    re.compile(
        r"\\formalstatus\{[^}]*\}\s*=>?\s*\\theoryclosure",
    ),
)


def detect_axis_confusion(*, worktree: Path, base_sha: str) -> list[str]:
    """Refuse diffs whose prose or structure makes one axis depend on the
    other. A list of forbidden phrasings is matched against added lines
    only; the gate is a fast lint, not a semantic check."""
    violations: list[str] = []
    for rel in _changed_tex_files(worktree=worktree, base_sha=base_sha):
        for line_no, content in _added_lines_per_file(
            worktree=worktree, base_sha=base_sha, rel_path=rel
        ):
            for pat in AXIS_CONFUSION_PHRASES:
                if pat.search(content):
                    violations.append(
                        f"{rel}:{line_no}: closure/verification axis "
                        f"confusion — {content.strip()[:120]}"
                    )
                    break
    return violations
```

- [ ] **Step 2: Register the gate**

In `GATE_DISPATCH` (line 280), add the `"axis-confusion"` entry:

```python
GATE_DISPATCH = {
    "register-only": detect_register_only,
    "vocab": detect_vocab,
    "math": detect_math,
    "oversized": detect_oversized,
    "leanvariant": detect_leanvariant,
    "axis-confusion": detect_axis_confusion,
}
```

- [ ] **Step 3: Update the docstring's `--gate` choice list (line 18)**

```python
        [--gate register-only|vocab|math|oversized|leanvariant|axis-confusion|all]
```

- [ ] **Step 4: Wire the gate into `codex_revise.py`**

Open `papers/bedc/scripts/codex_revise.py` and locate the gate-result handling block around line 1779. After the `leanvariant` warning block, add:

```python
    # Gate F — axis-confusion (closure × verification): hard fail.
    axis_v = gate_results.get("axis-confusion", [])
    if axis_v:
        logger.error(
            f"[P{wt.round_number}] axis-confusion gate violations: {len(axis_v)}"
        )
        for v in axis_v[:20]:
            logger.error(f"  {v}")
        return False
```

- [ ] **Step 5: Smoke-test the gate**

Create a temporary scratch file and stage a violating line:

```bash
cd /tmp
echo "The theory is closed because it is machine-checked." > scratch.tex
python3 - <<'PY'
import re, sys
sys.path.insert(0, '/Users/auric/newmath/papers/bedc/scripts')
from phase_paper_gates import AXIS_CONFUSION_PHRASES
hit = any(p.search('The theory is closed because it is machine-checked.') for p in AXIS_CONFUSION_PHRASES)
assert hit, 'gate failed to flag the canonical axis-confusion sentence'
print('axis-confusion smoke test passed')
PY
```

Expected: prints `axis-confusion smoke test passed`.

- [ ] **Step 6: Milestone P4 commit**

Confirm gates green:

```bash
cd lean4 && lake build && cd .. && \
cd papers/bedc && make && cd ../.. && \
python3 tools/check-axioms.py && \
python3 lean4/scripts/bedc_ci.py audit && \
python3 lean4/scripts/test_closurestatus_audit.py
```

Stage and commit:

```bash
git add lean4/scripts/bedc_ci.py \
        lean4/scripts/critical_path.py \
        lean4/scripts/test_closurestatus_audit.py \
        papers/bedc/scripts/phase_paper_gates.py \
        papers/bedc/scripts/codex_revise.py
git commit -m "$(cat <<'EOF'
P4 closure-vs-verification: audit + critical-path + axis-confusion gate

- bedc_ci.py audit: parse \\begin{closurestatus} blocks; require
  \\theoryclosure, \\formalstatus, \\scopeclosed, \\notclaimed,
  \\upgradepath; resolve \\leantarget under lean4/BEDC/.
- critical_path.py: retire chapters that carry both
  theoryclosure>=scopedClosure and formalstatus>=theoremCheckedV.
- phase_paper_gates.py: new axis-confusion gate flags prose that
  conflates the closure and verification axes.
- codex_revise.py: hard-fail rounds that trip the gate.
- test_closurestatus_audit.py: 5 unit tests for the new parser.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11 — Update codex prompts

**Files:**
- Modify: `papers/bedc/scripts/prompts/phase_review.txt` (lines 24, 161-163, scattered references).
- Modify: `papers/bedc/scripts/prompts/phase_revise.txt` (Step 9 entirely; scattered references).
- Modify: `papers/bedc/scripts/prompts/{conflict_resolve,post_rebase_audit_resolve,round_fallback_resolve}.txt` (closureat references).
- Modify: `lean4/scripts/prompts/{phase_c,post_rebase_audit_resolve,round_fallback_resolve}.txt` (closureat references).

**Goal:** Teach every codex round about the two-axis discipline. The codex agents must not author rounds that re-confuse the axes.

- [ ] **Step 1: Update `phase_review.txt`**

Replace the line "the four-strength gradient (naming seed → paper certificate → machine-checked certificate → standard bridge);" with:

```
the two-axis discipline of \autoref{ch:closure-and-verification-discipline}: a closure axis (seed/obligation/scopedClosed/publicClosed/bridgedClosed/maturePackageClosed) read entirely from paper-side witnesses, and a verification axis (unformalized/.../bridgeChecked) read entirely from Lean-side audit. Neither axis is a function of the other; reading paper closure as evidence for verification, or vice versa, is a discipline violation.
```

In §"Closure proposals (`kind = "closure_mark"`)" (around line 163), replace the entire paragraph with the two-axis variant:

```
**Closure proposals (`kind = "closure_mark"`)**. If a horizon `<X>Up` chapter has every NameCert clause (carrier / classifier / stability / exactness / ledger / standard bridge if applicable) with a `\leanchecked` to a Lean target that resolves under `lean4/BEDC/`, AND the chapter does NOT yet carry a closurestatus block whose theoryclosure is scopedClosure-or-above and whose formalstatus is theoremCheckedV-or-above, propose a `closure_mark` target. The proposal MUST specify both axes explicitly, plus scope / not-claimed / upgrade-path text, and MUST NOT make either axis a function of the other. The block template is:

  \begin{closurestatus}{\<X>Up}
    \theoryclosure{\scopedClosure}      % paper-side closure grade
    \scopeclosed{<one-sentence binding scope>}
    \formalstatus{\theoremCheckedV}     % Lean-side verification grade
    \leantarget{BEDC.<...>.<theorem>}  % must resolve under lean4/BEDC/
    \bridgestatus{none}
    \notclaimed{<one-sentence list of what the chapter does NOT close>}
    \upgradepath{<one-sentence next-grade obligation>}
  \end{closurestatus}

Pick `<theorem>` from the chapter's already-`\leanchecked` set, in priority order: (1) `*semanticNameCert` / `*_semantic_name_certificate`, (2) `*_name_certificate`, (3) `*_stability_certificate_fields`, (4) `*_laws`. `bedc_ci.py audit` rejects a `closure_mark` whose `\leantarget` doesn't resolve to a real Lean declaration. Closure proposals always rank ahead of new theory_extensions for the same chapter — adding the closurestatus block retires the chapter from `critical_path.top` and frees Phase B to attack new fronts. To detect closure-eligible chapters: from the critical_path output, check chapters with `thms >= 10` that are still in `top`; their NameCert is likely complete and just needs the explicit closurestatus block.
```

- [ ] **Step 2: Update `phase_revise.txt`**

Replace Step 9 in its entirety (the `\closureat` discipline). The new Step 9:

```
9. **Closurestatus block (`\begin{closurestatus}{\<X>Up}…\end{closurestatus}`)**: a chapter is retired from horizon work iff it carries a closurestatus block whose theoryclosure is scopedClosure-or-above and whose formalstatus is theoremCheckedV-or-above. `lean4/scripts/critical_path.py` excludes retired chapters from `top`, so adding a complete closurestatus block is the only way the lean pipeline retires a horizon. Rules:
   - **When to add**: a target with `kind=closure_mark` proposes the closurestatus block for chapter `<X>Up`. BEFORE adding, verify every NameCert clause (carrier / classifier / stability fields / exactness / ledger / standard bridge if applicable) has a `\leanchecked` whose target resolves under `lean4/BEDC/<X>Up.lean` (or `<X>Up/...`). `python3 lean4/scripts/bedc_ci.py audit` must report 0 unresolved markers for this chapter.
   - **Where to add**: at the END of the chapter's last sub-file, on its own lines, OUTSIDE any `\begin{theorem}/\begin{definition}` block.
   - **What to write** — the block has seven mandatory fields:
     ```
     \begin{closurestatus}{\<X>Up}
       \theoryclosure{\scopedClosure}
       \scopeclosed{<one-sentence binding scope>}
       \formalstatus{\theoremCheckedV}
       \leantarget{BEDC.Derived.<X>Up.<theorem>}
       \bridgestatus{none}
       \notclaimed{<one-sentence list of what the chapter does NOT close>}
       \upgradepath{<one-sentence next-grade obligation>}
     \end{closurestatus}
     ```
     The two axis tokens are independent: a paper proof closes the theory axis at scopedClosure (or whatever grade the chapter actually witnesses), while the Lean target closes the verification axis at theoremCheckedV. Picking the wrong combination — e.g.\ scopedClosure with formalstatus=unformalizedV when the cited target exists, or publicClosure when the chapter only exhibits a singleton certificate — is a closure-discipline violation; the audit catches the obvious cases via the axis-confusion gate.
     The grounding theorem MUST be a real Lean target — `bedc_ci.py audit` enforces this and fails the round if the grounding doesn't resolve. `_` in the target must be `\_`-escaped (same as `\leanchecked`).
     Use `\publicClosure` only when the chapter exhibits a public-object surface; use `\bridgedClosure` only if the chapter exhibits a complete `\StdBridge` per `\autoref{ch:acceptance-bridge}`.
   - **Removing or downgrading** a closurestatus block is a deliberate downgrade and reopens the chapter to lean rounds. Don't do this lightly — it should be a separate target, justified by a found defect.
   - The block is the manuscript's binding commitment that the theory has reached the named closure grade and the cited Lean target has been verified at the named verification grade. Adding it without coverage or with a fake grounding is a discipline violation that the audit catches.
```

Search the file for any further references to `\paperCertStr`, `\checkedCertStr`, `\bridgeCertStr`, `\AcceptGate`, or `\closureat` and replace with the two-axis vocabulary.

- [ ] **Step 3: Update conflict-resolve / post-rebase-audit-resolve / round-fallback-resolve prompts**

In all four prompt files (`papers/bedc/scripts/prompts/{conflict_resolve,post_rebase_audit_resolve,round_fallback_resolve}.txt` and `lean4/scripts/prompts/{post_rebase_audit_resolve,round_fallback_resolve}.txt`), search for `closureat` and `checkedCert` references and replace with closurestatus-equivalent guidance. Specifically, any `\closureat{...}{\checkedCertStr}[<grounding>]` snippet becomes the seven-line `\begin{closurestatus}…\end{closurestatus}` block; any prose mentioning "checked strength" becomes "theoryclosure × formalstatus axes".

- [ ] **Step 4: Update Lean-formalize prompt `lean4/scripts/prompts/phase_c.txt`**

Search the file for `\leanchecked` discipline lines and update any reference to "the four-strength gradient" or "checkedCert" with the two-axis vocabulary; the Lean side primarily speaks the verification axis ("a new theorem at $\theoremCheckedV$").

- [ ] **Step 5: Bump prompt version**

In `papers/bedc/scripts/prompts/phase_revise.txt` and `phase_review.txt`, change the `## Prompts version` block from `v2.6` to `v3.0` (we're crossing a major-axis boundary). Update the body line that mentions the version mirror in the sibling prompt.

- [ ] **Step 6: Milestone P5 commit**

Confirm gates green:

```bash
cd lean4 && lake build && cd .. && \
cd papers/bedc && make && cd ../.. && \
python3 tools/check-axioms.py && \
python3 lean4/scripts/bedc_ci.py audit && \
python3 lean4/scripts/test_closurestatus_audit.py
```

Stage and commit:

```bash
git add papers/bedc/scripts/prompts/ lean4/scripts/prompts/
git commit -m "$(cat <<'EOF'
P5 closure-vs-verification: codex prompts on the two-axis discipline

Update every codex prompt — paper-revise, paper-review, conflict-resolve,
post-rebase audit-resolve, round-fallback resolve, Lean phase C — so
codex rounds are written and read against the two-axis closure-and-
verification discipline. Closure proposals (kind=closure_mark) now emit
a full closurestatus block with theoryclosure and formalstatus
specified independently; the axis-confusion gate added in P4 is the
guardrail. Prompt-pair version bumps from v2.6 to v3.0.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12 — Sync CLAUDE.md

**Files:**
- Modify: `CLAUDE.md` "状态宏 (preamble.tex)" section + "marker 使用纪律".

**Goal:** Project doc reflects the new vocabulary; codex workers reading CLAUDE.md as part of their warm-up know about the two axes.

- [ ] **Step 1: Replace the "状态宏 (preamble.tex)" subsection**

Find the section starting `## 状态宏 (preamble.tex)` and replace it with:

```markdown
## 状态宏 (preamble.tex)

每个论文中讨论的 Lean 目标在论文里通过两类宏标注：

### Lean 标记宏 (verification 轴 only)

- `\leanchecked{Lean.Target.name}` — 该 paper site 的 canonical 主实现 (绿 ✓), 每 paper site 只一条; 对应 `formalstatus = theoremCheckedV`
- `\leanvariant{Lean.Target.name}` — 同一 paper claim 的 wrapper / projection / 不同 binder 风格 / 弱化结论等变体 (灰小字, `↪ variant` 缩进), 每 primary 下可多条
- `\leansorryd{Lean.Target.name}{rationale}` — 暂用 sorry (橙) -- 项目 invariant 是 0 sorry, 此宏用于未来如有重新出现; 对应 `formalstatus = formalTargetV`
- `\leanstmt{Lean.Target.name}` — statement-only / structure 字段 (蓝); 对应 `formalstatus = formalTargetV`
- `\leandef{Lean.Target.name}` — `def` 或 `inductive` 定义 (灰); 对应 `formalstatus = encodedDefV`

这些宏只描述 Lean-side 验证状态. 它们不暗示 paper 一侧的 closure 等级.

### Closurestatus 块 (theory × verification 两轴)

每个 `<X>Up` 章末尾用 `closurestatus` 环境记录两轴状态:

```latex
\begin{closurestatus}{\<X>Up}
  \theoryclosure{\scopedClosure}      % paper 一侧理论闭合等级
  \scopeclosed{<一句话写清精确闭合范围>}
  \formalstatus{\theoremCheckedV}     % Lean 一侧验证等级
  \leantarget{BEDC.<...>.<theorem>}  % 必须在 lean4/BEDC/ 真存在
  \bridgestatus{none}                 % none / paperBridge / bridgeChecked
  \notclaimed{<一句话: 本章明确不闭合的内容>}
  \upgradepath{<一句话: 升级到下一闭合等级所需补足>}
\end{closurestatus}
```

闭合等级 (理论轴) 取自 `seed | obligation | scopedClosed | publicClosed | bridgedClosed | maturePackageClosed`, 验证等级取自 `unformalized | formalTarget | encodedDef | scaffoldChecked | theoremChecked | auditClean | axiomClean | bridgeChecked`.

两个轴是**独立的**: paper 闭合不依赖 Lean 验证, Lean 验证也不创造 paper 闭合. 二者只通过 `VerifiedGate(N, c, v) := TheoryGate(N, c) ∧ FormalStatus(N, v)` 同时报告.

### 下划线规则

- 调用 `\leanchecked` / `\leantarget` 等时, underscore 必须写成 `\_`, 例如 `BEDC.BaseReflection.PackageReflection\_base`
- `xstring` 把 `\_` 替换为细空格, PDF 中不显示字面下划线
- 命名空间 `.` 保持字面

### marker 使用纪律

- 每个 Lean 目标在论文中**只标注一次**(primary site)
- 每个 paper 定理点**最多一条 `\leanchecked`** (canonical 主实现); 同 claim 的变体用 `\leanvariant` 标注
- `papers/bedc/parts/proof_obligations/lean_scaffold_contract.tex §41.4` 是例外: 5 个 base-reflection 目标的"一站式"摘要块
- 状态变化时 (sorry → checked, def → checked) 同一 commit 更新 marker; `bedc_ci.py audit` 强制所有 `\leanchecked` / `\leanvariant` / `\leantarget` 的 X 在 Lean 真存在
- **绝不**把 closure 轴写成 verification 轴的函数, 也不要反过来; codex pipeline 的 `axis-confusion` gate 会拒绝这类 round
```

- [ ] **Step 2: Milestone P6 commit**

```bash
git add CLAUDE.md
git commit -m "$(cat <<'EOF'
P6 closure-vs-verification: sync CLAUDE.md vocabulary

Update the project's status-macro and marker-discipline section to
describe the two-axis closurestatus block and the new theoryclosure /
formalstatus tokens. Codex workers reading CLAUDE.md at warm-up now
know that closure and verification are independent axes.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 13 — Final verification + summary

- [ ] **Step 1: Run the five-gate full verification**

```bash
cd lean4 && lake build
cd ../papers/bedc && make
cd ../.. && python3 tools/check-axioms.py
python3 lean4/scripts/bedc_ci.py audit
python3 lean4/scripts/bedc_ci.py axiom-purity --strict
python3 lean4/scripts/test_closurestatus_audit.py
```

Expected: all six exit 0.

- [ ] **Step 2: Confirm the working tree is clean**

```bash
git status -uno
```

Expected: nothing to commit; working tree clean.

- [ ] **Step 3: Confirm no legacy tokens linger**

```bash
grep -rn "checkedCertStr\|paperCertStr\|bridgeCertStr\|seedStr\|AcceptGate\|closureat\|legacy-shim\|four-strength" papers/bedc/ lean4/scripts/ 2>/dev/null | grep -v "logs/" | grep -v "__pycache__"
```

Expected: zero hits. Any hit means a site was missed during P3 or P5; iterate.

- [ ] **Step 4: Confirm the closurestatus blocks count matches the migrated chapters**

```bash
grep -rln "begin{closurestatus}" papers/bedc/parts/ | wc -l
```

Expected: 30 (one per migrated `\closureat` site).

- [ ] **Step 5: Surface the per-axis distribution**

```bash
python3 lean4/scripts/bedc_ci.py audit | grep -E "closurestatus|theory|formal"
```

Expected: every block reports `theoryclosure=scopedClosure formalstatus=theoremCheckedV` (current state); none flagged with diagnostics.

- [ ] **Step 6: Push deferred — confirm with the user before pushing**

The branch is local-only. Per CLAUDE.md, the codex-auto-dev branch has continuously running workers; the merge of `closure-vs-verification` into `codex-auto-dev` is the user's call after they've reviewed the seven commits.

---

## Self-review

- **Spec coverage.** The 20 sections of the user's design document map onto Tasks as follows:
  - §1 (理论闭合 ≠ 形式化) → Task 2 §I; Task 5 §IV (closure reading convention); Task 6 (chapter 04).
  - §2 (五级理论闭合) → Task 1 (preamble macros); Task 2 (definition).
  - §3 (七级形式化状态 + bridgeChecked) → Task 1 macros; Task 2 §II.
  - §4 (TheoryGate / VerifiedGate / FormalStatus 公式语法) → Task 2 §III.
  - §5 (第 146 章改名) → Task 2 (chapter title `Closure and Verification Discipline`).
  - §6 (`\theorystatus` / `\closurestatus` block; "Theory closure / Formal verification / Lean target / Bridge / Not claimed / Upgrade path" 行) → Task 1 env definition; Tasks 7 (per-chapter migrations).
  - §7 (Closure Reading Convention) → Task 5 §IV; Task 6.
  - §8 (per-object table) → Task 6.
  - §9-§13 (per-object 升级 + Field/VecSpace/Determinant/Homology/Cohomology 范围措辞) → Task 7 examples; the per-chapter scope/notclaimed/upgradepath text follows the user's wording.
  - §14 (Anti-confusion list, 15 项) → Task 5 §V (`\sec:anti-confusion-register`).
  - §15 (摘要 / Preface 段落) → Task 7 Step 4.
  - §16 (Roadmap 二维 exit criterion) → Task 7 Step 6.
  - §17 (Appendix B 增加 §B.3 Relation to theoretical closure) → Task 7 Step 5.
  - §18 (审稿人友好措辞 — 不再写 "closed because checked") → Task 11 axis-confusion prompt + Task 10 gate.
  - §19 (Closure / Verification / Export claim 三行最终语法) → Task 2 §III; Task 6.
  - §20 (一句话总结) → Task 2 chapter intro paragraph.
- **Placeholder scan.** Every step contains the actual content; the only `<...>` placeholders are inside templates the engineer fills per chapter (Task 7 Step 2 — explicit per-chapter examples for Nat, VecSpace, Determinant; the rest of the 30 chapters follow the same template). No "TODO", "implement later", "TBD".
- **Type / name consistency.** The closure-axis tokens (`\seedClosure`, `\obligationClosure`, `\scopedClosure`, `\publicClosure`, `\bridgedClosure`, `\matureClosure`) and verification-axis tokens (`\unformalizedV`, `\formalTargetV`, `\encodedDefV`, `\scaffoldCheckedV`, `\theoremCheckedV`, `\auditCleanV`, `\axiomCleanV`, `\bridgeCheckedV`) are used identically across preamble macros, chapter prose, audit Python regex (`VALID_CLOSURE_GRADES` / `VALID_FORMAL_GRADES`), and prompt templates. Field names inside `closurestatus` (`theoryclosure` / `formalstatus` / `leantarget` / `bridgestatus` / `scopeclosed` / `notclaimed` / `upgradepath`) match between LaTeX env, audit regex, prompt templates, and CLAUDE.md.

---

## Execution handoff

**Plan complete and saved to `docs/superpowers/plans/2026-05-05-bedc-closure-vs-verification.md`. Two execution options:**

1. **Subagent-Driven (recommended)** — I dispatch a fresh subagent per Task (Tasks 1-12 each become an independent run). Reviews land between tasks; the milestone commits act as natural checkpoints. Best when the user wants minimum context in the orchestrating session.

2. **Inline Execution** — I execute Tasks 1-12 in the current session using the `superpowers:executing-plans` skill, with checkpoints at each milestone commit. Best when the user wants to watch the migration unfold and intervene mid-stream (e.g.\ to refine the per-chapter scope/notclaimed text in Task 7).

Note: the codex pipeline runs continuously on `codex-auto-dev`. While this branch (`closure-vs-verification`) is local, the eventual merge has to follow CLAUDE.md's `git fetch && git merge` (not rebase) discipline and pick a quiet window per `gh run list --branch codex-auto-dev --limit 5`.

**Which approach?**
