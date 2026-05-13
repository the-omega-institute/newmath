# BEDC Deep Reasoning Board

Purpose: drive a self-iterating BEDC paper-extension loop. Each entry below is
a target the oracle deep-reasoning loop runs to a complete result, then
appends as canonical current-state LaTeX into `papers/bedc/parts/`. The
downstream `lean4/scripts/codex_formalize.py` lane (on dev) picks up new
theorem sites by scanning the paper.

Lane edge:
- This lane never edits `lean4/`. The handshake to formalization is the
  appended LaTeX in `papers/bedc/parts/<theme>/<concept>.tex` (no marker
  macros — those are added by `codex_formalize.py` after the Lean target lands).
- New targets are auto-spawned by Stage 1.5 topic discovery and appended to
  this board with `Status: Candidate (auto-spawned)`.

Each target card carries enough context (Object, Local inputs) for the loop
to build its initial prompt without external lookups.

---

### B-719 - CofinalRegularLimitBudget window-route determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CofinalRegularLimitBudget window-route determinacy |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If a CofinalRegularLimitBudget carrier routes the same precision request through two displayed cofinal-window ledgers to the same RegSeqRat and RealUp seal rows, then the two window ledgers are hsame under the carrier transport ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/3409_cofinalregularlimitbudget_namecert_construction.tex`

Rationale:
The carrier is a finite packet B=(q,w,r,e,h,c,p,n) with q as the precision request, w as the cofinal-window ledger, r as RegSeqRat handoff, e as RealUp seal, h as componentwise hsame transports, and c as the displayed Cont route at papers/bedc/parts/concrete_instances/3409_cofinalregularlimitbudget_namecert_construction.tex:7-24. The existing theorem at lines 27-37 lists carrier admission, cofinal-window coverage, handoff, seal routing, and non-escape, but it does not state uniqueness or determinacy of w for a shared request-route endpoint. Focused rg for CofinalRegularLimitBudget found only this chapter, its index input, and one vision concretization reference; there is no separate theorem label for window determinacy or cofinal-window uniqueness. The claim is a finite route determinacy theorem about the existing budget packet and its displayed hsame/Cont rows.

---

