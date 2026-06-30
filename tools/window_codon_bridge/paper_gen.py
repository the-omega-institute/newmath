#!/usr/bin/env python3
"""Generate the Window6--codon-Q6 bridge paper from bridge registries."""
from __future__ import annotations

import json
import re
import textwrap
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
CLAIMS = SCRIPT_DIR / "registries" / "claims.json"
EXPERIMENTS = SCRIPT_DIR / "registries" / "experiments.json"
LEDGER = REPO_ROOT / "papers" / "window_codon_bridge" / "bridge_ledger.jsonl"
PAPER_DIR = REPO_ROOT / "papers" / "window_codon_bridge"
PARTS_DIR = PAPER_DIR / "parts"

STATUS_WORDS = {"certified", "refuted", "coincidence", "needs_derivation"}
BIO_DIRECTIONS = {"bio->bridge", "orchestrator->bridge"}


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def load_ledger(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        raw = line.strip()
        if not raw:
            continue
        try:
            rows.append(json.loads(raw))
        except json.JSONDecodeError as exc:
            raise SystemExit(f"{path}:{line_no}: invalid JSONL row: {exc}") from exc
    return rows


def tex_escape(text: Any) -> str:
    s = str(text if text is not None else "")
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(ch, ch) for ch in s)


def normalize_ascii(text: Any) -> str:
    s = str(text if text is not None else "")
    replacements = {
        "→": " -> ",
        "↔": " <-> ",
        "≥": ">=",
        "≤": "<=",
        "≈": "~",
        "≠": "!=",
        "×": " x ",
        "φ": "phi",
        "λ": "lambda",
        "μ": "mu",
        "ρ": "rho",
        "−": "-",
        "–": "--",
        "—": "--",
        "“": '"',
        "”": '"',
        "‘": "'",
        "’": "'",
        "₆": "6",
        "₇": "7",
        "₈": "8",
        "₉": "9",
        "¹": "1",
        "²": "2",
        "³": "3",
    }
    for old, new in replacements.items():
        s = s.replace(old, new)
    s = s.encode("ascii", "ignore").decode("ascii")
    s = re.sub(r"\.v[0-9]+\b", "", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def tex(text: Any) -> str:
    return tex_escape(normalize_ascii(text))


def wrap_paragraph(text: Any) -> str:
    s = tex(text)
    return textwrap.fill(s, width=100, break_long_words=False, break_on_hyphens=False)


def mathize(s: str) -> str:
    replacements = [
        (r"Q\textasciicircum{}(2)", r"$Q^{(2)}$"),
        (r"mu=6*lambda\_M-1", r"$\mu=6\lambda_M-1$"),
        (r"lambda\_M/lambda\_R/mu", r"$\lambda_M/\lambda_R/\mu$"),
        (r"lambda\_M", r"$\lambda_M$"),
        (r"lambda\_R", r"$\lambda_R$"),
        (r"d\_perp", r"$d_{\perp}$"),
        (r"U\_R", r"$U_R$"),
        (r"|dU\_R|/(6|U\_R|)=8/9", r"$|dU_R|/(6|U_R|)=8/9$"),
        (r"rho6-s6=3", r"$\rho_6-s_6=3$"),
        (r"w1=w6=1", r"$w_1=w_6=1$"),
        (r"|R|=13=F7", r"$|R|=13=F_7$"),
        (r"X6=21=F8", r"$X_6=21=F_8$"),
        (r"21=F8", r"$21=F_8$"),
        (r"13=F7", r"$13=F_7$"),
        (r"Fibonacci cube Gamma6/Gamma5", r"Fibonacci cubes $\Gamma_6/\Gamma_5$"),
        (r"|M|=20", r"$|M|=20$"),
        (r"|Gamma6|=21", r"$|\Gamma_6|=21$"),
        (r"x\textasciicircum{}2-x-1", r"$x^2-x-1$"),
    ]
    for old, new in replacements:
        s = s.replace(old, new)
    return s


def tex_content(text: Any) -> str:
    return mathize(tex(text))


def wrap_content(text: Any) -> str:
    s = tex_content(text)
    return textwrap.fill(s, width=100, break_long_words=False, break_on_hyphens=False)


def sentence_from_history(claim: dict[str, Any], ledger_by_id: dict[str, dict[str, Any]]) -> str:
    history = claim.get("history") or []
    latest = history[-1] if history else {}
    reason = latest.get("reason") or latest.get("note")
    if not reason:
        reason = ledger_by_id.get(str(claim.get("claim_id")), {}).get("note")
    if not reason:
        reason = "No derivation note is recorded yet."
    reason = normalize_ascii(reason)
    pieces = re.split(r"(?<=[.!?])\s+", reason)
    for piece in pieces:
        piece = piece.strip()
        if piece:
            return piece
    return reason[:240]


def claim_short_name(claim_id: str) -> str:
    tail = claim_id.rsplit(".", 1)[-1]
    words = [w for w in tail.split("_") if w]
    return " ".join(w.capitalize() for w in words) or claim_id


def label_for_claim(claim_id: str) -> str:
    tail = claim_id.rsplit(".", 1)[-1]
    return re.sub(r"[^a-z0-9-]+", "-", tail.replace("_", "-").lower()).strip("-")


def latest_by_id(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in rows:
        ident = row.get("id")
        if ident:
            out[str(ident)] = row
    return out


def experiment_map(experiments_doc: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        str(exp.get("experiment_id")): exp
        for exp in experiments_doc.get("experiments", [])
        if exp.get("experiment_id")
    }


def ledger_bio_inputs(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    for row in rows:
        direction = str(row.get("direction") or "")
        ident = str(row.get("id") or "")
        if direction != "bio->bridge":
            continue
        if ident.startswith("BIO-") or ident.startswith("BC5-DATA"):
            selected.append(row)
    return selected


def main_tex() -> str:
    return r"""\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{microtype}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{array}
\usepackage{longtable}
\usepackage{hyperref}

% BEDC-style macros stubbed for the standalone bridge paper.
\newcommand{\origin}[1]{}
\newcommand{\closureat}[2]{}
\providecommand{\path}{}\renewcommand{\path}[1]{\texttt{\detokenize{#1}}}
\providecommand{\WindowSix}{\mathrm{Window6}}
\providecommand{\CodonQSix}{\mathrm{Codon}\mbox{-}Q_6}
\newtheorem{definition}{Definition}[section]
\newtheorem{theorem}[definition]{Theorem}
\newtheorem{lemma}[definition]{Lemma}
\newtheorem{proposition}[definition]{Proposition}

\title{Window6--Codon-Q6 Bridge: Forced-Correspondence Certificates and Anti-Numerology Verdicts}
\author{The Omega Institute}
\date{}

\begin{document}
\maketitle

\origin{ai}
\closureat{\WindowSix}{scoped}

\input{parts/scope}
\input{parts/correspondences}
\input{parts/bio_inputs}
\input{parts/synthesis}

\end{document}
"""


def scope_tex() -> str:
    return r"""\section{Scope}
The Window6--codon-Q6 bridge is a certificate factory between two finite objects that
are already constructed elsewhere: the forced Window6 Fibonacci horizon on the
mathematical side and the codon-Q6 boundary organization on the biological side.  The
bridge does not promote a numerical resemblance to a biological conclusion.  It records
only verdicts produced by the bridge registries and the bridge ledger.

A forced-correspondence certificate means an explicit structural map between the two
finite carriers together with a necessity argument showing that the biological quantity
is forced by the mathematical structure under that map.  A naked equality of numbers,
including a Fibonacci or golden-ratio shaped equality, is only a prompt for a certificate.
It is not a certificate.

The verdict vocabulary is fixed by the bridge daemon.  A verdict of \texttt{certified}
means that a structural forcing argument is recorded.  A verdict of \texttt{refuted}
means that the proposed correspondence is false in the tested structural form.  A
verdict of \texttt{coincidence} means that numbers may match, but no structural forcing
argument is present.  A verdict of \texttt{needs\_derivation} means that the bridge lacks
the derivation or input needed to decide the claim.

This paper is generated from \path{tools/window_codon_bridge/registries/claims.json},
\path{tools/window_codon_bridge/registries/experiments.json}, and
\path{papers/window_codon_bridge/bridge_ledger.jsonl}.  The generated text is therefore
a view of the pipeline state, not a separate source of truth.
"""


def correspondences_tex(
    claims_doc: dict[str, Any],
    experiments_doc: dict[str, Any],
    ledger_rows: list[dict[str, Any]],
) -> str:
    claims = list(claims_doc.get("claims", []))
    exp_by_id = experiment_map(experiments_doc)
    ledger_by_id = latest_by_id(ledger_rows)
    lines: list[str] = [
        r"\section{Bridge Correspondence Verdicts}",
        "The following table lists every bridge claim in the registry.  The verdict column is",
        "generated directly from the registry status field.",
        "",
        r"\begin{longtable}{>{\raggedright\arraybackslash}p{0.22\linewidth}>{\raggedright\arraybackslash}p{0.55\linewidth}>{\raggedright\arraybackslash}p{0.15\linewidth}}",
        r"\textbf{Claim} & \textbf{Statement} & \textbf{Verdict} \\",
        r"\hline",
    ]
    for claim in claims:
        cid = str(claim.get("claim_id") or "")
        status = str(claim.get("status") or "")
        lines.append(
            rf"% CLAIM_STATUS claim_id={cid} status={status}"
        )
        lines.append(
            rf"{tex(claim_short_name(cid))} & {tex_content(claim.get('statement', ''))} & \texttt{{{tex(status)}}} \\"
        )
    lines.extend([r"\end{longtable}", ""])

    for claim in claims:
        cid = str(claim.get("claim_id") or "")
        status = str(claim.get("status") or "")
        exp = exp_by_id.get(str(claim.get("experiment_id") or ""), {})
        why = sentence_from_history(claim, ledger_by_id)
        if not why.endswith((".", "!", "?")):
            why += "."
        lines.extend(
            [
                rf"\subsection{{{tex(claim_short_name(cid))}}}\label{{sec:bridge-{label_for_claim(cid)}}}",
                rf"% CLAIM_DETAIL claim_id={cid} status={status}",
                rf"\textbf{{Statement.}} {wrap_content(claim.get('statement', ''))}",
                "",
                rf"\textbf{{Verdict.}} \texttt{{{tex(status)}}}.",
                "",
                rf"\textbf{{Why.}} {wrap_content(why)}",
                "",
            ]
        )
        script_path = exp.get("script_path")
        if script_path:
            lines.append(rf"\textbf{{Derivation script.}} {wrap_paragraph(script_path)}")
            lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def bio_inputs_tex(ledger_rows: list[dict[str, Any]]) -> str:
    selected = ledger_bio_inputs(ledger_rows)
    lines: list[str] = [
        r"\section{Biological Inputs Returned to the Bridge}",
        "The bridge ledger records biological reality contact as incoming constraints on the",
        "mathematical certificate search.  The entries below are generated from ledger rows with",
        r"\texttt{bio->bridge} direction.",
        "",
    ]
    if not selected:
        lines.append("No biological input rows are currently recorded in the ledger.")
        return "\n".join(lines).rstrip() + "\n"

    for row in selected:
        ident = str(row.get("id") or "ledger-input")
        status = str(row.get("status") or "")
        item = row.get("item") or ""
        note = row.get("note") or row.get("ask") or row.get("ref") or ""
        lines.extend(
            [
                rf"\subsection{{{tex(ident)}}}",
                rf"\textbf{{Status.}} \texttt{{{tex(status)}}}.",
                "",
                wrap_content(item),
            ]
        )
        if note:
            lines.extend(["", wrap_content(note)])
        linked = row.get("linked_bio_experiment")
        if linked:
            lines.extend(["", rf"\textbf{{Linked biological experiment.}} {tex(linked)}."])
        ref = row.get("ref")
        if ref:
            lines.extend(["", rf"\textbf{{Reference.}} {tex(ref)}."])
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def synthesis_tex(claims_doc: dict[str, Any], ledger_rows: list[dict[str, Any]]) -> str:
    claims = claims_doc.get("claims", [])
    status_by_tail = {
        str(c.get("claim_id", "")).rsplit(".", 1)[-1]: str(c.get("status") or "")
        for c in claims
    }
    bio_rows = ledger_bio_inputs(ledger_rows)
    trna = next((r for r in bio_rows if str(r.get("id")) == "BIO-N-OPT-TRNA"), None)
    f3 = next((r for r in bio_rows if str(r.get("id")) == "BIO-O-RESIDUAL-F3"), None)
    usage = next((r for r in bio_rows if str(r.get("id")) == "BIO-Q-THIRD-AXIS-ID"), None)
    rtrna = next((r for r in bio_rows if str(r.get("id")) == "BIO-M-RTRNA"), None)

    lines = [
        r"\section{Synthesis}",
        "The bridge verdicts separate Window6 mathematics from codon biology without",
        "collapsing either side into numerology.  The cardinality claim is currently",
        rf"\texttt{{{tex(status_by_tail.get('cardinality_forcing', 'unknown'))}}}; the two spectral",
        "claims are refuted in the coarse Markov and killed-walk forms; the foldbin-to-codon",
        rf"position claim is \texttt{{{tex(status_by_tail.get('foldbin_codon_positions', 'unknown'))}}};",
        "and the cyclic sector frame claim is refuted.  These negative and coincidence",
        "verdicts are first-class bridge outputs: they prevent the paper from treating",
        "Fibonacci-shaped counts, golden-looking scalars, or three-coordinate analogies as",
        "biological structure without a forcing certificate.",
        "",
        "The resulting current-state conclusion is that the golden and Fibonacci structure",
        "belongs to the Window6 constraint side in the tested cardinality, spectral, foldbin,",
        "and cyclic dimensions.  The biological side does have a real organization, but the",
        "ledger identifies it as a selection geometry rather than as a direct Fibonacci image.",
    ]

    facts: list[str] = []
    if rtrna:
        facts.append("the boundary set $R$ is recorded as tRNA-poor")
    if trna:
        facts.append("tRNA-supply is recorded as a major universal optimality axis")
    if f3:
        facts.append("$f_3$-ramp selection is recorded as a residual translational-selection axis")
    if usage:
        facts.append("usage-frequency is recorded as the provisional third universal axis $d_{\\perp}$")
    if facts:
        lines.extend(["", "In the current ledger, " + tex("; ".join(facts)) + "."])

    lines.extend(
        [
            "",
            "Thus the bridge paper records a conservative synthesis.  Window6 supplies strong",
            "finite mathematical constraints.  Codon-Q6 supplies biological contact through",
            "tRNA-supply, the $f_3$ ramp, and the usage-frequency residual axis.  A bridge claim",
            "can become certified only when it gives a structure-respecting map and a forcing",
            "argument across those carriers.  Until then, a match remains either refuted, a",
            "coincidence, or a derivation target.",
        ]
    )
    return "\n".join(lines).rstrip() + "\n"


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main() -> int:
    claims_doc = load_json(CLAIMS)
    experiments_doc = load_json(EXPERIMENTS)
    ledger_rows = load_ledger(LEDGER)

    write(PAPER_DIR / "main.tex", main_tex())
    write(PARTS_DIR / "scope.tex", scope_tex())
    write(PARTS_DIR / "correspondences.tex", correspondences_tex(claims_doc, experiments_doc, ledger_rows))
    write(PARTS_DIR / "bio_inputs.tex", bio_inputs_tex(ledger_rows))
    write(PARTS_DIR / "synthesis.tex", synthesis_tex(claims_doc, ledger_rows))
    print(f"[paper-gen] wrote {PAPER_DIR.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
