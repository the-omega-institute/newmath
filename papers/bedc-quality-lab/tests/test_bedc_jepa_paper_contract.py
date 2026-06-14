from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "bedc_jepa"


def _tex_files() -> list[Path]:
    return [PAPER / "main.tex", *sorted((PAPER / "parts").glob("*.tex"))]


def test_bedc_jepa_paper_avoids_engineering_status_prose():
    forbidden = [
        "blocked",
        "blocking gate",
        "not_contact_ready",
        "checkpoint-contact",
        "external-contact",
        "artifact pointers",
        "JSON artifacts",
        "legacy",
        "deprecated",
        "supersede",
        "migration",
        "v1.5",
        "patch",
    ]
    offenders: list[tuple[str, str]] = []

    for path in _tex_files():
        text = path.read_text(encoding="utf-8")
        lowered = text.lower()
        for term in forbidden:
            if term.lower() in lowered:
                offenders.append((str(path.relative_to(ROOT)), term))

    assert offenders == []


def test_bedc_jepa_paper_uses_project_math_display_style():
    forbidden = [
        "\\[",
        "\\]",
        "\\begin{equation}",
        "\\begin{equation*}",
        "\\begin{align}",
        "\\begin{align*}",
        "\\begin{eqnarray}",
        "\\begin{eqnarray*}",
    ]
    offenders: list[tuple[str, str]] = []

    for path in _tex_files():
        text = path.read_text(encoding="utf-8")
        for token in forbidden:
            if token in text:
                offenders.append((str(path.relative_to(ROOT)), token))

    assert offenders == []


def test_bedc_jepa_tex_files_stay_below_project_line_limit():
    too_long = [
        (str(path.relative_to(ROOT)), len(path.read_text(encoding="utf-8").splitlines()))
        for path in _tex_files()
        if len(path.read_text(encoding="utf-8").splitlines()) > 800
    ]

    assert too_long == []


def test_bedc_jepa_paper_records_current_minigrid_calibration_scope():
    evidence = (PAPER / "parts" / "evidence_packet.tex").read_text(encoding="utf-8")
    boundary = (PAPER / "parts" / "cannot_claim_boundary.tex").read_text(encoding="utf-8")

    assert "Public baseline metric template" in evidence
    assert "analysis over $75$ executed rows" in evidence
    assert "five seeds, three planning-state budgets" in evidence
    assert "\\texttt{MiniGrid-DoorKey-5x5-v0}" in evidence
    assert "\\texttt{MiniGrid-DoorKey-6x6-v0}" in evidence
    assert "\\texttt{MiniGrid-Unlock-v0}" in evidence
    assert "\\texttt{MiniGrid-KeyCorridorS3R1-v0}" in evidence
    assert "$0.482848$" in evidence
    assert "$-0.051649$" in evidence
    assert "analysis over $12$ executed rows" not in evidence
    assert "$0.359776$" not in evidence
    assert "fillable metric template" in boundary
