from itertools import combinations

from bedc_quality_lab.ledger import (
    LedgerEntry,
    LedgerRowKey,
    critical_gap,
    ledger_complete,
    ledger_debt,
    ledger_gap,
    recorded_rows,
    required_rows,
)


UNIVERSE = (
    LedgerRowKey("source", "source-coverage"),
    LedgerRowKey("classifier", "optimizer-certificate"),
    LedgerRowKey("verification", "proof-backend"),
    LedgerRowKey("semantic", "label-boundary"),
)


def powerset(rows):
    for size in range(len(rows) + 1):
        for members in combinations(rows, size):
            yield frozenset(members)


def test_thm_ledger_completeness_gap_free():
    """thm:philosophy-ledger-completeness-gap-free; Lean: BEDC.GroundCompiler.NameCertGenerated.LedgerCompleteNameCertFlow and BEDC.GroundCompiler.ChapterFlow.LedgerSound."""
    for required in powerset(UNIVERSE):
        for recorded in powerset(UNIVERSE):
            gap = ledger_gap(required, recorded)

            assert ledger_complete(required, recorded) == (gap == frozenset())

    required = {UNIVERSE[0]}
    assert ledger_complete(required, required)
    assert not ledger_complete(required, frozenset())


def test_thm_ledger_extension_no_new_fixed_gaps():
    """thm:philosophy-ledger-extension-no-new-fixed-gaps; Lean: BEDC.GroundCompiler.ChapterFlow.LedgerSound."""
    for required in powerset(UNIVERSE):
        for recorded in powerset(UNIVERSE):
            for extension in powerset(UNIVERSE):
                if recorded.issubset(extension):
                    assert ledger_gap(required, extension).issubset(ledger_gap(required, recorded))

    required = {UNIVERSE[0], UNIVERSE[1]}
    recorded = {UNIVERSE[0]}
    extended = {UNIVERSE[0], UNIVERSE[1]}
    assert ledger_gap(required, extended) == frozenset()
    assert ledger_gap(required, recorded) == frozenset({UNIVERSE[1]})


def test_thm_complete_ledger_zero_debt():
    """thm:philosophy-complete-ledger-zero-debt; Lean: BEDC.GroundCompiler.NameCertGenerated.certified_derived_carry_ledger."""
    cost_map = {row: float(index + 1) for index, row in enumerate(UNIVERSE)}
    for required in powerset(UNIVERSE):
        for recorded in powerset(UNIVERSE):
            gap = ledger_gap(required, recorded)
            if ledger_complete(required, recorded):
                assert ledger_debt(gap, cost_map) == 0.0

    required = {UNIVERSE[0]}
    assert ledger_debt(ledger_gap(required, required), cost_map) == 0.0
    assert ledger_debt(ledger_gap(required, frozenset()), cost_map) > 0.0


def test_thm_ledger_debt_monotone_extension():
    """thm:philosophy-ledger-debt-monotone-extension; Lean: BEDC.GroundCompiler.ChapterFlow.LedgerSound and BEDC.GroundCompiler.MetricsFlow.LedgerDepth."""
    cost_map = {
        UNIVERSE[0]: 0.0,
        UNIVERSE[1]: 0.25,
        UNIVERSE[2]: 0.5,
        UNIVERSE[3]: 1.0,
    }
    for required in powerset(UNIVERSE):
        for recorded in powerset(UNIVERSE):
            for extension in powerset(UNIVERSE):
                if recorded.issubset(extension):
                    original = ledger_debt(ledger_gap(required, recorded), cost_map)
                    extended = ledger_debt(ledger_gap(required, extension), cost_map)
                    assert extended <= original

    required = {UNIVERSE[1], UNIVERSE[2]}
    recorded = {UNIVERSE[1]}
    extended = {UNIVERSE[1], UNIVERSE[2]}
    assert ledger_debt(ledger_gap(required, extended), cost_map) < ledger_debt(
        ledger_gap(required, recorded),
        cost_map,
    )


def test_thm_critical_debt_blocks_strong_claims():
    """thm:philosophy-critical-debt-blocks-strong-claims; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertLedgerSoundnessEvent."""
    critical_entries = (
        LedgerEntry(UNIVERSE[0], "source-ledger", 0.18, critical=True),
        LedgerEntry(UNIVERSE[1], "classifier-ledger", 0.20, critical=True),
        LedgerEntry(UNIVERSE[2], "verification-ledger", 0.30, critical=False),
    )
    required = required_rows(critical_entries)

    for recorded in powerset(UNIVERSE):
        gap_rows = ledger_gap(required, recorded)
        gap_entries = tuple(entry for entry in critical_entries if entry.row in gap_rows)
        strong_claim_closed = not critical_gap(gap_entries)

        assert strong_claim_closed == all(
            entry.row in recorded for entry in critical_entries if entry.critical
        )

    assert critical_gap((critical_entries[0],)) == frozenset({UNIVERSE[0]})
    assert critical_gap((critical_entries[2],)) == frozenset()


def test_thm_ledger_kinds_not_substitutable():
    """thm:philosophy-ledger-kinds-not-substitutable; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertFieldRole.ledger and BEDC.GroundCompiler.ChapterFlow.ChapLedger."""
    shared_residue = "boundary"
    verification = LedgerRowKey("verification", shared_residue)
    behavior = LedgerRowKey("behavior", shared_residue)
    classifier = LedgerRowKey("classifier", shared_residue)
    semantic = LedgerRowKey("semantic", shared_residue)
    intervention = LedgerRowKey("intervention", shared_residue)
    other_kinds = (behavior, classifier, semantic, intervention)
    local_universe = (verification, *other_kinds)

    for recorded in powerset(local_universe):
        for required in powerset(other_kinds):
            gap = ledger_gap(required, recorded)
            expected = required - recorded
            assert gap == expected

    for row in other_kinds:
        assert ledger_gap({row}, {verification}) == frozenset({row})
        assert recorded_rows((LedgerEntry(verification, "verification-ledger"),)) != recorded_rows(
            (LedgerEntry(row, f"{row.kind}-ledger"),)
        )
