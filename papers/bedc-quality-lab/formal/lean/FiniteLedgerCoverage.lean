import Ledger

namespace FiniteLedgerCoverage

open Ledger

def recordedWitnesses : List RecordedRow :=
  [ { key := RowKey.classifierEquivalence, label := "Classifier.sameClass_equivalence" }
  , { key := RowKey.marginStability, label := "MarginStability.mark_stable_of_margin" }
  , { key := RowKey.finiteCoverage, label := "FiniteLedgerCoverage.coverage_of_recorded_witnesses" }
  , { key := RowKey.missingEvidence, label := "FiniteLedgerCoverage.missingRow_not_covered" }
  ]

def missingEvidenceRows : List RecordedRow :=
  [ { key := RowKey.classifierEquivalence, label := "Classifier.sameClass_equivalence" }
  , { key := RowKey.marginStability, label := "MarginStability.mark_stable_of_margin" }
  , { key := RowKey.finiteCoverage, label := "FiniteLedgerCoverage.coverage_of_recorded_witnesses" }
  ]

private theorem classifier_witness_recorded :
    recordedContains recordedWitnesses RowKey.classifierEquivalence := by
  simp [recordedContains, recordedWitnesses]

private theorem margin_witness_recorded :
    recordedContains recordedWitnesses RowKey.marginStability := by
  simp [recordedContains, recordedWitnesses]

private theorem coverage_witness_recorded :
    recordedContains recordedWitnesses RowKey.finiteCoverage := by
  simp [recordedContains, recordedWitnesses]

private theorem missing_witness_recorded :
    recordedContains recordedWitnesses RowKey.missingEvidence := by
  simp [recordedContains, recordedWitnesses]

private theorem missing_witness_absent :
    ¬ recordedContains missingEvidenceRows RowKey.missingEvidence := by
  simp [recordedContains, missingEvidenceRows]

theorem coverage_of_recorded_witnesses :
    CoversRequired recordedWitnesses := by
  intro key hrequired
  cases key <;>
    simp [IsRequired, recordedContains, requiredRows, recordedWitnesses] at *

theorem missingRow_not_covered :
    ¬ CoversRequired missingEvidenceRows := by
  intro hcoverage
  have hrequired : IsRequired RowKey.missingEvidence := by
    simp [IsRequired, requiredRows]
  have hrecorded := hcoverage RowKey.missingEvidence hrequired
  simp [recordedContains, missingEvidenceRows] at hrecorded

theorem negative_example_has_required_missing_row :
    IsRequired RowKey.missingEvidence ∧
      ¬ recordedContains missingEvidenceRows RowKey.missingEvidence := by
  constructor
  · simp [IsRequired, requiredRows]
  · exact missing_witness_absent

end FiniteLedgerCoverage
