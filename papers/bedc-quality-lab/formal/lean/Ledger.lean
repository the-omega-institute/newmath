import Mathlib.Data.List.Basic

namespace Ledger

inductive RowKey where
  | classifierEquivalence
  | marginStability
  | finiteCoverage
  | missingEvidence
  deriving DecidableEq, Repr

structure RecordedRow where
  key : RowKey
  label : String
  deriving Repr

def requiredRows : List RowKey :=
  [ RowKey.classifierEquivalence
  , RowKey.marginStability
  , RowKey.finiteCoverage
  , RowKey.missingEvidence
  ]

theorem classifierEquivalence_required :
    RowKey.classifierEquivalence ∈ requiredRows := by
  simp [requiredRows]

theorem marginStability_required :
    RowKey.marginStability ∈ requiredRows := by
  simp [requiredRows]

theorem finiteCoverage_required :
    RowKey.finiteCoverage ∈ requiredRows := by
  simp [requiredRows]

theorem missingEvidence_required :
    RowKey.missingEvidence ∈ requiredRows := by
  simp [requiredRows]

def IsRequired (key : RowKey) : Prop :=
  key ∈ requiredRows

def recordedContains (rows : List RecordedRow) (key : RowKey) : Prop :=
  key ∈ rows.map (fun row => row.key)

def CoversRequired (rows : List RecordedRow) : Prop :=
  ∀ key, IsRequired key → recordedContains rows key

def mem_required_decidable (key : RowKey) :
    Decidable (IsRequired key) := by
  unfold IsRequired
  exact inferInstanceAs (Decidable (key ∈ requiredRows))

theorem required_or_not_required (key : RowKey) :
    IsRequired key ∨ ¬ IsRequired key := by
  exact @Decidable.em (IsRequired key) (mem_required_decidable key)

theorem requiredRows_complete (key : RowKey) :
    IsRequired key := by
  cases key <;> simp [IsRequired, requiredRows]

end Ledger
