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

end Ledger
