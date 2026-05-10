import BEDC.FKernel.Cont

namespace BEDC.Derived.HaltingDistinctionLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

structure SourceRow where
  query : BHist
  fuel : BHist
  result : BHist
  terminationLedger : BHist
  diagonalBranch : BHist
  diagonalResult : BHist
  obstructionLedger : BHist

def SourceRows : Type := SourceRow

def Pattern (s : SourceRows) : Prop :=
  Cont s.query s.fuel s.result ∧
    Cont s.query s.result s.terminationLedger ∧
      Cont s.query s.terminationLedger s.diagonalBranch ∧
        Cont s.diagonalBranch s.query s.diagonalResult ∧
          Cont s.diagonalResult s.terminationLedger s.obstructionLedger

def Classifier (s t : SourceRows) : Prop :=
  hsame s.query t.query ∧
    hsame s.fuel t.fuel ∧
      hsame s.result t.result ∧
        hsame s.terminationLedger t.terminationLedger ∧
          hsame s.diagonalBranch t.diagonalBranch ∧
            hsame s.diagonalResult t.diagonalResult ∧
              hsame s.obstructionLedger t.obstructionLedger

theorem stability {s t : SourceRows} :
    Classifier s t -> Pattern s -> Pattern t := by
  cases s with
  | mk query fuel result terminationLedger diagonalBranch diagonalResult obstructionLedger =>
  cases t with
  | mk query' fuel' result' terminationLedger' diagonalBranch' diagonalResult'
      obstructionLedger' =>
  intro same pattern
  cases same with
  | intro sameQuery rest =>
      cases rest with
      | intro sameFuel rest =>
          cases rest with
          | intro sameResult rest =>
              cases rest with
              | intro sameTerminationLedger rest =>
                  cases rest with
                  | intro sameDiagonalBranch rest =>
                      cases rest with
                      | intro sameDiagonalResult sameObstructionLedger =>
                          cases sameQuery
                          cases sameFuel
                          cases sameResult
                          cases sameTerminationLedger
                          cases sameDiagonalBranch
                          cases sameDiagonalResult
                          cases sameObstructionLedger
                          exact pattern

structure LedgerRow where
  source : SourceRows
  terminationTrace : BHist
  diagonalTrace : BHist
  publicEndpoint : BHist

def Ledger : Type := LedgerRow

end BEDC.Derived.HaltingDistinctionLimitUp
