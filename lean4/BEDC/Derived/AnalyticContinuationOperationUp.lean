import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AnalyticContinuationOperationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

structure AnalyticContinuationOperationCarrier where
  domainLeft : BHist
  domainRight : BHist
  inputLeft : BHist
  inputRight : BHist
  overlap : BHist
  operation : BHist
  output : BHist
  ledger : BHist
  transport : BHist
  route : BHist
  pkg : BHist
  name : BHist
  domain_input_overlap : Cont domainLeft inputLeft overlap
  operation_overlap_output : Cont operation overlap output
  right_input_ledger : Cont domainRight inputRight ledger
  transport_names_output : hsame transport output
  package_names_ledger : hsame pkg ledger
  name_names_overlap : hsame name overlap
  name_names_output : hsame name output

namespace AnalyticContinuationOperationCarrier

def SourceSpec (p : AnalyticContinuationOperationCarrier) (row : BHist) : Prop :=
  hsame row p.name ∧ Cont p.domainLeft p.inputLeft p.overlap ∧
    Cont p.operation p.overlap p.output

def PatternSpec (p : AnalyticContinuationOperationCarrier)
    (_inputRoute : Cont p.domainLeft p.inputLeft p.overlap) (row : BHist) : Prop :=
  hsame row p.overlap ∧ Cont p.domainLeft p.inputLeft p.overlap

def LedgerPolicy (p : AnalyticContinuationOperationCarrier)
    (_outputRoute : Cont p.operation p.overlap p.output) (row : BHist) : Prop :=
  hsame row p.output ∧ hsame p.transport p.output ∧ Cont p.operation p.overlap p.output

end AnalyticContinuationOperationCarrier

theorem AnalyticContinuationOperationCarrier_namecert_obligations
    (p : AnalyticContinuationOperationCarrier)
    (inputRoute : Cont p.domainLeft p.inputLeft p.overlap)
    (outputRoute : Cont p.operation p.overlap p.output) :
    SemanticNameCert (AnalyticContinuationOperationCarrier.SourceSpec p)
      (AnalyticContinuationOperationCarrier.PatternSpec p inputRoute)
      (AnalyticContinuationOperationCarrier.LedgerPolicy p outputRoute) hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro p.name
        (And.intro (hsame_refl p.name)
          (And.intro p.domain_input_overlap p.operation_overlap_output))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro (hsame_trans (hsame_symm same) sourceRow.left) sourceRow.right
    }
    pattern_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.left p.name_names_overlap) inputRoute
    ledger_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.left p.name_names_output)
        (And.intro p.transport_names_output outputRoute)
  }

end BEDC.Derived.AnalyticContinuationOperationUp
