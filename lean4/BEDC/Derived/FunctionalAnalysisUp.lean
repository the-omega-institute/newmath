import BEDC.Derived.BanachUp
import BEDC.Derived.LinearMapUp
import BEDC.Derived.RealUp.Core
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FunctionalAnalysisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.BanachUp
open BEDC.Derived.LinearMapUp
open BEDC.Derived.RealUp

def FunctionalAnalysisBoundedOperatorRow
    (f source target bound ledger : BHist) : Prop :=
  LinearMapSingletonCarrier f ∧ BanachSingletonCarrier source ∧
    BanachSingletonCarrier target ∧
      RealConstantHistoryClassifier bound (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        Cont source target ledger

theorem FunctionalAnalysisBoundedOperatorRow_visible_ledger
    {f source target bound ledger : BHist} :
    FunctionalAnalysisBoundedOperatorRow f source target bound ledger ->
      LinearMapSingletonCarrier f ∧ BanachSingletonCarrier source ∧
        BanachSingletonCarrier target ∧
          RealConstantHistoryClassifier bound (BHist.e1 (BHist.e1 BHist.Empty)) ∧
            Cont source target ledger ∧ UnaryHistory ledger := by
  intro row
  have sourceUnary : UnaryHistory source := by
    exact unary_transport unary_empty (hsame_symm row.right.left.left)
  have targetUnary : UnaryHistory target := by
    exact unary_transport unary_empty (hsame_symm row.right.right.left.left)
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceUnary targetUnary row.right.right.right.right
  exact And.intro row.left
    (And.intro row.right.left
      (And.intro row.right.right.left
        (And.intro row.right.right.right.left
          (And.intro row.right.right.right.right ledgerUnary))))

end BEDC.Derived.FunctionalAnalysisUp
