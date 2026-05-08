import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DirichletUnitUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def DirichletUnitHistoryCarrier
    (source unit inverse law unitLedger lawLedger provenance : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory unit ∧ UnaryHistory inverse ∧ UnaryHistory law ∧
    Cont source unit unitLedger ∧ Cont inverse law lawLedger ∧
      Cont unitLedger lawLedger provenance

theorem DirichletUnitHistoryCarrier_readback_obligation
    {source unit inverse law unitLedger lawLedger provenance : BHist} :
    DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger provenance ->
      UnaryHistory unitLedger ∧ UnaryHistory lawLedger ∧ UnaryHistory provenance ∧
        Cont source unit unitLedger ∧ Cont inverse law lawLedger ∧
          Cont unitLedger lawLedger provenance := by
  intro carrier
  have unitLedgerUnary : UnaryHistory unitLedger :=
    unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.right.left
  have lawLedgerUnary : UnaryHistory lawLedger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed unitLedgerUnary lawLedgerUnary carrier.right.right.right.right.right.right
  exact And.intro unitLedgerUnary
    (And.intro lawLedgerUnary
      (And.intro provenanceUnary
        (And.intro carrier.right.right.right.right.left
          (And.intro carrier.right.right.right.right.right.left
            carrier.right.right.right.right.right.right))))

end BEDC.Derived.DirichletUnitUp
