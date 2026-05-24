import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSpaceUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CantorSpaceStreamNameBoolScope
    {schedule window boolLedger listSpine endpoint publicRead : BHist}
    {bundle : ProbeBundle BHist} :
    UnaryHistory schedule ->
      UnaryHistory window ->
        UnaryHistory boolLedger ->
          UnaryHistory listSpine ->
            Cont schedule window publicRead ->
              Cont boolLedger listSpine endpoint ->
                InBundle schedule bundle ->
                  InBundle boolLedger bundle ->
                    UnaryHistory publicRead ∧ UnaryHistory endpoint ∧
                      Cont schedule window publicRead ∧ Cont boolLedger listSpine endpoint ∧
                        InBundle schedule bundle ∧ InBundle boolLedger bundle := by
  intro scheduleUnary windowUnary boolLedgerUnary listSpineUnary publicReadCont endpointCont
    scheduleInBundle boolLedgerInBundle
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed scheduleUnary windowUnary publicReadCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed boolLedgerUnary listSpineUnary endpointCont
  exact And.intro publicReadUnary
    (And.intro endpointUnary
      (And.intro publicReadCont
        (And.intro endpointCont
          (And.intro scheduleInBundle boolLedgerInBundle))))

end BEDC.Derived.CantorSpaceUp
