import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_pin_consumer_source_exactness [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger unit' vector'
      product' boundary' cliffordEndpoint' groupWord' spinEndpoint' ledger' fiberLedger
      actionLedger conjugationLedger consumerLedger finalLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      SpinGroupRootCarrier unit' vector' product' boundary' cliffordEndpoint' groupWord'
          spinEndpoint' ledger' bundle pkg ->
        Cont spinEndpoint spinEndpoint' fiberLedger ->
          Cont fiberLedger boundary actionLedger ->
            Cont actionLedger groupWord conjugationLedger ->
              Cont conjugationLedger BHist.Empty consumerLedger ->
                Cont consumerLedger BHist.Empty finalLedger ->
                  UnaryHistory finalLedger ∧ hsame finalLedger consumerLedger ∧
                    UnaryHistory consumerLedger ∧ hsame consumerLedger conjugationLedger ∧
                      hsame actionLedger (append fiberLedger boundary) ∧
                        PkgSig bundle ledger pkg := by
  intro carrier carrier' fiberCont actionCont conjugationCont consumerCont finalCont
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have sourceScope' := SpinGroupRootCarrier_source_scope carrier'
  have fiberUnary : UnaryHistory fiberLedger :=
    unary_cont_closed sourceScope.right.right.left sourceScope'.right.right.left fiberCont
  have actionUnary : UnaryHistory actionLedger :=
    unary_cont_closed fiberUnary carrier.left.right.right.left actionCont
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm sourceScope.right.left)
  have conjugationUnary : UnaryHistory conjugationLedger :=
    unary_cont_closed actionUnary groupUnary conjugationCont
  have consumerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed conjugationUnary unary_empty consumerCont
  have finalUnary : UnaryHistory finalLedger :=
    unary_cont_closed consumerUnary unary_empty finalCont
  exact And.intro finalUnary
    (And.intro (cont_right_unit_result finalCont)
      (And.intro consumerUnary
        (And.intro (cont_right_unit_result consumerCont)
          (And.intro actionCont sourceScope.right.right.right.right))))

end BEDC.Derived.SpinGroupUp
