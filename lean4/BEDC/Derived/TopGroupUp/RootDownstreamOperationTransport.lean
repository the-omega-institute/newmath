import BEDC.Derived.TopGroupUp.DownstreamLedgerObligation

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_root_downstream_operation_transport
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      productLedger' inverseLedger' product' inverse' neighborhood' operationLedger
      operationLedger' : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product product' ->
        hsame inverse inverse' ->
          hsame neighborhood neighborhood' ->
            Cont product neighborhood productLedger ->
              Cont product' neighborhood' productLedger' ->
                Cont inverse neighborhood inverseLedger ->
                  Cont inverse' neighborhood' inverseLedger' ->
                    Cont productLedger inverseLedger operationLedger ->
                      Cont productLedger' inverseLedger' operationLedger' ->
                        hsame operationLedger operationLedger' ∧
                          UnaryHistory operationLedger' ∧
                            hsame operationLedger (append productLedger inverseLedger) ∧
                              hsame operationLedger'
                                (append productLedger' inverseLedger') ∧
                                hsame provenance ledger := by
  intro package sameProduct sameInverse sameNeighborhood productLedgerCont productLedgerCont'
    inverseLedgerCont inverseLedgerCont' operationLedgerCont operationLedgerCont'
  have sourceFiber :=
    TopGroupRootSourceFiber_continuity_obligation package sameProduct sameInverse
      sameNeighborhood productLedgerCont productLedgerCont' inverseLedgerCont inverseLedgerCont'
  have sameOperation : hsame operationLedger operationLedger' :=
    cont_respects_hsame sourceFiber.left sourceFiber.right.left operationLedgerCont
      operationLedgerCont'
  have operationLedgerUnary' : UnaryHistory operationLedger' :=
    unary_cont_closed sourceFiber.right.right.left sourceFiber.right.right.right.left
      operationLedgerCont'
  exact And.intro sameOperation
      (And.intro operationLedgerUnary'
        (And.intro operationLedgerCont
          (And.intro operationLedgerCont'
          sourceFiber.right.right.right.right)))

end BEDC.Derived.TopGroupUp
