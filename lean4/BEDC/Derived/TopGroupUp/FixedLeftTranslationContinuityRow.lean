import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_fixed_left_translation_continuity_row
    {group topology product inverse neighborhood ledger provenance fixed endpoint translated
      translatedLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame fixed group -> hsame endpoint topology -> Cont fixed endpoint translated ->
        Cont translated neighborhood translatedLedger ->
          UnaryHistory fixed ∧ UnaryHistory endpoint ∧ UnaryHistory translated ∧
            UnaryHistory translatedLedger ∧ hsame translated (append fixed endpoint) ∧
              hsame translatedLedger (append translated neighborhood) ∧
                hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package sameFixed sameEndpoint translatedCont translatedLedgerCont
  have rows := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have scope := TopGroupRootThreshold_carrier_scope package
  have fixedUnary : UnaryHistory fixed :=
    unary_transport scope.right.right.left (hsame_symm sameFixed)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport scope.right.right.right.left (hsame_symm sameEndpoint)
  have translatedUnary : UnaryHistory translated :=
    unary_cont_closed fixedUnary endpointUnary translatedCont
  have translatedLedgerUnary : UnaryHistory translatedLedger :=
    unary_cont_closed translatedUnary rows.right.right.right.right.left translatedLedgerCont
  exact
    And.intro fixedUnary
      (And.intro endpointUnary
        (And.intro translatedUnary
          (And.intro translatedLedgerUnary
            (And.intro translatedCont
              (And.intro translatedLedgerCont
                (And.intro rows.right.right.right.right.right.right.left
                  rows.right.right.right.right.right.right.right))))))

end BEDC.Derived.TopGroupUp
