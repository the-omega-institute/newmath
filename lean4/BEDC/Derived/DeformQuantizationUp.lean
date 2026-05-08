import BEDC.FKernel.Unary

namespace BEDC.Derived.DeformQuantizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DeformQuantizationStarLedger_first_order_bracket
    {mu0 mu1 mu1op kappa pi ledger : BHist} :
    UnaryHistory mu0 ->
      UnaryHistory mu1 ->
        UnaryHistory mu1op ->
          Cont mu1 mu1op kappa ->
            hsame kappa pi ->
              Cont kappa pi ledger ->
                UnaryHistory kappa ∧ UnaryHistory pi ∧ UnaryHistory ledger ∧ hsame kappa pi ∧
                  hsame ledger (append kappa pi) := by
  intro _mu0Unary mu1Unary mu1opUnary kappaRow kappaPi ledgerRow
  have kappaUnary : UnaryHistory kappa :=
    unary_cont_closed mu1Unary mu1opUnary kappaRow
  have piUnary : UnaryHistory pi :=
    unary_transport kappaUnary kappaPi
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed kappaUnary piUnary ledgerRow
  exact And.intro kappaUnary
    (And.intro piUnary
      (And.intro ledgerUnary
        (And.intro kappaPi ledgerRow)))

end BEDC.Derived.DeformQuantizationUp
