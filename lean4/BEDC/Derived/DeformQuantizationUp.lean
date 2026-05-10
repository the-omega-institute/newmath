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

theorem DeformQuantizationStarLedger_bracket_classifier_obligation
    {mu1 mu1op kappa pi mu1' mu1op' kappa' pi' : BHist} :
    Cont mu1 mu1op kappa ->
      Cont mu1' mu1op' kappa' ->
        hsame mu1 mu1' ->
          hsame mu1op mu1op' ->
            hsame kappa pi ->
              hsame kappa' pi' ->
                hsame kappa kappa' ∧ hsame pi pi' := by
  intro leftRow rightRow sameMu1 sameMu1op sameKappaPi sameKappaPi'
  have sameKappa : hsame kappa kappa' :=
    cont_respects_hsame sameMu1 sameMu1op leftRow rightRow
  have samePi : hsame pi pi' :=
    hsame_trans (hsame_symm sameKappaPi) (hsame_trans sameKappa sameKappaPi')
  exact And.intro sameKappa samePi

theorem DeformQuantizationStarLedger_carrier_obligation
    {muH mu0 mu1 mu1op kappa pi product provenance ledger : BHist} :
    UnaryHistory muH ->
      UnaryHistory mu0 ->
        UnaryHistory mu1 ->
          UnaryHistory mu1op ->
            Cont mu1 mu1op kappa ->
              hsame kappa pi ->
                Cont muH mu0 product ->
                  Cont product kappa provenance ->
                    Cont provenance pi ledger ->
                      UnaryHistory product ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
                        Cont mu1 mu1op kappa ∧ hsame kappa pi := by
  intro muHUnary mu0Unary mu1Unary mu1opUnary kappaRow kappaPi productRow
    provenanceRow ledgerRow
  have productUnary : UnaryHistory product :=
    unary_cont_closed muHUnary mu0Unary productRow
  have kappaUnary : UnaryHistory kappa :=
    unary_cont_closed mu1Unary mu1opUnary kappaRow
  have piUnary : UnaryHistory pi :=
    unary_transport kappaUnary kappaPi
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed productUnary kappaUnary provenanceRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed provenanceUnary piUnary ledgerRow
  exact
    ⟨productUnary, provenanceUnary, ledgerUnary, kappaRow, kappaPi⟩

end BEDC.Derived.DeformQuantizationUp
