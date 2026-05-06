import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ManifoldSingleton_transition_ledger_exhaustion {chart domain source target ledger : BHist} :
    ManifoldSingletonCarrier chart -> Cont BHist.Empty chart domain ->
      Cont chart BHist.Empty source -> Cont chart BHist.Empty target -> Cont source target ledger ->
        hsame domain BHist.Empty ∧ hsame source BHist.Empty ∧ hsame target BHist.Empty ∧
          hsame ledger BHist.Empty ∧ UnaryHistory domain ∧ UnaryHistory source ∧
            UnaryHistory target ∧ UnaryHistory ledger := by
  intro chartCarrier domainReadback sourceReadback targetReadback ledgerRow
  have domainChart : hsame domain chart :=
    cont_left_unit_result domainReadback
  have domainEmpty : hsame domain BHist.Empty :=
    hsame_trans domainChart chartCarrier
  have sourceChart : hsame source chart :=
    cont_right_unit_result sourceReadback
  have sourceEmpty : hsame source BHist.Empty :=
    hsame_trans sourceChart chartCarrier
  have targetChart : hsame target chart :=
    cont_right_unit_result targetReadback
  have targetEmpty : hsame target BHist.Empty :=
    hsame_trans targetChart chartCarrier
  have ledgerEmpty : hsame ledger BHist.Empty :=
    cont_respects_hsame sourceEmpty targetEmpty ledgerRow (cont_left_unit BHist.Empty)
  have domainUnary : UnaryHistory domain :=
    unary_transport unary_empty (hsame_symm domainEmpty)
  have sourceUnary : UnaryHistory source :=
    unary_transport unary_empty (hsame_symm sourceEmpty)
  have targetUnary : UnaryHistory target :=
    unary_transport unary_empty (hsame_symm targetEmpty)
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport unary_empty (hsame_symm ledgerEmpty)
  exact And.intro domainEmpty
    (And.intro sourceEmpty
      (And.intro targetEmpty
        (And.intro ledgerEmpty
          (And.intro domainUnary
            (And.intro sourceUnary (And.intro targetUnary ledgerUnary))))))

end BEDC.Derived.ManifoldUp
