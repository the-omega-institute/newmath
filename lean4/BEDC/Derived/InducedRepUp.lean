import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.InducedRepUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem InducedRepFrobeniusLedger_boundary
    {subgroup representation induction restriction frobenius unit counit provenance ledger :
      BHist} :
    UnaryHistory subgroup ->
      UnaryHistory representation ->
        UnaryHistory induction ->
          UnaryHistory restriction ->
            UnaryHistory unit ->
              Cont subgroup representation provenance ->
                Cont induction restriction frobenius ->
                  Cont frobenius unit counit ->
                    Cont provenance counit ledger ->
                      UnaryHistory provenance ∧ UnaryHistory frobenius ∧ UnaryHistory counit ∧
                        UnaryHistory ledger ∧ hsame provenance (append subgroup representation) ∧
                          hsame frobenius (append induction restriction) ∧
                            hsame counit (append frobenius unit) ∧
                              hsame ledger (append provenance counit) := by
  intro subgroupUnary representationUnary inductionUnary restrictionUnary unitUnary provenanceCont
    frobeniusCont counitCont ledgerCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed subgroupUnary representationUnary provenanceCont
  have frobeniusUnary : UnaryHistory frobenius :=
    unary_cont_closed inductionUnary restrictionUnary frobeniusCont
  have counitUnary : UnaryHistory counit :=
    unary_cont_closed frobeniusUnary unitUnary counitCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed provenanceUnary counitUnary ledgerCont
  exact And.intro provenanceUnary
    (And.intro frobeniusUnary
      (And.intro counitUnary
        (And.intro ledgerUnary
          (And.intro provenanceCont
            (And.intro frobeniusCont
              (And.intro counitCont ledgerCont))))))

end BEDC.Derived.InducedRepUp
