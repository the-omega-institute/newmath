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

def InducedRepContinuationLedgerSpine (start : BHist) : List BHist -> BHist -> Prop
  | [], final => hsame final start
  | row :: rows, final =>
      UnaryHistory row ∧
        exists next : BHist, Cont start row next ∧ InducedRepContinuationLedgerSpine next rows final

private theorem InducedRepContinuationLedgerSpine_normalized_cont_aux
    {start final : BHist} {rows : List BHist} :
    InducedRepContinuationLedgerSpine start rows final ->
      exists tail : BHist, UnaryHistory tail ∧ Cont start tail final := by
  intro spine
  induction rows generalizing start final with
  | nil =>
      exact Exists.intro BHist.Empty (And.intro unary_empty spine)
  | cons row rows ih =>
      cases spine with
      | intro rowUnary nextData =>
          cases nextData with
          | intro next nextRows =>
              cases nextRows with
              | intro rowCont tailSpine =>
                  have tailPack := ih tailSpine
                  cases tailPack with
                  | intro tail tailRows =>
                      have combinedUnary : UnaryHistory (append row tail) :=
                        unary_append_closed rowUnary tailRows.left
                      have combinedCont : Cont start (append row tail) final :=
                        hsame_trans tailRows.right
                          ((congrArg (fun h : BHist => append h tail) rowCont).trans
                            (append_assoc start row tail))
                      exact Exists.intro (append row tail) (And.intro combinedUnary combinedCont)

theorem InducedRepContinuationLedgerSpine_normalized_cont
    {provenance counit ledger final : BHist} {rows : List BHist} :
    InducedRepContinuationLedgerSpine ledger rows final ->
      hsame ledger (append provenance counit) ->
        exists tail : BHist, UnaryHistory tail ∧ Cont (append provenance counit) tail final := by
  intro spine ledgerNormalized
  have tailPack := InducedRepContinuationLedgerSpine_normalized_cont_aux spine
  cases tailPack with
  | intro tail tailRows =>
      have tailCont : Cont (append provenance counit) tail final :=
        hsame_trans tailRows.right (congrArg (fun h : BHist => append h tail) ledgerNormalized)
      exact Exists.intro tail (And.intro tailRows.left tailCont)

end BEDC.Derived.InducedRepUp
