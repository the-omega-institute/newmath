import BEDC.FKernel.Unary

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DiffFormBHistCarrier_coordinate_ledger
    {degree probe tensor scalar antisym ledger : BHist}
    (degreeUnary : UnaryHistory degree) (probeUnary : UnaryHistory probe)
    (tensorRoute : Cont degree probe tensor)
    (antisymUnary : UnaryHistory antisym)
    (scalarRoute : Cont tensor antisym scalar)
    (ledgerRoute : hsame ledger (append degree (append probe (append tensor (append scalar antisym))))) :
    UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧ UnaryHistory scalar ∧
      hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) := by
  have tensorUnary : UnaryHistory tensor := by
    cases tensorRoute
    exact unary_append_closed degreeUnary probeUnary
  have scalarUnary : UnaryHistory scalar := by
    cases scalarRoute
    exact unary_append_closed tensorUnary antisymUnary
  exact ⟨degreeUnary, probeUnary, tensorUnary, scalarUnary, ledgerRoute⟩

theorem DiffFormWedge_degree_additivity_ledger {d e d' e' out out' : BHist} :
    UnaryHistory d -> UnaryHistory e -> Cont d e out -> hsame d d' -> hsame e e' ->
      Cont d' e' out' -> UnaryHistory out' ∧ hsame out out' := by
  intro unaryD unaryE wedgeRow sameD sameE transportedRow
  have unaryD' : UnaryHistory d' := unary_transport unaryD sameD
  have unaryE' : UnaryHistory e' := unary_transport unaryE sameE
  have sameOut : hsame out out' :=
    cont_respects_hsame sameD sameE wedgeRow transportedRow
  have unaryOut' : UnaryHistory out' :=
    unary_continuation_closure_up_to_hsame unaryD' unaryE' transportedRow (hsame_refl out')
  exact And.intro unaryOut' sameOut

theorem DiffFormExteriorDerivative_degree_shift_boundary {d dPlus dPlus' : BHist} :
    UnaryHistory d -> Cont d (BHist.e1 BHist.Empty) dPlus -> hsame dPlus dPlus' ->
      UnaryHistory (BHist.e1 BHist.Empty) ∧ UnaryHistory dPlus' := by
  intro unaryD shiftRow sameShift
  have successorUnary : UnaryHistory (BHist.e1 BHist.Empty) :=
    unary_e1_closed unary_empty
  have targetUnary : UnaryHistory dPlus' :=
    unary_continuation_closure_up_to_hsame unaryD successorUnary shiftRow sameShift
  exact And.intro successorUnary targetUnary

end BEDC.Derived.DiffFormUp
