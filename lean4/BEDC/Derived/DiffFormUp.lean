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

theorem DiffFormExteriorDerivative_degree_raise_ledger
    {degree probe tensor scalar antisym ledger targetDegree : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) targetDegree ->
            UnaryHistory degree ∧ UnaryHistory targetDegree ∧
              Cont degree (BHist.e1 BHist.Empty) targetDegree ∧ UnaryHistory tensor ∧
                UnaryHistory scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute targetRoute
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have targetUnary : UnaryHistory targetDegree :=
    unary_cont_closed degreeUnary (unary_e1_closed unary_empty) targetRoute
  exact ⟨coordinateRows.left, targetUnary, targetRoute, coordinateRows.right.right.left,
    coordinateRows.right.right.right.left⟩

def DiffFormExteriorDerivativeLedger
    (omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source :
      BHist) :
    Prop :=
  UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory d ∧ UnaryHistory dplus ∧
    Cont d (BHist.e1 BHist.Empty) dplus ∧ hsame probe probe' ∧ hsame tensor tensor' ∧
      hsame scalar scalar' ∧ UnaryHistory antisym ∧ UnaryHistory source

theorem DiffFormExteriorDerivativeLedger_degree_raise
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
      scalar' antisym source ->
      UnaryHistory d ∧ UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus := by
  intro ledger
  exact And.intro ledger.right.right.left
    (And.intro ledger.right.right.right.left ledger.right.right.right.right.left)

end BEDC.Derived.DiffFormUp
