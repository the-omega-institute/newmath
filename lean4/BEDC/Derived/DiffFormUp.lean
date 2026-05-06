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

def DiffFormBHistClassifier
    (degree probe tensor scalar antisym ledger degree' probe' tensor' scalar' antisym' ledger' :
      BHist) : Prop :=
  UnaryHistory degree ∧ UnaryHistory probe ∧ Cont degree probe tensor ∧
    UnaryHistory degree' ∧ UnaryHistory probe' ∧ Cont degree' probe' tensor' ∧
    hsame degree degree' ∧ hsame tensor tensor' ∧ hsame scalar scalar' ∧
    hsame antisym antisym' ∧ hsame ledger ledger'

theorem DiffFormBHistClassifier_symm
    {degree probe tensor scalar antisym ledger degree' probe' tensor' scalar' antisym' ledger' :
      BHist} :
    DiffFormBHistClassifier degree probe tensor scalar antisym ledger degree' probe' tensor'
      scalar' antisym' ledger' ->
      DiffFormBHistClassifier degree' probe' tensor' scalar' antisym' ledger' degree probe
        tensor scalar antisym ledger := by
  intro classified
  exact
    ⟨classified.right.right.right.left, classified.right.right.right.right.left,
      classified.right.right.right.right.right.left, classified.left, classified.right.left,
      classified.right.right.left, hsame_symm classified.right.right.right.right.right.right.left,
      hsame_symm classified.right.right.right.right.right.right.right.left,
      hsame_symm classified.right.right.right.right.right.right.right.right.left,
      hsame_symm classified.right.right.right.right.right.right.right.right.right.left,
      hsame_symm classified.right.right.right.right.right.right.right.right.right.right⟩

theorem DiffFormBHistClassifier_trans
    {d p t s a l e q u r b m f x v y c n : BHist} :
    DiffFormBHistClassifier d p t s a l e q u r b m ->
      DiffFormBHistClassifier e q u r b m f x v y c n ->
        DiffFormBHistClassifier d p t s a l f x v y c n := by
  intro left right
  exact
    ⟨left.left, left.right.left, left.right.right.left, right.right.right.right.left,
      right.right.right.right.right.left, right.right.right.right.right.right.left,
      hsame_trans left.right.right.right.right.right.right.left
        right.right.right.right.right.right.right.left,
      hsame_trans left.right.right.right.right.right.right.right.left
        right.right.right.right.right.right.right.right.left,
      hsame_trans left.right.right.right.right.right.right.right.right.left
        right.right.right.right.right.right.right.right.right.left,
      hsame_trans left.right.right.right.right.right.right.right.right.right.left
        right.right.right.right.right.right.right.right.right.right.left,
      hsame_trans left.right.right.right.right.right.right.right.right.right.right
        right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.DiffFormUp
