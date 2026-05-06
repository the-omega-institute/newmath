import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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
    (ScalarClassifier : BHist -> BHist -> Prop) (probes : ProbeBundle BHist)
    (degree probe tensor scalar antisym ledger degree' probe' tensor' scalar' antisym'
      ledger' : BHist) : Prop :=
  InBundle probe probes ∧ InBundle probe' probes ∧ hsame degree degree' ∧
    hsame probe probe' ∧ hsame tensor tensor' ∧ ScalarClassifier scalar scalar' ∧
      hsame antisym antisym' ∧ hsame ledger ledger'

theorem DiffFormBHistClassifier_symmetry_obligation
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      DiffFormBHistClassifier ScalarClassifier probes d' p' t' s' a' l' d p t s a l := by
  intro rows
  exact And.intro rows.right.left
    (And.intro rows.left
      (And.intro (hsame_symm rows.right.right.left)
        (And.intro (hsame_symm rows.right.right.right.left)
          (And.intro (hsame_symm rows.right.right.right.right.left)
            (And.intro (NameCert.equiv_symm scalarCert rows.right.right.right.right.right.left)
              (And.intro (hsame_symm rows.right.right.right.right.right.right.left)
                (hsame_symm rows.right.right.right.right.right.right.right)))))))

theorem DiffFormBHistClassifier_transitivity_obligation
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' d'' p'' t'' s'' a'' l'' : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      DiffFormBHistClassifier ScalarClassifier probes d' p' t' s' a' l' d'' p'' t'' s'' a'' l'' ->
        DiffFormBHistClassifier ScalarClassifier probes d p t s a l d'' p'' t'' s'' a'' l'' := by
  intro leftRows rightRows
  exact And.intro leftRows.left
    (And.intro rightRows.right.left
      (And.intro (hsame_trans leftRows.right.right.left rightRows.right.right.left)
        (And.intro (hsame_trans leftRows.right.right.right.left rightRows.right.right.right.left)
          (And.intro
            (hsame_trans leftRows.right.right.right.right.left
              rightRows.right.right.right.right.left)
            (And.intro
              (NameCert.equiv_trans scalarCert leftRows.right.right.right.right.right.left
                rightRows.right.right.right.right.right.left)
              (And.intro
                (hsame_trans leftRows.right.right.right.right.right.right.left
                  rightRows.right.right.right.right.right.right.left)
                (hsame_trans leftRows.right.right.right.right.right.right.right
                  rightRows.right.right.right.right.right.right.right)))))))

end BEDC.Derived.DiffFormUp
