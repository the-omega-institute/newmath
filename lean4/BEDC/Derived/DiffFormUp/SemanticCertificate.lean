import BEDC.Derived.DiffFormUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert

theorem DiffFormBHistClassifier_obligation
    {ScalarClassifier : BHist -> BHist -> Prop} {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      hsame d d' ∧ hsame p p' ∧ hsame t t' ∧ ScalarClassifier s s' ∧
        hsame a a' ∧ hsame l l' ∧ InBundle p probes ∧ InBundle p' probes := by
  intro rows
  exact And.intro rows.right.right.left
    (And.intro rows.right.right.right.left
      (And.intro rows.right.right.right.right.left
        (And.intro rows.right.right.right.right.right.left
          (And.intro rows.right.right.right.right.right.right.left
            (And.intro rows.right.right.right.right.right.right.right
              (And.intro rows.left rows.right.left))))))

theorem DiffFormExteriorDerivativeLedger_semantic_name_certificate
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
        scalar' antisym source ->
      SemanticNameCert
        (fun raised : BHist =>
          DiffFormExteriorDerivativeLedger omega domega d raised probe probe' tensor tensor'
            scalar scalar' antisym source)
        (fun raised : BHist =>
          DiffFormExteriorDerivativeLedger omega domega d raised probe probe' tensor tensor'
            scalar scalar' antisym source)
        (fun raised : BHist =>
          DiffFormExteriorDerivativeLedger omega domega d raised probe probe' tensor tensor'
            scalar scalar' antisym source)
        hsame := by
  intro ledger
  exact {
    core := {
      carrier_inhabited := Exists.intro dplus ledger
      equiv_refl := by
        intro raised _source
        exact hsame_refl raised
      equiv_symm := by
        intro _raised _raised' sameRaised
        exact hsame_symm sameRaised
      equiv_trans := by
        intro _raised _raised' _raised'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro raised raised' sameRaised sourceLedger
        exact
          (DiffFormExteriorDerivativeLedger_hsame_transport_degree_raise
            (hsame_refl omega) (hsame_refl domega) (hsame_refl d) sameRaised
            (hsame_refl probe) (hsame_refl probe') (hsame_refl tensor) (hsame_refl tensor')
            (hsame_refl scalar) (hsame_refl scalar') (hsame_refl antisym)
            (hsame_refl source) sourceLedger).left
    }
    pattern_sound := by
      intro _raised source
      exact source
    ledger_sound := by
      intro _raised source
      exact source
  }

end BEDC.Derived.DiffFormUp
