import BEDC.FKernel.Unary

namespace BEDC.Derived.MagmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem concrete_unary_history_magma_cont_laws :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    let mul : BHist -> BHist -> BHist := append
    (∀ {h k : BHist}, Carrier h -> Carrier k -> Carrier (mul h k) ∧ Cont h k (mul h k)) ∧
      (∀ {h h' k k' r r' : BHist}, Classifier h h' -> Classifier k k' ->
        Cont h k r -> Cont h' k' r' -> Classifier r r') := by
  dsimp
  constructor
  · intro h k unaryH unaryK
    exact And.intro (unary_append_closed unaryH unaryK) (cont_intro rfl)
  · intro h h' k k' r r' classifiedH classifiedK hcont hcont'
    have unaryR : UnaryHistory r :=
      unary_cont_closed classifiedH.left classifiedK.left hcont
    have unaryR' : UnaryHistory r' :=
      unary_cont_closed classifiedH.right.left classifiedK.right.left hcont'
    have sameR : hsame r r' :=
      cont_respects_hsame classifiedH.right.right classifiedK.right.right hcont hcont'
    exact And.intro unaryR (And.intro unaryR' sameR)

end BEDC.Derived.MagmaUp
