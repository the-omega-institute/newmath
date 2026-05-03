import BEDC.FKernel.Unary
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MagmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

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

theorem concrete_unary_history_magma_classifier_stability :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    (∀ {h : BHist}, Carrier h -> Classifier h h) ∧
      (∀ {h k : BHist}, Classifier h k -> Classifier k h) ∧
        (∀ {h k l : BHist}, Classifier h k -> Classifier k l -> Classifier h l) ∧
          (∀ {h k : BHist}, Classifier h k -> Carrier h ∧ Carrier k) := by
  dsimp
  constructor
  · intro h carrierH
    exact And.intro carrierH (And.intro carrierH (hsame_refl h))
  · constructor
    · intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    · constructor
      · intro h k l classifiedHK classifiedKL
        exact And.intro classifiedHK.left
          (And.intro classifiedKL.right.left
            (hsame_trans classifiedHK.right.right classifiedKL.right.right))
      · intro h k classified
        exact And.intro classified.left classified.right.left

theorem ConcreteUnaryHistoryMagma_semanticNameCert :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    SemanticNameCert Carrier Carrier Carrier Classifier ∧
      (∀ {h k : BHist}, Carrier h -> Carrier k ->
        Carrier (append h k) ∧ Cont h k (append h k)) ∧
      (∀ {h h' k k' r r' : BHist}, Classifier h h' -> Classifier k k' ->
        Cont h k r -> Cont h' k' r' -> Classifier r r') := by
  dsimp
  constructor
  · constructor
    · constructor
      · exact Exists.intro BHist.Empty unary_empty
      · intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      · intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      · intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      · intro h k classified _carrier
        exact classified.right.left
    · intro h source
      exact source
    · intro h source
      exact source
  · exact concrete_unary_history_magma_cont_laws

end BEDC.Derived.MagmaUp
