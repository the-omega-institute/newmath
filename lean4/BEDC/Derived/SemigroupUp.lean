import BEDC.Derived.MagmaUp

namespace BEDC.Derived.SemigroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

def ConcreteUnaryHistorySemigroupOppositeMul (h k : BHist) : BHist :=
  append k h

theorem concrete_unary_history_semigroup_cont_assoc_classifier {h k l hk kl left right : BHist} :
    UnaryHistory h -> UnaryHistory k -> UnaryHistory l ->
      Cont h k hk -> Cont hk l left -> Cont k l kl -> Cont h kl right ->
        (UnaryHistory left ∧ UnaryHistory right ∧ hsame left right) := by
  intro unaryH unaryK unaryL hhk hleft hkl hright
  have unaryHK : UnaryHistory hk :=
    unary_cont_closed unaryH unaryK hhk
  have unaryLeft : UnaryHistory left :=
    unary_cont_closed unaryHK unaryL hleft
  have unaryKL : UnaryHistory kl :=
    unary_cont_closed unaryK unaryL hkl
  have unaryRight : UnaryHistory right :=
    unary_cont_closed unaryH unaryKL hright
  exact And.intro unaryLeft
    (And.intro unaryRight (cont_assoc_hsame hhk hleft hkl hright))

theorem concrete_unary_history_semigroup_opposite_cont_assoc_classifier
    {h k l hk kl left right : BHist} :
    UnaryHistory h -> UnaryHistory k -> UnaryHistory l ->
      Cont k h hk -> Cont l hk left -> Cont l k kl -> Cont kl h right ->
        (UnaryHistory left ∧ UnaryHistory right ∧ hsame left right) := by
  intro unaryH unaryK unaryL hkh hlhk hlk hklh
  have unaryKH : UnaryHistory hk :=
    unary_cont_closed unaryK unaryH hkh
  have unaryLeft : UnaryHistory left :=
    unary_cont_closed unaryL unaryKH hlhk
  have unaryLK : UnaryHistory kl :=
    unary_cont_closed unaryL unaryK hlk
  have unaryRight : UnaryHistory right :=
    unary_cont_closed unaryLK unaryH hklh
  exact And.intro unaryLeft
    (And.intro unaryRight (hsame_symm (cont_assoc_hsame hlk hklh hkh hlhk)))

theorem ConcreteUnaryHistorySemigroup_semanticNameCert :
    let Carrier : BHist -> Prop := UnaryHistory
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    SemanticNameCert Carrier Carrier Carrier Classifier ∧
      (∀ {h k : BHist}, Carrier h -> Carrier k ->
        Carrier (append h k) ∧ Cont h k (append h k)) ∧
      (∀ {h h' k k' r r' : BHist}, Classifier h h' -> Classifier k k' ->
        Cont h k r -> Cont h' k' r' -> Classifier r r') ∧
      (∀ {h k l hk kl left right : BHist}, Carrier h -> Carrier k -> Carrier l ->
        Cont h k hk -> Cont hk l left -> Cont k l kl -> Cont h kl right ->
          Classifier left right) := by
  dsimp
  constructor
  · exact BEDC.Derived.MagmaUp.ConcreteUnaryHistoryMagma_semanticNameCert.left
  · constructor
    · exact BEDC.Derived.MagmaUp.ConcreteUnaryHistoryMagma_semanticNameCert.right.left
    · constructor
      · exact BEDC.Derived.MagmaUp.ConcreteUnaryHistoryMagma_semanticNameCert.right.right
      · intro h k l hk kl left right
        exact concrete_unary_history_semigroup_cont_assoc_classifier

theorem ConcreteUnaryHistorySemigroup_opposite_semanticNameCert :
    let Carrier : BHist -> Prop := UnaryHistory
    let OppMul : BHist -> BHist -> BHist := fun h k => append k h
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    SemanticNameCert Carrier Carrier Carrier Classifier ∧
      (∀ {h k : BHist}, Carrier h -> Carrier k ->
        Carrier (OppMul h k) ∧ Cont k h (OppMul h k)) ∧
      (∀ {h h' k k' r r' : BHist}, Classifier h h' -> Classifier k k' ->
        Cont k h r -> Cont k' h' r' -> Classifier r r') ∧
      (∀ {h k l hk kl left right : BHist}, Carrier h -> Carrier k -> Carrier l ->
        Cont k h hk -> Cont l k kl -> Cont l hk left -> Cont kl h right ->
          Classifier left right) := by
  dsimp
  constructor
  · exact BEDC.Derived.MagmaUp.ConcreteUnaryHistoryMagma_semanticNameCert.left
  · constructor
    · intro h k unaryH unaryK
      exact And.intro (unary_append_closed unaryK unaryH) (cont_intro rfl)
    · constructor
      · intro h h' k k' r r' classifiedH classifiedK kh k'h'
        have unaryR : UnaryHistory r :=
          unary_cont_closed classifiedK.left classifiedH.left kh
        have unaryR' : UnaryHistory r' :=
          unary_cont_closed classifiedK.right.left classifiedH.right.left k'h'
        have sameR : hsame r r' :=
          cont_respects_hsame classifiedK.right.right classifiedH.right.right kh k'h'
        exact And.intro unaryR (And.intro unaryR' sameR)
      · intro h k l hk kl left right unaryH unaryK unaryL kh lk lhk klh
        exact
          BEDC.Derived.MagmaUp.concrete_unary_history_magma_classifier_stability.right.left
            (concrete_unary_history_semigroup_cont_assoc_classifier
              unaryL unaryK unaryH lk klh kh lhk)

def ConcreteUnaryHistorySemigroup_oppMul (h k : BHist) : BHist :=
  append k h

end BEDC.Derived.SemigroupUp
